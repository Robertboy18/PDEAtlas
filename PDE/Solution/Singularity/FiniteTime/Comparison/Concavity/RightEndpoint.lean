/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.Basic
import PDE.Solution.Singularity.FiniteTime.Comparison.QuadraticGrowth

/-!
# Forward endpoint bounds from the concavity method

Levine's concavity method proves finite-time blowup for an evolution equation by showing that
some positive functional `I(t)` of the solution (typically a weighted `L²` mass) satisfies,
with `P = I'`, the differential inequality

`(1 + a) P(t)² ≤ I(t) (P'(t) - b)`,   `a > 0`, `b ≥ 0`.

Equivalently `I I'' - (1 + a) (I')² ≥ b I`, which makes `I^{-a}` concave; a positive
concave function with negative initial slope reaches zero in finite time, so `I` cannot stay
finite. This is the step from (II-3) to (II-4) in Levine's proof of Theorem I (1974), with
`F = I` and `α = a`, where `F` becomes infinite before `F(0) / (α F'(0))`. The quantitative
form used here goes through the logarithmic derivative `y = P / I`: the inequality gives the
Riccati bound `y' ≥ a y²`, and if `y(t₀) > 0` then `y` becomes infinite no later than
`t₀ + 1 / (a y(t₀))`. A solution that exists on `[t₀, T]` therefore forces
`T < t₀ + (a P(t₀) / I(t₀))⁻¹`.

Every statement concerns two real functions `I, P` on an interval. The
analytic content of the method, that the mass of a PDE solution satisfies the concavity
inequality, enters only as the hypothesis `hconcavity`. The negative-energy nonlinear wave
argument in `PDE.Hyperbolic.NonlinearWave.NegativeEnergy` proves it for one model.

## Main results

* `right_endpoint_lt_riccati_horizon`: on a closed interval `[t₀, T]` with `P(t₀) > 0`,
  `T < t₀ + (a P(t₀) / I(t₀))⁻¹`.
* `right_endpoint_le_riccati_horizon`: the non-strict version on `[t₀, T)`, the form suited to
  a maximal existence interval.
* `momentum_pos_at_add`: with positive forcing `b > 0`, `P' ≥ b`, so `P` becomes strictly
  positive after any waiting time `δ > 0` even when `P(t₀) = 0`.
* `right_endpoint_lt_shifted_riccati_horizon`, `right_endpoint_le_shifted_riccati_horizon`:
  the endpoint bounds restarted at `t₀ + δ`, for a nonnegative initial momentum.

## Implementation notes

The forcing constant `b` may be zero in the endpoint bounds; strict positivity is used only
to create a time at which the momentum is positive. The derivative hypotheses are pointwise
(`HasDerivAt I (P t) t` and differentiability of `P`), and the concavity inequality is only
required on the open interval, since the argument is a mean-value comparison for `y = P / I`
(`QuadraticGrowth.right_endpoint_lt_riccati_horizon`).

## References

* H. A. Levine, "Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `P u_tt = -A u + F(u)`", *Trans. Amer. Math. Soc.* 192 (1974), 1-21, proof of
  Theorem I, (II-2)-(II-4).
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
* H. A. Levine, "Some nonexistence and instability theorems for solutions of formally parabolic
  equations of the form `P u_t = -A u + F(u)`", *Arch. Rational Mech. Anal.* 51 (1973),
  371-386.
  <https://doi.org/10.1007/BF00263041>
-/

@[expose] public section

open Set

namespace PDE.Solution.Singularity.FiniteTime.Concavity

/-- If the concavity inequality holds on `[t₀, T]` and `P(t₀) > 0`, then
`T` lies strictly before the Riccati horizon of the logarithmic derivative
`P / I`.

The forcing coefficient `b` may vanish in this endpoint form. Its strict
positivity is only needed below to produce a time at which `I'` is positive. -/
theorem right_endpoint_lt_riccati_horizon
    {I P : ℝ → ℝ} {a b t₀ T : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hI : ∀ t ∈ Icc t₀ T, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Icc t₀ T, DifferentiableAt ℝ P t)
    (hI₀ : 0 < I t₀) (hP₀ : 0 < P t₀)
    (hpos : ∀ t ∈ Icc t₀ T, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo t₀ T,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    T < t₀ + (a * (P t₀ / I t₀))⁻¹ := by
  let y : ℝ → ℝ := fun t ↦ P t / I t
  have hy₀ : 0 < y t₀ := div_pos hP₀ hI₀
  have hI_cont : ContinuousOn I (Icc t₀ T) :=
    fun t ht ↦ (hI t ht).continuousAt.continuousWithinAt
  have hP_cont : ContinuousOn P (Icc t₀ T) :=
    fun t ht ↦ (hP t ht).continuousAt.continuousWithinAt
  have hy_cont : ContinuousOn y (Icc t₀ T) := by
    exact hP_cont.div hI_cont fun t ht ↦ (hpos t ht).ne'
  have hy_diff : DifferentiableOn ℝ y (Ioo t₀ T) := by
    intro t ht
    have ht' : t ∈ Icc t₀ T := Ioo_subset_Icc_self ht
    exact ((hP t ht').div (hI t ht').differentiableAt
      (hpos t ht').ne').differentiableWithinAt
  have hy_growth : ∀ t ∈ Ioo t₀ T, a * y t ^ 2 ≤ deriv y t := by
    intro t ht
    have ht' : t ∈ Icc t₀ T := Ioo_subset_Icc_self ht
    exact mul_sq_le_deriv_momentum_div_mass hb (hI t ht') (hP t ht')
      (hpos t ht') (hconcavity t ht)
  exact QuadraticGrowth.right_endpoint_lt_riccati_horizon
    ha hy₀ hy_cont hy_diff hy_growth

/-- If the concavity inequality holds on the half-open interval `[t₀, T)`,
then `T` is at most the Riccati horizon determined by `P(t₀) / I(t₀)`.

This is the endpoint form suited to maximal existence intervals. If the
horizon were strictly before `T`, an intermediate closed endpoint would
contradict `right_endpoint_lt_riccati_horizon`. -/
theorem right_endpoint_le_riccati_horizon
    {I P : ℝ → ℝ} {a b t₀ T : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hI : ∀ t ∈ Ico t₀ T, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Ico t₀ T, DifferentiableAt ℝ P t)
    (hI₀ : 0 < I t₀) (hP₀ : 0 < P t₀)
    (hpos : ∀ t ∈ Ico t₀ T, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo t₀ T,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    T ≤ t₀ + (a * (P t₀ / I t₀))⁻¹ := by
  let horizon := t₀ + (a * (P t₀ / I t₀))⁻¹
  have ht₀Horizon : t₀ < horizon := by
    exact lt_add_of_pos_right t₀
      (inv_pos.mpr (mul_pos ha (div_pos hP₀ hI₀)))
  change T ≤ horizon
  by_contra hbound
  have hHorizonT : horizon < T := lt_of_not_ge hbound
  let S := (horizon + T) / 2
  have hHorizonS : horizon < S := by
    dsimp only [S]
    linarith
  have hST : S < T := by
    dsimp only [S]
    linarith
  have hclosedBound :=
    right_endpoint_lt_riccati_horizon
      (I := I) (P := P) (a := a) (b := b) (t₀ := t₀) (T := S)
      ha hb
      (fun t ht ↦ hI t ⟨ht.1, ht.2.trans_lt hST⟩)
      (fun t ht ↦ hP t ⟨ht.1, ht.2.trans_lt hST⟩)
      hI₀ hP₀
      (fun t ht ↦ hpos t ⟨ht.1, ht.2.trans_lt hST⟩)
      (fun t ht ↦ hconcavity t ⟨ht.1, ht.2.trans hST⟩)
  change S < horizon at hclosedBound
  exact (not_lt_of_ge hHorizonS.le) hclosedBound

/-- Positive forcing makes the momentum strictly positive after every
positive time increment, provided the concavity inequality holds in between.

More precisely, `P' ≥ b` on `(t₀, t₀ + δ)`, so

`P(t₀ + δ) - P(t₀) ≥ b δ > 0`.

This lemma isolates the initial waiting-time step needed when the concavity
method starts with `P(t₀) = 0`. -/
theorem momentum_pos_at_add
    {I P : ℝ → ℝ} {a b t₀ δ : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hδ : 0 < δ)
    (hP : ∀ t ∈ Icc t₀ (t₀ + δ), DifferentiableAt ℝ P t)
    (hP₀ : 0 ≤ P t₀)
    (hpos : ∀ t ∈ Icc t₀ (t₀ + δ), 0 < I t)
    (hconcavity : ∀ t ∈ Ioo t₀ (t₀ + δ),
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    0 < P (t₀ + δ) := by
  have ht₀t₁ : t₀ < t₀ + δ := lt_add_of_pos_right t₀ hδ
  have hP_cont : ContinuousOn P (Icc t₀ (t₀ + δ)) :=
    fun t ht ↦ (hP t ht).continuousAt.continuousWithinAt
  have hP_diff : DifferentiableOn ℝ P (interior (Icc t₀ (t₀ + δ))) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hP t (Ioo_subset_Icc_self ht)).differentiableWithinAt
  have hsecond : ∀ t ∈ interior (Icc t₀ (t₀ + δ)), b ≤ deriv P t := by
    intro t ht
    rw [interior_Icc] at ht
    exact le_momentum_deriv_of_concavity ha
      (hpos t (Ioo_subset_Icc_self ht)) (hconcavity t ht)
  have hmomentum_growth :
      b * ((t₀ + δ) - t₀) ≤ P (t₀ + δ) - P t₀ := by
    exact (convex_Icc t₀ (t₀ + δ)).mul_sub_le_image_sub_of_le_deriv
      hP_cont hP_diff hsecond
      t₀ (left_mem_Icc.mpr ht₀t₁.le)
      (t₀ + δ) (right_mem_Icc.mpr ht₀t₁.le) ht₀t₁.le
  nlinarith

/-- If the concavity inequality has strictly positive forcing and
`P(t₀) ≥ 0`, wait for any positive time `δ` and apply the Riccati estimate
there:

`T < t₀ + δ + (a P(t₀ + δ) / I(t₀ + δ))⁻¹`.

The hypothesis `t₀ + δ ≤ T` says that the chosen waiting time lies in the
available interval. The preceding lemma proves that the logarithmic derivative
at this shifted base time is strictly positive. -/
theorem right_endpoint_lt_shifted_riccati_horizon
    {I P : ℝ → ℝ} {a b t₀ T δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hshift : t₀ + δ ≤ T)
    (hI : ∀ t ∈ Icc t₀ T, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Icc t₀ T, DifferentiableAt ℝ P t)
    (hP₀ : 0 ≤ P t₀)
    (hpos : ∀ t ∈ Icc t₀ T, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo t₀ T,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    T <
      t₀ + δ +
        (a * (P (t₀ + δ) / I (t₀ + δ)))⁻¹ := by
  have ht₀shift : t₀ < t₀ + δ := lt_add_of_pos_right t₀ hδ
  have hPShift : 0 < P (t₀ + δ) := by
    apply momentum_pos_at_add ha.le hb hδ
      (fun t ht ↦ hP t ⟨ht.1, ht.2.trans hshift⟩) hP₀
    · intro t ht
      exact hpos t ⟨ht.1, ht.2.trans hshift⟩
    · intro t ht
      exact hconcavity t ⟨ht.1, ht.2.trans_le hshift⟩
  apply right_endpoint_lt_riccati_horizon
    (I := I) (P := P) (t₀ := t₀ + δ) ha hb.le
  · intro t ht
    exact hI t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · intro t ht
    exact hP t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · exact hpos (t₀ + δ) ⟨ht₀shift.le, hshift⟩
  · exact hPShift
  · intro t ht
    exact hpos t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · intro t ht
    exact hconcavity t ⟨ht₀shift.trans ht.1, ht.2⟩

/-- On a half-open interval, a nonnegative initial momentum and positive
forcing give the shifted non-strict Riccati lifespan bound

`T ≤ t₀ + δ + (a P(t₀ + δ) / I(t₀ + δ))⁻¹`.

The strict inclusion `t₀ + δ < T` places the shifted base time inside the
available interval. Positive forcing makes the momentum strictly positive
there, after which `right_endpoint_le_riccati_horizon` applies. -/
theorem right_endpoint_le_shifted_riccati_horizon
    {I P : ℝ → ℝ} {a b t₀ T δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hshift : t₀ + δ < T)
    (hI : ∀ t ∈ Ico t₀ T, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Ico t₀ T, DifferentiableAt ℝ P t)
    (hP₀ : 0 ≤ P t₀)
    (hpos : ∀ t ∈ Ico t₀ T, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo t₀ T,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    T ≤
      t₀ + δ +
        (a * (P (t₀ + δ) / I (t₀ + δ)))⁻¹ := by
  have ht₀shift : t₀ < t₀ + δ := lt_add_of_pos_right t₀ hδ
  have hPShift : 0 < P (t₀ + δ) := by
    apply momentum_pos_at_add ha.le hb hδ
      (fun t ht ↦ hP t ⟨ht.1, ht.2.trans_lt hshift⟩) hP₀
    · intro t ht
      exact hpos t ⟨ht.1, ht.2.trans_lt hshift⟩
    · intro t ht
      exact hconcavity t ⟨ht.1, ht.2.trans hshift⟩
  apply right_endpoint_le_riccati_horizon
    (I := I) (P := P) (t₀ := t₀ + δ) ha hb.le
  · intro t ht
    exact hI t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · intro t ht
    exact hP t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · exact hpos (t₀ + δ) ⟨ht₀shift.le, hshift⟩
  · exact hPShift
  · intro t ht
    exact hpos t ⟨ht₀shift.le.trans ht.1, ht.2⟩
  · intro t ht
    exact hconcavity t ⟨ht₀shift.trans ht.1, ht.2⟩

end PDE.Solution.Singularity.FiniteTime.Concavity
