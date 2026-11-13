/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.RCLike.Basic
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.HalfLine
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.RightEndpoint

/-!
# Backward endpoint bounds from the concavity method

The forward estimates of Levine's concavity method (`Concavity.RightEndpoint`,
`Concavity.HalfLine`) bound how long a positive mass `I` with momentum `P = I'` can satisfy

`(1 + a) P(t)² ≤ I(t) (P'(t) - b)`

after a time at which `P` is positive. The mirror-image statements hold backward in time: if
`P` is negative at `t₀`, the inequality cannot have held for long before `t₀`, and it cannot have
held on an entire past half-line. These are the versions needed for a solution that is known
to exist up to `t₀` and whose mass is decreasing there.

The proofs are by time reflection. Setting `Ĩ(t) = I(-t)` and `P̃(t) = -P(-t)` gives
`Ĩ' = P̃`, `P̃² = P²`, and `P̃'(t) = P'(-t)`, so the concavity inequality keeps exactly the same
form for `(Ĩ, P̃)` on the reflected interval, and the forward theorems apply verbatim. As in
the forward file, `I` and `P` are arbitrary real functions and the inequality is a hypothesis;
no PDE enters.

## Main results

* `riccati_horizon_lt_left_endpoint`: on `[T, t₀]` with `P(t₀) < 0`,
  `t₀ - (a (-P(t₀)) / I(t₀))⁻¹ < T`.
* `riccati_horizon_le_left_endpoint`: the non-strict version on `(T, t₀]`.
* `shifted_riccati_horizon_lt_left_endpoint`, `shifted_riccati_horizon_le_left_endpoint`:
  the same bounds restarted at `t₀ - δ` when only `P(t₀) ≤ 0` is known and `b > 0`.
* `not_concavity_inequality_on_Iic`: with `a, b > 0` the inequality cannot hold at every
  time `t ≤ t₀`.

## References

* H. A. Levine, "Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `P u_tt = -A u + F(u)`", *Trans. Amer. Math. Soc.* 192 (1974), 1-21, proof of
  Theorem I, (II-2)-(II-4).
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

open Set

namespace PDE.Solution.Singularity.FiniteTime.Concavity

private def reflectedMass (I : ℝ → ℝ) : ℝ → ℝ :=
  I ∘ Neg.neg

private def reflectedMomentum (P : ℝ → ℝ) : ℝ → ℝ :=
  (-P) ∘ Neg.neg

private theorem hasDerivAt_reflectedMass
    {I P : ℝ → ℝ} {t : ℝ}
    (hI : HasDerivAt I (P (-t)) (-t)) :
    HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
  simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, neg_one_smul] using
    hI.scomp t (hasDerivAt_neg t)

private theorem hasDerivAt_reflectedMomentum
    {P : ℝ → ℝ} {t : ℝ}
    (hP : DifferentiableAt ℝ P (-t)) :
    HasDerivAt (reflectedMomentum P) (deriv P (-t)) t := by
  simpa only [reflectedMomentum, Function.comp_apply, Pi.neg_apply,
    neg_one_smul, neg_neg] using
    hP.hasDerivAt.neg.scomp t (hasDerivAt_neg t)

/-- If the concavity inequality holds on `[T, t₀]` and `P(t₀) < 0`, then
the left endpoint lies strictly after the backward Riccati horizon

`t₀ - (a (-P(t₀) / I(t₀)))⁻¹ < T`.

This is `right_endpoint_lt_riccati_horizon` applied after reflecting time.
The reflected momentum is `-P(-t)`, so it is positive at the reflected
initial time. -/
theorem riccati_horizon_lt_left_endpoint
    {I P : ℝ → ℝ} {a b T t₀ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hI : ∀ t ∈ Icc T t₀, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Icc T t₀, DifferentiableAt ℝ P t)
    (hI₀ : 0 < I t₀) (hP₀ : P t₀ < 0)
    (hpos : ∀ t ∈ Icc T t₀, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo T t₀,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    t₀ - (a * (-P t₀ / I t₀))⁻¹ < T := by
  have hreflectedMass :
      ∀ t ∈ Icc (-t₀) (-T),
        HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
    intro t ht
    apply hasDerivAt_reflectedMass
    exact hI (-t) (by constructor <;> linarith [ht.1, ht.2])
  have hreflectedMomentum :
      ∀ t ∈ Icc (-t₀) (-T),
        DifferentiableAt ℝ (reflectedMomentum P) t := by
    intro t ht
    exact (hasDerivAt_reflectedMomentum
      (hP (-t) (by constructor <;> linarith [ht.1, ht.2]))).differentiableAt
  have hendpoint :=
    right_endpoint_lt_riccati_horizon
      (I := reflectedMass I) (P := reflectedMomentum P)
      (t₀ := -t₀) (T := -T) ha hb
      hreflectedMass hreflectedMomentum (by
        simpa only [reflectedMass, Function.comp_apply, neg_neg] using hI₀) (by
        simpa only [reflectedMomentum, Function.comp_apply, Pi.neg_apply,
          neg_neg] using neg_pos.mpr hP₀)
      (fun t ht ↦ by
        exact hpos (-t) (by constructor <;> linarith [ht.1, ht.2]))
      (fun t ht ↦ by
        have htime : -t ∈ Ioo T t₀ := by
          constructor <;> linarith [ht.1, ht.2]
        have horiginal := hconcavity (-t) htime
        have hderiv :=
          (hasDerivAt_reflectedMomentum
            (hP (-t) (Ioo_subset_Icc_self htime))).deriv
        rw [hderiv]
        simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
          Pi.neg_apply, neg_sq] using horiginal)
  simp only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, neg_neg] at hendpoint
  linarith

/-- On a half-open past lifespan `(T, t₀]`, negative momentum at `t₀`
gives the non-strict backward Riccati bound

`t₀ - (a (-P(t₀) / I(t₀)))⁻¹ ≤ T`.

Time reflection turns `(T, t₀]` into the forward interval `[-t₀, -T)`, so
this follows from `right_endpoint_le_riccati_horizon`. -/
theorem riccati_horizon_le_left_endpoint
    {I P : ℝ → ℝ} {a b T t₀ : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b)
    (hI : ∀ t ∈ Ioc T t₀, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Ioc T t₀, DifferentiableAt ℝ P t)
    (hI₀ : 0 < I t₀) (hP₀ : P t₀ < 0)
    (hpos : ∀ t ∈ Ioc T t₀, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo T t₀,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    t₀ - (a * (-P t₀ / I t₀))⁻¹ ≤ T := by
  have hreflectedMass :
      ∀ t ∈ Ico (-t₀) (-T),
        HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
    intro t ht
    apply hasDerivAt_reflectedMass
    exact hI (-t) (by constructor <;> linarith [ht.1, ht.2])
  have hreflectedMomentum :
      ∀ t ∈ Ico (-t₀) (-T),
        DifferentiableAt ℝ (reflectedMomentum P) t := by
    intro t ht
    exact (hasDerivAt_reflectedMomentum
      (hP (-t) (by constructor <;> linarith [ht.1, ht.2]))).differentiableAt
  have hendpoint :=
    right_endpoint_le_riccati_horizon
      (I := reflectedMass I) (P := reflectedMomentum P)
      (t₀ := -t₀) (T := -T) ha hb
      hreflectedMass hreflectedMomentum (by
        simpa only [reflectedMass, Function.comp_apply, neg_neg] using hI₀) (by
        simpa only [reflectedMomentum, Function.comp_apply, Pi.neg_apply,
          neg_neg] using neg_pos.mpr hP₀)
      (fun t ht ↦ by
        exact hpos (-t) (by constructor <;> linarith [ht.1, ht.2]))
      (fun t ht ↦ by
        have htime : -t ∈ Ioo T t₀ := by
          constructor <;> linarith [ht.1, ht.2]
        have horiginal := hconcavity (-t) htime
        have hderiv :=
          (hasDerivAt_reflectedMomentum
            (hP (-t) ⟨htime.1, htime.2.le⟩)).deriv
        rw [hderiv]
        simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
          Pi.neg_apply, neg_sq] using horiginal)
  simp only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, neg_neg] at hendpoint
  linarith

/-- If `P(t₀) ≤ 0`, positive forcing makes the momentum strictly negative
at every earlier shifted time `t₀ - δ`. On `[T, t₀]` this gives

`t₀ - δ - (a (-P(t₀ - δ) / I(t₀ - δ)))⁻¹ < T`

whenever `δ > 0` and `T ≤ t₀ - δ`. -/
theorem shifted_riccati_horizon_lt_left_endpoint
    {I P : ℝ → ℝ} {a b T t₀ δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hshift : T ≤ t₀ - δ)
    (hI : ∀ t ∈ Icc T t₀, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Icc T t₀, DifferentiableAt ℝ P t)
    (hP₀ : P t₀ ≤ 0)
    (hpos : ∀ t ∈ Icc T t₀, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo T t₀,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    t₀ - δ -
        (a * (-P (t₀ - δ) / I (t₀ - δ)))⁻¹ <
      T := by
  have hreflectedMass :
      ∀ t ∈ Icc (-t₀) (-T),
        HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
    intro t ht
    apply hasDerivAt_reflectedMass
    exact hI (-t) (by constructor <;> linarith [ht.1, ht.2])
  have hreflectedMomentum :
      ∀ t ∈ Icc (-t₀) (-T),
        DifferentiableAt ℝ (reflectedMomentum P) t := by
    intro t ht
    exact (hasDerivAt_reflectedMomentum
      (hP (-t) (by constructor <;> linarith [ht.1, ht.2]))).differentiableAt
  have hendpoint :=
    right_endpoint_lt_shifted_riccati_horizon
      (I := reflectedMass I) (P := reflectedMomentum P)
      (t₀ := -t₀) (T := -T) ha hb hδ (by linarith)
      hreflectedMass hreflectedMomentum
      (by
        simpa only [reflectedMomentum, Function.comp_apply, Pi.neg_apply,
          neg_neg] using neg_nonneg.mpr hP₀)
      (fun t ht ↦ by
        exact hpos (-t) (by constructor <;> linarith [ht.1, ht.2]))
      (fun t ht ↦ by
        have htime : -t ∈ Ioo T t₀ := by
          constructor <;> linarith [ht.1, ht.2]
        have horiginal := hconcavity (-t) htime
        have hderiv :=
          (hasDerivAt_reflectedMomentum
            (hP (-t) (Ioo_subset_Icc_self htime))).deriv
        rw [hderiv]
        simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
          Pi.neg_apply, neg_sq] using horiginal)
  have htime : -(-t₀ + δ) = t₀ - δ := by ring
  simp only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, htime] at hendpoint
  linarith

/-- On `(T, t₀]`, nonpositive momentum at `t₀` gives the shifted bound

`t₀ - δ - (a (-P(t₀ - δ) / I(t₀ - δ)))⁻¹ ≤ T`

whenever `δ > 0` and `T < t₀ - δ`. This is the maximal-past-lifespan
counterpart of `shifted_riccati_horizon_lt_left_endpoint`. -/
theorem shifted_riccati_horizon_le_left_endpoint
    {I P : ℝ → ℝ} {a b T t₀ δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hshift : T < t₀ - δ)
    (hI : ∀ t ∈ Ioc T t₀, HasDerivAt I (P t) t)
    (hP : ∀ t ∈ Ioc T t₀, DifferentiableAt ℝ P t)
    (hP₀ : P t₀ ≤ 0)
    (hpos : ∀ t ∈ Ioc T t₀, 0 < I t)
    (hconcavity : ∀ t ∈ Ioo T t₀,
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b)) :
    t₀ - δ -
        (a * (-P (t₀ - δ) / I (t₀ - δ)))⁻¹ ≤
      T := by
  have hreflectedMass :
      ∀ t ∈ Ico (-t₀) (-T),
        HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
    intro t ht
    apply hasDerivAt_reflectedMass
    exact hI (-t) (by constructor <;> linarith [ht.1, ht.2])
  have hreflectedMomentum :
      ∀ t ∈ Ico (-t₀) (-T),
        DifferentiableAt ℝ (reflectedMomentum P) t := by
    intro t ht
    exact (hasDerivAt_reflectedMomentum
      (hP (-t) (by constructor <;> linarith [ht.1, ht.2]))).differentiableAt
  have hendpoint :=
    right_endpoint_le_shifted_riccati_horizon
      (I := reflectedMass I) (P := reflectedMomentum P)
      (t₀ := -t₀) (T := -T) ha hb hδ (by linarith)
      hreflectedMass hreflectedMomentum
      (by
        simpa only [reflectedMomentum, Function.comp_apply, Pi.neg_apply,
          neg_neg] using neg_nonneg.mpr hP₀)
      (fun t ht ↦ by
        exact hpos (-t) (by constructor <;> linarith [ht.1, ht.2]))
      (fun t ht ↦ by
        have htime : -t ∈ Ioo T t₀ := by
          constructor <;> linarith [ht.1, ht.2]
        have horiginal := hconcavity (-t) htime
        have hderiv :=
          (hasDerivAt_reflectedMomentum
            (hP (-t) ⟨htime.1, htime.2.le⟩)).deriv
        rw [hderiv]
        simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
          Pi.neg_apply, neg_sq] using horiginal)
  have htime : -(-t₀ + δ) = t₀ - δ := by ring
  simp only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, htime] at hendpoint
  linarith

/-- A positive mass and its momentum cannot satisfy the concavity inequality

`(1 + a) P(t)² ≤ I(t) (P'(t) - b)`

at every past time when `a > 0` and `b > 0`.

This is the time-reflected counterpart of
`not_concavity_inequality_on_Ici`. Under the change of variables `t ↦ -t`,
the reflected mass is `I(-t)` and its momentum is `-P(-t)`. The square of the
momentum is unchanged, while the derivative of the reflected momentum is
`P'(-t)`, so the same scalar inequality holds on a future half-line. -/
theorem not_concavity_inequality_on_Iic
    {I P : ℝ → ℝ} {a b t₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hI : ∀ t, t ≤ t₀ → HasDerivAt I (P t) t)
    (hP : ∀ t, t ≤ t₀ → DifferentiableAt ℝ P t)
    (hpos : ∀ t, t ≤ t₀ → 0 < I t) :
    ¬ ∀ t, t ≤ t₀ →
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b) := by
  intro hconcavity
  have hreflectedMass :
      ∀ t, -t₀ ≤ t →
        HasDerivAt (reflectedMass I) (reflectedMomentum P t) t := by
    intro t ht
    have htime : -t ≤ t₀ := by linarith
    exact hasDerivAt_reflectedMass (hI (-t) htime)
  have hreflectedMomentum :
      ∀ t, -t₀ ≤ t →
        HasDerivAt (reflectedMomentum P) (deriv P (-t)) t := by
    intro t ht
    have htime : -t ≤ t₀ := by linarith
    exact hasDerivAt_reflectedMomentum (hP (-t) htime)
  apply
    (not_concavity_inequality_on_Ici
      (I := reflectedMass I) (P := reflectedMomentum P)
      (t₀ := -t₀) ha hb hreflectedMass
      (fun t ht ↦ (hreflectedMomentum t ht).differentiableAt)
      (fun t ht ↦ by
        have htime : -t ≤ t₀ := by linarith
        exact hpos (-t) htime))
  intro t ht
  have htime : -t ≤ t₀ := by linarith
  have horiginal := hconcavity (-t) htime
  have hderiv :
      deriv (reflectedMomentum P) t = deriv P (-t) :=
    (hreflectedMomentum t ht).deriv
  rw [hderiv]
  simpa only [reflectedMass, reflectedMomentum, Function.comp_apply,
    Pi.neg_apply, neg_sq] using horiginal

end PDE.Solution.Singularity.FiniteTime.Concavity
