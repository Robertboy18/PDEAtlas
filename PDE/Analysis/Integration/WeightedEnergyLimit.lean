/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoffBounds
public import PDE.Analysis.Integration.WeightedEnergy
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Product
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Weighted energy bounds for weights without compact support

The weighted energy identity `integral_mul_similarityPairing` pairs the operator
`c v - ½ x·∇v + W·∇v - Δv` with `ψ v` for a compactly supported weight `ψ`. The weights of a
decay estimate, such as a bounded version of `|x|²`, are not compactly supported. This module
passes from the cutoff weights `χ_R ω` to `ω` itself, once for every weight: for a `C²` field
`v`, a bounded divergence-free `C¹` drift `W` and a nonnegative `C²` weight `ω` with

`ω |∇v|²`, `ω |v|²`, `|∇ω| (1 + |x|) |v|²` and `|Δω| |v|²` integrable,

the cutoff pairings converge to the integral of the energy density of `ω` as `R → ∞`, and a
bound `K + C/R` on the cutoff pairings gives the bound `K` for `ω`. Hou, Wang and Yang take this
limit in their weighted estimates, where they test the equation with `χ_R φ_L U` and let
`R → ∞`.

## Main results

* `exists_norm_fderiv_radialCutoff_le`: `|∇χ_R| ≤ B/R` for all radii, in every dimension.
* `integrable_energyDensity_of_integrable`: under the four integrability conditions the energy
  density of `ω` is integrable.
* `abs_energyDensity_radialCutoff_mul_le`: the energy densities of the weights `χ_R ω`, `R ≥ 1`,
  have an integrable majorant that does not depend on `R`.
* `tendsto_integral_radialCutoff_mul_similarityPairing`: `∫ χ_R ω · similarityPairing` tends to
  `∫ energyDensity ω` along `R = k + 1`.
* `integral_energyDensity_le_of_forall_radialCutoff`: if `∫ χ_R ω · similarityPairing ≤ K + C/R`
  for every `R ≥ 1`, then `∫ energyDensity ω ≤ K`.
* `tendsto_integral_radialCutoff_mul`: `∫ χ_R f → ∫ f` for every integrable `f`.

## How it works

For each `R` the identity holds with `ψ = χ_R ω`. Near a fixed point the cutoff `χ_R` is
identically one as soon as `R` is large, so the energy density of `χ_R ω` is eventually the
energy density of `ω` at that point. The densities are dominated uniformly in `R ≥ 1`: the
derivatives of `χ_R` are `O(1/R)` and `O(1/R²)` (`exists_abs_partialDeriv_radialCutoff_le`,
`exists_abs_laplacian_radialCutoff_le`), and where `∇χ_R ≠ 0` one has `|x| ≤ 2R`, so
`|x·∇χ_R|` is bounded. Dominated convergence gives the limit, and a bound on the pairings that is
uniform in `R` passes to the limit.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, the weighted
  estimates in the proof of Proposition 4. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology

namespace PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The gradient of the radial cutoff of radius `R` is `O(1/R)`, uniformly in the point. -/
theorem exists_norm_fderiv_radialCutoff_le (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      ‖fderiv ℝ (radialCutoff R) x‖ ≤ B * R⁻¹ := by
  choose B hB0 hB using fun i : Fin n ↦ exists_abs_partialDeriv_radialCutoff_le (n := n) i
  refine ⟨∑ i, B i, Finset.sum_nonneg fun i _ ↦ hB0 i, fun R hR x ↦ ?_⟩
  calc ‖fderiv ℝ (radialCutoff R) x‖ ≤ ∑ i, ‖∂[i] (radialCutoff R) x‖ :=
        norm_fderiv_le_sum_norm_partialDeriv _ x
    _ ≤ ∑ i, B i * R⁻¹ := Finset.sum_le_sum fun i _ ↦ by
        rw [Real.norm_eq_abs]
        exact hB i R hR x
    _ = (∑ i, B i) * R⁻¹ := by rw [Finset.sum_mul]

/-- Under the four integrability conditions on the weight `ω`, with a bounded continuous drift,
the energy density of `ω` is integrable. -/
theorem integrable_energyDensity_of_integrable {v : ℝ^n → E} {W : ℝ^n → ℝ^n} {ω : ℝ^n → ℝ}
    {M : ℝ} (hv : ContDiff ℝ 2 v) (hW : Continuous W) (hWb : ∀ x, ‖W x‖ ≤ M)
    (hω : ContDiff ℝ 2 ω)
    (h₁ : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ω x * ‖v x‖ ^ 2)
    (h₃ : Integrable fun x ↦ ‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2)
    (h₄ : Integrable fun x ↦ |laplacian ω x| * ‖v x‖ ^ 2) (c : ℝ) :
    Integrable (energyDensity c v W ω) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hWb 0)
  refine Integrable.mono' (g := fun x ↦ |ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2| +
      |c + n / 4| * |ω x * ‖v x‖ ^ 2| +
      (1 / 4 + M / 2) * (‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2) +
      (1 / 2 : ℝ) * (|laplacian ω x| * ‖v x‖ ^ 2))
    (((h₁.abs.add (h₂.abs.const_mul _)).add (h₃.const_mul _)).add (h₄.const_mul _))
    (continuous_energyDensity hv hW hω c).aestronglyMeasurable (.of_forall fun x ↦ ?_)
  have hq0 : 0 ≤ ‖v x‖ ^ 2 := by positivity
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hd0 : 0 ≤ ‖fderiv ℝ ω x‖ := norm_nonneg _
  have h1 : |fderiv ℝ ω x x| ≤ ‖fderiv ℝ ω x‖ * ‖x‖ := (fderiv ℝ ω x).le_opNorm x
  have h2 : |fderiv ℝ ω x (W x)| ≤ ‖fderiv ℝ ω x‖ * M :=
    ((fderiv ℝ ω x).le_opNorm (W x)).trans (mul_le_mul_of_nonneg_left (hWb x) hd0)
  have hT : |(c + n / 4) * ω x + (1 / 4 : ℝ) * fderiv ℝ ω x x -
      (1 / 2 : ℝ) * fderiv ℝ ω x (W x) - (1 / 2 : ℝ) * laplacian ω x| ≤
      |c + n / 4| * |ω x| + (1 / 4 + M / 2) * (‖fderiv ℝ ω x‖ * (1 + ‖x‖)) +
        (1 / 2 : ℝ) * |laplacian ω x| := by
    have e0 := abs_le.mp (le_of_eq (abs_mul (c + n / 4) (ω x)))
    have e1 := abs_le.mp h1
    have e2 := abs_le.mp h2
    have e3 := abs_le.mp (le_refl |laplacian ω x|)
    have p := mul_nonneg hM (mul_nonneg hd0 hx0)
    rw [abs_le]
    constructor <;> nlinarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, p, hd0]
  have habs : ∀ a b : ℝ, 0 ≤ b → |a * b| = |a| * b := fun a b hb ↦ by
    rw [abs_mul, abs_of_nonneg hb]
  have h₅ := mul_le_mul_of_nonneg_right hT hq0
  rw [Real.norm_eq_abs, energyDensity]
  refine (abs_add_le _ _).trans ?_
  rw [habs _ _ hq0, habs (ω x) _ hq0]
  linarith

/-- The energy density of a cutoff weight `χ_R ω`, `R ≥ 1`, is dominated by a combination of
`ω |∇v|²`, `ω |v|²`, `|∇ω| (1 + |x|) |v|²` and `|Δω| |v|²` with constants that do not depend on
`R`. Here `B₁` and `B₂` bound the first and second derivatives of the cutoff and `M` bounds the
drift. -/
theorem abs_energyDensity_radialCutoff_mul_le {v : ℝ^n → E} {W : ℝ^n → ℝ^n} {ω : ℝ^n → ℝ}
    {c M B₁ B₂ : ℝ} (hWb : ∀ x, ‖W x‖ ≤ M) (hω : ContDiff ℝ 2 ω) (hω0 : ∀ x, 0 ≤ ω x)
    (hB₁0 : 0 ≤ B₁) (hB₁ : ∀ R : ℝ, 0 < R → ∀ x : ℝ^n, ‖fderiv ℝ (radialCutoff R) x‖ ≤ B₁ * R⁻¹)
    (hB₂0 : 0 ≤ B₂)
    (hB₂ : ∀ R : ℝ, 0 < R → ∀ x : ℝ^n, |laplacian (radialCutoff R) x| ≤ B₂ * R⁻¹ ^ 2)
    {R : ℝ} (hR : 1 ≤ R) (x : ℝ^n) :
    |energyDensity c v W (fun y ↦ radialCutoff R y * ω y) x| ≤
      ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
        (|c + n / 4| + B₁ / 2 + B₁ * M / 2 + B₂ / 2) * (ω x * ‖v x‖ ^ 2) +
        (1 / 4 + M / 2 + n * B₁) * (‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2) +
        (1 / 2 : ℝ) * (|laplacian ω x| * ‖v x‖ ^ 2) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hWb 0)
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hR1 : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hRpos.le
  have hχc : ContDiff ℝ 2 (radialCutoff (n := n) R) := (radialCutoff_contDiff R).of_le (by simp)
  obtain ⟨hχ0, hχ1⟩ := radialCutoff_mem_Icc (n := n) R x
  have hD0 : 0 ≤ ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 := Finset.sum_nonneg fun i _ ↦ by positivity
  have hq0 : 0 ≤ ‖v x‖ ^ 2 := by positivity
  have hdω0 : 0 ≤ ‖fderiv ℝ ω x‖ := norm_nonneg _
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  -- The weight and its derivatives.
  have hψabs : |radialCutoff R x * ω x| ≤ ω x := by
    rw [abs_mul, abs_of_nonneg hχ0, abs_of_nonneg (hω0 x)]
    exact mul_le_of_le_one_left (hω0 x) hχ1
  have hfd : fderiv ℝ (fun y ↦ radialCutoff R y * ω y) x =
      radialCutoff R x • fderiv ℝ ω x + ω x • fderiv ℝ (radialCutoff R) x :=
    fderiv_fun_mul (hχc.differentiable (by norm_num) x) (hω.differentiable (by norm_num) x)
  have hDχ : ‖fderiv ℝ (radialCutoff R) x‖ ≤ B₁ * R⁻¹ := hB₁ R hRpos x
  have hDχ1 : ‖fderiv ℝ (radialCutoff R) x‖ ≤ B₁ := hDχ.trans (mul_le_of_le_one_right hB₁0 hR1)
  have hDχx : ‖fderiv ℝ (radialCutoff R) x‖ * ‖x‖ ≤ 2 * B₁ := by
    by_cases hxR : ‖x‖ ≤ 2 * R
    · calc ‖fderiv ℝ (radialCutoff R) x‖ * ‖x‖ ≤ B₁ * R⁻¹ * (2 * R) :=
            mul_le_mul hDχ hxR hx0 (mul_nonneg hB₁0 hRinv)
        _ = 2 * B₁ := by
            have hRne : R ≠ 0 := hRpos.ne'
            field_simp
    · have hnot : x ∉ tsupport (radialCutoff (n := n) R) := fun h ↦ hxR (by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          tsupport_radialCutoff_subset hRpos h)
      rw [fderiv_of_notMem_tsupport ℝ hnot, norm_zero, zero_mul]
      positivity
  have hdxx : |fderiv ℝ (fun y ↦ radialCutoff R y * ω y) x x| ≤
      ‖fderiv ℝ ω x‖ * ‖x‖ + 2 * B₁ * ω x := by
    rw [hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have h1 : |radialCutoff R x * fderiv ℝ ω x x| ≤ ‖fderiv ℝ ω x‖ * ‖x‖ := by
      rw [abs_mul, abs_of_nonneg hχ0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hχ1).trans ((fderiv ℝ ω x).le_opNorm x)
    have h2 : |ω x * fderiv ℝ (radialCutoff R) x x| ≤ 2 * B₁ * ω x := by
      rw [abs_mul, abs_of_nonneg (hω0 x), mul_comm]
      exact mul_le_mul_of_nonneg_right
        (((fderiv ℝ (radialCutoff R) x).le_opNorm x).trans hDχx) (hω0 x)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hdW : |fderiv ℝ (fun y ↦ radialCutoff R y * ω y) x (W x)| ≤
      ‖fderiv ℝ ω x‖ * M + B₁ * M * ω x := by
    rw [hfd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have h1 : |radialCutoff R x * fderiv ℝ ω x (W x)| ≤ ‖fderiv ℝ ω x‖ * M := by
      rw [abs_mul, abs_of_nonneg hχ0]
      exact (mul_le_of_le_one_left (abs_nonneg _) hχ1).trans
        (((fderiv ℝ ω x).le_opNorm (W x)).trans (mul_le_mul_of_nonneg_left (hWb x) hdω0))
    have h2 : |ω x * fderiv ℝ (radialCutoff R) x (W x)| ≤ B₁ * M * ω x := by
      rw [abs_mul, abs_of_nonneg (hω0 x), mul_comm]
      exact mul_le_mul_of_nonneg_right
        (((fderiv ℝ (radialCutoff R) x).le_opNorm (W x)).trans
          (mul_le_mul hDχ1 (hWb x) (norm_nonneg _) hB₁0)) (hω0 x)
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  have hΔ : |laplacian (fun y ↦ radialCutoff R y * ω y) x| ≤
      B₂ * ω x + 2 * (n * B₁ * ‖fderiv ℝ ω x‖) + |laplacian ω x| := by
    rw [PDE.laplacian_mul hχc.contDiffAt hω.contDiffAt]
    have h1 : |laplacian (radialCutoff R) x * ω x| ≤ B₂ * ω x := by
      rw [abs_mul, abs_of_nonneg (hω0 x)]
      exact mul_le_mul_of_nonneg_right ((hB₂ R hRpos x).trans
        (mul_le_of_le_one_right hB₂0 (pow_le_one₀ hRinv hR1))) (hω0 x)
    have h2 : |∑ i : Fin n, ∂[i] (radialCutoff R) x * ∂[i] ω x| ≤ n * B₁ * ‖fderiv ℝ ω x‖ := by
      calc |∑ i : Fin n, ∂[i] (radialCutoff R) x * ∂[i] ω x|
          ≤ ∑ i : Fin n, |∂[i] (radialCutoff R) x * ∂[i] ω x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, B₁ * ‖fderiv ℝ ω x‖ := Finset.sum_le_sum fun i _ ↦ by
            rw [abs_mul]
            exact mul_le_mul ((norm_partialDeriv_le_norm_fderiv i _ x).trans hDχ1)
              (norm_partialDeriv_le_norm_fderiv i ω x) (abs_nonneg _) hB₁0
        _ = n * B₁ * ‖fderiv ℝ ω x‖ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    have h2' : |2 * ∑ i : Fin n, ∂[i] (radialCutoff R) x * ∂[i] ω x| ≤
        2 * (n * B₁ * ‖fderiv ℝ ω x‖) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h3 : |radialCutoff R x * laplacian ω x| ≤ |laplacian ω x| := by
      rw [abs_mul, abs_of_nonneg hχ0]
      exact mul_le_of_le_one_left (abs_nonneg _) hχ1
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2')) h3)
  -- The coefficient of `|v|²`.
  have ha : |(c + n / 4) * (radialCutoff R x * ω x)| ≤ |c + n / 4| * ω x := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hψabs (abs_nonneg _)
  have hTabs : |(c + n / 4) * (radialCutoff R x * ω x) +
      (1 / 4 : ℝ) * fderiv ℝ (fun y ↦ radialCutoff R y * ω y) x x -
      (1 / 2 : ℝ) * fderiv ℝ (fun y ↦ radialCutoff R y * ω y) x (W x) -
      (1 / 2 : ℝ) * laplacian (fun y ↦ radialCutoff R y * ω y) x| ≤
      (|c + n / 4| + B₁ / 2 + B₁ * M / 2 + B₂ / 2) * ω x +
        (1 / 4 + M / 2 + n * B₁) * (‖fderiv ℝ ω x‖ * (1 + ‖x‖)) +
        (1 / 2 : ℝ) * |laplacian ω x| := by
    have e1 := abs_le.mp ha
    have e2 := abs_le.mp hdxx
    have e3 := abs_le.mp hdW
    have e4 := abs_le.mp hΔ
    have p1 : 0 ≤ M * (‖fderiv ℝ ω x‖ * ‖x‖) := mul_nonneg hM (mul_nonneg hdω0 hx0)
    have p2 : 0 ≤ n * B₁ * (‖fderiv ℝ ω x‖ * ‖x‖) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hB₁0) (mul_nonneg hdω0 hx0)
    rw [abs_le]
    constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2, p1, p2, hdω0]
  have habs : ∀ a b : ℝ, 0 ≤ b → |a * b| = |a| * b := fun a b hb ↦ by
    rw [abs_mul, abs_of_nonneg hb]
  have h₁ := mul_le_mul_of_nonneg_right hψabs hD0
  have h₂ := mul_le_mul_of_nonneg_right hTabs hq0
  unfold energyDensity
  refine (abs_add_le _ _).trans ?_
  rw [habs _ _ hD0, habs _ _ hq0]
  linarith

/-- **The limit of the cutoff pairings.** Let `v` be a `C²` field, `W` a bounded
divergence-free `C¹` drift and `ω ≥ 0` a `C²` weight such that `ω |∇v|²`, `ω |v|²`,
`|∇ω| (1 + |x|) |v|²` and `|Δω| |v|²` are integrable. Then the pairings of the operator
`c v - ½ x·∇v + W·∇v - Δv` with `χ_R ω v` converge, along `R = k + 1`, to

`∫ ω |∇v|² + ∫ ((c + n/4) ω + ¼ x·∇ω - ½ W·∇ω - ½ Δω) |v|²`.

This is the limit `R → ∞` of the weighted energy identity for the weights `χ_R ω`. -/
theorem tendsto_integral_radialCutoff_mul_similarityPairing {v : ℝ^n → E} {W : ℝ^n → ℝ^n}
    {ω : ℝ^n → ℝ} {c M : ℝ} (hv : ContDiff ℝ 2 v) (hW : ContDiff ℝ 1 W)
    (hdiv : ∀ x, ∇· W x = 0) (hWb : ∀ x, ‖W x‖ ≤ M) (hω : ContDiff ℝ 2 ω)
    (hω0 : ∀ x, 0 ≤ ω x)
    (h₁ : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ω x * ‖v x‖ ^ 2)
    (h₃ : Integrable fun x ↦ ‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2)
    (h₄ : Integrable fun x ↦ |laplacian ω x| * ‖v x‖ ^ 2) :
    Tendsto (fun k : ℕ ↦ ∫ x, radialCutoff ((k : ℝ) + 1) x * ω x * similarityPairing c v W x)
      atTop (𝓝 (∫ x, energyDensity c v W ω x)) := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  obtain ⟨B₂, hB₂0, hB₂⟩ := exists_abs_laplacian_radialCutoff_le (n := n)
  have hRpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k ↦ by positivity
  have hR1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k ↦ le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hψc : ∀ k : ℕ, ContDiff ℝ 2 (fun y : ℝ^n ↦ radialCutoff ((k : ℝ) + 1) y * ω y) :=
    fun k ↦ ((radialCutoff_contDiff _).of_le (by simp)).mul hω
  have hψs : ∀ k : ℕ, HasCompactSupport (fun y : ℝ^n ↦ radialCutoff ((k : ℝ) + 1) y * ω y) :=
    fun k ↦ (radialCutoff_hasCompactSupport (hRpos k)).mul_right
  -- The identity for each cutoff weight.
  have hid : ∀ k : ℕ, (∫ x, radialCutoff ((k : ℝ) + 1) x * ω x * similarityPairing c v W x) =
      ∫ x, energyDensity c v W (fun y ↦ radialCutoff ((k : ℝ) + 1) y * ω y) x := fun k ↦
    integral_mul_similarityPairing hv hW hdiv (hψc k) (hψs k) c
  -- At each point the density of the cutoff weight is eventually the density of `ω`.
  have hlim : ∀ x, ∀ᶠ k : ℕ in atTop, energyDensity c v W
      (fun y ↦ radialCutoff ((k : ℝ) + 1) y * ω y) x = energyDensity c v W ω x := fun x ↦ by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with k hk
    have hx : ‖x‖ < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hev : (fun y : ℝ^n ↦ radialCutoff ((k : ℝ) + 1) y * ω y) =ᶠ[𝓝 x] ω := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      rw [radialCutoff_eq_one (hRpos k) hy.le, one_mul]
    simp only [energyDensity, hev.eq_of_nhds, hev.fderiv_eq,
      EuclideanLaplacian.laplacian_congr_nhds hev]
  have hgint : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2 +
      (|c + n / 4| + B₁ / 2 + B₁ * M / 2 + B₂ / 2) * (ω x * ‖v x‖ ^ 2) +
      (1 / 4 + M / 2 + n * B₁) * (‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2) +
      (1 / 2 : ℝ) * (|laplacian ω x| * ‖v x‖ ^ 2) :=
    ((h₁.add (h₂.const_mul _)).add (h₃.const_mul _)).add (h₄.const_mul _)
  have htend := tendsto_integral_of_dominated_convergence _
    (fun k ↦ (continuous_energyDensity hv hW.continuous (hψc k) c).aestronglyMeasurable) hgint
    (fun k ↦ .of_forall fun x ↦ by
      rw [Real.norm_eq_abs]
      exact abs_energyDensity_radialCutoff_mul_le hWb hω hω0 hB₁0 hB₁ hB₂0 hB₂ (hR1 k) x)
    (.of_forall fun x ↦ tendsto_const_nhds.congr' ((hlim x).mono fun k hk ↦ hk.symm))
  exact htend.congr fun k ↦ (hid k).symm

/-- **Weighted energy bound by exhaustion.** Let `v` be a `C²` field, `W` a bounded
divergence-free `C¹` drift and `ω ≥ 0` a `C²` weight such that `ω |∇v|²`, `ω |v|²`,
`|∇ω| (1 + |x|) |v|²` and `|Δω| |v|²` are integrable. If the pairing of the operator
`c v - ½ x·∇v + W·∇v - Δv` with `χ_R ω v` is at most `K + C/R` for every cutoff radius `R ≥ 1`,
then

`∫ ω |∇v|² + ∫ ((c + n/4) ω + ¼ x·∇ω - ½ W·∇ω - ½ Δω) |v|² ≤ K`.

This is `tendsto_integral_radialCutoff_mul_similarityPairing` with a bound on the pairings. The
term `C/R` is room for the errors that come from derivatives of the cutoff. -/
theorem integral_energyDensity_le_of_forall_radialCutoff {v : ℝ^n → E} {W : ℝ^n → ℝ^n}
    {ω : ℝ^n → ℝ} {c K C M : ℝ} (hv : ContDiff ℝ 2 v) (hW : ContDiff ℝ 1 W)
    (hdiv : ∀ x, ∇· W x = 0) (hWb : ∀ x, ‖W x‖ ≤ M) (hω : ContDiff ℝ 2 ω)
    (hω0 : ∀ x, 0 ≤ ω x)
    (h₁ : Integrable fun x ↦ ω x * ∑ i : Fin n, ‖∂[i] v x‖ ^ 2)
    (h₂ : Integrable fun x ↦ ω x * ‖v x‖ ^ 2)
    (h₃ : Integrable fun x ↦ ‖fderiv ℝ ω x‖ * (1 + ‖x‖) * ‖v x‖ ^ 2)
    (h₄ : Integrable fun x ↦ |laplacian ω x| * ‖v x‖ ^ 2)
    (hK : ∀ R : ℝ, 1 ≤ R →
      (∫ x, radialCutoff R x * ω x * similarityPairing c v W x) ≤ K + C / R) :
    (∫ x, energyDensity c v W ω x) ≤ K := by
  have htend := tendsto_integral_radialCutoff_mul_similarityPairing (c := c) hv hW hdiv hWb hω
    hω0 h₁ h₂ h₃ h₄
  have hlimK : Tendsto (fun k : ℕ ↦ K + C * (1 / ((k : ℝ) + 1))) atTop (𝓝 K) := by
    simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C)
  refine le_of_tendsto_of_tendsto' htend hlimK fun k ↦ ?_
  rw [mul_one_div]
  exact hK ((k : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg k))

/-- The cutoffs exhaust an integral: `∫ χ_R f → ∫ f` along `R = k + 1`, for an integrable
`f`. -/
theorem tendsto_integral_radialCutoff_mul {f : ℝ^n → ℝ} (hf : Integrable f) :
    Tendsto (fun k : ℕ ↦ ∫ x, radialCutoff ((k : ℝ) + 1) x * f x) atTop (𝓝 (∫ x, f x)) := by
  have hRpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k ↦ by positivity
  refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
    (fun k ↦ ((radialCutoff_contDiff _).continuous.aestronglyMeasurable).mul
      hf.aestronglyMeasurable) hf.norm (fun k ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
  · obtain ⟨h0, h1⟩ := radialCutoff_mem_Icc (n := n) ((k : ℝ) + 1) x
    rw [norm_mul, Real.norm_of_nonneg h0]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    have hx : ‖x‖ ≤ (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rw [radialCutoff_eq_one (hRpos k) hx, one_mul]

end PDE.Analysis
