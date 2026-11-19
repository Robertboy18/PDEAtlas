/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Analysis.MeasureTheory.Lp.MultiplierPairing

/-!
# Interior energy estimate for Poisson's equation

Testing the weak equation `-Δu = f` with `η²u` bounds the localized gradient
by the L² norms of the field and forcing and the first derivatives of the
cutoff. The state has no boundary condition. Compact support of the cutoff
makes the test admissible in H¹₀.

The norms on the right are base L² norms, not Sobolev norms. This is the
energy step needed to obtain a quantitative interior estimate after local
Sobolev membership has been established from the distributional equation.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

open DifferenceQuotient

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Testing `-Δu = f` with `η²u` bounds the localized gradient using only
base L² data. The cutoff may have either sign. The open domain need not be
bounded or have a regular boundary, and the state need not have zero trace. -/
theorem poisson_cutoff_gradient_sq_le
    (hΩ : IsOpen Ω) (u : H¹(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i : Fin n, ⟪(u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i),
        derivCoordCLM i v⟫_ℝ) = ⟪f, baseCoordCLM v⟫_ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω) :
    (∑ i : Fin n, ‖testFunctionLpTop (Ω := Ω) η •
      (u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)‖ ^ 2) ≤
      2 * ‖f‖ * ‖testFunctionLpTop (Ω := Ω) η‖ ^ 2 *
        ‖(u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)‖ +
      4 * (∑ i : Fin n, ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2) *
        ‖(u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)‖ ^ 2 := by
  classical
  let u₀ : DerivLp n 2 Ω := (u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)
  let du (i : Fin n) : DerivLp n 2 Ω :=
    (u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)
  let q : DerivLp n ∞ Ω := testFunctionLpTop (Ω := Ω) η
  let d (i : Fin n) : DerivLp n ∞ Ω := partialTestFunctionLpTop (Ω := Ω) η i
  let v : H¹₀(Ω) := cutoffH1ToH10 hΩ (squaredCutoff η)
    ((tsupport_squaredCutoff_subset η).trans hη) u
  have hsq : testFunctionLpTop (Ω := Ω) (squaredCutoff η) =
      (q • q : DerivLp n ∞ Ω) :=
    testFunctionLpTop_mul η η
  have hv₀ : baseCoordCLM v = q • (q • u₀) := by
    change ((cutoffCLM (p := 2) (Ω := Ω) (squaredCutoff η) u :
      H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) = _
    rw [cutoffCLM_apply_coe, cutoffAmbient_apply]
    simp only [cutoffLpAt, firstOrderRows_baseIndex, ContinuousLinearMap.comp_apply]
    change testFunctionLpTop (Ω := Ω) (squaredCutoff η) • u₀ = _
    rw [hsq, lpSMul_top_top_two_assoc]
  have hvd (i : Fin n) : derivCoordCLM i v =
      q • (q • du i) + (q • (d i • u₀) + q • (d i • u₀)) := by
    change ((cutoffCLM (p := 2) (Ω := Ω) (squaredCutoff η) u :
      H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i) = _
    rw [cutoffCLM_apply_coe, cutoffAmbient_apply]
    simp only [cutoffLpAt, firstOrderRows_singleDerivIndex,
      ContinuousLinearMap.comp_apply]
    change cutoffDerivativeLp (p := 2) (Ω := Ω) (squaredCutoff η) i
      (u₀, du i) = _
    rw [cutoffDerivativeLp_apply, partialSquaredCutoff_smul, hsq,
      ← lpSMul_top_top_two_assoc]
  have hterm (i : Fin n) : ⟪du i, derivCoordCLM i v⟫_ℝ =
      ‖q • du i‖ ^ 2 + 2 * ⟪q • du i, d i • u₀⟫_ℝ := by
    rw [hvd, inner_add_right, inner_add_right]
    simp only [← MeasureTheory.Lp.inner_lpSMul_left q (du i) (q • du i),
      ← MeasureTheory.Lp.inner_lpSMul_left q (du i) (d i • u₀)]
    rw [real_inner_self_eq_norm_sq]
    ring
  have hrow (i : Fin n) :
      ‖q • du i‖ ^ 2 / 2 - 2 * ‖d i‖ ^ 2 * ‖u₀‖ ^ 2 ≤
        ⟪du i, derivCoordCLM i v⟫_ℝ := by
    have hbound : |⟪q • du i, d i • u₀⟫_ℝ| ≤ ‖q • du i‖ * (‖d i‖ * ‖u₀‖) :=
      (abs_real_inner_le_norm _ _).trans (by gcongr; exact MeasureTheory.Lp.norm_smul_le _ _)
    rw [hterm]
    nlinarith [neg_abs_le ⟪q • du i, d i • u₀⟫_ℝ,
      sq_nonneg (‖q • du i‖ - 2 * (‖d i‖ * ‖u₀‖))]
  have henergy :
      (∑ i : Fin n, ‖q • du i‖ ^ 2) / 2 -
          2 * (∑ i : Fin n, ‖d i‖ ^ 2) * ‖u₀‖ ^ 2 ≤
        ⟪f, q • (q • u₀)⟫_ℝ := by
    calc
      _ = ∑ i : Fin n,
          (‖q • du i‖ ^ 2 / 2 - 2 * ‖d i‖ ^ 2 * ‖u₀‖ ^ 2) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
      _ ≤ ∑ i : Fin n, ⟪du i, derivCoordCLM i v⟫_ℝ :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = ⟪f, q • (q • u₀)⟫_ℝ := by simpa only [hv₀] using hweak v
  have hforcing : ⟪f, q • (q • u₀)⟫_ℝ ≤ ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ := by
    calc
      _ ≤ ‖f‖ * ‖q • (q • u₀)‖ := real_inner_le_norm _ _
      _ ≤ ‖f‖ * (‖q‖ * (‖q‖ * ‖u₀‖)) := by
        gcongr
        exact (MeasureTheory.Lp.norm_smul_le _ _).trans
          (by gcongr; exact MeasureTheory.Lp.norm_smul_le _ _)
      _ = ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ := by ring
  change (∑ i : Fin n, ‖q • du i‖ ^ 2) ≤
    2 * ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ +
      4 * (∑ i : Fin n, ‖d i‖ ^ 2) * ‖u₀‖ ^ 2
  linarith only [henergy, hforcing]

/-- With a cutoff bounded by one, Young's inequality separates the forcing
and field norms. The free positive length `τ` can be chosen as the distance
between nested localization regions; no derivative bound for the state is
assumed. Bounds on cutoff derivatives remain explicit. -/
theorem poisson_cutoff_gradient_sq_le_scaled
    (hΩ : IsOpen Ω) (u : H¹(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ v : H¹₀(Ω),
      (∑ i : Fin n, ⟪(u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i),
        derivCoordCLM i v⟫_ℝ) = ⟪f, baseCoordCLM v⟫_ℝ)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (hηnorm : ‖testFunctionLpTop (Ω := Ω) η‖ ≤ 1) {τ : ℝ} (hτ : 0 < τ) :
    (∑ i : Fin n, ‖testFunctionLpTop (Ω := Ω) η •
      (u : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)‖ ^ 2) ≤
      τ ^ 2 * ‖f‖ ^ 2 +
      (τ⁻¹ ^ 2 + 4 * (∑ i : Fin n,
        ‖partialTestFunctionLpTop (Ω := Ω) η i‖ ^ 2)) *
        ‖(u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)‖ ^ 2 := by
  let u₀ : DerivLp n 2 Ω := (u : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)
  let q : DerivLp n ∞ Ω := testFunctionLpTop (Ω := Ω) η
  have hqnorm : ‖q‖ ≤ 1 := hηnorm
  have hq : ‖q‖ ^ 2 ≤ 1 := by nlinarith only [hqnorm, norm_nonneg q]
  have hproduct : 2 * ‖f‖ * ‖q‖ ^ 2 * ‖u₀‖ ≤ 2 * ‖f‖ * ‖u₀‖ := by
    calc
      _ = (2 * ‖f‖ * ‖u₀‖) * ‖q‖ ^ 2 := by ring
      _ ≤ (2 * ‖f‖ * ‖u₀‖) * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := mul_one _
  have hYoung : 2 * ‖f‖ * ‖u₀‖ ≤ τ ^ 2 * ‖f‖ ^ 2 + τ⁻¹ ^ 2 * ‖u₀‖ ^ 2 := by
    have hcancel : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ.ne'
    have hprod : (τ * ‖f‖) * (τ⁻¹ * ‖u₀‖) = ‖f‖ * ‖u₀‖ := by
      calc
        _ = (τ * τ⁻¹) * (‖f‖ * ‖u₀‖) := by ring
        _ = _ := by rw [hcancel, one_mul]
    nlinarith only [hprod, sq_nonneg (τ * ‖f‖ - τ⁻¹ * ‖u₀‖)]
  have h := poisson_cutoff_gradient_sq_le hΩ u f hweak η hη
  dsimp only [u₀, q] at hproduct hYoung
  nlinarith only [h, hproduct, hYoung]

end SobolevSpace.GraphSpace
