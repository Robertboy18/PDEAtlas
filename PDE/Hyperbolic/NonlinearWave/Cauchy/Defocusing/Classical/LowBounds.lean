/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Composition
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Projection
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Restriction

/-!
# Energy controls the next Sobolev level for the cubic wave

On a fixed energy ball the restricted H¹ source grows linearly in the
H² × H¹ wave norm. The conserved energy and the displacement equation
place every finite higher trajectory in a known energy ball. Restricted
Grönwall then bounds H² × H¹ on each finite horizon.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- The cubic velocity source has linear H¹ growth on each energy ball.
The higher input norm does not enter the coefficient. -/
theorem exists_restricted_source_bound {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h2 : 2 ≤ k)
    (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3),
      ‖energyProjectionCLM k z‖ ≤ R →
      ‖higherWaveRestrictionCLM 3 (by omega : 1 ≤ k)
        (higherSmoothMap hk (contDiff_id.pow 3) (by simp) z)‖ ≤
        C * ‖higherWaveRestrictionCLM 3 (by omega : 1 ≤ k) z‖ := by
  obtain ⟨C, hC, hcube⟩ := exists_lower_cubic_h1_bound hk h2
  refine ⟨1 + C * R ^ 2, by positivity, ?_⟩
  intro z hz
  let q : W^{k,2}(ℝ^3) := lowerOrderCLM (Nat.le_succ k) z.1
  let L := higherWaveRestrictionCLM 3 (by omega : 1 ≤ k)
  have hq1 : ‖lowerOrderCLM (by omega : 1 ≤ k) q‖ ≤ R := by
    dsimp only [q]
    rw [lowerOrderCLM_trans_apply]
    exact (norm_fst_le (energyProjectionCLM k z)).trans hz
  have hq2 : ‖lowerOrderCLM h2 q‖ ≤ ‖L z‖ := by
    dsimp only [q]
    rw [lowerOrderCLM_trans_apply]
    exact norm_fst_le (L z)
  have hq12 : ‖lowerOrderCLM (by omega : 1 ≤ k) q‖ ≤ ‖L z‖ := by
    have h := norm_lowerOrderCLM_apply_le (by decide : 1 ≤ 2) (lowerOrderCLM h2 q)
    rw [lowerOrderCLM_trans_apply] at h
    exact h.trans hq2
  have hcub :
      ‖lowerOrderCLM (by omega : 1 ≤ k)
        (higherComposition hk (contDiff_id.pow 3) (by simp) q)‖ ≤ C * R ^ 2 * ‖L z‖ :=
    (hcube q).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq1 2) hC)
      hq2 (norm_nonneg _) (by positivity))
  change ‖(lowerOrderCLM _ (0 : W^{k + 1,2}(ℝ^3)),
    lowerOrderCLM (by omega : 1 ≤ k)
      (q - higherComposition hk (contDiff_id.pow 3) (by simp) q))‖ ≤ _
  simp only [map_zero, map_sub, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  exact ((norm_sub_le _ _).trans (add_le_add hq12 hcub)).trans_eq (by
    simp only [L, Prod.norm_def]
    ring)

/-- Conservation supplies a uniform H² × H¹ bound for every higher cubic
trajectory on a fixed finite horizon, from its initial datum alone. -/
theorem exists_restricted_norm_bound {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h2 : 2 ≤ k)
    (x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) {H : ℝ} (hH : 0 ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧
      ∀ {τ : ℝ≥0}, (τ : ℝ) ≤ H → ∀ {u : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3))},
        (higherLinearSemigroup 3 k).IsMildSolutionOn (higherSmoothMap hk (contDiff_id.pow 3)
        (by simp)) x τ u → ∀ t, ‖higherWaveRestrictionCLM 3 (by omega : 1 ≤ k) (u t)‖ ≤ R := by
  let y := energyProjectionCLM k x
  let E := ‖(energyTriple 3).inclusion y.1‖ + (H + 1) * Real.sqrt (2 * cubicNonlinearity.energy y)
  obtain ⟨C, hC, hsource⟩ := exists_restricted_source_bound hk h2 E
  obtain ⟨R, hR, hbound⟩ := exists_norm_higherWaveRestriction_bound_of_affine_source
    (by omega : 1 ≤ k) x hH hC
  refine ⟨R, hR, ?_⟩
  intro τ hτ u hu
  apply hbound hτ hu
  intro t
  have he : ‖energyProjectionCLM k (u t)‖ ≤ E :=
    (cubicNonlinearity.norm_of_mildSolutionOn
      (energyProjection_isMildSolutionOn hk (by omega) hu) t).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (add_le_add (t.property.2.trans hτ) le_rfl) (Real.sqrt_nonneg _)))
  exact (hsource (u t) he).trans
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num)) hC)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
