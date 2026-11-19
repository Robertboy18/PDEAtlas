/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.LowBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.LowEmbedding

/-!
# Global higher Sobolev persistence of the three-dimensional cubic wave

Conserved energy gives the H² bound proved in `LowBounds`. H² embeds in
bounded continuous functions in dimension three. Tame composition and
Grönwall then bound every higher wave norm on every finite horizon.
The maximal evolution therefore has infinite lifespan. Its projection
is the global energy solution.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- Every sufficiently high Sobolev datum for the defocusing cubic in ℝ³
has infinite forward lifespan. All continuation bounds are derived. -/
theorem higher_mildLifespan_eq_top {k : ℕ}
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1))
    (x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) :
    (higherLinearSemigroup 3 k).mildLifespan
      (higherSmoothMap hk (contDiff_id.pow 3) (by simp)) x = ∞ := by
  have h2 : 2 ≤ k := by
    have h : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast h
    omega
  have hq : (3 : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  let A := boundedSobolevRepresentativeCLM (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))
  have hLip := exists_lipschitzOn_higherSmoothMap hk (contDiff_id.pow 3) (by simp)
  apply (higherLinearSemigroup 3 k).mildLifespan_eq_top_of_finite_time_bounds fun R _ ↦ hLip R
  intro H hH
  obtain ⟨R₂, hR₂, hbound₂⟩ := exists_restricted_norm_bound hk h2 x hH.le
  have hB : 0 ≤ ‖A‖ * R₂ := mul_nonneg A.opNorm_nonneg hR₂
  obtain ⟨C, hC, hsource⟩ :=
    exists_affine_higherSmoothMap_bound hk hq (contDiff_id.pow 3) (by simp) hB
  obtain ⟨R, _, hbound⟩ :=
    exists_norm_mildSolutionOn_bound_of_affine_source (higherLinearSemigroup 3 k) x hH.le hC
  refine ⟨R, ?_⟩
  intro τ hτ u hu
  have hrestricted := hbound₂ hτ hu
  apply hbound hτ hu
  intro t
  apply hsource
  intro y
  rw [← boundedSobolevRepresentativeCLM_lowerOrderCLM
    (by norm_num : (3 : ℝ) < 2 * (2 : ℝ)) hq (by omega : 2 ≤ k + 1)]
  change ‖A (lowerOrderCLM (by omega : 2 ≤ k + 1) (u t).1) y‖ ≤ ‖A‖ * R₂
  exact ((A _).norm_coe_le_norm y).trans ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_fst_le (higherWaveRestrictionCLM 3 (by omega : 1 ≤ k) (u t))).trans
        (hrestricted t)) A.opNorm_nonneg))

/-- The sealed global energy solution has a global continuous higher Sobolev
lift for every sufficiently regular initial datum. -/
theorem exists_global_higher_lift {k : ℕ} (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1))
    (x : W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t → energyProjectionCLM k (U t) =
        cubicNonlinearity.globalSolution (energyProjectionCLM k x) t := by
  have h1 : 1 ≤ k := by
    have h : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast h
    omega
  let T := higherLinearSemigroup 3 k
  let F := higherSmoothMap hk (contDiff_id.pow 3) (by simp)
  have hF : LocallyLipschitz F :=
    locallyLipschitz_higherSmoothSource hk (contDiff_id.pow 3) (by simp)
  have htop := higher_mildLifespan_eq_top hk x
  have hglobal := T.maximalMildSolution_global_of_lifespan_eq_top hF x htop
  let U : C(ℝ, W^{k + 1,2}(ℝ^3) × W^{k,2}(ℝ^3)) := ⟨fun t ↦ T.maximalMildSolution hF x (max t 0),
      hglobal.1.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)⟩
  refine ⟨U, ?_, ?_⟩
  · change T.maximalMildSolution hF x (max 0 0) = x
    rw [max_self]
    exact T.maximalMildSolution_zero hF x
  · intro t ht
    obtain ⟨V, hV, hmax⟩ := T.exists_mildSolutionOn_eqOn_maximalMildSolution
      hF x (τ := ⟨t, ht⟩) (by rw [htop]; exact ENNReal.coe_lt_top)
    have hp := energyProjection_eq_globalSolution hk h1 hV ⟨t, ht, le_rfl⟩
    have hm := hmax ⟨ht, le_rfl⟩
    erw [IccExtend_of_mem (show (0 : ℝ) ≤ t from ht) V ⟨ht, le_rfl⟩] at hm
    erw [hm] at hp
    simpa only [U, ContinuousMap.coe_mk, max_eq_left ht] using hp

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
