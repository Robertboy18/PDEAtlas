/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.SourceBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.LowEmbedding
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.SpatialSolution

/-!
# Global higher Sobolev persistence in dimension five

The global H² energy evolution and interpolation give affine H³ growth of the
H² source on finite intervals. Restricted Grönwall bounds displacement in H³,
which bounds amplitude in dimension five. Tame composition and Grönwall bound all higher levels.
The global second-derivative bound is explicit; higher scalar derivatives
are only bounded on the attained compact value ranges.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {k : ℕ} {f : ℝ → ℝ} {K : ℝ≥0}

/-- In dimension five, smooth globally Lipschitz reactions with bounded second
derivative preserve every sufficiently high Sobolev energy level globally.
Neither amplitude nor any high norm bound is an input. -/
theorem higherSmooth_mildLifespan_eq_top_five (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0) {D : ℝ} (hD : 0 ≤ D)
    (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D) (x : W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5)) :
    (higherLinearSemigroup 5 k).mildLifespan (higherSmoothMap hk hs hf0) x = ∞ := by
  have hk2 : 2 ≤ k := by
    have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  have hq : (5 : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  obtain ⟨e, d, Q, he, _, hQ, _⟩ := exists_unique_h2EnergySolution hf hf0
    (hs.of_le (by simp)) (lowerOrderCLM (by omega : 2 ≤ k + 1) x.1)
    (lowerOrderCLM (by omega : 1 ≤ k) x.2)
  have he' : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e := by
    have hi :
        (lowerOrderCLM (by decide : 1 ≤ 2)
          (lowerOrderCLM (by omega : 2 ≤ k + 1) x.1),
          (energyTriple 5).inclusion (lowerOrderCLM (by omega : 1 ≤ k) x.2)) =
        (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) := by
      rw [lowerOrderCLM_trans_apply]
      rfl
    exact hi ▸ he.toIsEnergySolutionOn
  let A := boundedSobolevRepresentativeCLM (by norm_num : (5 : ℝ) < 2 * (3 : ℝ))
  apply (higherLinearSemigroup 5 k).mildLifespan_eq_top_of_finite_time_bounds
    (fun R _ ↦ exists_lipschitzOn_higherSmoothMap hk hs hf0 R)
  intro H hH
  obtain ⟨B₂, hb₂⟩ := isCompact_Icc.bddAbove_image (Q.continuous.norm.continuousOn (s := Icc 0 H))
  have hB₂ : 0 ≤ B₂ := (norm_nonneg (Q 0)).trans (hb₂ ⟨0, ⟨le_rfl, hH.le⟩, rfl⟩)
  obtain ⟨C₂, hC₂, hsource₂⟩ :=
    exists_norm_higherWaveRestriction_source_affine_bound_five hk hk2 hs hf hf0 hD hsecond hB₂
  obtain ⟨R₃, hR₃, hbound₃⟩ :=
    exists_norm_higherWaveRestriction_bound_of_affine_source hk2 x hH.le hC₂
  have hB : 0 ≤ ‖A‖ * R₃ := mul_nonneg A.opNorm_nonneg hR₃
  obtain ⟨C, hC, hsource⟩ := exists_affine_higherSmoothMap_bound hk hq hs hf0 hB
  obtain ⟨R, _, hR⟩ :=
    exists_norm_mildSolutionOn_bound_of_affine_source (higherLinearSemigroup 5 k) x hH.le hC
  refine ⟨R, ?_⟩
  intro τ hτ V hV
  have hlow (t : Icc (0 : ℝ) (τ : ℝ)) :
      lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1 = Q t := by
    have hp := congrArg Prod.fst
      (he'.eq_higherSmooth_mild_projection hk hs hf hf0 x V hV t t.property)
    erw [IccExtend_val τ.coe_nonneg V t] at hp
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative (lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1)
      =ᵐ[domainMeasure 5 univ] baseRepresentative (Q t)
    have hbase := congrArg baseRepresentative (hp.trans (hQ t t.property.1).1.symm)
    simp only [baseRepresentative_lowerOrderCLM] at hbase ⊢
    rw [hbase]
  have hrestricted : ∀ t, ‖higherWaveRestrictionCLM 5 hk2 (V t)‖ ≤ R₃ :=
    hbound₃ hτ hV (fun t ↦ hsource₂ _ (by
      rw [hlow]
      exact hb₂ ⟨t, ⟨t.property.1, t.property.2.trans hτ⟩, rfl⟩))
  apply hR hτ hV
  intro t
  apply hsource
  intro y
  rw [← boundedSobolevRepresentativeCLM_lowerOrderCLM
    (by norm_num : (5 : ℝ) < 2 * (3 : ℝ)) hq (by omega : 3 ≤ k + 1)]
  change ‖A (lowerOrderCLM (by omega : 3 ≤ k + 1) (V t).1) y‖ ≤ ‖A‖ * R₃
  exact ((A _).norm_coe_le_norm y).trans ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_fst_le (higherWaveRestrictionCLM 5 hk2 (V t))).trans (hrestricted t)) A.opNorm_nonneg))

/-- The original energy solution has a global higher Sobolev lift in dimension
five under the separate global bound on the second reaction derivative. -/
theorem IsEnergySolution.exists_global_higherOrder_smoothReaction_five
    (hk : (5 : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    {D : ℝ} (hD : 0 ≤ D) (hsecond : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ D)
    (x : W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5))
    {e : C(ℝ, H¹(ℝ^5) × DerivLp 5 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^5) × W^{k,2}(ℝ^5)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = e t := by
  exact he.exists_global_higherOrder_of_mildLifespan_eq_top hk hs hf hf0 x
    (higherSmooth_mildLifespan_eq_top_five hk hs hf hf0 hD hsecond x)

end PDE.Hyperbolic.NonlinearWave.Cauchy
