/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.LowEmbedding
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.SpatialSolution

/-!
# Global higher Sobolev persistence in dimensions below four

The global H² energy evolution bounds amplitude on every finite
time interval. Higher mild solutions project to that same energy evolution.
The tame composition estimate and Grönwall therefore bound their high norms,
which rules out a finite higher lifespan.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- Smooth globally Lipschitz reactions preserve every sufficiently high
Sobolev energy level globally when the spatial dimension is below four.
The finite-time high norm bounds are derived from the global H² evolution. -/
theorem higherSmooth_mildLifespan_eq_top_of_dimension_lt_four (hn : n < 4)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f)
    (hf0 : f 0 = 0) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x = ∞ := by
  have hk2 : 2 ≤ k := by
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    have : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast this
    omega
  have hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hn2 : (n : ℝ) < 2 * (2 : ℝ) := by exact_mod_cast hn
  obtain ⟨e, d, Q, he, _, hQ, _⟩ := exists_unique_h2EnergySolution hf hf0
    (hs.of_le (by simp)) (lowerOrderCLM (by omega : 2 ≤ k + 1) x.1)
    (lowerOrderCLM (by omega : 1 ≤ k) x.2)
  have he' : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e := by
    have hi :
        (lowerOrderCLM (by decide : 1 ≤ 2)
          (lowerOrderCLM (by omega : 2 ≤ k + 1) x.1),
          (energyTriple n).inclusion (lowerOrderCLM (by omega : 1 ≤ k) x.2)) =
        (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) := by
      rw [lowerOrderCLM_trans_apply]
      rfl
    exact hi ▸ he.toIsEnergySolutionOn
  let A := boundedSobolevRepresentativeCLM hn2
  apply (higherLinearSemigroup n k).mildLifespan_eq_top_of_finite_time_bounds
    (fun R _ ↦ exists_lipschitzOn_higherSmoothMap hk hs hf0 R)
  intro H hH
  obtain ⟨B, hbound⟩ := isCompact_Icc.bddAbove_image
    ((A.continuous.comp Q.continuous).norm.continuousOn (s := Icc 0 H))
  have hB : 0 ≤ B := (norm_nonneg (A (Q 0))).trans (hbound ⟨0, ⟨le_rfl, hH.le⟩, rfl⟩)
  obtain ⟨C, hC, hsource⟩ := exists_affine_higherSmoothMap_bound hk hq hs hf0 hB
  obtain ⟨R, _, hR⟩ :=
    exists_norm_mildSolutionOn_bound_of_affine_source (higherLinearSemigroup n k) x hH.le hC
  refine ⟨R, ?_⟩
  intro τ hτ V hV
  apply hR hτ hV
  intro t
  apply hsource
  intro y
  have hp := congrArg Prod.fst
    (he'.eq_higherSmooth_mild_projection hk hs hf hf0 x V hV t t.property)
  erw [IccExtend_val τ.coe_nonneg V t] at hp
  have hlow : lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1 = Q t := by
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative (lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1)
      =ᵐ[domainMeasure n univ] baseRepresentative (Q t)
    have hbase := congrArg baseRepresentative (hp.trans (hQ t t.property.1).1.symm)
    simp only [baseRepresentative_lowerOrderCLM] at hbase ⊢
    rw [hbase]
  rw [← boundedSobolevRepresentativeCLM_lowerOrderCLM hn2 hq
    (by omega : 2 ≤ k + 1), hlow]
  exact ((A (Q t)).norm_coe_le_norm y).trans
    (hbound ⟨t, ⟨t.property.1, t.property.2.trans hτ⟩, rfl⟩)

/-- Every energy solution from sufficiently high Sobolev data has a global
continuous lift to that Sobolev energy level in dimensions below four. -/
theorem IsEnergySolution.exists_global_higherOrder_smoothReaction
    (hn : n < 4) (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = e t := by
  exact he.exists_global_higherOrder_of_mildLifespan_eq_top hk hs hf hf0 x
    (higherSmooth_mildLifespan_eq_top_of_dimension_lt_four hn hk hs hf hf0 x)

end PDE.Hyperbolic.NonlinearWave.Cauchy
