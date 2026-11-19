/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FourDimensional.Restriction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Restriction
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.Amplitude
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.LowEmbedding
import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.SpatialSolution

/-!
# Global higher Sobolev persistence from an affine bound of the restricted source

## Main result

`higherSmooth_mildLifespan_eq_top_of_affine_source`: let `0 < n < 6` and let the reaction `f` be
smooth and globally Lipschitz with `f 0 = 0`. Suppose that on every ball of `H²` displacements
the `H³ × H²` restriction of the wave source is bounded affinely by the `H³ × H²` restriction of
the state. Then the mild lifespan at every sufficiently high Sobolev level `k` is infinite, for
all data in `W^{k+1,2}(ℝⁿ) × W^{k,2}(ℝⁿ)`.

The theorem is a criterion: its hypothesis is the only step of the persistence argument that
depends on the dimension. Dimensions four and five supply it under a global bound on the second
derivative of the reaction. In dimension four the restricted source is bounded on `H²` balls
(`higherSmooth_mildLifespan_eq_top_four`), and in dimension five interpolation gives the affine
bound (`higherSmooth_mildLifespan_eq_top_five`). Dimensions below four need no such hypothesis
(`higherSmooth_mildLifespan_eq_top_of_dimension_lt_four`).

## How it works

The global `H²` energy evolution (`exists_unique_h2EnergySolution`) keeps the displacement in an
`H²` ball on every finite time interval, and every higher mild solution projects to it
(`IsEnergySolution.eq_higherSmooth_mild_projection`). On that ball the hypothesis bounds the
restricted source affinely, so Grönwall for the restricted Duhamel formula
(`exists_norm_higherWaveRestriction_bound_of_affine_source`) bounds the `H³ × H²` restriction of
the solution. In dimensions below six `H³` embeds into the bounded continuous functions
(`boundedSobolevRepresentativeCLM`), which bounds the amplitude. The tame composition estimate
(`exists_affine_higherSmoothMap_bound`) and Grönwall at the level `k`
(`exists_norm_mildSolutionOn_bound_of_affine_source`) then bound the high norm on the interval,
and a mild solution with such bounds on every finite interval has infinite lifespan
(`mildLifespan_eq_top_of_finite_time_bounds`).

These are standard energy and continuation arguments, and the proof follows no particular source.
-/

@[expose] public noncomputable section

open Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ} {K : ℝ≥0}

/-- **Global persistence from an affine bound of the restricted source.** Let `n < 6` and let
`f` be smooth and globally Lipschitz with `f 0 = 0`. Suppose that for every `R ≥ 0` there is a
constant `C` such that, for every state `z` whose displacement has `H²` norm at most `R`, the
`H³ × H²` restriction of the wave source at `z` is bounded by `C` times one plus the norm of the
`H³ × H²` restriction of `z`. Then the mild lifespan at the Sobolev level `k` is infinite for all
data in `W^{k+1,2} × W^{k,2}`. Neither amplitude nor any high norm bound is an input. -/
theorem higherSmooth_mildLifespan_eq_top_of_affine_source (hn : n < 6)
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (hk2 : 2 ≤ k)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (hsource : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n), ‖lowerOrderCLM (hk2.trans (Nat.le_succ k)) z.1‖ ≤ R →
        ‖higherWaveRestrictionCLM n hk2 (higherSmoothMap hk hs hf0 z)‖ ≤
          C * (1 + ‖higherWaveRestrictionCLM n hk2 z‖))
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x = ∞ := by
  have hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith
  have hn3 : (n : ℝ) < 2 * (3 : ℝ) := by exact_mod_cast hn
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
  let A := boundedSobolevRepresentativeCLM hn3
  apply (higherLinearSemigroup n k).mildLifespan_eq_top_of_finite_time_bounds
    (fun R _ ↦ exists_lipschitzOn_higherSmoothMap hk hs hf0 R)
  intro H hH
  obtain ⟨B₂, hb₂⟩ := isCompact_Icc.bddAbove_image (Q.continuous.norm.continuousOn (s := Icc 0 H))
  have hB₂ : 0 ≤ B₂ := (norm_nonneg (Q 0)).trans (hb₂ ⟨0, ⟨le_rfl, hH.le⟩, rfl⟩)
  obtain ⟨C₂, hC₂, hsource₂⟩ := hsource B₂ hB₂
  obtain ⟨R₃, hR₃, hbound₃⟩ :=
    exists_norm_higherWaveRestriction_bound_of_affine_source hk2 x hH.le hC₂
  have hB : 0 ≤ ‖A‖ * R₃ := mul_nonneg A.opNorm_nonneg hR₃
  obtain ⟨C, hC, hsource⟩ := exists_affine_higherSmoothMap_bound hk hq hs hf0 hB
  obtain ⟨R, _, hR⟩ :=
    exists_norm_mildSolutionOn_bound_of_affine_source (higherLinearSemigroup n k) x hH.le hC
  refine ⟨R, ?_⟩
  intro τ hτ V hV
  have hlow (t : Icc (0 : ℝ) (τ : ℝ)) :
      lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1 = Q t := by
    have hp := congrArg Prod.fst
      (he'.eq_higherSmooth_mild_projection hk hs hf hf0 x V hV t t.property)
    erw [IccExtend_val τ.coe_nonneg V t] at hp
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative (lowerOrderCLM (by omega : 2 ≤ k + 1) (V t).1)
      =ᵐ[domainMeasure n univ] baseRepresentative (Q t)
    have hbase := congrArg baseRepresentative (hp.trans (hQ t t.property.1).1.symm)
    simp only [baseRepresentative_lowerOrderCLM] at hbase ⊢
    rw [hbase]
  have hrestricted : ∀ t, ‖higherWaveRestrictionCLM n hk2 (V t)‖ ≤ R₃ :=
    hbound₃ hτ hV (fun t ↦ hsource₂ _ (by
      rw [hlow]
      exact hb₂ ⟨t, ⟨t.property.1, t.property.2.trans hτ⟩, rfl⟩))
  apply hR hτ hV
  intro t
  apply hsource
  intro y
  rw [← boundedSobolevRepresentativeCLM_lowerOrderCLM hn3 hq (by omega : 3 ≤ k + 1)]
  change ‖A (lowerOrderCLM (by omega : 3 ≤ k + 1) (V t).1) y‖ ≤ ‖A‖ * R₃
  exact ((A _).norm_coe_le_norm y).trans ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_fst_le (higherWaveRestrictionCLM n hk2 (V t))).trans (hrestricted t)) A.opNorm_nonneg))

end PDE.Hyperbolic.NonlinearWave.Cauchy
