/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Lipschitz
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongEvolution

/-!
# General smooth reactions preserve higher regularity locally

The Sobolev composition estimate constructs a locally Lipschitz vector field.
Projection commutes with the higher linear semigroup and the forcing, so energy
uniqueness identifies the local higher trajectory with the global energy
solution for every smooth globally Lipschitz reaction fixing zero.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n k : ℕ} [NeZero n]
variable {f : ℝ → ℝ} {K : ℝ≥0}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The higher reaction and the L² reaction are the same class. -/
theorem wkpBaseCoordinateCLM_higherComposition_smooth (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0) (u : W^{k,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (higherComposition hk hs hf0 u) =
      hf.compLp hf0 (wkpBaseCoordinateCLM u) := by
  apply Lp.ext
  have hN := higherComposition_ae hk hs hf0 u
  have hL := hf.coeFn_compLp hf0 (wkpBaseCoordinateCLM u)
  simp only [domainMeasure, Measure.restrict_univ] at hL ⊢
  exact hN.trans hL.symm

/-- The mass-canceling source at the higher Sobolev energy level. -/
def higherSmoothSource (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) :=
  (0, lowerOrderCLM (Nat.le_succ k) z.1 -
    higherComposition hk hs hf0
      (lowerOrderCLM (Nat.le_succ k) z.1))

/-- The general smooth reaction gives a locally Lipschitz higher vector field. -/
theorem locallyLipschitz_higherSmoothSource (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    LocallyLipschitz (higherSmoothSource hk hs hf0) := by
  let Q : (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ] W^{k,2}(ℝ^n) :=
    (lowerOrderCLM (Nat.le_succ k)).comp (ContinuousLinearMap.fst ℝ _ _)
  have hQ : LocallyLipschitz Q := Q.lipschitzWith.locallyLipschitz
  exact (LocallyLipschitz.const (0 : W^{k + 1,2}(ℝ^n))).prodMk
    (hQ.sub ((locallyLipschitz_higherComposition hk hs hf0).comp hQ))

/-- The higher source as a continuous state map. -/
def higherSmoothMap (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
  ⟨higherSmoothSource hk hs hf0, (locallyLipschitz_higherSmoothSource hk hs hf0).continuous⟩

/-- Projection of the higher source is exactly the original energy source. -/
theorem higherEnergyInclusionCLM_higherSmoothMap (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherEnergyInclusionCLM n k (higherSmoothMap hk hs hf0 z) =
      nonlinearMap hf hf0 (higherEnergyInclusionCLM n k z) := by
  apply (C).injective
  rw [coordinates_higherEnergyInclusionCLM]
  change (lowerOrderCLM _ 0, wkpBaseCoordinateCLM (lowerOrderCLM (Nat.le_succ k) z.1 -
      higherComposition hk hs hf0 (lowerOrderCLM (Nat.le_succ k) z.1))) = _
  rw [map_zero, map_sub, wkpBaseCoordinateCLM_higherComposition_smooth hk hs hf hf0]
  change _ = C ((C).symm (0, source hf hf0 (C (higherEnergyInclusionCLM n k z)).1))
  rw [ContinuousLinearEquiv.apply_symm_apply, coordinates_higherEnergyInclusionCLM]
  rfl

/-- Every higher mild trajectory projects to the original energy evolution.
This holds on its entire interval of existence, not only on a first local strip. -/
theorem IsEnergySolution.eq_higherSmooth_mild_projection
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u)
    {τ : ℝ≥0} (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hs hf0) x τ V) :
    ∀ t ∈ Icc 0 (τ : ℝ),
      (lowerOrderCLM (by omega : 1 ≤ k + 1) (IccExtend τ.property V t).1,
        wkpBaseCoordinateCLM (IccExtend τ.property V t).2) = u t := by
  let v : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) :=
    ⟨fun t ↦ higherEnergyInclusionCLM n k (V t),
      (higherEnergyInclusionCLM n k).continuous.comp V.continuous⟩
  let w : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) :=
    ⟨fun t ↦ (C).symm (u t), (C).symm.continuous.comp (u.continuous.comp continuous_subtype_val)⟩
  have hv : (linearSemigroup n).IsMildSolutionOn (nonlinearMap hf hf0)
      (higherEnergyInclusionCLM n k x) τ v := by
    intro t
    have heq := congrArg (higherEnergyInclusionCLM n k) (hV t)
    rw [map_add, higherEnergyInclusionCLM_higherLinearSemigroup] at heq
    have hd := higherEnergyInclusionCLM_duhamel n k
      (F := fun s ↦ higherSmoothMap hk hs hf0 (IccExtend τ.property V s))
      ((higherSmoothMap hk hs hf0).continuous.comp (V.continuous.Icc_extend' (h := τ.property))) t
    erw [hd] at heq
    change v t = _ at heq
    rw [heq]
    congr 1
    apply (linearSemigroup n).duhamel_congr t.property.1
    intro s hst
    dsimp only
    rw [higherEnergyInclusionCLM_higherSmoothMap hk hs hf hf0]
    rfl
  have hw : (linearSemigroup n).IsMildSolutionOn (nonlinearMap hf hf0)
      (higherEnergyInclusionCLM n k x) τ w := by
    intro t
    have heq := h.mild_eq t.property.1
    change w t = _ at heq
    rw [heq]
    congr 1
    apply (linearSemigroup n).duhamel_congr t.property.1
    intro s hst
    dsimp only
    erw [IccExtend_of_mem τ.property w ⟨hst.1, hst.2.trans t.property.2⟩]
    change (C).symm (0, _) = (C).symm (0, source hf hf0 (C ((C).symm (u s))).1)
    rw [ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n) hf hf0
  have hvw := hv.eq_of_locallyLipschitz hK.locallyLipschitz hw
  intro t ht
  have heq := congrArg (fun z : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) ↦ C (z ⟨t, ht⟩)) hvw
  change C (higherEnergyInclusionCLM n k (V ⟨t, ht⟩)) = C ((C).symm (u t)) at heq
  rw [coordinates_higherEnergyInclusionCLM, ContinuousLinearEquiv.apply_symm_apply] at heq
  rw [IccExtend_of_mem τ.property V ht]
  exact heq

/-- Higher Sobolev regularity of the data yields a positive interval on which every
energy solution has a continuous Hᵏ⁺¹ × Hᵏ lift with the original initial values. -/
theorem IsEnergySolution.exists_local_higherOrder_smoothReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u) :
    ∃ b : ℝ, 0 < b ∧ ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      U 0 = x ∧ ∀ t ∈ Icc 0 b,
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
  have hF : LocallyLipschitz (higherSmoothMap hk hs hf0) :=
    (locallyLipschitz_higherSmoothSource hk hs hf0)
  let S := higherLinearSemigroup n k
  obtain ⟨τ, hτ, V, hV, _⟩ :=
    S.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted hF x
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  refine ⟨τ, hτ, U, ?_, ?_⟩
  · exact (IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩).trans hV.initial_value
  · exact h.eq_higherSmooth_mild_projection hk hs hf hf0 x V hV

/-- If the higher Sobolev mild lifespan of the data is infinite, every energy solution from
these data has a global continuous Hᵏ⁺¹ × Hᵏ lift with the original initial values. The lift is
the maximal higher mild solution, extended by its initial value to negative times. -/
theorem IsEnergySolution.exists_global_higherOrder_of_mildLifespan_eq_top
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {e : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (he : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) e)
    (htop : (higherLinearSemigroup n k).mildLifespan (higherSmoothMap hk hs hf0) x = ⊤) :
    ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)), U 0 = x ∧
      ∀ t : ℝ, 0 ≤ t →
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = e t := by
  let T := higherLinearSemigroup n k
  let F := higherSmoothMap hk hs hf0
  have hF : LocallyLipschitz F := locallyLipschitz_higherSmoothSource hk hs hf0
  have hglobal := T.maximalMildSolution_global_of_lifespan_eq_top (F := F) hF x htop
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨fun t ↦ T.maximalMildSolution (F := F) hF x (max t 0),
      hglobal.1.comp_continuous (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)⟩
  refine ⟨U, ?_, ?_⟩
  · change T.maximalMildSolution (F := F) hF x (max 0 0) = x
    rw [max_self]
    exact T.maximalMildSolution_zero (F := F) hF x
  · intro t ht
    obtain ⟨V, hV, hmax⟩ := T.exists_mildSolutionOn_eqOn_maximalMildSolution
      (F := F) hF x (τ := ⟨t, ht⟩) (by rw [htop]; exact ENNReal.coe_lt_top)
    have hp := he.eq_higherSmooth_mild_projection hk hs hf hf0 x V hV t ⟨ht, le_rfl⟩
    erw [hmax ⟨ht, le_rfl⟩] at hp
    simpa only [U, ContinuousMap.coe_mk, max_eq_left ht] using hp

end PDE.Hyperbolic.NonlinearWave.Cauchy
