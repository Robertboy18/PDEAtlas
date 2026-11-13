/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Reaction
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongEvolution

/-!
# Local higher regularity of the energy evolution

For the globally Lipschitz reaction `s / (1 + s²)`, a smooth Sobolev vector
field constructs a local trajectory directly in Hᵏ⁺¹ × Hᵏ. Projection commutes
with the semigroup and forcing, so mild uniqueness identifies this trajectory
with every energy solution having the same data. This avoids requiring
composition on all lower Sobolev levels in high dimension.

The hypotheses concern only the data and the explicit threshold `n < 2(k - 1)`.
The conclusion here is local Sobolev regularity; classical time differentiation is separate.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n k : ℕ} [NeZero n]

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The higher reaction and the L² reaction are the same class. -/
theorem wkpBaseCoordinateCLM_higherComposition_saturatingReaction (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (u : W^{k,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (higherComposition hk contDiff_saturatingReaction saturatingReaction_zero
      u) = lipschitzWith_saturatingReaction.compLp saturatingReaction_zero (wkpBaseCoordinateCLM
      u) := by
  apply Lp.ext
  have hN := higherComposition_ae hk contDiff_saturatingReaction saturatingReaction_zero u
  have hL := lipschitzWith_saturatingReaction.coeFn_compLp saturatingReaction_zero
    (wkpBaseCoordinateCLM u)
  simp only [domainMeasure, Measure.restrict_univ] at hL ⊢
  exact hN.trans hL.symm

/-- The mass-canceling source at the higher Sobolev energy level. -/
def higherSaturatingSource (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) :=
  (0, lowerOrderCLM (Nat.le_succ k) z.1 -
    higherComposition hk contDiff_saturatingReaction saturatingReaction_zero
      (lowerOrderCLM (Nat.le_succ k) z.1))

/-- The higher wave vector field is smooth in its state variable. -/
theorem contDiff_higherSaturatingSource (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (higherSaturatingSource hk) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (fun z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n) ↦
        lowerOrderCLM (Nat.le_succ k) z.1) := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (⊤ : ℕ∞))
      (E := W^{k + 1,2}(ℝ^n)) (F := W^{k,2}(ℝ^n)) (lowerOrderCLM (Nat.le_succ k))).comp contDiff_fst
  exact contDiff_const.prodMk (hq.sub ((contDiff_higherComposition_saturatingReaction hk).comp hq))

/-- The higher source as a continuous state map. -/
def higherSaturatingMap (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    C(W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
  ⟨higherSaturatingSource hk, (contDiff_higherSaturatingSource hk).continuous⟩

/-- Projection of the higher source is exactly the original energy source. -/
theorem higherEnergyInclusionCLM_higherSaturatingMap (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (z : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherEnergyInclusionCLM n k (higherSaturatingMap hk z) =
      nonlinearMap lipschitzWith_saturatingReaction saturatingReaction_zero
      (higherEnergyInclusionCLM n k z) := by
  apply (C).injective
  rw [coordinates_higherEnergyInclusionCLM]
  change (lowerOrderCLM _ 0, wkpBaseCoordinateCLM (lowerOrderCLM (Nat.le_succ k) z.1 -
      higherComposition hk contDiff_saturatingReaction saturatingReaction_zero
        (lowerOrderCLM (Nat.le_succ k) z.1))) = _
  rw [map_zero, map_sub, wkpBaseCoordinateCLM_higherComposition_saturatingReaction]
  change _ = C ((C).symm (0, source lipschitzWith_saturatingReaction saturatingReaction_zero
      (C (higherEnergyInclusionCLM n k z)).1))
  rw [ContinuousLinearEquiv.apply_symm_apply, coordinates_higherEnergyInclusionCLM]
  rfl

/-- Higher smoothness of the data yields a positive interval on which every
energy solution has a continuous Hᵏ⁺¹ × Hᵏ lift with the original initial values. -/
theorem IsEnergySolution.exists_local_higherOrder_saturatingReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution lipschitzWith_saturatingReaction saturatingReaction_zero
      (lowerOrderCLM (by omega : 1 ≤ k + 1) x.1, wkpBaseCoordinateCLM x.2) u) :
    ∃ b : ℝ, 0 < b ∧ ∃ U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)),
      U 0 = x ∧ ∀ t ∈ Icc 0 b,
        (lowerOrderCLM (by omega : 1 ≤ k + 1) (U t).1,
          wkpBaseCoordinateCLM (U t).2) = u t := by
  have hF : LocallyLipschitz (higherSaturatingMap hk) :=
    ((contDiff_higherSaturatingSource hk).of_le (by simp)).locallyLipschitz
  let S := higherLinearSemigroup n k
  obtain ⟨τ, hτ, V, hV, _⟩ :=
    S.exists_pos_existsUnique_mildSolutionOn_of_locallyLipschitz_unrestricted hF x
  let U : C(ℝ, W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  let v : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) := ⟨fun t ↦ higherEnergyInclusionCLM n k (V t),
      (higherEnergyInclusionCLM n k).continuous.comp V.continuous⟩
  let w : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) := ⟨fun t ↦ (C).symm (u t),
      (C).symm.continuous.comp (u.continuous.comp continuous_subtype_val)⟩
  have hv : (linearSemigroup n).IsMildSolutionOn
      (nonlinearMap lipschitzWith_saturatingReaction saturatingReaction_zero)
      (higherEnergyInclusionCLM n k x) τ v := by
    intro t
    have heq := congrArg (higherEnergyInclusionCLM n k) (hV t)
    rw [map_add, higherEnergyInclusionCLM_higherLinearSemigroup] at heq
    have hd := higherEnergyInclusionCLM_duhamel n k
      (F := fun s ↦ higherSaturatingMap hk (IccExtend τ.property V s))
      ((higherSaturatingMap hk).continuous.comp (V.continuous.Icc_extend' (h := τ.property))) t
    erw [hd] at heq
    change v t = _ at heq
    rw [heq]
    congr 1
    apply (linearSemigroup n).duhamel_congr t.property.1
    intro s hs
    dsimp only
    rw [higherEnergyInclusionCLM_higherSaturatingMap]
    rfl
  have hw : (linearSemigroup n).IsMildSolutionOn
      (nonlinearMap lipschitzWith_saturatingReaction saturatingReaction_zero)
      (higherEnergyInclusionCLM n k x) τ w := by
    intro t
    have heq := h.mild_eq t.property.1
    change w t = _ at heq
    rw [heq]
    congr 1
    apply (linearSemigroup n).duhamel_congr t.property.1
    intro s hs
    dsimp only
    erw [IccExtend_of_mem τ.property w ⟨hs.1, hs.2.trans t.property.2⟩]
    change (C).symm (0, _) = (C).symm (0,
      source lipschitzWith_saturatingReaction saturatingReaction_zero (C ((C).symm (u s))).1)
    rw [ContinuousLinearEquiv.apply_symm_apply]
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz (n := n)
    lipschitzWith_saturatingReaction saturatingReaction_zero
  have hvw := hv.eq_of_locallyLipschitz hK.locallyLipschitz hw
  refine ⟨τ, hτ, U, ?_, ?_⟩
  · exact (IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩).trans hV.initial_value
  · intro t ht
    have heq := congrArg (fun z : C(Icc (0 : ℝ) (τ : ℝ), EnergyState n) ↦ C (z ⟨t, ht⟩)) hvw
    change C (higherEnergyInclusionCLM n k (V ⟨t, ht⟩)) = C ((C).symm (u t)) at heq
    rw [coordinates_higherEnergyInclusionCLM, ContinuousLinearEquiv.apply_symm_apply] at heq
    change (lowerOrderCLM _ (IccExtend τ.property V t).1,
      wkpBaseCoordinateCLM (IccExtend τ.property V t).2) = u t
    rw [IccExtend_of_mem τ.property V ht]
    exact heq

end PDE.Hyperbolic.NonlinearWave.Cauchy
