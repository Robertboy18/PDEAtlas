/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.LocalEvolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.StrongSolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.SpatialDerivatives

/-!
# Lifting the integrated wave equations

Injectivity of the Sobolev base coordinate detects a Banach-valued primitive.
The energy displacement equation therefore gives the higher velocity as a
strong time derivative. The velocity equation, tested through the H¹ dual,
similarly gives the higher acceleration. Neither time derivative is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- An injective bounded linear map detects a continuous vector-valued primitive.
This does not require a bounded inverse for that map. -/
theorem hasDerivWithinAt_of_mapped_integral {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (A : E →L[ℝ] F)
    (hA : Function.Injective A) (v w : C(ℝ, E)) {a b : ℝ}
    (hi : ∀ t ∈ Icc a b, (∫ s in a..t, A (w s)) = A (v t) - A (v a)) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt v (w t) (Icc a b) t := by
  have hprimitive (r : ℝ) (hr : r ∈ Icc a b) : v r = (∫ s in a..r, w s) + v a := by
    apply hA
    rw [map_add, ← A.intervalIntegral_comp_comm (w.continuous.intervalIntegrable a r),
      hi r hr, sub_add_cancel]
  have hd := intervalIntegral.integral_hasDerivAt_right (w.continuous.intervalIntegrable a t)
    w.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter w.continuous.continuousAt
  exact (hd.add_const (v a)).hasDerivWithinAt.congr_of_mem hprimitive ht

variable {n k : ℕ} [NeZero n]

/-- The higher acceleration for the saturating reaction. -/
def higherSaturatingAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (q : W^{k + 2,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  higherOrderLaplacianCLM le_rfl q -
    higherComposition hk contDiff_saturatingReaction saturatingReaction_zero
      (lowerOrderCLM (by omega : k ≤ k + 2) q)

/-- The higher acceleration depends continuously on the displacement. -/
theorem continuous_higherSaturatingAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) :
    Continuous (higherSaturatingAcceleration hk) :=
  (higherOrderLaplacianCLM le_rfl).continuous.sub
    ((contDiff_higherComposition_saturatingReaction hk).continuous.comp
      (lowerOrderCLM (by omega : k ≤ k + 2)).continuous)

/-- Projecting the higher acceleration gives the weak PDE acceleration. -/
theorem pivotToDual_higherSaturatingAcceleration
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) (q : W^{k + 2,2}(ℝ^n)) :
    (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (higherSaturatingAcceleration hk q)) =
      acceleration lipschitzWith_saturatingReaction saturatingReaction_zero
        (lowerOrderCLM (by omega : 1 ≤ k + 2) q) := by
  have heq := acceleration_h2 lipschitzWith_saturatingReaction saturatingReaction_zero
    (lowerOrderCLM (by omega : 2 ≤ k + 2) q)
  rw [lowerOrderCLM_trans_apply] at heq
  rw [heq]
  congr 1
  simp only [higherSaturatingAcceleration, map_sub, higherOrderLaplacianCLM_base,
    wkpBaseCoordinateCLM_higherComposition_saturatingReaction]
  rfl

/-- Both integrated energy equations lift to strong time derivatives at the
higher Sobolev level, including within-interval derivatives at the endpoints. -/
theorem IsEnergySolution.hasDerivWithinAt_higherOrder
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution lipschitzWith_saturatingReaction saturatingReaction_zero
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) u)
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))) (hU₀ : U 0 = x)
    {b : ℝ} (hU : ∀ t ∈ Icc 0 b,
      (lowerOrderCLM (by omega : 1 ≤ k + 2) (U t).1,
        wkpBaseCoordinateCLM (U t).2) = u t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1)
        (U t).2 (Icc 0 b) t ∧
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2)
        (higherSaturatingAcceleration hk (U t).1) (Icc 0 b) t := by
  constructor
  · apply hasDerivWithinAt_of_mapped_integral wkpBaseCoordinateCLM
      (wkpBaseCoordinateCLM_injective isOpen_univ)
      ⟨_, (lowerOrderCLM (Nat.le_succ (k + 1))).continuous.comp U.continuous.fst⟩
      ⟨_, U.continuous.snd⟩ (t := t) (ht := ht)
    intro r hr
    have heq := h.displacement r hr.1
    rw [← hU r hr] at heq
    change (∫ s in (0 : ℝ)..r, wkpBaseCoordinateCLM (U s).2) =
      wkpBaseCoordinateCLM (U r).1 - wkpBaseCoordinateCLM (U 0).1
    rw [hU₀]
    refine Eq.trans ?_ heq
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    exact congrArg Prod.snd (hU s ⟨hs.1, hs.2.trans hr.2⟩)
  · let A := (energyTriple n).pivotToDual.comp (wkpBaseCoordinateCLM (n := n) (m := k))
    apply hasDerivWithinAt_of_mapped_integral A ((energyTriple n).pivotToDual_injective.comp
        (wkpBaseCoordinateCLM_injective isOpen_univ))
      ⟨_, (lowerOrderCLM (Nat.le_succ k)).continuous.comp U.continuous.snd⟩
      ⟨_, (continuous_higherSaturatingAcceleration hk).comp U.continuous.fst⟩ (t := t) (ht := ht)
    intro r hr
    have heq := h.velocity r hr.1
    rw [← hU r hr] at heq
    change (∫ s in (0 : ℝ)..r, (energyTriple n).pivotToDual
      (wkpBaseCoordinateCLM (higherSaturatingAcceleration hk (U s).1))) =
      (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (U r).2) -
        (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (U 0).2)
    rw [hU₀]
    refine Eq.trans ?_ heq
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    dsimp only
    rw [pivotToDual_higherSaturatingAcceleration hk, ← hU s ⟨hs.1, hs.2.trans hr.2⟩]

end PDE.Hyperbolic.NonlinearWave.Cauchy
