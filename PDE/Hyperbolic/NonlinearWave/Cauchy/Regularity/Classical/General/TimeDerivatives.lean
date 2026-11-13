/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.LocalEvolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.TimeDerivatives

/-!
# Lifting the integrated wave equations

Injectivity of the Sobolev base coordinate detects a Banach-valued primitive.
The energy displacement equation therefore gives the higher velocity as a
strong time derivative. The velocity equation, tested through the H¹ dual,
similarly gives the higher acceleration. Neither time derivative is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]
variable {f : ℝ → ℝ} {K : ℝ≥0}

/-- The higher acceleration for a general smooth reaction. -/
def higherSmoothAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    (q : W^{k + 2,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  higherOrderLaplacianCLM le_rfl q -
    higherComposition hk hs hf0
      (lowerOrderCLM (by omega : k ≤ k + 2) q)

/-- The higher acceleration depends continuously on the displacement. -/
theorem continuous_higherSmoothAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) :
    Continuous (higherSmoothAcceleration hk hs hf0) :=
  (higherOrderLaplacianCLM le_rfl).continuous.sub
    ((locallyLipschitz_higherComposition hk hs hf0).continuous.comp
      (lowerOrderCLM (by omega : k ≤ k + 2)).continuous)

/-- Projecting the higher acceleration gives the weak PDE acceleration. -/
theorem pivotToDual_higherSmoothAcceleration
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (q : W^{k + 2,2}(ℝ^n)) :
    (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (higherSmoothAcceleration hk hs hf0 q)) =
      acceleration hf hf0
        (lowerOrderCLM (by omega : 1 ≤ k + 2) q) := by
  have heq := acceleration_h2 hf hf0
    (lowerOrderCLM (by omega : 2 ≤ k + 2) q)
  rw [lowerOrderCLM_trans_apply] at heq
  rw [heq]
  congr 1
  simp only [higherSmoothAcceleration, map_sub, higherOrderLaplacianCLM_base,
    wkpBaseCoordinateCLM_higherComposition_smooth hk hs hf hf0]
  rfl

/-- Both integrated energy equations lift to strong time derivatives at the
higher Sobolev level, including within-interval derivatives at the endpoints. -/
theorem IsEnergySolution.hasDerivWithinAt_higherOrder_smoothReaction
    (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf : LipschitzWith K f) (hf0 : f 0 = 0)
    (x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) u)
    (U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n))) (hU₀ : U 0 = x)
    {b : ℝ} (hU : ∀ t ∈ Icc 0 b,
      (lowerOrderCLM (by omega : 1 ≤ k + 2) (U t).1,
        wkpBaseCoordinateCLM (U t).2) = u t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1)
        (U t).2 (Icc 0 b) t ∧
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2)
        (higherSmoothAcceleration hk hs hf0 (U t).1) (Icc 0 b) t := by
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
    intro s hst
    rw [uIcc_of_le hr.1] at hst
    exact congrArg Prod.snd (hU s ⟨hst.1, hst.2.trans hr.2⟩)
  · let A := (energyTriple n).pivotToDual.comp (wkpBaseCoordinateCLM (n := n) (m := k))
    apply hasDerivWithinAt_of_mapped_integral A ((energyTriple n).pivotToDual_injective.comp
        (wkpBaseCoordinateCLM_injective isOpen_univ))
      ⟨_, (lowerOrderCLM (Nat.le_succ k)).continuous.comp U.continuous.snd⟩
      ⟨_, (continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst⟩ (t := t) (ht := ht)
    intro r hr
    have heq := h.velocity r hr.1
    rw [← hU r hr] at heq
    change (∫ s in (0 : ℝ)..r, (energyTriple n).pivotToDual
      (wkpBaseCoordinateCLM (higherSmoothAcceleration hk hs hf0 (U s).1))) =
      (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (U r).2) -
        (energyTriple n).pivotToDual (wkpBaseCoordinateCLM (U 0).2)
    rw [hU₀]
    refine Eq.trans ?_ heq
    apply intervalIntegral.integral_congr
    intro s hst
    rw [uIcc_of_le hr.1] at hst
    dsimp only
    rw [pivotToDual_higherSmoothAcceleration hk hs hf hf0, ← hU s ⟨hst.1, hst.2.trans hr.2⟩]

end PDE.Hyperbolic.NonlinearWave.Cauchy
