/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Classical.Projection
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.TimeDerivatives

/-!
# Strong time derivatives of the defocusing cubic energy solution

The integrated displacement and velocity equations lift through injective
Sobolev coordinates. The weak acceleration is exactly the projection of
`Δu − u³`, with no globally Lipschitz scalar extension.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

variable {k : ℕ}

/-- On H² displacement the cubic weak acceleration belongs to L². -/
theorem acceleration_h2 (u : W^{2,2}(ℝ^3)) :
    cubicNonlinearity.acceleration (lowerOrderCLM (by decide : 1 ≤ 2) u) =
      (energyTriple 3).pivotToDual
        (Δ u - cubicNonlinearity.source (lowerOrderCLM (by decide : 1 ≤ 2) u)) := by
  rw [← cubicNonlinearity.force_sub_massForm (lowerOrderCLM (by decide : 1 ≤ 2) u, 0),
    massForm_h2, ← map_sub]
  congr 1
  change (wkpBaseCoordinateCLM u -
      cubicNonlinearity.source (lowerOrderCLM (by decide : 1 ≤ 2) u)) -
    (wkpBaseCoordinateCLM u - Δ u) = _
  abel

/-- Higher cubic acceleration projects to the weak PDE acceleration. -/
theorem pivotToDual_higherSmoothAcceleration_cubic
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1)) (h1 : 1 ≤ k)
    (q : W^{k + 2,2}(ℝ^3)) :
    (energyTriple 3).pivotToDual (wkpBaseCoordinateCLM
      (higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) q)) =
      cubicNonlinearity.acceleration (lowerOrderCLM (by omega : 1 ≤ k + 2) q) := by
  have heq := acceleration_h2 (lowerOrderCLM (by omega : 2 ≤ k + 2) q)
  rw [lowerOrderCLM_trans_apply] at heq
  rw [heq]
  congr 1
  simp only [higherSmoothAcceleration, map_sub, higherOrderLaplacianCLM_base,
    wkpBaseCoordinateCLM_higherComposition_cubic hk h1, lowerOrderCLM_trans_apply]

/-- Both integrated energy equations lift to strong time derivatives at the
higher Sobolev level, including within-interval derivatives at the endpoints. -/
theorem hasDerivWithinAt_higherOrder_cubic
    (hk : (3 : ℝ) < 2 * ((k : ℝ) - 1))
    (x : W^{k + 2,2}(ℝ^3) × W^{k + 1,2}(ℝ^3))
    {u : C(ℝ, H¹(ℝ^3) × DerivLp 3 2 univ)}
    (h : cubicNonlinearity.IsEnergySolution
      (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2) u)
    (U : C(ℝ, W^{k + 2,2}(ℝ^3) × W^{k + 1,2}(ℝ^3))) (hU₀ : U 0 = x)
    {b : ℝ} (hU : ∀ t ∈ Icc 0 b,
      (lowerOrderCLM (by omega : 1 ≤ k + 2) (U t).1,
        wkpBaseCoordinateCLM (U t).2) = u t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1)
        (U t).2 (Icc 0 b) t ∧
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2)
        (higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) (U t).1) (Icc 0 b) t := by
  have h1 : 1 ≤ k := by
    have h : (1 : ℝ) < k := by linarith
    have : 1 < k := by exact_mod_cast h
    omega
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
  · let A := (energyTriple 3).pivotToDual.comp (wkpBaseCoordinateCLM (n := 3) (m := k))
    apply hasDerivWithinAt_of_mapped_integral A ((energyTriple 3).pivotToDual_injective.comp
        (wkpBaseCoordinateCLM_injective isOpen_univ))
      ⟨_, (lowerOrderCLM (Nat.le_succ k)).continuous.comp U.continuous.snd⟩
      ⟨_, (continuous_higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp)).comp
        U.continuous.fst⟩ (t := t) (ht := ht)
    intro r hr
    have heq := h.velocity r hr.1
    rw [← hU r hr] at heq
    change (∫ s in (0 : ℝ)..r, (energyTriple 3).pivotToDual
      (wkpBaseCoordinateCLM (higherSmoothAcceleration hk (contDiff_id.pow 3) (by simp) (U s).1))) =
      (energyTriple 3).pivotToDual (wkpBaseCoordinateCLM (U r).2) -
        (energyTriple 3).pivotToDual (wkpBaseCoordinateCLM (U 0).2)
    rw [hU₀]
    refine Eq.trans ?_ heq
    apply intervalIntegral.integral_congr
    intro s hst
    rw [uIcc_of_le hr.1] at hst
    dsimp only
    rw [pivotToDual_higherSmoothAcceleration_cubic hk h1, ← hU s ⟨hst.1, hst.2.trans hr.2⟩]


end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
