/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedPairing
public import PDE.Analysis.MeasureTheory.Lp.NonnegativeMultiplier

/-!
# Weighted energy of first-jet wave trajectories

Bounded spatial weights define continuous quadratic forms on the natural
energy space. The Sobolev H² persistence theorem makes the energy trajectory
absolutely continuous, so the quadratic-form chain rule applies.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n : ℕ}

/-- The weighted L² pairing pulled back along one energy coordinate. -/
def weightedCoordinateForm (a : DerivLp n ∞ univ)
    (B : (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ] DerivLp n 2 univ) :
    (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ]
      StrongDual ℝ (H¹(ℝ^n) × DerivLp n 2 univ) :=
  ((innerSL ℝ).comp ((ContinuousLinearMap.mul ℝ ℝ).holderL
    (domainMeasure n univ) ∞ 2 2 a)).bilinearComp B B

private theorem weightedCoordinateForm_apply (a : DerivLp n ∞ univ)
    (B : (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ] DerivLp n 2 univ) (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    weightedCoordinateForm a B z w = ⟪a • B z, B w⟫_ℝ := by
  rfl

/-- The weighted sum of the displacement, velocity and gradient L² pairings. -/
def weightedEnergyForm (a : DerivLp n ∞ univ) :
    (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ]
      StrongDual ℝ (H¹(ℝ^n) × DerivLp n 2 univ) :=
  weightedCoordinateForm a (ContinuousLinearMap.snd ℝ _ _) +
    weightedCoordinateForm a ((energyTriple n).inclusion.comp
      (ContinuousLinearMap.fst ℝ _ _)) +
    ∑ i : Fin n, weightedCoordinateForm a
      ((wkpCoordinateCLM (singleDerivIndex n i)).comp (ContinuousLinearMap.fst ℝ _ _))

/-- The quadratic form uses precisely the natural energy coordinates. -/
theorem weightedEnergyForm_apply (a : DerivLp n ∞ univ) (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    weightedEnergyForm a z w = ⟪a • z.2, w.2⟫_ℝ + ⟪a • wkpBaseCoordinateCLM z.1,
      wkpBaseCoordinateCLM w.1⟫_ℝ + ∑ i : Fin n, ⟪a • wkpCoordinateCLM (singleDerivIndex n i) z.1,
      wkpCoordinateCLM (singleDerivIndex n i) w.1⟫_ℝ := by
  simp only [weightedEnergyForm, add_apply, sum_apply, weightedCoordinateForm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', energyTriple]

/-- Real spatial multiplication gives a symmetric energy form. -/
theorem weightedEnergyForm_symmetric (a : DerivLp n ∞ univ) (z w : H¹(ℝ^n) × DerivLp n 2 univ) :
    weightedEnergyForm a z w = weightedEnergyForm a w z := by
  simp only [weightedEnergyForm_apply]
  congr 2
  · rw [Lp.inner_lpSMul_left, real_inner_comm]
  · rw [Lp.inner_lpSMul_left, real_inner_comm]
  · funext i
    rw [Lp.inner_lpSMul_left, real_inner_comm]

/-- Nonnegative weights give nonnegative localized energy. -/
theorem weightedEnergyForm_nonneg (a : DerivLp n ∞ univ)
    (ha : ∀ᵐ x ∂domainMeasure n univ, 0 ≤ a x)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) : 0 ≤ weightedEnergyForm a z z := by
  rw [weightedEnergyForm_apply]
  exact add_nonneg (add_nonneg (Lp.inner_lpSMul_self_nonneg a ha _)
    (Lp.inner_lpSMul_self_nonneg a ha _))
    (Finset.sum_nonneg fun _ _ ↦ Lp.inner_lpSMul_self_nonneg a ha _)

/-- A bounded spatial weight obeys the exact energy identity along every
first-jet solution with bounded higher velocity and acceleration lifts. -/
theorem IsEnergySolution.weighted_energy_identity {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
    {hf : LipschitzWith L f} {hf0 : f 0 = 0} {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (h : IsEnergySolution hf hf0 x u) {T : ℝ} (hT : 0 ≤ T)
    {V : ℝ → H¹(ℝ^n)} {A : ℝ → DerivLp n 2 univ} (hV : MemLp V ∞ (volume.restrict (Icc 0 T)))
    (hA : MemLp A ∞ (volume.restrict (Icc 0 T)))
    (hrepV : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).inclusion (V t) = (u t).2)
    (hrepA : ∀ t ∈ Icc (0 : ℝ) T, (energyTriple n).pivotToDual (A t) = acceleration hf hf0 (u t))
    (a : DerivLp n ∞ univ) :
    weightedEnergyForm a (u T) (u T) - weightedEnergyForm a x x =
      ∫ t in (0 : ℝ)..T, 2 * weightedEnergyForm a (u t) (V t, A t) := by
  obtain ⟨hAC, hd⟩ := h.absolutelyContinuous_of_lifts hT hV hA hrepV hrepA
  have hd' : ∀ᵐ t ∂volume.restrict (uIoc 0 T), HasDerivAt u (V t, A t) t := by
    simpa only [uIoc_of_le hT, ← restrict_Ioo_eq_restrict_Ioc] using hd
  have he := integrated_symmetric_quadratic_form_chain_rule
    (A := fun _ ↦ weightedEnergyForm a) (Adot := fun _ ↦ 0) (v := u) (dv := fun t ↦ (V t, A t))
    (LipschitzWith.const (weightedEnergyForm a)).lipschitzOnWith.absolutelyContinuousOnInterval hAC
    (Eventually.of_forall fun t ↦ hasDerivAt_const t (weightedEnergyForm a)) hd'
    (fun _ _ z w ↦ weightedEnergyForm_symmetric a z w)
  simpa only [h.initial, zero_apply, zero_add] using he

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
