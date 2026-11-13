/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedLinear
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.QuadraticDuhamel

/-!
# Weighted Duhamel bounds in physical wave coordinates

The quadratic semigroup estimate transfers through the energy-coordinate
isomorphism. The resulting retarded estimate applies to spatial L² forcing
integrable in time, as produced by compact localization of weak waves.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The coordinate Duhamel integral has the retarded weighted energy bound. -/
theorem sqrt_weightedEnergyForm_duhamel_le (χ : W^{1,∞}(ℝ^n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ, |(χ : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n i) y| ≤ ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    {F : ℝ → DerivLp n 2 univ} {t : ℝ} (ht : 0 ≤ t) (hF : IntervalIntegrable F volume 0 t) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    let d := C ((linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F s)) t)
    Real.sqrt (weightedEnergyForm a d d) ≤
      ∫ s in (0 : ℝ)..t, Real.exp ((3 + (n : ℝ) * ρ) * (t - s) / 2) *
        Real.sqrt (weightedEnergyForm a (0, F s) (0, F s)) := by
  intro a d
  let B := (weightedEnergyForm a).bilinearComp (C).toContinuousLinearMap (C).toContinuousLinearMap
  have hpos : ∀ x, 0 ≤ B x x := fun x ↦ weightedEnergyForm_nonneg a ha (C x)
  have hbound (r : NNReal) (x : EnergyState n) : B (linearSemigroup n r x) (linearSemigroup n r x) ≤
        B x x * Real.exp ((3 + (n : ℝ) * ρ) * r) := by
    have h := weightedEnergyForm_linearCoordinateOrbit_le χ hρ ha hd (C x) r.coe_nonneg
    simpa only [B, a, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, linearCoordinateOrbit, ContinuousMap.coe_mk,
      StronglyContinuousSemigroup.realOrbit, ContinuousLinearEquiv.symm_apply_apply,
      Real.toNNReal_coe] using h
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := (C).symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hJ : IntervalIntegrable (fun s ↦ (C).symm (0, F s)) volume 0 t :=
    intervalIntegrable_iff.mpr (J.integrable_comp hF.def')
  have h := sqrt_bilinear_duhamel_le B hpos (linearSemigroup n) hbound ht hJ
  simpa only [B, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using h

/-- Subtracting two integrable Duhamel terms subtracts their forces. -/
theorem duhamel_sub_of_intervalIntegrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : StronglyContinuousSemigroup E) {M : ℝ} (hS : ∀ r, ‖S r‖ ≤ M)
    {f g : ℝ → E} {t : ℝ} (hf : IntervalIntegrable f volume 0 t)
    (hg : IntervalIntegrable g volume 0 t) :
    S.duhamel f t - S.duhamel g t = S.duhamel (fun s ↦ f s - g s) t := by
  rw [StronglyContinuousSemigroup.duhamel, StronglyContinuousSemigroup.duhamel,
    StronglyContinuousSemigroup.duhamel, ← intervalIntegral.integral_sub
      (intervalIntegrable_duhamelIntegrand S hS hf t)
      (intervalIntegrable_duhamelIntegrand S hS hg t)]
  simp only [map_sub]

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
