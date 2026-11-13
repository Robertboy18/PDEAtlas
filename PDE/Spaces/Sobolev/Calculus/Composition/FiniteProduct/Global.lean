/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Smooth

/-!
# Sobolev composition of a finite family

The finite-product chain rule constructs a scalar element of the Sobolev
graph space. Its base row is the composed function and every first derivative row is
the derivative of the composing map applied to the corresponding weak derivative
column. All identifications are almost everywhere, so the construction is independent
of the representatives chosen by the underlying `Lᵖ` classes.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  {F : ℝ^m → ℝ} {C : ℝ≥0}

/-- The rows prescribed by the finite-product chain rule. -/
def compositionRows (F : ℝ^m → ℝ) (U : Fin m → W^{1,p}(Ω))
    (a : DerivIndex n 1) : ℝ^n → ℝ :=
  firstOrderRows (fun x ↦ F (values U x))
    (fun i x ↦ fderiv ℝ F (values U x) (derivatives U i x)) a

/-- Each prescribed row belongs to `Lᵖ`, on any measure domain. -/
theorem compositionRows_memLp (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C) (U : Fin m → W^{1,p}(Ω))
    (a : DerivIndex n 1) : MemLp (compositionRows F U a) p (domainMeasure n Ω) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · refine MemLp.ae_eq ?_ (memLp_valueIntegrand hF hzero hbound (vectorWkpFirstJetCLM U))
    filter_upwards [valuesCLM_firstJet_ae U] with x hx
    simpa only [compositionRows, firstOrderRows_baseIndex, valueIntegrand] using congrArg F hx
  · refine MemLp.ae_eq ?_ (memLp_derivativeIntegrand hF hbound i (vectorWkpFirstJetCLM U))
    filter_upwards [valuesCLM_firstJet_ae U, derivativeCLM_firstJet_ae U i] with x hx hy
    simpa only [compositionRows, firstOrderRows_singleDerivIndex, derivativeIntegrand] using
      congrArg₂ (fun z v ↦ fderiv ℝ F z v) hx hy

/-- On the whole space, each prescribed row is the corresponding weak derivative. -/
theorem compositionRows_weak (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(ℝ^n)) (a : DerivIndex n 1) :
    HasWeakDerivativeOn univ a.toList (fun x ↦ F (values U x)) (compositionRows F U a) := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · have hm := compositionRows_memLp hF hzero hbound U (baseIndex n 1)
    simp only [compositionRows, firstOrderRows_baseIndex] at hm
    simpa only [compositionRows, firstOrderRows_baseIndex, baseIndex_toList] using
      hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hm Fact.out)
  · simpa only [compositionRows, firstOrderRows_singleDerivIndex, singleDerivIndex_toList] using
      hasWeakDerivativeOn_comp hp hF hzero hbound U i

/-- Compose a finite family of global Sobolev fields with a zero-preserving `C¹`
function whose derivative is bounded. -/
def composition (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(ℝ^n)) : W^{1,p}(ℝ^n) :=
  mkWkpSpaceOnOfWeakDerivatives (fun x ↦ F (values U x)) (compositionRows F U)
    (by simp [compositionRows]) (compositionRows_memLp hF hzero hbound U)
    (compositionRows_weak hp hF hzero hbound U)

/-- The base representative of finite-product composition is the composed value. -/
theorem composition_base_ae (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(ℝ^n)) :
    (wkpBaseCoordinateCLM (composition hp hF hzero hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n univ] fun x ↦ F (values U x) := by
  have h := mkWkpSpaceOnOfWeakDerivatives_apply_ae
    (fun x ↦ F (values U x)) (compositionRows F U) (by simp [compositionRows])
    (compositionRows_memLp hF hzero hbound U) (compositionRows_weak hp hF hzero hbound U)
    (baseIndex n 1)
  simpa only [composition, wkpBaseCoordinateCLM_apply,
    compositionRows, firstOrderRows_baseIndex] using h

/-- Every first derivative representative is the derivative applied to its weak column. -/
theorem composition_derivative_ae (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(ℝ^n)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i) (composition hp hF hzero hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n univ]
        fun x ↦ fderiv ℝ F (values U x) (derivatives U i x) := by
  have h := mkWkpSpaceOnOfWeakDerivatives_apply_ae
    (fun x ↦ F (values U x)) (compositionRows F U) (by simp [compositionRows])
    (compositionRows_memLp hF hzero hbound U) (compositionRows_weak hp hF hzero hbound U)
    (singleDerivIndex n i)
  simpa only [composition, wkpCoordinateCLM_apply,
    compositionRows, firstOrderRows_singleDerivIndex] using h

end SobolevSpace.GraphSpace.FiniteProductComposition
