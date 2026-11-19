/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Global
public import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore

/-!
# Finite-product composition on extension domains

Extending each scalar field lets the global chain rule act on a finite family.
Open-domain uniqueness of weak derivatives identifies every extended coordinate on the
original domain. Zero-preserving functions require no measure bound. On finite-measure
domains, subtracting and restoring the value at zero allows arbitrary affine shifts.

The extension operator is an intermediate analytic interface. Geometric applications
supply it from their boundary hypotheses.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open Filter MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
  {F : ℝ^m → ℝ} {C : ℝ≥0}

/-- Extending a finite family preserves its value vector almost everywhere on the domain. -/
theorem values_extension_ae (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (U : Fin m → W^{1,p}(Ω)) :
    values (fun j ↦ E.toContinuousLinearMap (U j)) =ᵐ[domainMeasure n Ω] values U := by
  have hb := ae_all_iff.mpr fun j ↦
    DomainComposition.extension_coordinate_ae hΩ E (U j) (baseIndex n 1)
  filter_upwards [hb] with x hx
  ext j
  exact hx j

/-- Extending a finite family preserves each derivative column on the domain. -/
theorem derivatives_extension_ae (hΩ : IsOpen Ω) (E : Extension.GraphSpace.Operator n 1 p Ω)
    (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    derivatives (fun j ↦ E.toContinuousLinearMap (U j)) i
      =ᵐ[domainMeasure n Ω] derivatives U i := by
  have hd := ae_all_iff.mpr fun j ↦
    DomainComposition.extension_coordinate_ae hΩ E (U j) (singleDerivIndex n i)
  filter_upwards [hd] with x hx
  ext j
  exact hx j

/-- Zero-preserving finite-product composition on an open extension domain, with no
finiteness requirement on its measure. -/
def zeroPreservingCompositionOn (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) : W^{1,p}(Ω) :=
  restrictCLM hΩ.measurableSet (subset_univ Ω)
    (composition hp hF hzero hbound (fun j ↦ E.toContinuousLinearMap (U j)))

/-- Zero-preserving domain composition has the expected value representative. -/
theorem zeroPreservingCompositionOn_base_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) :
    (wkpBaseCoordinateCLM (zeroPreservingCompositionOn hΩ E hp hF hzero hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ F (values U x) := by
  let V := composition hp hF hzero hbound (fun j ↦ E.toContinuousLinearMap (U j))
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  have hg := (composition_base_ae hp hF hzero hbound
    (fun j ↦ E.toContinuousLinearMap (U j))).filter_mono (ae_mono hmeasure)
  filter_upwards [restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) V (baseIndex n 1),
    hg, values_extension_ae hΩ E U] with x hr hv he
  change (wkpBaseCoordinateCLM (restrictCLM hΩ.measurableSet (subset_univ Ω) V) : ℝ^n → ℝ) x = _
  rw [show wkpBaseCoordinateCLM (restrictCLM hΩ.measurableSet (subset_univ Ω) V) x =
    wkpBaseCoordinateCLM V x from hr, hv, he]

/-- Zero-preserving domain composition has the expected weak derivative columns. -/
theorem zeroPreservingCompositionOn_derivative_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i)
      (zeroPreservingCompositionOn hΩ E hp hF hzero hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ fderiv ℝ F (values U x) (derivatives U i x) := by
  let V := composition hp hF hzero hbound (fun j ↦ E.toContinuousLinearMap (U j))
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  have hg := (composition_derivative_ae hp hF hzero hbound
    (fun j ↦ E.toContinuousLinearMap (U j)) i).filter_mono (ae_mono hmeasure)
  filter_upwards [restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) V
    (singleDerivIndex n i), hg, values_extension_ae hΩ E U,
    derivatives_extension_ae hΩ E U i] with x hr hv he hd
  change (wkpCoordinateCLM (singleDerivIndex n i)
    (restrictCLM hΩ.measurableSet (subset_univ Ω) V) : ℝ^n → ℝ) x = _
  rw [show wkpCoordinateCLM (singleDerivIndex n i)
    (restrictCLM hΩ.measurableSet (subset_univ Ω) V) x =
      wkpCoordinateCLM (singleDerivIndex n i) V x from hr, hv, he, hd]

variable [IsFiniteMeasure (domainMeasure n Ω)]

/-- Finite-product composition on a finite-measure domain, allowing arbitrary `F 0`. -/
def compositionOnOfExtension (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) : W^{1,p}(Ω) :=
  zeroPreservingCompositionOn (C := C) hΩ E hp (hF.sub contDiff_const) (sub_self (F 0))
    (fun z ↦ by simpa only [fderiv_sub_const] using hbound z) U +
      wkpConstant (F 0)

/-- Restoring the finite constant gives the uncentered value. -/
theorem compositionOnOfExtension_base_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) :
    (wkpBaseCoordinateCLM (compositionOnOfExtension hΩ E hp hF hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ F (values U x) := by
  let V := zeroPreservingCompositionOn (C := C) hΩ E hp (hF.sub contDiff_const) (sub_self (F 0))
    (fun z ↦ by simpa only [fderiv_sub_const] using hbound z) U
  have hv := zeroPreservingCompositionOn_base_ae (C := C) hΩ E hp (hF.sub contDiff_const)
    (sub_self (F 0)) (fun z ↦ by simpa only [fderiv_sub_const] using hbound z) U
  filter_upwards [DomainComposition.coordinate_add_ae V (wkpConstant (F 0))
    (baseIndex n 1), hv, wkpConstant_base_ae (p := p) (Ω := Ω) (F 0)]
    with x hs hb hc
  change wkpBaseCoordinateCLM (V + wkpConstant (F 0)) x = _
  change wkpBaseCoordinateCLM (V + wkpConstant (F 0)) x =
    wkpBaseCoordinateCLM V x + wkpBaseCoordinateCLM (wkpConstant (F 0)) x at hs
  change wkpBaseCoordinateCLM (wkpConstant (p := p) (Ω := Ω) (F 0)) x =
    F 0 at hc
  rw [hs, hb, hc]
  exact sub_add_cancel _ _

/-- Constant restoration leaves every chain-rule derivative unchanged. -/
theorem compositionOnOfExtension_derivative_ae (hΩ : IsOpen Ω)
    (E : Extension.GraphSpace.Operator n 1 p Ω) (hp : p ≠ ∞)
    (hF : ContDiff ℝ 1 F) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (U : Fin m → W^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i)
      (compositionOnOfExtension hΩ E hp hF hbound U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ fderiv ℝ F (values U x) (derivatives U i x) := by
  let V := zeroPreservingCompositionOn (C := C) hΩ E hp (hF.sub contDiff_const) (sub_self (F 0))
    (fun z ↦ by simpa only [fderiv_sub_const] using hbound z) U
  have hv := zeroPreservingCompositionOn_derivative_ae (C := C) hΩ E hp (hF.sub contDiff_const)
    (sub_self (F 0)) (fun z ↦ by simpa only [fderiv_sub_const] using hbound z) U i
  filter_upwards [DomainComposition.coordinate_add_ae V (wkpConstant (F 0))
    (singleDerivIndex n i), hv, wkpConstant_deriv_ae
      (p := p) (Ω := Ω) (F 0) i] with x hs hb hc
  change wkpCoordinateCLM (singleDerivIndex n i) (V + wkpConstant (F 0)) x = _
  change wkpCoordinateCLM (singleDerivIndex n i) (V + wkpConstant (F 0)) x =
    wkpCoordinateCLM (singleDerivIndex n i) V x +
      wkpCoordinateCLM (singleDerivIndex n i) (wkpConstant (F 0)) x at hs
  change wkpCoordinateCLM (singleDerivIndex n i)
    (wkpConstant (p := p) (Ω := Ω) (F 0)) x = 0 at hc
  rw [hs, hb, hc, add_zero, fderiv_sub_const]

end SobolevSpace.GraphSpace.FiniteProductComposition
