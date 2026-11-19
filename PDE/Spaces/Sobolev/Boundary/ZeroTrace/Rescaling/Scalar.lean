/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.FirstOrder
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero.Gradient
public import PDE.DistributionTheory.TestFunction.ProperPrecomposition
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Rescaling functions with zero boundary values

Extend a function by zero, rescale it on the whole space, and restrict it to the
new domain. This construction preserves zero boundary values whenever the rescaled
original domain lies in the new one: a compactly supported smooth approximation
rescales to another such approximation.

The argument uses the definition of `W¹ᵖ₀` as a closure. It needs neither a smooth
boundary nor a trace theorem, and the scalar may be negative. Star-shaped domains
provide one useful application of the domain inclusion.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.ZeroTrace

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω V : Set (ℝ^n)}

/-- Pull a supported smooth function back by a nonzero scalar. The domain inclusion
ensures that its new support lies in `V`. -/
def dilationTestFunction (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V)
    (φ : TestFunctionOn n Ω) : TestFunctionOn n V :=
  let e : ℝ^n ≃L[ℝ] ℝ^n := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  ⟨TestFunction.precompProper e e.contDiff e.toHomeomorph.isProperMap φ.1,
    fun _ hx ↦ hΩV (φ.2 (tsupport_comp_subset_preimage φ.1 e.continuous hx))⟩

/-- The rescaled test function is ordinary composition. -/
@[simp] theorem dilationTestFunction_apply (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V)
    (φ : TestFunctionOn n Ω) (x : ℝ^n) :
    (dilationTestFunction a ha hΩV φ).1 x = φ.1 (a • x) :=
  rfl

/-- Extend by zero, dilate globally, and restrict to the target domain. -/
def dilationW1p0ToW1p (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : MeasurableSet V) (a : ℝ) (ha : a ≠ 0) :
    W₀^{1,p}(Ω) →L[ℝ] W^{1,p}(V) :=
  (restrictCLM hV (subset_univ V)).comp
    ((dilationW1pCLM hp a ha).comp (zeroExtendWkp0 hΩ))

/-- The rescaled Sobolev value is the rescaled zero extension, almost everywhere. -/
theorem dilationW1p0ToW1p_base_ae (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : MeasurableSet V) (a : ℝ) (ha : a ≠ 0) (u : W₀^{1,p}(Ω)) :
    baseRepresentative (dilationW1p0ToW1p hp hΩ hV a ha u)
      =ᵐ[domainMeasure n V]
        fun x ↦ Ω.indicator (baseRepresentative (u : W^{1,p}(Ω))) (a • x) := by
  have hres := restrictCLM_apply_ae hV (subset_univ V)
    (dilationW1pCLM hp a ha (zeroExtendWkp0 hΩ u)) (baseIndex n 1)
  have hdil := dilationW1pCLM_base_ae hp a ha (zeroExtendWkp0 hΩ u)
  have hzero := zeroExtendWkp0_coordinate_apply_ae hΩ u (baseIndex n 1)
  simp only [domainMeasure, Measure.restrict_univ] at hdil
  have hzeroa := (Measure.quasiMeasurePreserving_smul volume ha).ae hzero
  have hμ : domainMeasure n V ≤ (volume : Measure (ℝ^n)) :=
    Measure.restrict_le_self
  filter_upwards [hres, hdil.filter_mono (ae_mono hμ),
    hzeroa.filter_mono (ae_mono hμ)] with x hr hd hz
  exact hr.trans (hd.trans hz)

/-- On supported smooth functions, Sobolev rescaling is the usual rescaling. -/
theorem dilationW1p0ToW1p_testFunction (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (φ : TestFunctionOn n Ω) :
    dilationW1p0ToW1p hp hΩ hV.measurableSet a ha (testFunctionToWkp0 φ) =
      testFunctionToWkp (dilationTestFunction a ha hΩV φ) := by
  apply WkpSpaceOn.ext_of_base_ae hV
  have hzero : zeroExtendWkp0 hΩ (testFunctionToWkp0 (k := 1) (p := p) φ) =
      testFunctionToWkp (k := 1) (p := p)
        (⟨φ.1, subset_univ _⟩ : TestFunctionOn n univ) :=
    zeroExtendWkp0_testFunction hΩ φ
  have hres := restrictCLM_apply_ae hV.measurableSet (subset_univ V)
    (dilationW1pCLM hp a ha (zeroExtendWkp0 hΩ (testFunctionToWkp0 φ)))
    (baseIndex n 1)
  have hglobal := dilationW1pCLM_base_ae hp a ha
    (zeroExtendWkp0 hΩ (testFunctionToWkp0 φ))
  have hφ := testFunctionToWkp_coordinate_ae (k := 1) (p := p)
    (⟨φ.1, subset_univ _⟩ : TestFunctionOn n univ) (baseIndex n 1)
  rw [← hzero] at hφ
  simp only [domainMeasure, Measure.restrict_univ] at hφ hglobal
  have hφa := (Measure.quasiMeasurePreserving_smul volume ha).ae hφ
  have hθ := testFunctionToWkp_coordinate_ae (k := 1) (p := p)
    (dilationTestFunction a ha hΩV φ) (baseIndex n 1)
  have hμ : domainMeasure n V ≤ (volume : Measure (ℝ^n)) :=
    Measure.restrict_le_self
  filter_upwards [hres, hglobal.filter_mono (ae_mono hμ),
    hφa.filter_mono (ae_mono hμ), hθ] with x hr hg hφx hθx
  simp only [baseIndex_toList, iteratedPartialDeriv] at hφx hθx
  change _ = φ.1 (a • x) at hφx hθx
  exact hr.trans (hg.trans (hφx.trans hθx.symm))

/-- Rescaling preserves the supported-core closure when the rescaled domain lies
inside the target domain. -/
theorem dilationW1p0ToW1p_mem (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (u : W₀^{1,p}(Ω)) :
    dilationW1p0ToW1p hp hΩ hV.measurableSet a ha u ∈
      (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := V)).toSubmodule := by
  refine DenseRange.induction_on denseRange_testFunctionToWkp0Linear u ?_ ?_
  · exact (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := V)).isClosed'.preimage
      (dilationW1p0ToW1p hp hΩ hV.measurableSet a ha).continuous
  · intro φ
    rw [show testFunctionToWkp0Linear φ = testFunctionToWkp0 φ from rfl,
      dilationW1p0ToW1p_testFunction hp hΩ hV a ha hΩV]
    exact testFunctionToWkp_mem_Wkp0 _

/-- Dilation as a bounded map between the zero-boundary Sobolev spaces. -/
def dilationW1p0CLM (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) :
    W₀^{1,p}(Ω) →L[ℝ] W₀^{1,p}(V) :=
  (dilationW1p0ToW1p hp hΩ hV.measurableSet a ha).codRestrict
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := V)).toSubmodule
    (dilationW1p0ToW1p_mem hp hΩ hV a ha hΩV)

/-- The zero-boundary operator agrees with rescaling on its dense smooth core. -/
@[simp] theorem dilationW1p0CLM_testFunction (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (φ : TestFunctionOn n Ω) :
    dilationW1p0CLM hp hΩ hV a ha hΩV (testFunctionToWkp0 φ) =
      testFunctionToWkp0 (dilationTestFunction a ha hΩV φ) := by
  apply Subtype.ext
  exact dilationW1p0ToW1p_testFunction hp hΩ hV a ha hΩV φ

/-- Extending the rescaled zero-boundary element agrees with rescaling the original
zero extension. This equality also identifies all weak derivative coordinates. -/
theorem zeroExtendWkp0_dilationW1p0CLM (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (u : W₀^{1,p}(Ω)) :
    zeroExtendWkp0 hV.measurableSet (dilationW1p0CLM hp hΩ hV a ha hΩV u) =
      dilationW1pCLM hp a ha (zeroExtendWkp0 hΩ u) := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  have hlocal := dilationW1p0ToW1p_base_ae hp hΩ hV.measurableSet a ha u
  change _ =ᵐ[volume.restrict V] _ at hlocal
  have hlocal' := (ae_restrict_iff' hV.measurableSet).mp hlocal
  have hzero := zeroExtendWkp0_coordinate_apply_ae hV.measurableSet
    (dilationW1p0CLM hp hΩ hV a ha hΩV u) (baseIndex n 1)
  have hglobal := dilationW1p0ToW1p_base_ae hp hΩ MeasurableSet.univ a ha u
  simp only [dilationW1p0ToW1p, ContinuousLinearMap.comp_apply,
    restrictCLM_self, ContinuousLinearMap.id_apply,
    domainMeasure, Measure.restrict_univ] at hglobal
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hlocal', hzero, hglobal] with x hl hz hg
  change baseRepresentative (zeroExtendWkp0 hV.measurableSet
    (dilationW1p0CLM hp hΩ hV a ha hΩV u)) x =
      baseRepresentative (dilationW1pCLM hp a ha (zeroExtendWkp0 hΩ u)) x
  change baseRepresentative (zeroExtendWkp0 hV.measurableSet
    (dilationW1p0CLM hp hΩ hV a ha hΩV u)) x = _ at hz
  rw [hz, hg]
  by_cases hx : x ∈ V
  · rw [indicator_of_mem hx]
    exact hl hx
  · have hax : a • x ∉ Ω := fun hax ↦ hx (hΩV hax)
    rw [indicator_of_notMem hx, indicator_of_notMem hax]

/-- Rescaling changes the full gradient norm by the usual Jacobian and chain-rule
factors. Zero boundary values allow the formula to hold even when the rescaled
domain is a proper subset of the target domain. -/
theorem norm_wkpGradientCLM_dilationW1p0CLM (hp : p ≠ ∞) (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (u : W₀^{1,p}(Ω)) :
    ‖∇ (dilationW1p0CLM hp hΩ hV a ha hΩV u : W^{1,p}(V))‖ =
      |a| * |(a ^ n)⁻¹| ^ (1 / p).toReal *
        ‖∇ (u : W^{1,p}(Ω))‖ := by
  rw [← norm_wkpGradientCLM_zeroExtendWkp0 hV.measurableSet,
    zeroExtendWkp0_dilationW1p0CLM, norm_wkpGradientCLM_dilationW1pCLM,
    norm_wkpGradientCLM_zeroExtendWkp0]

/-- The squared `L²` gradient norm has the Dirichlet-energy scaling factor.
This form avoids square roots in variational calculations. -/
theorem norm_wkpGradientCLM_dilationW1p0CLM_sq (hΩ : MeasurableSet Ω)
    (hV : IsOpen V) (a : ℝ) (ha : a ≠ 0)
    (hΩV : (fun x : ℝ^n ↦ a • x) ⁻¹' Ω ⊆ V) (u : W₀^{1,2}(Ω)) :
    ‖∇ (dilationW1p0CLM (by norm_num) hΩ hV a ha hΩV u : W^{1,2}(V))‖ ^ 2 =
      a ^ 2 * |(a ^ n)⁻¹| * ‖∇ (u : W^{1,2}(Ω))‖ ^ 2 := by
  rw [norm_wkpGradientCLM_dilationW1p0CLM, mul_pow, mul_pow, sq_abs,
    ← Real.rpow_mul_natCast (abs_nonneg _) _ 2]
  norm_num

end SobolevSpace.GraphSpace.ZeroTrace
