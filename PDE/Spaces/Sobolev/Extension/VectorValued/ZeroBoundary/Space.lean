/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
public import PDE.Spaces.Sobolev.Extension.VectorValued.ZeroBoundary.Coordinates

/-!
# Zero extension of Banach-valued Sobolev functions with zero boundary values

Interior test functions extend smoothly by zero. The ambient extension preserves the
Sobolev norm, so closedness of the weak derivative graph extends this construction to
their closure `W₀^{k,p}(Ω; F)`. No regularity of the open domain is needed. Both exponent
endpoints and every finite derivative order are included.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Zero extension of a test function agrees with its inclusion in the ambient test space. -/
theorem zeroExtendAmbient_testFunctionToWkp (φ : 𝓓(Ω, F)) :
    zeroExtendAmbient (testFunctionToWkp (k := k) (p := p) φ).val =
      (testFunctionToWkp
        (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens ℝ^n), F))).val := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  have hzero := zeroExtendAmbient_apply_ae
    (testFunctionToWkp (k := k) (p := p) φ).val a
  have hlocal := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp
    (testFunctionToWkp_coordinate_ae (k := k) (p := p) φ a)
  have hglobal := testFunctionToWkp_coordinate_ae (k := k) (p := p)
    (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens ℝ^n), F)) a
  have hsupp : support (iteratedPartialDeriv a.toList (φ : ℝ^n → F)) ⊆ Ω :=
    (subset_tsupport _).trans
      ((PDE.tsupport_iteratedPartialDeriv_subset a.toList φ).trans φ.tsupport_subset)
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ,
    TestFunction.monoCLM_apply, le_refl, le_top, and_self, ↓reduceIte] at hzero hglobal ⊢
  exact hzero.trans (hlocal.trans
    ((Filter.EventuallyEq.of_eq (indicator_eq_self.mpr hsupp)).trans hglobal.symm))

/-- Zero extension preserves the weak derivative graph on the supported smooth closure. -/
theorem isWkpOn_zeroExtendAmbient (U : W₀^{k,p}(Ω; F)) :
    IsWkpOn (zeroExtendAmbient U.val.val) := by
  apply Wkp0SpaceOn.closed_property_of_testFunctions
    (isClosed_wkpSubmoduleOn.preimage
      (zeroExtendAmbient.comp (wkpSubmoduleOn n k p Ω F).subtypeL).continuous) ?_ U
  intro φ
  change IsWkpOn (zeroExtendAmbient (testFunctionToWkp φ).val)
  rw [zeroExtendAmbient_testFunctionToWkp]
  exact (testFunctionToWkp
    (TestFunction.monoCLM ℝ φ : 𝓓((⊤ : Opens ℝ^n), F))).property

/-- Extension by zero is a linear isometry from the supported smooth closure to whole space. -/
def zeroExtension : W₀^{k,p}(Ω; F) →ₗᵢ[ℝ] W^{k,p}((⊤ : Opens ℝ^n); F) where
  toFun U := ⟨zeroExtendAmbient U.val.val, isWkpOn_zeroExtendAmbient U⟩
  map_add' U V := by
    apply Subtype.ext
    exact map_add zeroExtendAmbient U.val.val V.val.val
  map_smul' c U := by
    apply Subtype.ext
    exact map_smul zeroExtendAmbient c U.val.val
  norm_map' U := norm_zeroExtendAmbient U.val.val

/-- Every derivative of the zero extension is the zero extension of that derivative. -/
theorem zeroExtension_coordinate_ae (U : W₀^{k,p}(Ω; F)) (a : DerivIndex n k) :
    ((zeroExtension U).val a : ℝ^n → F) =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)]
      (Ω : Set ℝ^n).indicator (U.val.val a : ℝ^n → F) := by
  change (zeroExtendAmbient U.val.val a : ℝ^n → F)
    =ᵐ[domainMeasure n (⊤ : Opens ℝ^n)] _
  simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
    zeroExtendAmbient_apply_ae U.val.val a

/-- Zero extension preserves the Sobolev norm, including at `p = 1` and `p = ∞`. -/
theorem norm_zeroExtension (U : W₀^{k,p}(Ω; F)) :
    ‖zeroExtension U‖ = ‖U‖ :=
  zeroExtension.norm_map U

/-- Restricting the zero extension recovers the original Sobolev function. -/
@[simp] theorem restrict_zeroExtension (U : W₀^{k,p}(Ω; F)) :
    restrictCLM (le_top : Ω ≤ ⊤) (zeroExtension U) = U.val := by
  apply WkpSpaceOn.ext_of_base_ae
  have hzero := zeroExtension_coordinate_ae U (baseIndex n k)
  have hlocal := ae_mono (Measure.restrict_mono (show (Ω : Set ℝ^n) ⊆ Set.univ from
    subset_univ _) le_rfl) hzero
  refine (restrictCLM_apply_ae le_top (zeroExtension U) (baseIndex n k)).trans ?_
  filter_upwards [hlocal, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  simpa only [indicator_of_mem hxΩ] using hx

end SobolevSpace.VectorValued
