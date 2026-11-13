/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Localization.Cutoff.ExtensionCoordinates

/-!
# Lipschitz chain rules on open domains

The weak chain rule is local. For a test function supported inside an open
domain, choose a smooth cutoff equal to one near its support. The cutoff
extends the Sobolev function to the whole space and preserves its first
derivatives on that support. The whole-space chain rule therefore gives the
original distributional identity.

No boundary regularity, extension operator, or finite-volume assumption is
needed. A zero-preserving Lipschitz map also preserves global `Lᵖ`
integrability on an unbounded domain, for every `1 ≤ p ≤ ∞`.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function
open CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped ENNReal NNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- The derivative prescribed by the Lipschitz chain rule belongs to the
same `Lᵖ` space as the original derivative. -/
theorem memLp_lipschitz_chainDerivative
    {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    MemLp (fun x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x)
      p (domainMeasure n Ω) := by
  have hu : MemLp (baseRepresentative U) p (domainMeasure n Ω) := Lp.memLp _
  have hdu := Lp.memLp (U.val (singleDerivIndex n i))
  apply MemLp.of_le_mul (c := (C : ℝ)) hdu
  · exact ((measurable_deriv F).aestronglyMeasurable.comp_aemeasurable
      hu.aestronglyMeasurable.aemeasurable).mul hdu.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hF) (norm_nonneg _)

variable [Fact (1 ≤ p)]

/-- The scalar Lipschitz chain rule holds on every open domain. The
zero-preserving assumption ensures integrability on domains of infinite
volume; the proof uses only compact localization of each test. -/
private theorem hasWeakDerivativeOn_comp_lipschitz_zero_of_isOpen
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hFzero : F 0 = 0)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (F ∘ baseRepresentative U)
      (fun x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x) := by
  have : Fact (0 < n) := ⟨lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩
  have hu : MemLp (baseRepresentative U) p (domainMeasure n Ω) := Lp.memLp _
  refine ⟨memLp_locallyIntegrableOn_domain (hF.comp_memLp hFzero hu) Fact.out,
    memLp_locallyIntegrableOn_domain (memLp_lipschitz_chainDerivative hF U i) Fact.out, ?_⟩
  intro φ hφ
  obtain ⟨ψ, hψΩ, hψone, hψnhds, _⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ φ.hasCompactSupport.isCompact hφ
  let V := extendByCutoff hΩ (subset_univ Ω) ψ hψΩ U
  have hlocal := (hasWeakDerivativeOn_comp_lipschitz hF hFzero V i).mono
    hΩ.measurableSet (subset_univ Ω)
  have hmeasure : domainMeasure n Ω ≤ domainMeasure n Set.univ := by
    simpa only [domainMeasure, Measure.restrict_univ] using Measure.restrict_le_self
  have hv := (extendByCutoff_base_ae hΩ (subset_univ Ω) ψ hψΩ U).filter_mono
    (ae_mono hmeasure)
  have hdv := (extendByCutoff_derivative_ae_on_core hΩ (subset_univ Ω) ψ hψΩ U i
    hψnhds).filter_mono (ae_mono hmeasure)
  have hleft :
      (∫ x, F (baseRepresentative U x) * iteratedPartialDeriv [i] φ.toFun x
        ∂domainMeasure n Ω) =
      ∫ x, F (baseRepresentative V x) * iteratedPartialDeriv [i] φ.toFun x
        ∂domainMeasure n Ω := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    by_cases hxs : x ∈ tsupport φ.toFun
    · have heq : baseRepresentative V x = baseRepresentative U x := by
        simpa only [hψone x hxs, one_mul] using hx
      rw [heq]
    · have hzero : iteratedPartialDeriv [i] φ.toFun x = 0 :=
        image_eq_zero_of_notMem_tsupport fun hx ↦
          hxs (tsupport_iteratedPartialDeriv_subset_tsupport [i] φ.toFun hx)
      simp only [hzero, mul_zero]
  have hright :
      (∫ x, (deriv F (baseRepresentative V x) * V.val (singleDerivIndex n i) x) *
        φ.toFun x ∂domainMeasure n Ω) =
      ∫ x, (deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x) *
        φ.toFun x ∂domainMeasure n Ω := by
    apply integral_congr_ae
    filter_upwards [hv, hdv] with x hx hdx
    by_cases hxs : x ∈ tsupport φ.toFun
    · have heq : baseRepresentative V x = baseRepresentative U x := by
        simpa only [hψone x hxs, one_mul] using hx
      rw [heq, hdx hxs]
    · simp only [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  change (∫ x, F (baseRepresentative U x) * iteratedPartialDeriv [i] φ.toFun x
      ∂domainMeasure n Ω) =
    (-1 : ℝ) ^ [i].length * ∫ x,
      (deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x) *
        φ.toFun x ∂domainMeasure n Ω
  rw [hleft, ← hright]
  exact hlocal φ hφ

/-- A scalar Lipschitz map satisfies the weak chain rule on any open
domain, including at `p = 1` and `p = ∞`. Neither finite volume nor
`F(0) = 0` is needed for this local derivative identity. -/
theorem hasWeakDerivativeOn_comp_lipschitz_on
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (U : W^{1,p}(Ω)) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (F ∘ baseRepresentative U)
      (fun x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x) := by
  have hcenter : LipschitzWith C (fun x ↦ F x - F 0) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [dist_sub_right] using hF.dist_le_mul x y
  have hchain := hasWeakDerivativeOn_comp_lipschitz_zero_of_isOpen hΩ hcenter
    (sub_self (F 0)) U i
  have hconstant : HasWeakDerivativeOn Ω [i] (fun _ ↦ F 0) (fun _ ↦ 0) := by
    simpa only [iteratedPartialDeriv, partialDeriv, fderiv_const_apply, zero_apply] using
      hasWeakDerivativeOn_iteratedPartialDeriv
        (Ω := Ω) (f := fun _ : ℝ^n ↦ F 0) contDiff_const [i]
  simpa only [Pi.add_def, Function.comp_def, sub_add_cancel,
    deriv_sub_const, add_zero] using hasWeakDerivativeOn_add hchain hconstant

/-- Compose a Sobolev function on an arbitrary open domain with a
Lipschitz scalar map. The sole additional condition is that the resulting
base function belongs to `Lᵖ`; its weak derivatives then belong to `Lᵖ`
automatically. -/
def lipschitzCompositionOfMemLp
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω))
    (hmem : MemLp (F ∘ baseRepresentative U) p (domainMeasure n Ω)) :
    W^{1,p}(Ω) :=
  let f := F ∘ baseRepresentative U
  let d := fun i x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x
  mkWkpSpaceOnOfWeakDerivatives f (firstOrderRows f d)
    (firstOrderRows_baseIndex f d)
    (fun a ↦ by
      rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
      · simpa only [firstOrderRows_baseIndex] using hmem
      · simpa only [firstOrderRows_singleDerivIndex] using memLp_lipschitz_chainDerivative hF U i)
    (fun a ↦ by
      rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
      · simpa only [baseIndex_toList, firstOrderRows_baseIndex] using
          hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hmem Fact.out)
      · simpa only [singleDerivIndex_toList, firstOrderRows_singleDerivIndex] using
          hasWeakDerivativeOn_comp_lipschitz_on hΩ hF U i)

/-- The composition's base representative is the ordinary pointwise
composition, up to the almost-everywhere equality inherent in `Lᵖ`. -/
theorem lipschitzCompositionOfMemLp_base_ae
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω))
    (hmem : MemLp (F ∘ baseRepresentative U) p (domainMeasure n Ω)) :
    baseRepresentative (lipschitzCompositionOfMemLp hΩ hF U hmem)
      =ᵐ[domainMeasure n Ω] F ∘ baseRepresentative U := by
  simpa [lipschitzCompositionOfMemLp, baseRepresentative,
    mkWkpSpaceOnOfWeakDerivatives] using hmem.coeFn_toLp

/-- The first derivative coordinates of composition are the products
specified by the weak chain rule. -/
theorem lipschitzCompositionOfMemLp_derivative_ae
    (hΩ : IsOpen Ω) {F : ℝ → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (U : W^{1,p}(Ω))
    (hmem : MemLp (F ∘ baseRepresentative U) p (domainMeasure n Ω)) (i : Fin n) :
    ((lipschitzCompositionOfMemLp hΩ hF U hmem).val (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        fun x ↦ deriv F (baseRepresentative U x) * U.val (singleDerivIndex n i) x := by
  simpa [lipschitzCompositionOfMemLp, mkWkpSpaceOnOfWeakDerivatives] using
    (memLp_lipschitz_chainDerivative hF U i).coeFn_toLp

end SobolevSpace.GraphSpace
