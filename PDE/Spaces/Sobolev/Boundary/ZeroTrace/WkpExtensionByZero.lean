/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Zero extension of the supported Sobolev core closure

Coordinatewise zero extension is an isometry on the finite derivative bundle.
For a smooth function supported inside the domain, this bundle is the bundle
of its global classical derivatives. Closedness of the weak derivative graph
then gives a global Sobolev function for every element of the supported-core
closure.

The construction applies to every derivative order and every `1 ≤ p ≤ ∞`.
The domain need only be measurable. On open domains its source is the usual
`W^{k,p}_0`; no boundary atlas or trace characterization is used.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.ZeroTrace

open Function MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Extend each weak derivative coordinate by zero, before imposing the
global weak derivative identities. -/
def zeroExtendAmbient (hΩ : MeasurableSet Ω) :
    WkpAmbientOn n k p Ω →L[ℝ] WkpAmbientOn n k p Set.univ := by
  classical
  let eΩ := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n k ↦ DerivLp n p Ω)
  let eUniv := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n k ↦ DerivLp n p Set.univ)
  exact eUniv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
      (Extension.Lp.zeroExtendLp hΩ).comp (ContinuousLinearMap.proj a)).comp
        eΩ.toContinuousLinearMap)

/-- Each coordinate is the linear `Lp` zero extension. -/
@[simp] theorem zeroExtendAmbient_apply (hΩ : MeasurableSet Ω)
    (U : WkpAmbientOn n k p Ω) (a : DerivIndex n k) :
    zeroExtendAmbient hΩ U a = Extension.Lp.zeroExtendLp hΩ (U a) := by
  classical
  simp [zeroExtendAmbient]

/-- Extending every coordinate preserves the product norm, including its
supremum-norm endpoint. -/
theorem norm_zeroExtendAmbient (hΩ : MeasurableSet Ω)
    (U : WkpAmbientOn n k p Ω) :
    ‖zeroExtendAmbient hΩ U‖ = ‖U‖ := by
  classical
  by_cases hp : p = ∞
  · subst p
    simp only [PiLp.norm_eq_ciSup, zeroExtendAmbient_apply,
      Extension.Lp.norm_zeroExtendLp]
  · have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    rw [PiLp.norm_eq_sum (ENNReal.toReal_pos hp0 hp),
      PiLp.norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    simp only [zeroExtendAmbient_apply, Extension.Lp.norm_zeroExtendLp]

/-- The supported classical derivatives vanish off the domain, so their
coordinate extensions are the same global smooth derivative bundle. -/
theorem zeroExtendAmbient_testFunction_eq
    (hΩ : MeasurableSet Ω) (φ : TestFunctionOn n Ω) :
    zeroExtendAmbient hΩ
        (testFunctionToWkp (k := k) (p := p) φ : WkpAmbientOn n k p Ω) =
      (testFunctionToWkp (k := k) (p := p)
        (⟨φ.1, subset_univ _⟩ : TestFunctionOn n Set.univ) :
          WkpAmbientOn n k p Set.univ) := by
  classical
  apply PiLp.ext
  intro a
  apply MeasureTheory.Lp.ext
  have hlocal := testFunctionToWkp_coordinate_ae (k := k) (p := p) φ a
  have hglobal := testFunctionToWkp_coordinate_ae (k := k) (p := p)
    (⟨φ.1, subset_univ _⟩ : TestFunctionOn n Set.univ) a
  have hzero := Extension.Lp.zeroExtendLp_apply_ae hΩ
    ((testFunctionToWkp (k := k) (p := p) φ : WkpAmbientOn n k p Ω) a)
  change _ =ᵐ[volume.restrict Ω] _ at hlocal
  have hlocal' := (ae_restrict_iff' hΩ).mp hlocal
  simp only [domainMeasure, Measure.restrict_univ] at hglobal hzero ⊢
  filter_upwards [hlocal', hglobal, hzero] with x hx hglobalx hzerox
  change (Extension.Lp.zeroExtendLp hΩ
    ((testFunctionToWkp (k := k) (p := p) φ : WkpAmbientOn n k p Ω) a)) x = _
  rw [hzerox, hglobalx]
  by_cases hxΩ : x ∈ Ω
  · exact (indicator_of_mem hxΩ _).trans (hx hxΩ)
  · rw [Extension.Lp.extensionByZero, indicator_of_notMem hxΩ]
    symm
    by_contra hne
    exact hxΩ (φ.2 (tsupport_iteratedPartialDeriv_subset_tsupport
      (n := n) a.toList φ.1.toFun (subset_tsupport _ hne)))

/-- The global weak derivative identities pass from supported smooth
functions to their closure through the continuous coordinate extension. -/
theorem zeroExtendAmbient_mem_globalWkp
    (hΩ : MeasurableSet Ω) (u : W₀^{k,p}(Ω)) :
    zeroExtendAmbient hΩ
        ((u : W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) ∈
      wkpSubmoduleOn n k p (Set.univ : Set (ℝ^n)) := by
  let A : W^{k,p}(Ω) →L[ℝ] WkpAmbientOn n k p Set.univ :=
    (zeroExtendAmbient hΩ).comp (Submodule.subtypeL (wkpSubmoduleOn n k p Ω))
  let S : Set (W^{k,p}(Ω)) :=
    A ⁻¹' (wkpSubmoduleOn n k p (Set.univ : Set (ℝ^n)) :
      Set (WkpAmbientOn n k p Set.univ))
  have hclosed : IsClosed S :=
    (isClosed_WkpSubmoduleOn n k p Set.univ).preimage A.continuous
  apply Wkp0SpaceOn.closed_property_of_testFunctions hclosed ?_ u
  intro φ
  change zeroExtendAmbient hΩ
      (testFunctionToWkp (k := k) (p := p) φ : WkpAmbientOn n k p Ω) ∈
    wkpSubmoduleOn n k p (Set.univ : Set (ℝ^n))
  rw [zeroExtendAmbient_testFunction_eq]
  exact (testFunctionToWkp (k := k) (p := p)
    (⟨φ.1, subset_univ _⟩ : TestFunctionOn n Set.univ)).property

/-- Zero extension from the supported-core Sobolev space to the whole-space
Sobolev space. All global weak derivatives are constructed by closure. -/
def zeroExtendWkp0 (hΩ : MeasurableSet Ω) :
    W₀^{k,p}(Ω) →L[ℝ] W^{k,p}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((zeroExtendAmbient hΩ).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n k p Ω)).comp
        (Submodule.subtypeL (wkp0SubmoduleOn (n := n) (k := k) (p := p)
          (Ω := Ω)).toSubmodule)))
    (wkpSubmoduleOn n k p (Set.univ : Set (ℝ^n)))
    (zeroExtendAmbient_mem_globalWkp hΩ)

/-- Extending a supported smooth function recovers its global Sobolev class. -/
@[simp] theorem zeroExtendWkp0_testFunction (hΩ : MeasurableSet Ω)
    (φ : TestFunctionOn n Ω) :
    zeroExtendWkp0 hΩ (testFunctionToWkp0 (k := k) (p := p) φ) =
      testFunctionToWkp (k := k) (p := p)
        (⟨φ.1, subset_univ _⟩ : TestFunctionOn n univ) := by
  apply Subtype.ext
  exact zeroExtendAmbient_testFunction_eq hΩ φ

/-- Zero extension preserves the Sobolev norm exactly. -/
theorem norm_zeroExtendWkp0 (hΩ : MeasurableSet Ω) (u : W₀^{k,p}(Ω)) :
    ‖zeroExtendWkp0 hΩ u‖ = ‖u‖ :=
  norm_zeroExtendAmbient hΩ
    ((u : W^{k,p}(Ω)) : WkpAmbientOn n k p Ω)

/-- Projection onto any derivative commutes with zero extension. -/
theorem zeroExtendWkp0_coordinate (hΩ : MeasurableSet Ω)
    (u : W₀^{k,p}(Ω)) (a : DerivIndex n k) :
    wkpCoordinateCLM a (zeroExtendWkp0 hΩ u) =
      Extension.Lp.zeroExtendLp hΩ
        (wkpCoordinateCLM a (u : W^{k,p}(Ω))) :=
  zeroExtendAmbient_apply hΩ
    ((u : W^{k,p}(Ω)) : WkpAmbientOn n k p Ω) a

/-- Each coordinate of zero extension is represented by the corresponding indicator. -/
theorem zeroExtendWkp0_coordinate_apply_ae (hΩ : MeasurableSet Ω)
    (u : W₀^{k,p}(Ω)) (a : DerivIndex n k) :
    (wkpCoordinateCLM a (zeroExtendWkp0 hΩ u) : ℝ^n → ℝ) =ᵐ[volume]
      Ω.indicator (wkpCoordinateCLM a (u : W^{k,p}(Ω)) : ℝ^n → ℝ) := by
  rw [zeroExtendWkp0_coordinate]
  simpa only [domainMeasure, Measure.restrict_univ, Extension.Lp.extensionByZero] using
    Extension.Lp.zeroExtendLp_apply_ae hΩ
      (wkpCoordinateCLM a (u : W^{k,p}(Ω)))

/-- Every coordinate of the extended Sobolev function vanishes almost
everywhere off the original measurable domain. -/
theorem zeroExtendWkp0_coordinate_ae_eq_zero (hΩ : MeasurableSet Ω)
    (u : W₀^{k,p}(Ω)) (a : DerivIndex n k) :
    ∀ᵐ x ∂volume, x ∉ Ω →
      (wkpCoordinateCLM a (zeroExtendWkp0 hΩ u) : ℝ^n → ℝ) x = 0 := by
  filter_upwards [zeroExtendWkp0_coordinate_apply_ae hΩ u a] with x hx hxΩ
  rw [hx, indicator_of_notMem hxΩ]

/-- Restriction to the original domain recovers each derivative coordinate. -/
theorem restrict_zeroExtendWkp0_coordinate (hΩ : MeasurableSet Ω)
    (u : W₀^{k,p}(Ω)) (a : DerivIndex n k) :
    restrictDerivLp (subset_univ Ω) (wkpCoordinateCLM a (zeroExtendWkp0 hΩ u)) =
      wkpCoordinateCLM a (u : W^{k,p}(Ω)) := by
  rw [zeroExtendWkp0_coordinate, Extension.Lp.restrict_zeroExtendLp]

/-- On the original domain, every coordinate of zero extension represents the
original weak derivative almost everywhere. -/
theorem zeroExtendWkp0_coordinate_ae_on (hΩ : MeasurableSet Ω)
    (u : W₀^{k,p}(Ω)) (a : DerivIndex n k) :
    (wkpCoordinateCLM a (zeroExtendWkp0 hΩ u) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpCoordinateCLM a (u : W^{k,p}(Ω)) : ℝ^n → ℝ) := by
  have h := restrictDerivLp_apply_ae (subset_univ Ω)
    (wkpCoordinateCLM a (zeroExtendWkp0 hΩ u))
  rw [restrict_zeroExtendWkp0_coordinate] at h
  exact h.symm

end SobolevSpace.GraphSpace.ZeroTrace
