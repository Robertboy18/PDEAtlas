/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.Lp.ZeroExtension
public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Source pullbacks for C¹ boundary flattening

The first step in straightening a boundary patch is to move a single `L^p`
coordinate from the domain `Ω` to the flattened picture.  For the `i`-th
boundary chart `Φᵢ`, an element `u ∈ L^p(Ω)` is extended by zero to the chart
source and then pulled back through the inverse chart, `y ↦ u(Φᵢ⁻¹ y)`, but
only on the compact set `boundarySupportInTarget i = Φᵢ(supp ψᵢ)`, the image
of the support of the `i`-th partition function.  Restricting to a compact
subset of the chart target is what makes the pullback bounded on `L^p`: on a
compact set the Jacobian of the `C¹` map `Φᵢ⁻¹` is bounded above and below,
so `L^p` norms change by at most a constant factor.  The general bounded
pullback used here is `WeakChangeOfVariables.localizedPullbackCLM`.

## Main definitions and results

* `flattenCompactLp i : L^p(Ω) →L L^p(boundarySupportInTarget i)`: the
  compactly supported pullback `u ↦ 𝟙_{supp ψᵢ} · (𝟙_Ω u) ∘ Φᵢ⁻¹`.
* `flattenCompactLp_apply_ae`: its almost-everywhere formula.

The zero extension of the result to the upper half-space is carried out in
`Flattening.ZeroExtension`, and the Jacobian weights for the derivative
coordinates in `Flattening.Jacobian`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open Set
open scoped ENNReal Topology

namespace Extension

namespace C1

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

open MeasureTheory
open CompactSupportLocalization
open Boundary.C1ExtensionAtlas.DerivedCutoffs

namespace BoundaryPiece

variable [Fact (0 < n)] [Fact (1 ≤ p)] [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Regard an `Lᵖ(Ω)` coordinate as an `Lᵖ` coordinate on the chart source,
using zero outside `Ω`. -/
noncomputable def flattenSourceLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p Ω →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).source :=
  (SobolevSpace.GraphSpace.restrictDerivLp
    (n := n) (p := p) (Ω := (hΩ.chart i).source)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _)).comp
      (SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet)

/-- Almost-everywhere semantics of a source-chart coordinate obtained by zero
extension from `Ω`. -/
private theorem flattenSourceLp_apply_ae
    (i : Fin hΩ.N) (u : SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenSourceLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p (hΩ.chart i).source) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (hΩ.chart i).source]
        Ω.indicator (fun x ↦ u x) := by
  let z := SobolevSpace.Extension.Lp.zeroExtendLp
    (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet u
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p) (Ω := (hΩ.chart i).source)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _) z
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (Ω := Ω) hΩ.isOpen.measurableSet u
  have hzeroSource : ∀ᵐ x ∂ domainMeasure n (hΩ.chart i).source,
      (z : ℝ^n → ℝ) x = Ω.indicator (fun y ↦ u y) x := by
    simpa [z, SobolevSpace.Extension.Lp.extensionByZero, domainMeasure,
      Measure.restrict_restrict, inter_univ] using
      MeasureTheory.ae_restrict_of_ae (s := (hΩ.chart i).source) hzero
  simpa [flattenSourceLp, z] using hrestrict.trans hzeroSource

/-- Compactly supported pullback `f ↦ f ∘ chart.symm` on the `i`-th
partition support. -/
noncomputable def flattenCompactLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p Ω →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p
        (boundarySupportInTarget (n := n) (Ω := Ω) i) := by
  let pull := SobolevSpace.WeakChangeOfVariables.localizedPullbackCLM
    (n := n) (p := p) (E := (hΩ.chart i).symm)
    (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
    (isCompact_boundarySupport (n := n) (Ω := Ω) i)
    (boundarySupport_subset_source (n := n) (Ω := Ω) i)
  change SobolevSpace.GraphSpace.DerivLp n p Ω →L[ℝ]
    MeasureTheory.Lp ℝ p
      (domainMeasure n
        (SobolevSpace.WeakChangeOfVariables.compactPullbackSource
          (n := n) (hΩ.chart i).symm
          (boundarySupport (n := n) (Ω := Ω) i)))
  exact pull.comp (flattenSourceLp (n := n) (p := p) (Ω := Ω) i)

/-- Almost-everywhere semantics of compact inverse-chart pullback. -/
theorem flattenCompactLp_apply_ae
    (i : Fin hΩ.N) (u : SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenCompactLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p
          (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n
        (boundarySupportInTarget (n := n) (Ω := Ω) i)]
        fun y ↦
          (boundarySupport (n := n) (Ω := Ω) i).indicator
            (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y) := by
  let E := (hΩ.chart i).symm
  let K := boundarySupport (n := n) (Ω := Ω) i
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  let sourceU := flattenSourceLp (n := n) (p := p) (Ω := Ω) i u
  have hpull := SobolevSpace.WeakChangeOfVariables.localizedPullbackLp_apply_ae
    (n := n) (p := p) (E := E)
    (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
    (isCompact_boundarySupport (n := n) (Ω := Ω) i)
    (boundarySupport_subset_source (n := n) (Ω := Ω) i)
    sourceU
  have hsource := flattenSourceLp_apply_ae (n := n) (p := p) (Ω := Ω) i u
  have hqmp :
      MeasureTheory.QuasiMeasurePreserving (fun y ↦ E y)
        (domainMeasure n E.source) (domainMeasure n E.target) :=
    SobolevSpace.WeakChangeOfVariables.quasiMeasurePreserving_partialHomeomorph
      (n := n) (E := E) (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
  have hcompTarget := hqmp.ae_eq_comp hsource
  have hKTsub : KT ⊆ E.source := by
    simpa [E, KT] using
      boundarySupportInTarget_subset_target (n := n) (Ω := Ω) i
  have hmeasure : (domainMeasure n E.source).restrict KT = domainMeasure n KT := by
    simpa [domainMeasure] using
      (Measure.restrict_restrict_of_subset
        (μ := (MeasureTheory.volume : Measure (ℝ^n))) hKTsub)
  have hcomp : ∀ᵐ y ∂ domainMeasure n KT,
      sourceU (E y) = Ω.indicator (fun x ↦ u x) (E y) := by
    simpa [← hmeasure] using MeasureTheory.ae_restrict_of_ae hcompTarget
  have hpull' : ∀ᵐ y ∂ domainMeasure n KT,
      ((flattenCompactLp (n := n) (p := p) (Ω := Ω) i u :
          SobolevSpace.GraphSpace.DerivLp n p KT) : ℝ^n → ℝ) y =
        SobolevSpace.WeakChangeOfVariables.localizedPullbackFun
          (n := n) (p := p) E K sourceU y := by
    change ∀ᵐ y ∂ domainMeasure n
        (SobolevSpace.WeakChangeOfVariables.compactPullbackSource
          (n := n) E K),
      ((SobolevSpace.WeakChangeOfVariables.localizedPullbackLp
          (n := n) (p := p) (E := E)
          (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
          (isCompact_boundarySupport
            (n := n) (Ω := Ω) i)
          (boundarySupport_subset_source
            (n := n) (Ω := Ω) i) sourceU) : ℝ^n → ℝ) y =
        SobolevSpace.WeakChangeOfVariables.localizedPullbackFun
          (n := n) (p := p) E K sourceU y
    change ∀ᵐ y ∂ domainMeasure n
        (SobolevSpace.WeakChangeOfVariables.compactPullbackSource
          (n := n) E K),
      ((SobolevSpace.WeakChangeOfVariables.localizedPullbackLp
          (n := n) (p := p) (E := E)
          (hΩ.chart_symm_contDiff i) (hΩ.chart_contDiff i)
          (isCompact_boundarySupport
            (n := n) (Ω := Ω) i)
          (boundarySupport_subset_source
            (n := n) (Ω := Ω) i) sourceU) : ℝ^n → ℝ) y =
        SobolevSpace.WeakChangeOfVariables.localizedPullbackFun
          (n := n) (p := p) E K sourceU y at hpull
    exact hpull
  filter_upwards [hpull', hcomp] with y hypull hycomp
  rw [hypull]
  by_cases hyK : E y ∈ K
  · simp only [SobolevSpace.WeakChangeOfVariables.localizedPullbackFun,
      Set.indicator_of_mem hyK]
    simpa [E, K, Set.indicator_of_mem hyK] using hycomp
  · simp [SobolevSpace.WeakChangeOfVariables.localizedPullbackFun, E, K, hyK]

end BoundaryPiece

end C1

end Extension

end SobolevSpace
