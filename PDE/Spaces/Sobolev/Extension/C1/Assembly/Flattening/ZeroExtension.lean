/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.SourcePullback
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport -- shake: keep

/-!
# Zero extension of flattened C¹ coordinates

After a coordinate has been pulled back through a boundary chart onto the
compact set `boundarySupportInTarget i` (see `Flattening.SourcePullback`), it
must be regarded as a function on the whole upper half-space `ℝ^n₊`, where the
half-space reflection operator acts.  Since the compact set lies inside the
chart target and the function vanishes off it, extension by zero followed by
restriction to `ℝ^n₊` is a bounded map on `L^p`, and the resulting element is
represented by the indicator of the compact set times the pulled-back function.

## Main definitions and results

* `compactToUpperLp i : L^p(boundarySupportInTarget i) →L L^p(ℝ^n₊)`: zero
  extension followed by restriction to the upper half-space, with its
  almost-everywhere formula `compactToUpperLp_apply_ae`.
* `flattenUpperLp i : L^p(Ω) →L L^p(ℝ^n₊)`: the composite of the compact pullback
  with this zero extension, so that `flattenUpperLp i u` is
  `𝟙_{Φᵢ(supp ψᵢ)} · (𝟙_{supp ψᵢ} 𝟙_Ω u) ∘ Φᵢ⁻¹` almost everywhere on `ℝ^n₊`
  (`flattenUpperLp_apply_ae`).

The same zero extension is applied in `Flattening.Assembly` to the
Jacobian-weighted derivative coordinates of `Flattening.Jacobian`.
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

/-- Extend an `Lᵖ` coordinate on `boundarySupportInTarget i` by zero and retain it on the
upper half-space. -/
noncomputable def compactToUpperLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p
        (boundarySupportInTarget (n := n) (Ω := Ω) i) →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n) :=
  (SobolevSpace.GraphSpace.restrictDerivLp
    (n := n) (p := p) (Ω := SobolevSpace.HalfSpace.upper n)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _)).comp
      (SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p)
        (Ω := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (isCompact_boundarySupportInTarget
          (n := n) (Ω := Ω) i).measurableSet)

/-- Almost-everywhere semantics of compact zero extension followed by upper
restriction. -/
theorem compactToUpperLp_apply_ae
    (i : Fin hΩ.N)
    (u : SobolevSpace.GraphSpace.DerivLp n p
      (boundarySupportInTarget (n := n) (Ω := Ω) i)) :
    ((compactToUpperLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
          (fun y ↦ u y) := by
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  let globalU := SobolevSpace.Extension.Lp.zeroExtendLp
    (n := n) (p := p) (Ω := KT)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).measurableSet u
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p) (Ω := SobolevSpace.HalfSpace.upper n)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _) globalU
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (Ω := KT)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).measurableSet u
  have hzeroUpper := MeasureTheory.ae_restrict_of_ae
    (s := SobolevSpace.HalfSpace.upper n) hzero
  have hzeroUpper' : ∀ᵐ y ∂ domainMeasure n (SobolevSpace.HalfSpace.upper n),
      (globalU : ℝ^n → ℝ) y =
        SobolevSpace.Extension.Lp.extensionByZero
          (n := n) (p := p) (Ω := KT) u y := by
    simpa [domainMeasure, Measure.restrict_restrict, inter_univ] using hzeroUpper
  have hrestrict' :
      ((compactToUpperLp (n := n) (p := p) (Ω := Ω) i u :
          SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
          (globalU : ℝ^n → ℝ) := by
    simpa [compactToUpperLp, globalU] using hrestrict
  filter_upwards [hrestrict', hzeroUpper'] with y hyrestrict hyzero
  rw [hyrestrict, hyzero]
  by_cases hyKT : y ∈ KT <;>
    simp [SobolevSpace.Extension.Lp.extensionByZero, KT, hyKT]

/-- Extend a compact flattened coordinate by zero and retain it on the upper
half-space. -/
noncomputable def flattenUpperLp (i : Fin hΩ.N) :
    SobolevSpace.GraphSpace.DerivLp n p Ω →L[ℝ]
      SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n) :=
  (SobolevSpace.GraphSpace.restrictDerivLp
    (n := n) (p := p) (Ω := SobolevSpace.HalfSpace.upper n)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _)).comp
      ((SobolevSpace.Extension.Lp.zeroExtendLp
        (n := n) (p := p)
        (Ω := boundarySupportInTarget (n := n) (Ω := Ω) i)
        (isCompact_boundarySupportInTarget
          (n := n) (Ω := Ω) i).measurableSet).comp
        (flattenCompactLp (n := n) (p := p) (Ω := Ω) i))

/-- Almost-everywhere semantics after zero extension from the compact chart
image and restriction to the upper half-space. -/
theorem flattenUpperLp_apply_ae
    (i : Fin hΩ.N) (u : SobolevSpace.GraphSpace.DerivLp n p Ω) :
    ((flattenUpperLp (n := n) (p := p) (Ω := Ω) i u :
        SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
        ℝ^n → ℝ)
      =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
        (boundarySupportInTarget (n := n) (Ω := Ω) i).indicator
          (fun y ↦
            (boundarySupport (n := n) (Ω := Ω) i).indicator
              (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y)) := by
  let KT := boundarySupportInTarget (n := n) (Ω := Ω) i
  let compactU := flattenCompactLp (n := n) (p := p) (Ω := Ω) i u
  let globalU := SobolevSpace.Extension.Lp.zeroExtendLp
    (n := n) (p := p) (Ω := KT)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).measurableSet compactU
  have hrestrict := SobolevSpace.GraphSpace.restrictDerivLp_apply_ae
    (n := n) (p := p) (Ω := SobolevSpace.HalfSpace.upper n)
    (Ωbig := (Set.univ : Set (ℝ^n)))
    (subset_univ _) globalU
  have hzero := SobolevSpace.Extension.Lp.zeroExtendLp_apply_ae
    (n := n) (p := p) (Ω := KT)
    (isCompact_boundarySupportInTarget
      (n := n) (Ω := Ω) i).measurableSet compactU
  have hcompact := flattenCompactLp_apply_ae (n := n) (p := p) (Ω := Ω) i u
  have hcompactImp : ∀ᵐ y ∂ domainMeasure n (Set.univ : Set (ℝ^n)),
      y ∈ KT →
        (compactU : ℝ^n → ℝ) y =
          (boundarySupport (n := n) (Ω := Ω) i).indicator
            (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y) := by
    apply (MeasureTheory.ae_restrict_iff'
      (μ := domainMeasure n (Set.univ : Set (ℝ^n))) (s := KT)
      (isCompact_boundarySupportInTarget
        (n := n) (Ω := Ω) i).measurableSet).1
    change ∀ᵐ y ∂ domainMeasure n KT,
      (compactU : ℝ^n → ℝ) y =
        (boundarySupport (n := n) (Ω := Ω) i).indicator
          (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y) at hcompact
    simpa [domainMeasure, Measure.restrict_restrict, inter_univ, compactU, KT] using hcompact
  have hzeroUpper := MeasureTheory.ae_restrict_of_ae
    (s := SobolevSpace.HalfSpace.upper n) hzero
  have hcompactUpper := MeasureTheory.ae_restrict_of_ae
    (s := SobolevSpace.HalfSpace.upper n) hcompactImp
  have hzeroUpper' : ∀ᵐ y ∂ domainMeasure n (SobolevSpace.HalfSpace.upper n),
      (globalU : ℝ^n → ℝ) y =
        SobolevSpace.Extension.Lp.extensionByZero
          (n := n) (p := p) (Ω := KT) compactU y := by
    simpa [domainMeasure, Measure.restrict_restrict, inter_univ] using hzeroUpper
  have hcompactUpper' : ∀ᵐ y ∂ domainMeasure n (SobolevSpace.HalfSpace.upper n),
      y ∈ KT →
        (compactU : ℝ^n → ℝ) y =
          (boundarySupport (n := n) (Ω := Ω) i).indicator
            (Ω.indicator fun x ↦ u x) ((hΩ.chart i).symm y) := by
    simpa [domainMeasure, Measure.restrict_restrict, inter_univ] using hcompactUpper
  have hrestrict' :
      ((flattenUpperLp (n := n) (p := p) (Ω := Ω) i u :
          SobolevSpace.GraphSpace.DerivLp n p (SobolevSpace.HalfSpace.upper n)) :
          ℝ^n → ℝ)
        =ᵐ[domainMeasure n (SobolevSpace.HalfSpace.upper n)]
          (globalU : ℝ^n → ℝ) := by
    simpa [flattenUpperLp, globalU, compactU] using hrestrict
  filter_upwards [hrestrict', hzeroUpper', hcompactUpper'] with y hyrestrict hyzero hycompact
  rw [hyrestrict, hyzero]
  by_cases hyKT : y ∈ KT
  · simp [SobolevSpace.Extension.Lp.extensionByZero, KT, hyKT,
      hycompact hyKT]
  · simp [SobolevSpace.Extension.Lp.extensionByZero, KT, hyKT]

end BoundaryPiece

end C1

end Extension

end SobolevSpace
