/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasIndependence
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Lifting

/-!
# The change of atlas on the half-order boundary space

Two operational C¹ atlases on the same domain give continuously linearly equivalent
half-order boundary spaces. Lift the datum using the first atlas and take its fractional
trace using the second. The physical H¹ trace is independent of the atlas, and the physical
surface value determines all fractional coordinates. These facts give both inverse identities.
The equivalence preserves surface L² values and commutes with the fractional trace. The
boundary dimension may be zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open scoped Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable (A B : Boundary.C1ExtensionAtlas (m + 1) Ω)

private theorem trace_eq (u : H¹(Ω)) :
    trace (hΩ := A) u = trace (hΩ := B) u := by
  obtain ⟨v, rfl⟩ := (domainW1pTwoEquivH1 (m := m) (Ω := Ω)).surjective u
  rw [← boundaryLpTwoEquivL2_traceLp (hΩ := A),
    ← boundaryLpTwoEquivL2_traceLp (hΩ := B), traceLp_eq_of_atlases A B 2]

/-- Tracing a lifting in another atlas recovers the same physical surface datum. -/
theorem boundaryValue_fractionalTrace_lifting
    (g : HalfOrderBoundarySpace (hΩ := A)) :
    boundaryValue (hΩ := B) (fractionalTrace (hΩ := B) (lifting (hΩ := A) g)) =
      boundaryValue (hΩ := A) g := by
  calc
    _ = trace (hΩ := B) (lifting (hΩ := A) g) :=
      boundaryValue_fractionalTrace (hΩ := B) _
    _ = trace (hΩ := A) (lifting (hΩ := A) g) := trace_eq B A _
    _ = boundaryValue (hΩ := A) g := trace_lifting (hΩ := A) g

/-- The canonical change of atlas lifts with the source atlas and traces with the target atlas. -/
def atlasEquiv :
    HalfOrderBoundarySpace (hΩ := A) ≃L[ℝ] HalfOrderBoundarySpace (hΩ := B) :=
  ContinuousLinearEquiv.equivOfInverse
    ((fractionalTrace (hΩ := B)).comp (lifting (hΩ := A)))
    ((fractionalTrace (hΩ := A)).comp (lifting (hΩ := B)))
    (by
      intro g
      apply boundaryValue_injective (hΩ := A)
      exact (boundaryValue_fractionalTrace_lifting B A _).trans
        (boundaryValue_fractionalTrace_lifting A B g))
    (by
      intro g
      apply boundaryValue_injective (hΩ := B)
      exact (boundaryValue_fractionalTrace_lifting A B _).trans
        (boundaryValue_fractionalTrace_lifting B A g))

/-- The change of atlas uses the bounded lifting and fractional trace. -/
theorem atlasEquiv_apply (g : HalfOrderBoundarySpace (hΩ := A)) :
    atlasEquiv A B g = fractionalTrace (hΩ := B) (lifting (hΩ := A) g) := rfl

/-- Changing the atlas preserves the physical surface L² value. -/
@[simp]
theorem boundaryValue_atlasEquiv (g : HalfOrderBoundarySpace (hΩ := A)) :
    boundaryValue (hΩ := B) (atlasEquiv A B g) = boundaryValue (hΩ := A) g :=
  boundaryValue_fractionalTrace_lifting A B g

/-- The inverse change of atlas is obtained by exchanging the atlases. -/
@[simp]
theorem atlasEquiv_symm : (atlasEquiv A B).symm = atlasEquiv B A := rfl

/-- Using the same atlas gives the identity on its half-order boundary space. -/
@[simp]
theorem atlasEquiv_refl :
    atlasEquiv A A = ContinuousLinearEquiv.refl ℝ (HalfOrderBoundarySpace (hΩ := A)) := by
  apply ContinuousLinearEquiv.ext
  funext g
  apply boundaryValue_injective (hΩ := A)
  exact boundaryValue_atlasEquiv A A g

/-- Changes of atlas compose without dependence on the intermediate atlas. -/
@[simp]
theorem atlasEquiv_trans (C : Boundary.C1ExtensionAtlas (m + 1) Ω) :
    (atlasEquiv A B).trans (atlasEquiv B C) = atlasEquiv A C := by
  apply ContinuousLinearEquiv.ext
  funext g
  apply boundaryValue_injective (hΩ := C)
  simp only [ContinuousLinearEquiv.trans_apply, boundaryValue_atlasEquiv]

/-- The change of atlas is characterized by equality of physical surface values. -/
theorem atlasEquiv_apply_eq_iff (g : HalfOrderBoundarySpace (hΩ := A))
    (h : HalfOrderBoundarySpace (hΩ := B)) :
    atlasEquiv A B g = h ↔ boundaryValue (hΩ := A) g = boundaryValue (hΩ := B) h := by
  rw [← (boundaryValue_injective (hΩ := B)).eq_iff, boundaryValue_atlasEquiv]

/-- Taking the fractional trace commutes with changing the boundary atlas. -/
@[simp]
theorem atlasEquiv_fractionalTrace (u : H¹(Ω)) :
    atlasEquiv A B (fractionalTrace (hΩ := A) u) = fractionalTrace (hΩ := B) u := by
  apply boundaryValue_injective (hΩ := B)
  rw [boundaryValue_atlasEquiv A B, boundaryValue_fractionalTrace (hΩ := A),
    boundaryValue_fractionalTrace (hΩ := B)]
  exact trace_eq A B u

end SobolevSpace.Trace.C1.Fractional
