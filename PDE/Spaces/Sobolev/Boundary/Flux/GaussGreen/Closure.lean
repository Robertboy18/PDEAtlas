/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Vector
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.VectorValued
import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Gauss–Green from raw classical closure data

Interior C¹ regularity and uniformly continuous first derivatives give an
ambient C¹ extension. Prescribed continuous closure values identify this
extension on the boundary, while equality on the open domain identifies its
divergence there. The resulting formula uses Hausdorff measure
and includes integrability of both signed integrands.

`gaussGreen_of_contDiffUpToBoundary` is the divergence theorem (2) of Evans App. C.2, Theorem 1(ii),
under Evans's hypothesis `F ∈ C¹(Ū; ℝⁿ)`: each component of `F` is C¹ up to the boundary
(`ContDiffUpToBoundary`) and `F` is continuous on `closure Ω`, so its boundary values are the limits
of its interior values. The ambient extension is `exists_contDiff_succ_extension_vector`, and the
formula for it is `integral_divergence_eq_normalFlux`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1(ii), (2), pp. 711-712; and App. A.3,
  p. 702, for `C¹(Ū)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- Divergence theorem (Evans App. C.2, Theorem 1(ii)) for `F ∈ C¹(Ū; ℝⁿ)`: if `Ω` carries a
`C1ExtensionAtlas` (so is bounded and open) and has C¹ graph boundary, every component of `F` is C¹
up to the boundary and `F` is continuous on `closure Ω`, then `div F` is integrable on `Ω`, `F · ν`
is integrable for the surface measure, and `∫_Ω div F dx = ∫_{∂Ω} F · ν dS`. -/
theorem gaussGreen_of_contDiffUpToBoundary [hΩ : C1ExtensionAtlas (m + 1) Ω]
    (hgraph : HasC1GraphBoundary Ω) {F : ℝ^(m + 1) → ℝ^(m + 1)}
    (hF : ∀ i, ContDiffUpToBoundary 1 (fun x ↦ F x i) Ω)
    (hc : ContinuousOn F (closure Ω)) :
    IntegrableOn (∇· F) Ω ∧
      Integrable (normalFlux (Ω := Ω) F) (surfaceMeasure Ω) ∧
        (∫ x in Ω, ∇· F x) =
          ∫ x, normalFlux (Ω := Ω) F x ∂surfaceMeasure Ω := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_succ_extension_vector 0 hF hc
    hΩ.isOpen hΩ.bounded (hasContDiffGraphBoundary_one_iff.mpr hgraph)
  have hd : EqOn (∇· U) (∇· F) Ω := by
    intro x hx
    have hgerm : U =ᶠ[nhds x] F := by
      filter_upwards [hΩ.isOpen.mem_nhds hx] with y hy
      exact heq (subset_closure hy)
    exact hgerm.divergence_eq
  have hdae : ∇· U =ᵐ[volume.restrict Ω] ∇· F := by
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    exact hd hx
  have hfae : normalFlux (Ω := Ω) U =ᵐ[surfaceMeasure Ω] normalFlux (Ω := Ω) F := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    simp only [normalFlux_eq_inner _ hx, heq (frontier_subset_closure hx)]
  refine ⟨(integrableOn_divergence hU).congr hdae,
    integrable_normalFlux (hc.mono frontier_subset_closure), ?_⟩
  rw [← integral_congr_ae hdae, integral_divergence_eq_normalFlux hgraph hU,
    integral_congr_ae hfae]

/-- `gaussGreen_of_contDiffUpToBoundary` for a bounded open `Ω` with C¹ graph boundary, with no
atlas assumed: the normal and surface measure are those of the atlas
`hgraph.c1ExtensionAtlas hopen hbounded`. -/
theorem gaussGreen_of_raw_graph
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {F : ℝ^(m + 1) → ℝ^(m + 1)}
    (hF : ∀ i, ContDiffUpToBoundary 1 (fun x ↦ F x i) Ω)
    (hc : ContinuousOn F (closure Ω)) :
    letI := hgraph.c1ExtensionAtlas hopen hbounded
    IntegrableOn (∇· F) Ω ∧
      Integrable (normalFlux (Ω := Ω) F) (surfaceMeasure Ω) ∧
        (∫ x in Ω, ∇· F x) =
          ∫ x, normalFlux (Ω := Ω) F x ∂surfaceMeasure Ω := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  exact gaussGreen_of_contDiffUpToBoundary hgraph hF hc

end SobolevSpace.Boundary.Flux
