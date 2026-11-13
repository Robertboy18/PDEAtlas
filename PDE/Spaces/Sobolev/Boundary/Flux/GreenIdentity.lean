/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Vector
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.Gradient
import PDE.Analysis.Calculus.Divergence.Continuity
import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Green's identities on a C¹ graph domain

The boundary integrals use the completed interior gradients and the
outward normal with Hausdorff surface measure. A C¹ extension of the scalar
factor and a separate C¹ extension of the other gradient suffice for
Gauss–Green. Thus raw C² closure data require neither C² boundary charts nor
an ambient C² extension of the scalar function.

`green_first_identity_of_contDiffUpToBoundary` is Evans App. C.2, Theorem 3(ii),
`∫_Ω Du · Dv dx = -∫_Ω u Δv dx + ∫_{∂Ω} u ∂v/∂ν dS`, and
`green_second_identity_of_contDiffUpToBoundary` is Theorem 3(iii). Evans assumes `u, v ∈ C²(Ū)`; for
(ii) we need only `u ∈ C¹(Ū)`. Evans proves (ii) from the integration by parts formula (3) with
`v_{x_i}` in place of `v`; we apply the divergence theorem `integral_divergence_eq_normalFlux` to
`U G`, where `U` and `G` are C¹ extensions of `u` and of the gradient of `v`
(`ContDiffUpToBoundary.exists_contDiff_one_extension` and
`ContDiffUpToBoundary.exists_contDiff_one_gradient_extension`). As in Evans, (iii) follows by
exchanging `u` and `v` in (ii) and subtracting.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 2, (3), and Theorem 3 with its proof,
  p. 712.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

open scoped Gradient

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure PDE.Analysis

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Green's first identity (Evans App. C.2, Theorem 3(ii)): if `Ω` carries a `C1ExtensionAtlas`
and has C¹ graph boundary, `u` is C¹ up to the boundary and continuous on `closure Ω`, and `v` is C²
up to the boundary, then `u Δv` and `Du · Dv` are integrable on `Ω`, `u ∂v/∂ν` is integrable for
the surface measure, and `∫_Ω u Δv dx + ∫_Ω Du · Dv dx = ∫_{∂Ω} u ∂v/∂ν dS`. Here `∂v/∂ν` is the
normal component of `Dv`, the continuous extension of the gradient of `v` to `closure Ω`. -/
theorem green_first_identity_of_contDiffUpToBoundary
    (hgraph : HasC1GraphBoundary Ω) {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 1 u Ω) (hc : ContinuousOn u (closure Ω))
    (hv : ContDiffUpToBoundary 2 v Ω) :
    let Dv := (hv.of_le (show 1 ≤ 2 by omega)).completedGradient
    IntegrableOn (fun x ↦ u x * laplacian v x) Ω ∧
      IntegrableOn (fun x ↦ inner ℝ (∇ u x) (∇ v x)) Ω ∧
      Integrable (fun x ↦ u x * normalFlux (Ω := Ω) Dv x) (surfaceMeasure Ω) ∧
      (∫ x in Ω, u x * laplacian v x) +
        (∫ x in Ω, inner ℝ (∇ u x) (∇ v x)) =
          ∫ x, u x * normalFlux (Ω := Ω) Dv x ∂surfaceMeasure Ω := by
  have hv₁ := hv.of_le (show 1 ≤ 2 by omega)
  obtain ⟨U, hU, _, heqU⟩ :=
    hu.exists_contDiff_one_extension hΩ.isOpen hΩ.bounded hgraph
  have hextU : EqOn U u (closure Ω) :=
    heqU.of_subset_closure hU.continuous.continuousOn hc subset_closure Subset.rfl
  obtain ⟨G, hG, hextG⟩ :=
    hv.exists_contDiff_one_gradient_extension hΩ.isOpen hΩ.bounded hgraph
  have heqG : EqOn G (∇ v) Ω :=
    (hextG.mono subset_closure).trans hv₁.completedGradient_eq_gradient
  have hdu {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
      fderiv ℝ U x (G x) = inner ℝ (∇ u x) (∇ v x) := by
    rw [(heqU.eventuallyEq_of_mem (hΩ.isOpen.mem_nhds hx)).fderiv_eq, heqG hx,
      inner_gradient_left]
  have hlap {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
      ∇· G x = laplacian v x :=
    (heqG.eventuallyEq_of_mem (hΩ.isOpen.mem_nhds hx)).divergence_eq.trans
      (PDE.laplacian_eq_divergence_gradient v x).symm
  have hi : IntegrableOn (fun x ↦ u x * laplacian v x) Ω := by
    have h := ((hU.continuous.mul hG.continuous_divergence).continuousOn.integrableOn_compact
      (μ := volume) hΩ.bounded.isCompact_closure).mono_set (s := Ω) subset_closure
    apply h.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    change U x * ∇· G x = u x * laplacian v x
    rw [heqU hx, hlap hx]
  have hj : IntegrableOn (fun x ↦ inner ℝ (∇ u x) (∇ v x)) Ω := by
    have h := (((hU.continuous_fderiv one_ne_zero).clm_apply
      hG.continuous).continuousOn.integrableOn_compact
      (μ := volume) hΩ.bounded.isCompact_closure).mono_set (s := Ω) subset_closure
    apply h.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    exact hdu hx
  have hfield : ContDiff ℝ 1 (fun x ↦ U x • G x) := hU.smul hG
  have hboundary : normalFlux (Ω := Ω) (fun x ↦ U x • G x)
      =ᵐ[surfaceMeasure Ω] fun x ↦ u x * normalFlux (Ω := Ω) hv₁.completedGradient x := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    simp only [normalFlux_eq_inner _ hx, hextU (frontier_subset_closure hx),
      hextG (frontier_subset_closure hx), inner_smul_left, starRingEnd_apply, star_trivial]
  refine ⟨hi, hj, (integrable_normalFlux hfield.continuous.continuousOn).congr hboundary, ?_⟩
  have hdiv : EqOn (∇· (fun x ↦ U x • G x))
      (fun x ↦ u x * laplacian v x + inner ℝ (∇ u x) (∇ v x)) Ω := by
    intro x hx
    rw [divergence_smul (hU.differentiable one_ne_zero x)
      (hG.differentiable one_ne_zero x), hdu hx, heqU hx, hlap hx, add_comm]
  have hgg := integral_divergence_eq_normalFlux hgraph hfield
  rw [setIntegral_congr_fun hΩ.isOpen.measurableSet (fun x hx ↦ hdiv hx),
    integral_add hi hj, integral_congr_ae hboundary] at hgg
  exact hgg

/-- Green's second identity (Evans App. C.2, Theorem 3(iii)): if `Ω` carries a
`C1ExtensionAtlas` and has C¹ graph boundary, and `u` and `v` are C² up to the boundary and
continuous on `closure Ω`, then `u Δv - v Δu` is integrable on `Ω`, `u ∂v/∂ν - v ∂u/∂ν` is
integrable for the surface measure, and
`∫_Ω (u Δv - v Δu) dx = ∫_{∂Ω} (u ∂v/∂ν - v ∂u/∂ν) dS`, with the normal derivatives taken from
the continuous extensions `Du` and `Dv` of the gradients. Neither function has to vanish on the
boundary. -/
theorem green_second_identity_of_contDiffUpToBoundary
    (hgraph : HasC1GraphBoundary Ω) {u v : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hcu : ContinuousOn u (closure Ω))
    (hv : ContDiffUpToBoundary 2 v Ω) (hcv : ContinuousOn v (closure Ω)) :
    let Du := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    let Dv := (hv.of_le (show 1 ≤ 2 by omega)).completedGradient
    IntegrableOn (fun x ↦ u x * laplacian v x - v x * laplacian u x) Ω ∧
      Integrable (fun x ↦ u x * normalFlux (Ω := Ω) Dv x -
        v x * normalFlux (Ω := Ω) Du x) (surfaceMeasure Ω) ∧
      (∫ x in Ω, u x * laplacian v x - v x * laplacian u x) =
        ∫ x, u x * normalFlux (Ω := Ω) Dv x -
          v x * normalFlux (Ω := Ω) Du x ∂surfaceMeasure Ω := by
  obtain ⟨hi, _, hb, heq⟩ :=
    green_first_identity_of_contDiffUpToBoundary hgraph (hu.of_le (by omega)) hcu hv
  obtain ⟨hi', _, hb', heq'⟩ :=
    green_first_identity_of_contDiffUpToBoundary hgraph (hv.of_le (by omega)) hcv hu
  refine ⟨hi.sub hi', hb.sub hb', ?_⟩
  rw [integral_sub hi hi', integral_sub hb hb']
  have heqinner : (∫ x in Ω, inner ℝ (∇ u x) (∇ v x)) =
      ∫ x in Ω, inner ℝ (∇ v x) (∇ u x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  linarith

end SobolevSpace.Boundary.Flux
