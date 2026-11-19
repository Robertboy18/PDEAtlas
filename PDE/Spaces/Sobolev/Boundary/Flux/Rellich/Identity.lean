/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Vector
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.ClassicalGradient
public import PDE.Spaces.Sobolev.Extension.C1.ClassicalHigherOrder.Gradient
public import PDE.Analysis.Calculus.Rellich.NormalComponent
import PDE.Analysis.Calculus.Divergence.Continuity

/-!
# Rellich's identity with the full signed boundary term

For a bounded open `Ω ⊆ ℝⁿ`, `n = m + 1`, with C¹ graph boundary and `u` that is C² up to the
boundary and zero on `∂Ω`, `rellich_identity_of_contDiffUpToBoundary` proves
`∫_Ω ((x - c) · ∇u) Δu dx + (1 - n/2) ∫_Ω |∇u|² dx = (1/2) ∫_{∂Ω} |∇u|² ((x - c) · ν) dS`. For
`c = 0` it is equivalent to the formula `A = (2 - n)/2 ∫_U |Du|² dx - (1/2) ∫_{∂U} |Du|² (ν · x) dS`
for `A = ∫_U (-Δu)(x · Du) dx`, derived from (15)-(17) in steps 2-3 of the proof of Evans §9.4.2,
Theorem 3, where `u ∈ C²(Ū)` and `∂U` is C¹. The boundary term uses the completed gradient and the
Hausdorff surface measure `surfaceMeasure Ω`.

## How it works

Evans integrates by parts twice. We apply the divergence theorem `integral_divergence_eq_normalFlux`
once, to the field `PDE.Analysis.rellichField c G = ((x - c) · G) G - (|G|²/2) (x - c)`, where `G`
is a C¹ extension of `∇u` from `ContDiffUpToBoundary.exists_contDiff_one_gradient_extension`; no C²
boundary charts are needed. On `∂Ω` the gradient is normal (`completedGradient_eq_normal_smul`), as
in Evans's step 3, so the flux of the field is `(1/2) |∇u|² ((x - c) · ν)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, proof of Theorem 3, steps 2-3, (15)-(17), p. 553.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

open scoped Gradient

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure PDE.Analysis

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Rellich's identity with center `c` (Evans §9.4.2, proof of Theorem 3, (15)-(17), for
`c = 0`): if `Ω` carries a `C1ExtensionAtlas` (so is bounded and open) and has C¹ graph boundary,
and `u` is C² up to the boundary, continuous on `closure Ω` and zero on `frontier Ω`, then
`|∇u|²` and `((x - c) · ∇u) Δu` are integrable on `Ω`, the flux of `|G₀|² (x - c)` is integrable
for the surface measure, and
`∫_Ω ((x - c) · ∇u) Δu + (1 - (m + 1)/2) ∫_Ω |∇u|² = (1/2) ∫_{∂Ω} |G₀|² ((x - c) · ν) dS`,
where `G₀` is the completed gradient of `u`. -/
theorem rellich_identity_of_contDiffUpToBoundary
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) (c : ℝ^(m + 1)) :
    let G₀ := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω ∧
      IntegrableOn (fun x ↦ inner ℝ (x - c) (∇ u x) * laplacian u x) Ω ∧
        Integrable (normalFlux (Ω := Ω) (fun x ↦ ‖G₀ x‖ ^ 2 • (x - c)))
          (surfaceMeasure Ω) ∧
          (∫ x in Ω, inner ℝ (x - c) (∇ u x) * laplacian u x) +
              (1 - ((m + 1 : ℕ) : ℝ) / 2) * (∫ x in Ω, ‖∇ u x‖ ^ 2) =
            (1 / 2 : ℝ) *
              ∫ x, normalFlux (Ω := Ω) (fun y ↦ ‖G₀ y‖ ^ 2 • (y - c)) x
                ∂surfaceMeasure Ω := by
  have hu₁ := hu.of_le (show 1 ≤ 2 by omega)
  let G₀ := hu₁.completedGradient
  obtain ⟨G, hG, hext⟩ :=
    hu.exists_contDiff_one_gradient_extension hΩ.isOpen hΩ.bounded hgraph
  have heq : EqOn G (∇ u) Ω :=
    (hext.mono subset_closure).trans hu₁.completedGradient_eq_gradient
  have hgerm {x : ℝ^(m + 1)} (hx : x ∈ Ω) : G =ᶠ[nhds x] ∇ u :=
    heq.eventuallyEq_of_mem (hΩ.isOpen.mem_nhds hx)
  have hlap {x : ℝ^(m + 1)} (hx : x ∈ Ω) : ∇· G x = laplacian u x :=
    (hgerm hx).divergence_eq.trans (PDE.laplacian_eq_divergence_gradient u x).symm
  have he : IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω := by
    have h := ((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact (μ := volume)
      hΩ.bounded.isCompact_closure).mono_set (s := Ω) subset_closure
    apply h.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    change ‖G x‖ ^ 2 = ‖∇ u x‖ ^ 2
    rw [heq hx]
  have ha :
      IntegrableOn (fun x ↦ inner ℝ (x - c) (∇ u x) * laplacian u x) Ω := by
    have hcont : Continuous (fun x ↦ inner ℝ (x - c) (G x) * ∇· G x) :=
      ((continuous_id.sub continuous_const).inner (𝕜 := ℝ) hG.continuous).mul
        hG.continuous_divergence
    have h := (hcont.continuousOn.integrableOn_compact (μ := volume)
      hΩ.bounded.isCompact_closure).mono_set (s := Ω) subset_closure
    apply h.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    rw [heq hx, hlap hx]
  have hs : Integrable (normalFlux (Ω := Ω) (fun x ↦ ‖G₀ x‖ ^ 2 • (x - c)))
      (surfaceMeasure Ω) :=
    integrable_normalFlux
      ((hu₁.continuous_completedGradient.norm.pow 2).smul
        (continuous_id.sub continuous_const)).continuousOn
  refine ⟨he, ha, hs, ?_⟩
  have hd : EqOn (∇· (rellichField c G))
      (fun x ↦ inner ℝ (x - c) (∇ u x) * laplacian u x +
        (1 - ((m + 1 : ℕ) : ℝ) / 2) * ‖∇ u x‖ ^ 2) Ω := by
    intro x hx
    rw [divergence_rellichField_of_gradient
      (hu.contDiffOn.contDiffAt (hΩ.isOpen.mem_nhds hx))
      (hG.differentiable one_ne_zero x) (hgerm hx) c, heq hx]
  have hb : normalFlux (Ω := Ω) (rellichField c G) =ᵐ[surfaceMeasure Ω]
      fun x ↦ (1 / 2 : ℝ) *
        normalFlux (Ω := Ω) (fun y ↦ ‖G₀ y‖ ^ 2 • (y - c)) x := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    have hnormal : G x =
        inner ℝ (G x) (outwardUnitNormal (Ω := Ω) ⟨x, hx⟩) •
          outwardUnitNormal (Ω := Ω) ⟨x, hx⟩ := by
      rw [hext (frontier_subset_closure hx)]
      exact completedGradient_eq_normal_smul hgraph hu₁ hc hzero hx
    rw [normalFlux_eq_inner _ hx, normalFlux_eq_inner _ hx,
      inner_rellichField_of_normal c x _ hnormal, hext (frontier_subset_closure hx)]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    ring
  have hgg := integral_divergence_eq_normalFlux hgraph (contDiff_rellichField hG c)
  rw [setIntegral_congr_fun hΩ.isOpen.measurableSet (fun x hx ↦ hd hx),
    integral_add ha (he.const_mul _), integral_const_mul,
    integral_congr_ae hb, integral_const_mul] at hgg
  exact hgg

omit hΩ in
/-- `rellich_identity_of_contDiffUpToBoundary` for a bounded open `Ω` with C¹ graph boundary,
with no atlas assumed: the normal and surface measure are those of the atlas
`hgraph.c1ExtensionAtlas hopen hbounded`. -/
theorem rellich_identity_of_raw_graph
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) (c : ℝ^(m + 1)) :
    letI := hgraph.c1ExtensionAtlas hopen hbounded
    let G := (hu.of_le (show 1 ≤ 2 by omega)).completedGradient
    IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω ∧
      IntegrableOn (fun x ↦ inner ℝ (x - c) (∇ u x) * laplacian u x) Ω ∧
        Integrable (normalFlux (Ω := Ω) (fun x ↦ ‖G x‖ ^ 2 • (x - c)))
          (surfaceMeasure Ω) ∧
          (∫ x in Ω, inner ℝ (x - c) (∇ u x) * laplacian u x) +
              (1 - ((m + 1 : ℕ) : ℝ) / 2) * (∫ x in Ω, ‖∇ u x‖ ^ 2) =
            (1 / 2 : ℝ) *
              ∫ x, normalFlux (Ω := Ω) (fun y ↦ ‖G y‖ ^ 2 • (y - c)) x
                ∂surfaceMeasure Ω := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  exact rellich_identity_of_contDiffUpToBoundary hgraph hu hc hzero c

end SobolevSpace.Boundary.Flux
