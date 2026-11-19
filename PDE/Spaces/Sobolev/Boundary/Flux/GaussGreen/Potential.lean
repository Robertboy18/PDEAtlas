/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Vector
public import PDE.Spaces.Sobolev.Extension.C1.Classical
public import PDE.Analysis.Calculus.Rellich.Field

/-!
# Integrating a potential against a radial field

Gauss–Green applied to `V(u) (x-c)` integrates the radial derivative of a
potential. The zero boundary values and normalization `V(0)=0` remove precisely
this flux. No boundary flux of the Rellich field is discarded.

For `V(t) = |t|^{p+1}/(p+1)` and `c = 0`, `integral_radial_gradient_mul_deriv_potential` is the
computation `B = -n/(p+1) ∫_U |u|^{p+1} dx` in step 4 of the proof of Evans §9.4.2, Theorem 3, where
`u ∈ C²(Ū)` solves `-Δu = |u|^{p-1}u` with `u = 0` on `∂U`. Here `u` need only be C¹ up to the
boundary, continuous on `closure Ω` and zero on `∂Ω`, and `V` is any C¹ function with `V(0) = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, proof of Theorem 3, step 4, p. 553.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Gradient

namespace SobolevSpace.Boundary.Flux

open Set MeasureTheory Trace.C1 Geometry.SurfaceMeasure PDE.Analysis

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- Let `Ω` carry a `C1ExtensionAtlas` and have C¹ graph boundary, let `u` be C¹ up to the
boundary, continuous on `closure Ω` and zero on `∂Ω`, and let `V` be C¹ with `V(0) = 0`. Then
`V(u)` and `((x - c) · Du) V'(u)` are integrable on `Ω`, and
`∫_Ω ((x - c) · Du) V'(u) dx = -(m + 1) ∫_Ω V(u) dx` for every `c`. This is step 4 of the proof
of Evans §9.4.2, Theorem 3, for `V(t) = |t|^{p+1}/(p+1)` and `c = 0`. -/
theorem integral_radial_gradient_mul_deriv_potential
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 1 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0) (c : ℝ^(m + 1)) :
    IntegrableOn (fun x ↦ V (u x)) Ω ∧
      IntegrableOn (fun x ↦ inner ℝ (x - c) (∇ u x) * deriv V (u x)) Ω ∧
        (∫ x in Ω, inner ℝ (x - c) (∇ u x) * deriv V (u x)) =
          -((m + 1 : ℕ) : ℝ) * ∫ x in Ω, V (u x) := by
  obtain ⟨U, hU, _, heq⟩ := hu.exists_contDiff_one_extension
    hΩ.isOpen hΩ.bounded hgraph
  have hext : EqOn U u (closure Ω) :=
    heq.of_subset_closure hU.continuous.continuousOn hc subset_closure Subset.rfl
  have hgerm {x : ℝ^(m + 1)} (hx : x ∈ Ω) : U =ᶠ[nhds x] u :=
    heq.eventuallyEq_of_mem (hΩ.isOpen.mem_nhds hx)
  have hgrad {x : ℝ^(m + 1)} (hx : x ∈ Ω) : ∇ U x = ∇ u x :=
    (hgerm hx).gradient_eq
  have hi : IntegrableOn (fun x ↦ V (u x)) Ω := by
    have hiU : IntegrableOn (fun x ↦ V (U x)) Ω :=
      ((hV.continuous.comp hU.continuous).continuousOn.integrableOn_compact
        hΩ.bounded.isCompact_closure).mono_set subset_closure
    apply hiU.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    rw [heq hx]
  have ha : IntegrableOn
      (fun x ↦ inner ℝ (x - c) (∇ u x) * deriv V (u x)) Ω := by
    have hcont : Continuous (fun x ↦
        fderiv ℝ U x (x - c) * deriv V (U x)) :=
      ((hU.continuous_fderiv one_ne_zero).clm_apply
        (continuous_id.sub continuous_const)).mul
        ((hV.continuous_deriv le_rfl).comp hU.continuous)
    have hiU : IntegrableOn
        (fun x ↦ fderiv ℝ U x (x - c) * deriv V (U x)) Ω :=
      (hcont.continuousOn.integrableOn_compact hΩ.bounded.isCompact_closure).mono_set
        subset_closure
    apply hiU.congr
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    rw [← inner_gradient_left, hgrad hx, real_inner_comm, heq hx]
  refine ⟨hi, ha, ?_⟩
  let W : ℝ^(m + 1) → ℝ^(m + 1) := fun x ↦ V (U x) • (x - c)
  have hW : ContDiff ℝ 1 W := (hV.comp hU).smul (contDiff_id.sub contDiff_const)
  have hd : EqOn (∇· W)
      (fun x ↦ inner ℝ (x - c) (∇ u x) * deriv V (u x) +
        ((m + 1 : ℕ) : ℝ) * V (u x)) Ω := by
    intro x hx
    have hchain : HasFDerivAt (fun y ↦ V (U y))
        (deriv V (U x) • fderiv ℝ U x) x :=
      (hV.differentiable_one (U x)).hasDerivAt.comp_hasFDerivAt x
        (hU.differentiable_one x).hasFDerivAt
    have hr : DifferentiableAt ℝ (fun y : ℝ^(m + 1) ↦ y - c) x :=
      differentiableAt_id.sub_const c
    change ∇· (fun y ↦ V (U y) • (y - c)) x = _
    rw [divergence_smul hchain.differentiableAt hr,
      divergence_sub_const, hchain.fderiv]
    simp only [smul_apply, smul_eq_mul]
    rw [← inner_gradient_left, hgrad hx, real_inner_comm, heq hx]
    ring
  have hb : normalFlux (Ω := Ω) W =ᵐ[surfaceMeasure Ω] fun _ ↦ 0 := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
    rw [normalFlux_eq_inner _ hx]
    simp only [W, hext (frontier_subset_closure hx), hzero x hx, hV0, zero_smul,
      inner_zero_left]
  have hgg := integral_divergence_eq_normalFlux hgraph hW
  rw [setIntegral_congr_fun hΩ.isOpen.measurableSet (fun x hx ↦ hd hx),
    integral_add ha (hi.const_mul _), integral_const_mul,
    integral_congr_ae hb, integral_zero] at hgg
  linarith

end SobolevSpace.Boundary.Flux
