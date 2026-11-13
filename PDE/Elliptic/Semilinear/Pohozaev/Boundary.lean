/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Rellich.Identity
public import PDE.Spaces.Sobolev.Boundary.Flux.GaussGreen.Potential
public import PDE.EnergyMethods.Dirichlet.Classical.ZeroBoundary

/-!
# Pohozaev's identity on a bounded domain

A classical solution of `-Δu = V'(u)` with zero boundary values satisfies the energy identity
`∫ |Du|² = ∫ u V'(u)` and, for every center `c`,

`(n-2)/2 ∫|Du|² + 1/2 ∫∂Ω |Du|² (x-c)·ν = n ∫V(u)`

(`pohozaev_identity_of_zero_boundary`). The full signed boundary integral uses Hausdorff surface
measure. The assumptions are C¹ graph geometry, C² closure regularity, a `C¹` potential with
`V(0) = 0` and the pointwise PDE. All integrability and integration identities are proved.

For `V(u) = |u|^{p+1}/(p+1)` and `c = 0` the second identity is the Derrick-Pohozaev identity (18)
of Evans's §9.4.2, and the first is the identity `∫ |Du|² = ∫ |u|^{p+1}` that he combines with (19).

## How it works

We follow Evans's computation (14)-(18) with the multiplier `(x - c) · Du`. The Rellich identity
with its signed boundary term, `rellich_identity_of_contDiffUpToBoundary`, combines his steps 2 and
3, (15)-(17); it extends the gradient to a `C¹` vector field, so that the Gauss-Green theorem
applies without `C²` boundary charts. The potential term
`integral_radial_gradient_mul_deriv_potential` is his step 4 for a general `V`, and the energy
identity is `EnergyMethods.integral_mul_laplacian_eq_neg_energy_of_zero_boundary`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2 (Derrick-Pohozaev identity), proof of Theorem 3
  (Nonexistence of nontrivial solution), (14)-(18), pp. 552-553, and the energy identity after (19),
  p. 554.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public noncomputable section

namespace PDE.Elliptic.Semilinear

open Set MeasureTheory SobolevSpace Boundary Boundary.Flux Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : C1ExtensionAtlas (m + 1) Ω]

/-- The energy and Pohozaev identities with their full signed boundary
term, for a normalized C¹ potential on a bounded C¹ graph domain. -/
theorem pohozaev_identity_of_zero_boundary
    (hgraph : HasC1GraphBoundary Ω) {u : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hc : ContinuousOn u (closure Ω))
    (hzero : ∀ x ∈ frontier Ω, u x = 0) {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) (hV0 : V 0 = 0)
    (hpde : ∀ x ∈ Ω, -laplacian u x = deriv V (u x)) (c : ℝ^(m + 1)) :
    IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) Ω ∧
      IntegrableOn (fun x ↦ V (u x)) Ω ∧
        IntegrableOn (fun x ↦ u x * deriv V (u x)) Ω ∧
          Integrable (normalFlux (Ω := Ω)
            (fun x ↦ ‖(hu.of_le (show 1 ≤ 2 by omega)).completedGradient x‖ ^ 2 • (x - c)))
            (surfaceMeasure Ω) ∧
            (∫ x in Ω, ‖∇ u x‖ ^ 2) = ∫ x in Ω, u x * deriv V (u x) ∧
              (((m + 1 : ℕ) : ℝ) - 2) / 2 * (∫ x in Ω, ‖∇ u x‖ ^ 2) +
                  (1 / 2 : ℝ) *
                    (∫ x, normalFlux (Ω := Ω)
                      (fun y ↦ ‖(hu.of_le (show 1 ≤ 2 by omega)).completedGradient y‖ ^ 2 •
                        (y - c)) x
                      ∂surfaceMeasure Ω) =
                ((m + 1 : ℕ) : ℝ) * ∫ x in Ω, V (u x) := by
  obtain ⟨he, ha, hq, hr⟩ :=
    rellich_identity_of_contDiffUpToBoundary hgraph hu hc hzero c
  obtain ⟨hv, _, hd⟩ := integral_radial_gradient_mul_deriv_potential
    hgraph (hu.of_le (show 1 ≤ 2 by omega)) hc hzero hV hV0 c
  obtain ⟨hl, _, heq⟩ :=
    EnergyMethods.integral_mul_laplacian_eq_neg_energy_of_zero_boundary
      hΩ.isOpen hΩ.bounded hgraph hu hc hzero
  have hsource : (fun x ↦ -(u x * laplacian u x)) =ᵐ[volume.restrict Ω]
      fun x ↦ u x * deriv V (u x) := by
    filter_upwards [ae_restrict_mem hΩ.isOpen.measurableSet] with x hx
    rw [← hpde x hx, mul_neg]
  have henergy : (∫ x in Ω, ‖∇ u x‖ ^ 2) = ∫ x in Ω, u x * deriv V (u x) := by
    rw [← integral_congr_ae hsource, integral_neg, heq, neg_neg]
  refine ⟨he, hv, hl.neg.congr hsource, hq, henergy, ?_⟩
  have hradial : (∫ x in Ω, inner ℝ (x - c) (∇ u x) * deriv V (u x)) =
      -(∫ x in Ω, inner ℝ (x - c) (∇ u x) * laplacian u x) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun hΩ.isOpen.measurableSet
    intro x hx
    dsimp only
    rw [← hpde x hx, mul_neg]
  rw [hradial] at hd
  linarith

end PDE.Elliptic.Semilinear
