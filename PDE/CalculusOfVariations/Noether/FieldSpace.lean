/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Noether.Invariance
public import PDE.Analysis.Calculus.Divergence.Locality

/-!
# Noether's theorem for transformations of fields and space

A spatial transformation `Φ` and a field transformation `Ψ` act on the graph of `u` by
`U t (Φ t x) = Ψ t x (u x)`. Here `U t` is the induced field in the transformed
coordinates. Differentiating this graph identity proves that its fixed-coordinate
variation is `η - Du X`, where `η` and `X` are the parameter derivatives of
`Ψ` and `Φ`.

The conservation theorem uses invariance of the transformed density, including the
gradient of `U t` and determinant of the spatial Jacobian. The induced family
is supplied with joint `C²` regularity only near `(0, x)`; `Noether/InducedField`
constructs it from inverse spatial maps.
The graph law and differentiability of `Ψ` are needed only for spatial points near `x`.
Arbitrary nonlinear, position-dependent field transformations are allowed. The conservation
law is Noether's theorem, Evans, §8.6.2, Theorem 1 (ii), for fields with any finite number
of components and with the invariance stated pointwise for the transformed density.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.6.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Elementwise Topology

namespace PDE.CalculusOfVariations.Noether

open Analysis

variable {n m : ℕ} {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ}
  {U : ℝ → ℝ^n → ℝ^m} {Φ : ℝ → ℝ^n → ℝ^n}
  {Ψ : ℝ → ℝ^n → ℝ^m → ℝ^m} {x : ℝ^n}

/-- The graph transformation law determines the field variation at a point:
it is the field generator minus transport by the spatial generator. -/
theorem variation_eq_field_generator_sub_transport
    (hU : DifferentiableAt ℝ (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : DifferentiableAt ℝ (fun t ↦ Φ t x) 0)
    (hΦ₀ : Φ 0 x = x)
    (hΨ : DifferentiableAt ℝ (fun t ↦ Ψ t x (U 0 x)) 0)
    (hgraph : (fun t ↦ U t (Φ t x)) =ᶠ[𝓝 0] (fun t ↦ Ψ t x (U 0 x))) :
    deriv (fun t ↦ U t x) 0 = deriv (fun t ↦ Ψ t x (U 0 x)) 0 -
      fderiv ℝ (U 0) x (deriv (fun t ↦ Φ t x) 0) := by
  have hmove := hasDerivAt_moving_point hU hΦ.hasDerivAt hΦ₀
  exact eq_sub_iff_add_eq.mpr
    (hmove.unique (hΨ.hasDerivAt.congr_of_eventuallyEq hgraph))

/-- Noether conservation for a simultaneous spatial transformation and nonlinear field
transformation. Invariance is equality of transformed densities near the identity.
The conserved current has components
`Σₖ L_{Pₖᵢ} (ηₖ - (Du X)ₖ) + L Xᵢ`, with generators given by derivatives.
The graph law is assumed for the induced transformed fields; the infinitesimal graph
law, density variation, and divergence identity are all proved. -/
theorem noether_field_space
    (hL : ContDiffAt ℝ 2
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      (jacobianMatrix (U 0) x, (U 0 x, x)))
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ U p.1 p.2) (0, x))
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ^n ↦ Φ p.1 p.2) (0, x))
    (hΦ₀ : Φ 0 =ᶠ[𝓝 x] id)
    (hΨ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun t ↦ Ψ t y (U 0 y)) 0)
    (hgraph : ∀ᶠ y in 𝓝 x, (fun t ↦ U t (Φ t y)) =ᶠ[𝓝 0]
      (fun t ↦ Ψ t y (U 0 y)))
    (hinvariant : (fun t ↦
      L (jacobianMatrix (U t) (Φ t x)) (Ψ t x (U 0 x)) (Φ t x) *
        (jacobianMatrix (Φ t) x).det) =ᶠ[𝓝 0] (fun _ ↦ fieldDensity L (U 0) x))
    (hEL : ∀ k, classicalEulerLagrange L (U 0) x k = 0) :
    ∇· (noetherCurrent L (U 0)
      (fun y ↦ deriv (fun t ↦ Ψ t y (U 0 y)) 0 -
        fderiv ℝ (U 0) y (deriv (fun t ↦ Φ t y) 0))
      (fun y ↦ deriv (fun t ↦ Φ t y) 0)) x = 0 := by
  have hvariation : (fun y ↦ deriv (fun t ↦ U t y) 0) =ᶠ[𝓝 x]
      (fun y ↦ deriv (fun t ↦ Ψ t y (U 0 y)) 0 -
        fderiv ℝ (U 0) y (deriv (fun t ↦ Φ t y) 0)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
      (hU.eventually (by norm_num)),
      (continuousAt_const.prodMk continuousAt_id).eventually
        (hΦ.eventually (by norm_num)), hΦ₀, hΨ, hgraph] with y hUy hΦy hbase hΨy hgy
    have hpath : ContDiffAt ℝ 2 (fun t : ℝ ↦ Φ t y) 0 :=
      hΦy.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
    exact variation_eq_field_generator_sub_transport (hUy.differentiableAt (by norm_num))
      (hpath.differentiableAt (by norm_num)) hbase hΨy hgy
  have hcurrent : noetherCurrent L (U 0) (fun y ↦ deriv (fun t ↦ U t y) 0)
      (fun y ↦ deriv (fun t ↦ Φ t y) 0) =ᶠ[𝓝 x]
      noetherCurrent L (U 0)
        (fun y ↦ deriv (fun t ↦ Ψ t y (U 0 y)) 0 -
          fderiv ℝ (U 0) y (deriv (fun t ↦ Φ t y) 0))
        (fun y ↦ deriv (fun t ↦ Φ t y) 0) := by
    filter_upwards [hvariation] with y hy
    simp only [noetherCurrent, hy]
  rw [← hcurrent.divergence_eq]
  apply noether_of_invariant_variation hL hU hΦ hΦ₀ _ hEL
  filter_upwards [hinvariant, hgraph.self_of_nhds] with t ht hgraph_t
  simpa only [transformedDensity, fieldDensity, hgraph_t] using ht

end PDE.CalculusOfVariations.Noether
