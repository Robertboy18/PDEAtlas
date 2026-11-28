/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.ConvectionSkew
public import PDE.Fluid.NavierStokes.Stationary.StrainPairing
public import PDE.Fluid.NavierStokes.Stationary.SharpProduct
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# The convection form against the strain of a divergence-free field

The convection form `b(g, f, h) = ∫ (g·∇)f·h` is bounded by `‖g‖₄ ‖∇f‖₂ ‖h‖₄` with constant one
(`norm_convectionTrilinear_le_l4`). When `f` is divergence free and the form is symmetrized in
`g` and `h`, it sees only the strain of `f`, and the constant becomes `1/√3`. This bounds the
quadratic term `b(w + z, z, w)` of a perturbed Navier–Stokes equation, and the cross terms
`b(u, z, w) + b(z, u, w)`, with that constant. The statements are in dimension three, as for the
strain estimate.

## Main results

All for fields of `H¹(ℝ³)³` with the stated divergence conditions.

* `memLp_four_representative`, `memLp_norm_mul_norm_representative`: a field is in `L⁴`, and
  `|g| |h|` is in `L²`.
* `convectionTrilinear_add_swap`: `b(g, f, h) + b(h, f, g) = 2 ∫ (g ⊗ h) : Sf`.
* `abs_convectionTrilinear_add_swap_le`: for a divergence-free `f`,
  `|b(g, f, h) + b(h, f, g)| ≤ (2/√3) ‖∇f‖₂ ‖|g| |h|‖₂`.
* `abs_convectionTrilinear_self_le`: for a divergence-free `f`,
  `|b(g, f, g)| ≤ (1/√3) ‖∇f‖₂ ‖g‖₄²`.
* `abs_convectionTrilinear_add_le`: for divergence-free `w`, `z`,
  `|b(w + z, z, w)| ≤ (1/√3) (‖∇z‖₂ ‖w‖₄² + ‖∇w‖₂ ‖z‖₄²)`.
* `abs_convectionTrilinear_cross_le`: for divergence-free `u`, `z`, `w`,
  `|b(u, z, w) + b(z, u, w)| ≤ (2/√3) ‖∇w‖₂ ‖|u| |z|‖₂`.

## How it works

The sum `b(g, f, h) + b(h, f, g)` pairs the symmetric tensor `g ⊗ h + h ⊗ g` with the gradient of
`f`, so it is `2 ∫ (g ⊗ h) : Sf` with the strain `Sf`. The strain estimate
`abs_integral_tensor_strain_le` bounds this by `(2/√3) ‖∇f‖₂ ‖|g| |h|‖₂`, and for `h = g` the
last factor is `‖g‖₄²`. For divergence-free `w`, `z` the term `b(w + z, z, w)` is
`b(w, z, w) - b(z, w, z)`, by the skew symmetry of the form in its last two arguments
(`convectionTrilinear_skew`), and both terms are of the first kind. With the Sobolev bounds for
`‖g‖₄²` and for `‖|u| |z|‖₂` (`toReal_eLpNorm_four_representative_sq_le`,
`toReal_eLpNorm_norm_mul_norm_representative_le`) these are the estimates (4.40), (4.54) and the
one after (4.54) of Hou, Wang and Yang.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3, the display before
  (4.40), and Section 4.4, (4.54) and the display after it. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

set_option linter.missingDocs true

local notation "E" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The representative of a field of `H¹(ℝ³)³` lies in `L⁴(ℝ³; ℝ³)`. -/
theorem memLp_four_representative (v : E) : MemLp (representative v) 4 volume := by
  refine memLp_piLp_iff.mpr fun i ↦ ?_
  have h := Lp.memLp (l4CLM v i)
  simp only [domainMeasure, Measure.restrict_univ] at h
  exact h.ae_eq (by filter_upwards [l4CLM_apply_ae v] with x hx using hx i)

/-- For two fields `g`, `h` of `H¹(ℝ³)³` the product of lengths `|g| |h|` is square
integrable. -/
theorem memLp_norm_mul_norm_representative (g h : E) :
    MemLp (fun x ↦ ‖representative g x‖ * ‖representative h x‖) 2 volume :=
  (memLp_four_representative g).norm.fun_mul (memLp_four_representative h).norm

/-- **The symmetrized convection form is a strain pairing.** For fields `g`, `f`, `h` of
`H¹(ℝ³)³`, `b(g, f, h) + b(h, f, g) = 2 ∫ (g ⊗ h) : Sf`, with `Sf` the strain of `f`. -/
theorem convectionTrilinear_add_swap (g f h : E) :
    convectionTrilinear g f h + convectionTrilinear h f g =
      2 * ∫ x, ∑ i, ∑ j, representative g x i * representative h x j * strain f x i j := by
  rw [convectionTrilinear_eq_integral, convectionTrilinear_eq_integral,
    ← integral_add (integrable_convectionDensity g f h) (integrable_convectionDensity h f g),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [strain, Fin.sum_univ_three]
  ring

/-- **The symmetrized convection form against a divergence-free field.** For a divergence-free
`f` and any `g`, `h` in `H¹(ℝ³)³`,

`|b(g, f, h) + b(h, f, g)| ≤ (2/√3) ‖∇f‖₂ ‖|g| |h|‖₂`. -/
theorem abs_convectionTrilinear_add_swap_le {f : E} (hf : divergenceCLM f = 0) (g h : E) :
    |convectionTrilinear g f h + convectionTrilinear h f g| ≤ 2 / √3 * ‖gradientCLM f‖ *
      (eLpNorm (fun x ↦ ‖representative g x‖ * ‖representative h x‖) 2 volume).toReal := by
  have hA2 := abs_integral_tensor_strain_le hf (memLp_norm_mul_norm_representative g h)
  rw [convectionTrilinear_add_swap, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc _ ≤ 2 * (1 / √3 * ‖gradientCLM f‖ *
        (eLpNorm (fun x ↦ ‖representative g x‖ * ‖representative h x‖) 2 volume).toReal) :=
      mul_le_mul_of_nonneg_left hA2 (by norm_num)
    _ = _ := by ring

/-- **The quadratic convection term against a divergence-free field.** For a divergence-free
`f` and any `g` in `H¹(ℝ³)³`, `|b(g, f, g)| = |∫ (g·∇)f·g| ≤ (1/√3) ‖∇f‖₂ ‖g‖₄²`. -/
theorem abs_convectionTrilinear_self_le {f : E} (hf : divergenceCLM f = 0) (g : E) :
    |convectionTrilinear g f g| ≤
      1 / √3 * ‖gradientCLM f‖ * (eLpNorm (representative g) 4 volume).toReal ^ 2 := by
  have h2 := abs_convectionTrilinear_add_swap_le hf g g
  rw [eLpNorm_norm_mul_norm_self (memLp_representative g).aestronglyMeasurable,
    ← ENNReal.toReal_rpow, Real.rpow_two, ← two_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have h3 : 2 * |convectionTrilinear g f g| ≤ 2 * (1 / √3 * ‖gradientCLM f‖ *
      (eLpNorm (representative g) 4 volume).toReal ^ 2) :=
    h2.trans (le_of_eq (by ring))
  linarith

/-- **The quadratic term of a perturbation and its correction.** For divergence-free `w`, `z`
in `H¹(ℝ³)³`,

`|b(w + z, z, w)| ≤ (1/√3) (‖∇z‖₂ ‖w‖₄² + ‖∇w‖₂ ‖z‖₄²)`.

The term is `b(w, z, w) - b(z, w, z)`, by the skew symmetry of the form for the advecting
field `z`. This is the display before (4.40) of Hou, Wang and Yang, with `w = U₁`, `z = U₂`. -/
theorem abs_convectionTrilinear_add_le {w z : E} (hw : divergenceCLM w = 0)
    (hz : divergenceCLM z = 0) :
    |convectionTrilinear (w + z) z w| ≤ 1 / √3 *
      (‖gradientCLM z‖ * (eLpNorm (representative w) 4 volume).toReal ^ 2 +
        ‖gradientCLM w‖ * (eLpNorm (representative z) 4 volume).toReal ^ 2) := by
  have h1 := abs_convectionTrilinear_self_le hz w
  have h2 := abs_convectionTrilinear_self_le hw z
  have hsplit : convectionTrilinear (w + z) z w =
      convectionTrilinear w z w - convectionTrilinear z w z := by
    simp only [map_add, add_apply]
    rw [convectionTrilinear_skew hz z w]
    ring
  rw [hsplit]
  calc _ ≤ |convectionTrilinear w z w| + |convectionTrilinear z w z| := abs_sub _ _
    _ ≤ 1 / √3 * ‖gradientCLM z‖ * (eLpNorm (representative w) 4 volume).toReal ^ 2 +
        1 / √3 * ‖gradientCLM w‖ * (eLpNorm (representative z) 4 volume).toReal ^ 2 :=
      add_le_add h1 h2
    _ = _ := by ring

/-- **The cross terms of two divergence-free fields against a third.** For divergence-free
`u`, `z`, `w` in `H¹(ℝ³)³`,

`|b(u, z, w) + b(z, u, w)| ≤ (2/√3) ‖∇w‖₂ ‖|u| |z|‖₂`.

By skew symmetry the left side is `|b(u, w, z) + b(z, w, u)| = 2 |∫ (u ⊗ z) : Sw|`. This is the
first line of the display after (4.54) of Hou, Wang and Yang, with `u = U`, `z = v₂`,
`w = v₁`. -/
theorem abs_convectionTrilinear_cross_le {u z w : E} (hu : divergenceCLM u = 0)
    (hz : divergenceCLM z = 0) (hw : divergenceCLM w = 0) :
    |convectionTrilinear u z w + convectionTrilinear z u w| ≤ 2 / √3 * ‖gradientCLM w‖ *
      (eLpNorm (fun x ↦ ‖representative u x‖ * ‖representative z x‖) 2 volume).toReal := by
  have h := abs_convectionTrilinear_add_swap_le hw u z
  rw [convectionTrilinear_skew hu z w, convectionTrilinear_skew hz u w, ← neg_add, abs_neg]
  exact h

end NavierStokes.Stationary
