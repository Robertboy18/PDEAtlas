/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Chart
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Local Legendre duality without convexity

For a local inverse X of the gradient of u, the explicit expression
`inner p (X p) - u (X p)` has gradient X. Its C² regularity follows from C¹ regularity of X,
so a nondegenerate C² germ of u suffices. This is local gradient inversion, not a global
convex conjugate, and no convexity is assumed. The expression is the Legendre transform (28)
of Evans, §4.4.3(b).

## Main results

* `localLegendre`, `hasGradientAt_localLegendre`, `contDiffOn_localLegendre`: the local dual,
  its gradient and its `C²` regularity.
* `exists_localLegendre_inverse_hessian`: near a point where the Hessian determinant of a
  `C²` function `u` on `ℝ^n` is nonzero, the gradient of `u` has a local `C¹` inverse, and the
  local dual is `C²`, with that inverse as its gradient and the inverse of the Hessian of `u`
  as its Hessian. In the plane this gives Evans's identities (29).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.3(b), (25)-(29), p. 210.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped ContDiff Gradient RealInnerProductSpace

namespace PDE.Analysis

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The local dual expression associated with a chosen inverse momentum map. -/
def localLegendre (u : E → ℝ) (X : E → E) (p : E) : ℝ :=
  ⟪p, X p⟫ - u (X p)

/-- Derivatives of the inverse momentum map cancel from the local dual expression. -/
theorem hasGradientAt_localLegendre
    {u : E → ℝ} {X : E → E} {p : E}
    (hu : HasGradientAt u p (X p)) (hX : DifferentiableAt ℝ X p) :
    HasGradientAt (localLegendre u X) (X p) p := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hinner := (hasFDerivAt_id p).inner ℝ hX.hasFDerivAt
  have hcomp := hu.hasFDerivAt.comp p hX.hasFDerivAt
  apply (hinner.sub hcomp).congr_fderiv
  ext z
  simp only [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.id_apply,
    InnerProductSpace.toDual_apply_apply, id_eq]
  rw [add_sub_cancel_left, real_inner_comm]

/-- A C¹ inverse momentum field makes the explicit local dual function C².
Only its first derivative is differentiated, avoiding a C² assumption on X. -/
theorem contDiffOn_localLegendre
    {u : E → ℝ} {X : E → E} {s : Set E}
    (hs : IsOpen s) (hX : ContDiffOn ℝ 1 X s)
    (hu : ∀ p ∈ s, HasGradientAt u p (X p)) :
    ContDiffOn ℝ 2 (localLegendre u X) s := by
  have hv (p : E) (hp : p ∈ s) :
      HasGradientAt (localLegendre u X) (X p) p :=
    hasGradientAt_localLegendre (hu p hp)
      ((hX.contDiffAt (hs.mem_nhds hp)).differentiableAt one_ne_zero)
  change ContDiffOn ℝ ((1 : ℕ∞ω) + 1) (localLegendre u X) s
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  refine ⟨fun p hp ↦ (hv p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  apply ((innerSL ℝ).contDiff.comp_contDiffOn hX).congr
  intro p hp
  exact (hv p hp).hasFDerivAt.fderiv

end Hilbert

/-- A nondegenerate C² germ has a C² local dual whose gradient is the inverse
gradient map and whose Hessian is the inverse original Hessian.
No convexity or global inverse is assumed. -/
theorem exists_localLegendre_inverse_hessian
    {n : ℕ} {u : ℝ^n → ℝ} {Ω : Set (ℝ^n)} {x : ℝ^n}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hdet : (jacobianMatrix (∇ u) x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (e : ℝ^n → ℝ^n) = ∇ u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ContDiffOn ℝ 2 (localLegendre u e.symm) e.target ∧
            (∀ p ∈ e.target, HasGradientAt (localLegendre u e.symm) (e.symm p) p) ∧
              ∀ p ∈ e.target,
                fderiv ℝ (∇ (localLegendre u e.symm)) p =
                  (fderiv ℝ (∇ u) (e.symm p)).inverse := by
  obtain ⟨e, he, hxe, hsource, hi, _hregular⟩ :=
    exists_regular_gradient_inverse_chart hΩ hx hu hdet
  have hsolve (p : ℝ^n) (hp : p ∈ e.target) :
      HasGradientAt u p (e.symm p) := by
    have hgrad := (hu.contDiffAt
      (hΩ.mem_nhds (hsource (e.map_target hp)))).differentiableAt (by norm_num)
    have hvalue : ∇ u (e.symm p) = p := by
      rw [← he]
      exact e.right_inv hp
    simpa only [hvalue] using hgrad.hasGradientAt
  have hv (p : ℝ^n) (hp : p ∈ e.target) :
      HasGradientAt (localLegendre u e.symm) (e.symm p) p :=
    hasGradientAt_localLegendre (hsolve p hp)
      ((hi.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt one_ne_zero)
  refine ⟨e, he, hxe, hsource, hi,
    contDiffOn_localLegendre e.open_target hi hsolve, hv, ?_⟩
  intro p hp
  have hnear : ∇ (localLegendre u e.symm) =ᶠ[𝓝 p] e.symm :=
    Filter.Eventually.mono (e.open_target.mem_nhds hp) fun q hq ↦ (hv q hq).gradient
  rw [hnear.fderiv_eq]
  have hg : DifferentiableAt ℝ e (e.symm p) := by
    rw [he]
    exact (contDiffAt_gradient (m := 1)
      (hu.contDiffAt (hΩ.mem_nhds (hsource (e.map_target hp))))).differentiableAt
        one_ne_zero
  have hXi := (hi.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt one_ne_zero
  simpa only [he] using inverse_chart_fderiv_symm e hp hg hXi

end PDE.Analysis
