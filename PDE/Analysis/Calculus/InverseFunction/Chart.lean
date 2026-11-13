/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.InverseFunction.Jacobian
public import PDE.Analysis.Calculus.Gradient

/-!
# Regular local inverse charts

A nonsingular C¹ germ gives a chart with C¹ inverse on its entire open target.
Both derivative compositions are identities, and the signed determinants multiply to one.
Restricting the chart keeps its source inside the prescribed open domain. For gradient maps,
C² regularity and nonsingularity of the Hessian at one point suffice; convexity is unnecessary.

The chart is the inverse function theorem of Evans, Appendix C.6, Theorem 8 (i) and (ii). The
local inverse comes from Mathlib's `ContDiffAt.toOpenPartialHomeomorph` and
`ContDiffAt.to_localInverse`, through `exists_openPartialHomeomorph_of_det_jacobianMatrix_ne_zero`.

## Main results

* `exists_contDiffOn_inverse_chart`, `exists_regular_contDiffOn_inverse_chart`: a `C¹` map on
  an open set `Ω` with nonzero Jacobian determinant at `x` has a local chart at `x` with source
  in `Ω`, `C¹` inverse on its target and nonzero Jacobian determinant on its source.
* `inverse_chart_fderiv_symm`, `inverse_chart_det_mul`: the derivative of the inverse is the
  inverse of the derivative, and the Jacobian determinants multiply to one.
* `exists_regular_gradient_inverse_chart`: the same chart for the gradient of a `C²` function.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.6, Theorem 8 (Inverse Function Theorem),
  pp. 716-717. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped Gradient

namespace PDE.Analysis

/-- A nonsingular C¹ map has a local inverse which is C¹ on its entire target,
with source contained in the prescribed open domain. -/
theorem exists_contDiffOn_inverse_chart
    {n : ℕ} {f : ℝ^n → ℝ^n} {Ω : Set (ℝ^n)} {x : ℝ^n}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hdet : (jacobianMatrix f x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (e : ℝ^n → ℝ^n) = f ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target := by
  obtain ⟨e, he, hxe, hi⟩ :=
    exists_openPartialHomeomorph_of_det_jacobianMatrix_ne_zero
      (hf.contDiffAt (hΩ.mem_nhds hx)) one_ne_zero hdet
  obtain ⟨W, hW, hdiff⟩ := hi.contDiffOn le_rfl (by simp)
  obtain ⟨V, hVW, hV, hxV⟩ := mem_nhds_iff.mp hW
  let eΩ := e.restrOpen Ω hΩ
  let eV := (eΩ.symm.restrOpen V hV).symm
  refine ⟨eV, he, ?_, ?_, ?_⟩
  · change x ∈ e.source ∩ Ω ∧ e x ∈ V
    exact ⟨⟨hxe, hx⟩, he ▸ hxV⟩
  · intro y hy
    change y ∈ e.source ∩ Ω ∧ e y ∈ V at hy
    exact hy.1.2
  · change ContDiffOn ℝ 1 e.symm (eΩ.target ∩ V)
    exact hdiff.mono fun _ hy ↦ hVW hy.2

/-- Differentiating the local right inverse gives the identity on target tangent vectors. -/
theorem inverse_chart_fderiv_comp
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  have hc := hf.hasFDerivAt.comp y hi.hasFDerivAt
  have he : (fun z ↦ e (e.symm z)) =ᶠ[𝓝 y] id := e.eventually_right_inverse hy
  exact (hc.congr_of_eventuallyEq he.symm).unique
    (hasFDerivAt_id y)

/-- Differentiating the local left inverse gives the identity on source tangent vectors. -/
theorem inverse_chart_symm_fderiv_comp
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    (fderiv ℝ e.symm y).comp (fderiv ℝ e (e.symm y)) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  have h := inverse_chart_fderiv_comp e.symm (e.map_target hy)
    (by simpa only [OpenPartialHomeomorph.symm_symm, e.right_inv hy] using hi) hf
  simpa only [OpenPartialHomeomorph.symm_symm, e.right_inv hy] using h

/-- The derivative of a differentiable inverse chart is the inverse linear map. -/
theorem inverse_chart_fderiv_symm
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    fderiv ℝ e.symm y = (fderiv ℝ e (e.symm y)).inverse :=
  (ContinuousLinearMap.inverse_eq (inverse_chart_fderiv_comp e hy hf hi)
    (inverse_chart_symm_fderiv_comp e hy hf hi)).symm

/-- The signed Jacobian determinants of inverse charts multiply to one. -/
theorem inverse_chart_det_mul
    {n : ℕ} (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    {y : ℝ^n} (hy : y ∈ e.target)
    (hf : DifferentiableAt ℝ e (e.symm y))
    (hi : DifferentiableAt ℝ e.symm y) :
    (jacobianMatrix e (e.symm y)).det * (jacobianMatrix e.symm y).det = 1 := by
  rw [det_jacobianMatrix hf, det_jacobianMatrix hi]
  have h := congrArg (fun L : ℝ^n →L[ℝ] ℝ^n ↦ LinearMap.det L.toLinearMap)
    (inverse_chart_fderiv_comp e hy hf hi)
  change LinearMap.det
    ((fderiv ℝ e (e.symm y)).toLinearMap.comp (fderiv ℝ e.symm y).toLinearMap) =
      LinearMap.det LinearMap.id at h
  simpa only [LinearMap.det_comp, LinearMap.det_id] using h

/-- The local chart can be chosen regular throughout its source, from nonsingularity
only at the initial point. Both inverse derivative identities are consequences. -/
theorem exists_regular_contDiffOn_inverse_chart
    {n : ℕ} {f : ℝ^n → ℝ^n} {Ω : Set (ℝ^n)} {x : ℝ^n}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hf : ContDiffOn ℝ 1 f Ω)
    (hdet : (jacobianMatrix f x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (e : ℝ^n → ℝ^n) = f ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ∀ z ∈ e.source, (jacobianMatrix f z).det ≠ 0 := by
  obtain ⟨e, he, hxe, hsource, hi⟩ :=
    exists_contDiffOn_inverse_chart hΩ hx hf hdet
  refine ⟨e, he, hxe, hsource, hi, ?_⟩
  intro z hz
  have hfz : DifferentiableAt ℝ e z := by
    rw [he]
    exact (hf.contDiffAt (hΩ.mem_nhds (hsource hz))).differentiableAt one_ne_zero
  have hiz := (hi.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt
    one_ne_zero
  have hd := inverse_chart_det_mul e (e.map_source hz)
    (by simpa only [e.left_inv hz] using hfz) hiz
  have hn := left_ne_zero_of_mul_eq_one hd
  rw [e.left_inv hz] at hn
  simpa only [he] using hn

/-- A C² scalar function with nonsingular Hessian at one point admits a C¹ local
gradient inverse, without any convexity assumption. -/
theorem exists_regular_gradient_inverse_chart
    {n : ℕ} {u : ℝ^n → ℝ} {Ω : Set (ℝ^n)} {x : ℝ^n}
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hu : ContDiffOn ℝ 2 u Ω)
    (hdet : (jacobianMatrix (∇ u) x).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (e : ℝ^n → ℝ^n) = ∇ u ∧ x ∈ e.source ∧ e.source ⊆ Ω ∧
        ContDiffOn ℝ 1 e.symm e.target ∧
          ∀ z ∈ e.source, (jacobianMatrix (∇ u) z).det ≠ 0 := by
  apply exists_regular_contDiffOn_inverse_chart hΩ hx ?_ hdet
  apply hΩ.contDiffOn_iff.mpr
  intro z hz
  exact contDiffAt_gradient (m := 1) (hu.contDiffAt (hΩ.mem_nhds hz))

end PDE.Analysis
