/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Construction
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Differentiable flow families from local initial data

For a C¹ vector field on a finite-dimensional real space, the local flow has
a state derivative solving the variational equation. Composing the
flow with a local C¹ initial map gives a jointly C¹ family. Its derivative
in an initial-data direction also solves the variational equation: the chain
rule composes the state derivative with the fixed derivative of the initial
map, so no second derivative of that map is required.

The characteristic ODE (31) of Evans, §3.2.4, with the initial conditions (32) at a point `y`
of the boundary, is a family of this kind: the vector field is autonomous in `(p, z, x)` and
the initial map is `y ↦ (q(y), g(y), y)`. His Lemma 2 applies the inverse function theorem to
`(y, s) ↦ x(y, s)`.

## Main results

* `exists_local_contDiff_one_family_with_initialData`: a jointly `C¹` family of solutions with
  the given initial data, whose derivative in an initial-data direction solves the variational
  equation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.4, the notation for the solution of (31), (32) and
  Lemma 2 (local invertibility) with its proof, pp. 105-106.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Metric Set
open scoped NNReal Topology

namespace PDE.Analysis.ODE

variable {E Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Construct a C¹ family from local C¹ initial data, retaining the time
derivative of its boundary variation.

The chain rule identifies this variation with the state derivative of the
flow composed with the derivative of the initial map. The latter is fixed
when time varies, so no second derivative of the initial map is needed. -/
theorem exists_local_contDiff_one_family_with_initialData
    (v : E → E) (hv : ContDiff ℝ 1 v)
    (initial : Y → E) (U : Set Y) (hU : IsOpen U)
    (hi : ContDiffOn ℝ 1 initial U) (y0 : Y) (hy0 : y0 ∈ U) :
    ∃ W : Set Y, IsOpen W ∧ y0 ∈ W ∧ W ⊆ U ∧
      ∃ T : ℝ, 0 < T ∧ ∃ curve : Y × ℝ → E,
        ContDiffOn ℝ 1 curve (W ×ˢ Ioo (-T) T) ∧
        ∀ y ∈ W,
          curve (y, 0) = initial y ∧
          ∀ t ∈ Ioo (-T) T,
            HasDerivAt (fun s ↦ curve (y, s)) (v (curve (y, t))) t ∧
            ∀ dy : Y,
              HasDerivAt (fun s ↦ fderiv ℝ curve (y, s) (dy, 0))
                (fderiv ℝ v (curve (y, t))
                  (fderiv ℝ curve (y, t) (dy, 0))) t := by
  obtain ⟨r, hr, T, hT, flow, variation, hf, _, _, hflow⟩ :=
    exists_local_contDiff_one_family_of_contDiff_one v hv (initial y0)
  let W : Set Y := U ∩ initial ⁻¹' ball (initial y0) r
  have hW : IsOpen W := hi.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hyW : y0 ∈ W := ⟨hy0, mem_ball_self hr⟩
  let curve : Y × ℝ → E := fun yt ↦ flow (initial yt.1, yt.2)
  have hlift : ContDiffOn ℝ 1 (fun yt : Y × ℝ ↦ (initial yt.1, yt.2))
      (W ×ˢ Ioo (-T) T) :=
    (hi.comp contDiffOn_fst (fun yt hyt ↦ hyt.1.1)).prodMk contDiffOn_snd
  have hc : ContDiffOn ℝ 1 curve (W ×ˢ Ioo (-T) T) :=
    hf.comp hlift (fun yt hyt ↦ ⟨hyt.1.2, hyt.2⟩)
  refine ⟨W, hW, hyW, inter_subset_left, T, hT, curve, hc, ?_⟩
  intro y hy
  refine ⟨(hflow (initial y) hy.2).1, ?_⟩
  intro t ht
  refine ⟨((hflow (initial y) hy.2).2.2 t ht).1, ?_⟩
  intro dy
  have hiAt : DifferentiableAt ℝ initial y :=
    (hi.contDiffAt (hU.mem_nhds hy.1)).differentiableAt (by norm_num)
  have hidentify (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      fderiv ℝ curve (y, s) (dy, 0) =
        variation (initial y, s) (fderiv ℝ initial y dy) := by
    have hcAt : DifferentiableAt ℝ curve (y, s) :=
      (hc.contDiffAt ((hW.prod isOpen_Ioo).mem_nhds ⟨hy, hs⟩)).differentiableAt
        (by norm_num)
    have hjoint := hcAt.hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) y s)
    have hstate := (((hflow (initial y) hy.2).2.2 s hs).2.2).comp y hiAt.hasFDerivAt
    have heq := hjoint.unique hstate
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] using
      congrArg (fun L : Y →L[ℝ] E ↦ L dy) heq
  have hJ := ((hflow (initial y) hy.2).2.2 t ht).2.1
  have hraw := hJ.clm_apply (hasDerivAt_const (x := t) (c := fderiv ℝ initial y dy))
  have hraw' : HasDerivAt
      (fun s ↦ variation (initial y, s) (fderiv ℝ initial y dy))
      (fderiv ℝ v (curve (y, t))
        (variation (initial y, t) (fderiv ℝ initial y dy))) t := by
    simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using hraw
  rw [← hidentify t ht] at hraw'
  apply hraw'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.eventually_mem ht] with s hs
  exact hidentify s hs


end PDE.Analysis.ODE

end
