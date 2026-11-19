/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Approximation.Basic
public import PDE.Analysis.Convex.Proximal.Yosida.Comparison

/-!
# Uniform comparison of constructed Yosida curves

For `λ, μ > 0` and `v ∈ ∂I(x₀)`, the Yosida flows from `x₀` satisfy
`‖u_λ(t) - u_μ(t)‖² ≤ ((λ + μ)/2) t ‖v‖²` for `t ≥ 0`. Both velocities have norm at
most `‖v‖`, so the monotonicity defect `⟪A_λ x - A_μ y, x - y⟫` is at least
`-((λ + μ)/4) ‖v‖²` along the flows, and the mean value inequality for
`½ ‖u_λ - u_μ‖²` gives the bound. This is (23) in Evans's proof of Theorem 3 of §9.6.2, with
any `v ∈ ∂I(x₀)` in place of the element of least norm `A⁰[u]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, step 3 of the proof of Theorem 3, (21)-(23),
  pp. 567-568. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set PDE.Analysis.Convex

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- Two-parameter estimate for the constructed Yosida flows:
`‖u_λ(t) - u_μ(t)‖² ≤ ((λ + μ)/2) t ‖v‖²` for `v ∈ ∂I(x₀)` and `t ≥ 0`. -/
theorem norm_yosidaFlow_sub_sq_le (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    {lambda mu : ℝ} (hlambda : 0 < lambda) (hmu : 0 < mu)
    {x₀ v : H} (hv : v ∈ subdifferential I x₀) {t : ℝ} (ht : 0 ≤ t) :
    ‖yosidaFlow I hproper hconvex hlsc lambda hlambda x₀ t -
      yosidaFlow I hproper hconvex hlsc mu hmu x₀ t‖ ^ 2 ≤
        (lambda + mu) / 2 * t * ‖v‖ ^ 2 := by
  let u := yosidaFlow I hproper hconvex hlsc lambda hlambda x₀
  let w := yosidaFlow I hproper hconvex hlsc mu hmu x₀
  let A := yosidaApproximation I hproper hconvex hlsc lambda hlambda
  let B := yosidaApproximation I hproper hconvex hlsc mu hmu
  have hu : IsIntegralCurveOn u (fun _ x ↦ -A x) (Ici 0) :=
    isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hlambda x₀
  have hw : IsIntegralCurveOn w (fun _ x ↦ -B x) (Ici 0) :=
    isIntegralCurveOn_yosidaFlow hproper hconvex hlsc hmu x₀
  let energy := fun r ↦ (1 / 2 : ℝ) * ‖u r - w r‖ ^ 2
  have hd (r : ℝ) (hr : r ∈ interior (Ici (0 : ℝ))) :
      HasDerivAt energy (-inner ℝ (A (u r) - B (w r)) (u r - w r)) r := by
    have h := hasDerivAt_half_norm_sq
      (((hu r (interior_subset hr)).hasDerivAt (mem_interior_iff_mem_nhds.1 hr)).sub
        ((hw r (interior_subset hr)).hasDerivAt (mem_interior_iff_mem_nhds.1 hr)))
    have hneg : -A (u r) - -B (w r) = -(A (u r) - B (w r)) := by abel
    simpa only [hneg, inner_neg_left, Pi.sub_apply, energy] using h
  have hbound (r : ℝ) (hr : r ∈ interior (Ici (0 : ℝ))) :
      deriv energy r ≤ (lambda + mu) / 4 * ‖v‖ ^ 2 := by
    rw [(hd r hr).deriv]
    have h := neg_mul_sq_le_inner_yosidaApproximation_sub hproper hconvex hlsc
      hlambda hmu (u r) (w r)
      (norm_yosidaFlow_velocity_le hproper hconvex hlsc hlambda hv (interior_subset hr))
      (norm_yosidaFlow_velocity_le hproper hconvex hlsc hmu hv (interior_subset hr))
    change -(lambda + mu) / 4 * ‖v‖ ^ 2 ≤ inner ℝ (A (u r) - B (w r)) (u r - w r) at h
    linarith
  have h := (convex_Ici (0 : ℝ)).image_sub_le_mul_sub_of_deriv_le
    (continuousOn_const.mul ((hu.continuousOn.sub hw.continuousOn).norm.pow 2))
    (fun r hr ↦ (hd r hr).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) t ht ht
  have hzero : energy 0 = 0 := by simp [energy, u, w, yosidaFlow_zero]
  change energy t - energy 0 ≤ _ at h
  rw [hzero] at h
  change ‖u t - w t‖ ^ 2 ≤ _
  dsimp only [energy] at h
  nlinarith

end PDE.Analysis.Evolution
