/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.DecayingHessian
import PDE.FDeriv.Reflection.Coordinate
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Axis quotients of the stream function and the velocity

Chen and Hou, Part I, (6.59b): for a source `f` odd in `x₀` in the weighted class of (6.59a)
(`|f(y)| ≤ M ⟨y⟩^{-b}` and `⟨y⟩^{-p} f` `α`-Hölder with constant `M` on the closed upper
half-plane, `⟨y⟩ = 1 + |y|`, `0 < b ≤ 1`), the stream function `Ψ = quadrantPotential f` and the
velocity `u = -∂₁Ψ`, `v = ∂₀Ψ` satisfy

`|Ψ/(x₀ x₁)| + |u/x₀| + |v/x₁| ≤ C M ⟨x⟩^{-b/2}`

in the open upper half-plane (`exists_abs_quotients_le_of_weighted`, stated without division).
`u` vanishes on the axis `x₀ = 0` because `Ψ` is odd in `x₀`, and `v` and `Ψ` vanish on the wall
`x₁ = 0`; each bound integrates the decay bound of the Hessian (6.59a) along a horizontal or
vertical segment from the axis or the wall. The decay in `⟨x⟩` survives the integration because
`∫₀^T (1 + max(c, t))^{-s} dt ≤ T (1 + max(c, T))^{-s}/(1 - s)` for `0 ≤ s < 1`
(`abs_le_of_abs_deriv_le`): the integrand is comparable to the derivative of
`t ↦ t (1 + t)^{-s}`. Part I states (6.59b) for `β ∈ (0, 1/4]`; our version takes `0 < b ≤ 1`.

## Main results

* `abs_le_of_abs_deriv_le`: if `h(0) = 0`, `h` is continuous on `[0, T]` and
  `|h'(t)| ≤ A (1 + max(c, t))^{-s}` on `(0, T)`, `c ≥ 0`, `0 ≤ s < 1`, then
  `|h(T)| ≤ A/(1 - s) · T (1 + max(c, T))^{-s}`.
* `exists_abs_quotients_le_of_weighted`: (6.59b), the axis quotient bound
  `|Ψ/(x₀ x₁)| + |u/x₀| + |v/x₁| ≤ C M ⟨x⟩^{-b/2}` in the open upper half-plane, without division.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, (6.59a) and (6.59b),
  p. 108.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace
open scoped Topology

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

/-- **Integration of a decaying derivative.** If `h(0) = 0`, `h` is continuous on `[0, T]` and
`|h'(t)| ≤ A (1 + max(c, t))^{-s}` on `(0, T)` with `c ≥ 0`, `0 ≤ s < 1`, then
`|h(T)| ≤ A/(1 - s) · T (1 + max(c, T))^{-s}`. -/
theorem abs_le_of_abs_deriv_le {h h' : ℝ → ℝ} {T A c s : ℝ} (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hs : 0 ≤ s) (hs1 : s < 1) (hcont : ContinuousOn h (Icc 0 T))
    (hder : ∀ t ∈ Ioo 0 T, HasDerivAt h (h' t) t) (h0 : h 0 = 0)
    (hb : ∀ t ∈ Ioo 0 T, |h' t| ≤ A * (1 + max c t) ^ (-s)) :
    |h T| ≤ A / (1 - s) * T * (1 + max c T) ^ (-s) := by
  rcases hT.eq_or_lt with hT0 | hTpos
  · subst hT0; simp [h0]
  have hA : 0 ≤ A := nonneg_of_mul_nonneg_left
    ((abs_nonneg _).trans (hb (T / 2) ⟨by linarith, by linarith⟩)) (by positivity)
  have hs1' : 0 < 1 - s := by linarith
  rcases le_or_gt T c with hTc | hcT
  · -- the constant majorant
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope h h' hTpos hcont hder
    have hmax : ∀ t ∈ Ioo 0 T, max c t = c := fun t ht ↦ max_eq_left (ht.2.le.trans hTc)
    have hξb := hb ξ hξ
    rw [hmax ξ hξ, hslope, h0, sub_zero, sub_zero, abs_div, abs_of_pos hTpos] at hξb
    rw [max_eq_left hTc]
    calc |h T| ≤ A * (1 + c) ^ (-s) * T := by rwa [div_le_iff₀ hTpos] at hξb
      _ = A * (T * (1 + c) ^ (-s)) := by ring
      _ ≤ A / (1 - s) * (T * (1 + c) ^ (-s)) := by
        gcongr; exact le_div_self hA hs1' (by linarith)
      _ = A / (1 - s) * T * (1 + c) ^ (-s) := by ring
  · -- the majorant `t (1 + t)^{-s}`
    set g := fun t : ℝ ↦ t * (1 + t) ^ (-s)
    set g' := fun t : ℝ ↦ (1 + t) ^ (-s) + t * (-s * (1 + t) ^ (-s - 1))
    have hgd : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t := fun t ht ↦ by
      simpa only [id, one_mul] using (hasDerivAt_id t).fun_mul
        (((hasDerivAt_id t).const_add 1).rpow_const (p := -s)
          (Or.inl (by simp only [id]; linarith)))
    have hgc : ContinuousOn g (Icc 0 T) := fun t ht ↦
      (hgd t ht.1).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hcauchy⟩ := exists_ratio_hasDerivAt_eq_ratio_slope h h' hTpos hcont hder g g'
      hgc fun t ht ↦ hgd t ht.1.le
    have hξ0 : 0 < ξ := hξ.1
    have h1ξ : 0 < 1 + ξ := by linarith
    have hpow : (1 + ξ) ^ (-s - 1) = (1 + ξ) ^ (-s) / (1 + ξ) := Real.rpow_sub_one h1ξ.ne' _
    have hg'ge : (1 - s) * (1 + ξ) ^ (-s) ≤ g' ξ := by
      simp only [g']
      rw [hpow]
      have hq : ξ / (1 + ξ) ≤ 1 := by rw [div_le_one h1ξ]; linarith
      have hP : 0 < (1 + ξ) ^ (-s) := Real.rpow_pos_of_pos h1ξ _
      have : ξ * (-s * ((1 + ξ) ^ (-s) / (1 + ξ))) = -s * (1 + ξ) ^ (-s) * (ξ / (1 + ξ)) := by
        field_simp
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left hq (mul_nonneg hs hP.le)]
    have hg'pos : 0 < g' ξ := lt_of_lt_of_le (by positivity) hg'ge
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0, h0, sub_zero, sub_zero] at hcauchy
    have hξb := hb ξ hξ
    have hmaxξ : (1 + max c ξ) ^ (-s) ≤ (1 + ξ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith [le_max_right c ξ]) (by linarith)
    have hgT : 0 ≤ g T := by simp only [g]; positivity
    have hkey : |h T| * g' ξ = g T * |h' ξ| := by
      rw [← abs_of_pos hg'pos, ← abs_of_nonneg hgT, ← abs_mul, ← abs_mul, hcauchy]
    have hmT : max c T = T := max_eq_right hcT.le
    rw [hmT]
    have hstep : |h T| * g' ξ ≤ (A / (1 - s) * T * (1 + T) ^ (-s)) * g' ξ := by
      rw [hkey]
      calc g T * |h' ξ| ≤ g T * (A * (1 + ξ) ^ (-s)) :=
            mul_le_mul_of_nonneg_left (hξb.trans (mul_le_mul_of_nonneg_left hmaxξ hA)) hgT
        _ = A / (1 - s) * g T * ((1 - s) * (1 + ξ) ^ (-s)) := by field_simp
        _ ≤ A / (1 - s) * g T * g' ξ := by gcongr
        _ = (A / (1 - s) * T * (1 + T) ^ (-s)) * g' ξ := by simp only [g]; ring
    exact le_of_mul_le_mul_right hstep hg'pos

/-! ### Segments and parities -/

/-- The point `x + (t - xᵢ) eᵢ`: the `i`-th coordinate of `x` moved to `t`. -/
private def segmentPoint (x : ℝ^2) (i : Fin 2) (t : ℝ) : ℝ^2 :=
  x + (t - x i) • EuclideanSpace.single i (1 : ℝ)

/-- The coordinate segment `t ↦ x + (t - xᵢ) eᵢ` has derivative `eᵢ`. -/
private theorem hasDerivAt_segmentPoint (x : ℝ^2) (i : Fin 2) (t : ℝ) :
    HasDerivAt (segmentPoint x i) (EuclideanSpace.single i 1) t := by
  have h := (((hasDerivAt_id t).sub_const (x i)).smul_const
    (EuclideanSpace.single i (1 : ℝ))).const_add x
  simp only [id, one_smul] at h
  exact h

/-- The coordinate segment `t ↦ x + (t - xᵢ) eᵢ` is continuous. -/
private theorem continuous_segmentPoint (x : ℝ^2) (i : Fin 2) : Continuous (segmentPoint x i) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_segmentPoint x i t).continuousAt

/-- The coordinate segment through `x` in direction `eᵢ` passes through `x` at `t = xᵢ`. -/
private theorem segmentPoint_self (x : ℝ^2) (i : Fin 2) : segmentPoint x i (x i) = x := by
  simp [segmentPoint]

/-- On the horizontal segment through `x` the `0`-th coordinate is the parameter `t`. -/
private theorem segmentPoint_zero_apply_zero (x : ℝ^2) (t : ℝ) : segmentPoint x 0 t 0 = t := by
  simp [segmentPoint]

/-- On the horizontal segment through `x` the `1`-st coordinate is `x₁`. -/
private theorem segmentPoint_zero_apply_one (x : ℝ^2) (t : ℝ) :
    segmentPoint x 0 t 1 = x 1 := by
  simp [segmentPoint]

/-- On the vertical segment through `x` the `0`-th coordinate is `x₀`. -/
private theorem segmentPoint_one_apply_zero (x : ℝ^2) (t : ℝ) :
    segmentPoint x 1 t 0 = x 0 := by
  simp [segmentPoint]

/-- On the vertical segment through `x` the `1`-st coordinate is the parameter `t`. -/
private theorem segmentPoint_one_apply_one (x : ℝ^2) (t : ℝ) : segmentPoint x 1 t 1 = t := by
  simp [segmentPoint]

/-- The derivative along a coordinate segment is the partial derivative. -/
private theorem hasDerivAt_comp_segmentPoint {φ : ℝ^2 → ℝ} (x : ℝ^2) (i : Fin 2) {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (segmentPoint x i t)) :
    HasDerivAt (fun t ↦ φ (segmentPoint x i t)) ((∂[i] φ) (segmentPoint x i t)) t :=
  hφ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_segmentPoint x i t)

/-- `(1 + max(|y₀|, |y₁|))^{-s} ≤ 2 (1 + |y|)^{-s}` for `0 ≤ s ≤ 1`. -/
private theorem one_add_max_rpow_le {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (y : ℝ^2) :
    (1 + max |y 0| |y 1|) ^ (-s) ≤ 2 * (1 + ‖y‖) ^ (-s) := by
  refine one_add_rpow_neg_le_two_mul hs hs1 (by positivity) ?_
  have := EuclideanSpace.norm_le_abs_add_abs_fin_two y
  have h0 := le_max_left |y 0| |y 1|
  have h1 := le_max_right |y 0| |y 1|
  linarith [abs_nonneg (y 0)]

/-- The coordinate reflection fixes the points of the axis `x₀ = 0`. -/
private theorem coordinateReflection_zero_of_eq_zero {y : ℝ^2} (hy : y 0 = 0) : 𝐑 0 y = y := by
  ext i
  fin_cases i
  · simp [PDE.Common.coordinateReflection_apply_same, hy]
  · simp

variable {α b p M : ℝ} {f : ℝ^2 → ℝ}

/-- The horizontal velocity derivative `∂₁Ψ` is odd in `x₀`. -/
private theorem partialDeriv_one_quadrantPotential_reflect (hd : Differentiable ℝ
    (quadrantPotential f)) (y : ℝ^2) :
    (∂[1] (quadrantPotential f)) (𝐑 0 y) = -(∂[1] (quadrantPotential f)) y := by
  have hfun : (fun w ↦ quadrantPotential f (𝐑 0 w)) = -quadrantPotential f :=
    funext fun w ↦ quadrantPotential_coordinateReflection_zero f w
  have h := PDE.Common.partialDeriv_comp_coordinateReflection_of_ne 0 1 (by decide)
    (quadrantPotential f) y (hd _)
  rw [hfun, PDE.partialDeriv_neg] at h
  exact h.symm

/-- `∂₀Ψ` vanishes on the wall. -/
private theorem partialDeriv_zero_quadrantPotential_of_eq_zero (hd : Differentiable ℝ
    (quadrantPotential f)) {y : ℝ^2} (hy : y 1 = 0) : (∂[0] (quadrantPotential f)) y = 0 := by
  have h := hasDerivAt_comp_segmentPoint (φ := quadrantPotential f) y 0 (t := y 0) (hd _)
  rw [segmentPoint_self] at h
  have hconst : (fun t : ℝ ↦ quadrantPotential f (segmentPoint y 0 t)) = fun _ ↦ 0 :=
    funext fun t ↦ quadrantPotential_of_eq_zero f (by rw [segmentPoint_zero_apply_one]; exact hy)
  rw [hconst] at h
  exact h.unique (hasDerivAt_const _ _)

/-- **Part I (6.59b), axis quotients.** For `0 < α < 1`, `0 < b ≤ 1` and `p ≥ 0` there is `C`
such that for every source `f` odd in `x₀` with `|f(y)| ≤ M ⟨y⟩^{-b}` and
`|⟨y⟩^{-p} f(y) - ⟨z⟩^{-p} f(z)| ≤ M |y - z|^α` on the closed upper half-plane, `⟨y⟩ = 1 + |y|`,
the stream function `Ψ = quadrantPotential f` satisfies in the open upper half-plane
`|∂₁Ψ(x)| ≤ C M |x₀| ⟨x⟩^{-b/2}`, `|∂₀Ψ(x)| ≤ C M x₁ ⟨x⟩^{-b/2}` and
`|Ψ(x)| ≤ C M |x₀| x₁ ⟨x⟩^{-b/2}`: the bounds on `u/x₀`, `v/x₁` and `Ψ/(x₀ x₁)` with
`u = -∂₁Ψ`, `v = ∂₀Ψ`. -/
theorem exists_abs_quotients_le_of_weighted (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b)
    (hb1 : b ≤ 1) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, (∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y) →
      (∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
        |(1 + ‖y‖) ^ (-p) * f y - (1 + ‖z‖) ^ (-p) * f z| ≤ M * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 →
        |(∂[1] (quadrantPotential f)) x| ≤ C * M * |x 0| * (1 + ‖x‖) ^ (-(b / 2)) ∧
        |(∂[0] (quadrantPotential f)) x| ≤ C * M * x 1 * (1 + ‖x‖) ^ (-(b / 2)) ∧
        |quadrantPotential f x| ≤ C * M * |x 0| * x 1 * (1 + ‖x‖) ^ (-(b / 2)) := by
  obtain ⟨C₁, hC₁, hT⟩ := exists_abs_hessian_le_of_weighted hα hα1 hb hb1 hp
  have hs0 : 0 ≤ b / 2 := by positivity
  have hs1 : b / 2 < 1 := by linarith
  have hs1' : b / 2 ≤ 1 := hs1.le
  have h1s : 0 < 1 - b / 2 := by linarith
  refine ⟨2 * C₁ / (1 - b / 2) ^ 2, by positivity, ?_⟩
  intro f M hodd hS hH x hx
  have hM := nonneg_of_abs_le_mul_rpow hS
  have hf := isHolderVorticity_of_weighted hα hα1 hb hp hodd hS hH
  have hC1 := hf.contDiff_one_quadrantPotential
  have hd : Differentiable ℝ (quadrantPotential f) := hC1.differentiable one_ne_zero
  have hcd (i : Fin 2) : Continuous (∂[i] (quadrantPotential f)) :=
    (hC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hHess : ∀ y : ℝ^2, 0 < y 1 → ∀ k l : Fin 2,
      |(∂[l] (∂[k] (quadrantPotential f))) y| ≤ C₁ * M * (1 + max |y 0| |y 1|) ^ (-(b / 2)) := by
    intro y hy k l
    refine (hT hodd hS hH y hy k l).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [max_le (EuclideanSpace.abs_apply_le_norm y 0) (EuclideanSpace.abs_apply_le_norm
          y 1)]) (by linarith)
  have hdiff2 : ∀ y : ℝ^2, 0 < y 1 → ∀ k : Fin 2,
      DifferentiableAt ℝ (∂[k] (quadrantPotential f)) y := fun y hy k ↦
    (PDE.contDiffAt_partialDeriv 1 (hf.contDiffAt_quadrantPotential hy) k).differentiableAt
      one_ne_zero
  -- the horizontal velocity
  have hU0 : ∀ y : ℝ^2, 0 < y 1 → 0 ≤ y 0 → |(∂[1] (quadrantPotential f)) y| ≤
      C₁ * M / (1 - b / 2) * y 0 * (1 + max (y 1) (y 0)) ^ (-(b / 2)) := by
    intro y hy hy0
    have h := abs_le_of_abs_deriv_le
      (h := fun t ↦ (∂[1] (quadrantPotential f)) (segmentPoint y 0 t))
      (h' := fun t ↦ (∂[0] (∂[1] (quadrantPotential f))) (segmentPoint y 0 t))
      (A := C₁ * M) hy0 hy.le hs0 hs1
      ((hcd 1).comp (continuous_segmentPoint y 0)).continuousOn
      (fun t _ ↦ hasDerivAt_comp_segmentPoint y 0
        (hdiff2 _ (by rw [segmentPoint_zero_apply_one]; exact hy) 1))
      (by
        have := partialDeriv_one_quadrantPotential_reflect hd (segmentPoint y 0 0)
        rw [coordinateReflection_zero_of_eq_zero (segmentPoint_zero_apply_zero y 0)] at this
        exact (by linarith : (∂[1] (quadrantPotential f)) (segmentPoint y 0 0) = 0))
      (fun t ht ↦ by
        have hz1 := segmentPoint_zero_apply_one y t
        have hz0 := segmentPoint_zero_apply_zero y t
        refine (hHess _ (by rw [hz1]; exact hy) 1 0).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)) (by positivity))
        rw [hz0, hz1, abs_of_pos ht.1, abs_of_pos hy, max_comm])
    simpa [segmentPoint_self] using h
  have hU : ∀ y : ℝ^2, 0 < y 1 → |(∂[1] (quadrantPotential f)) y| ≤
      C₁ * M / (1 - b / 2) * |y 0| * (1 + max (y 1) |y 0|) ^ (-(b / 2)) := by
    intro y hy
    rcases le_or_gt 0 (y 0) with hy0 | hy0
    · rw [abs_of_nonneg hy0]; exact hU0 y hy hy0
    · have hr0 : (𝐑 0 y) 0 = -y 0 := PDE.Common.coordinateReflection_apply_same 0 y
      have hr1 : (𝐑 0 y) 1 = y 1 := PDE.Common.coordinateReflection_apply_of_ne 0 1 (by decide) y
      have h := hU0 (𝐑 0 y) (by rw [hr1]; exact hy) (by rw [hr0]; linarith)
      rw [partialDeriv_one_quadrantPotential_reflect hd, abs_neg, hr0, hr1] at h
      rwa [abs_of_neg hy0]
  -- the vertical velocity
  have hV : |(∂[0] (quadrantPotential f)) x| ≤
      C₁ * M / (1 - b / 2) * x 1 * (1 + max |x 0| (x 1)) ^ (-(b / 2)) := by
    have h := abs_le_of_abs_deriv_le
      (h := fun t ↦ (∂[0] (quadrantPotential f)) (segmentPoint x 1 t))
      (h' := fun t ↦ (∂[1] (∂[0] (quadrantPotential f))) (segmentPoint x 1 t))
      (A := C₁ * M) (c := |x 0|) hx.le (abs_nonneg _) hs0 hs1
      ((hcd 0).comp (continuous_segmentPoint x 1)).continuousOn
      (fun t ht ↦ hasDerivAt_comp_segmentPoint x 1
        (hdiff2 _ (by rw [segmentPoint_one_apply_one]; exact ht.1) 0))
      (partialDeriv_zero_quadrantPotential_of_eq_zero hd (segmentPoint_one_apply_one x 0))
      (fun t ht ↦ by
        have hz1 := segmentPoint_one_apply_one x t
        have hz0 := segmentPoint_one_apply_zero x t
        refine (hHess _ (by rw [hz1]; exact ht.1) 0 1).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)) (by positivity))
        rw [hz0, hz1, abs_of_pos ht.1])
    simpa [segmentPoint_self] using h
  -- the stream function
  have hP : |quadrantPotential f x| ≤
      C₁ * M / (1 - b / 2) * |x 0| / (1 - b / 2) * x 1 * (1 + max |x 0| (x 1)) ^ (-(b / 2)) := by
    have h := abs_le_of_abs_deriv_le
      (h := fun t ↦ quadrantPotential f (segmentPoint x 1 t))
      (h' := fun t ↦ (∂[1] (quadrantPotential f)) (segmentPoint x 1 t))
      (A := C₁ * M / (1 - b / 2) * |x 0|) (c := |x 0|) hx.le (abs_nonneg _) hs0 hs1
      (hC1.continuous.comp (continuous_segmentPoint x 1)).continuousOn
      (fun t _ ↦ hasDerivAt_comp_segmentPoint x 1 (hd _))
      (quadrantPotential_of_eq_zero f (segmentPoint_one_apply_one x 0))
      (fun t ht ↦ by
        have hz1 := segmentPoint_one_apply_one x t
        have hz0 := segmentPoint_one_apply_zero x t
        have := hU _ (by rw [hz1]; exact ht.1)
        rw [hz0, hz1, max_comm] at this
        exact this)
    simpa [segmentPoint_self] using h
  -- the bracket
  have hY := one_add_max_rpow_le hs0 hs1' x
  have hmax : max |x 0| (x 1) = max |x 0| |x 1| := by rw [abs_of_pos hx]
  set Y := (1 + ‖x‖) ^ (-(b / 2))
  have hY0 : 0 ≤ Y := by positivity
  have hcoef : C₁ * M / (1 - b / 2) ≤ C₁ * M / (1 - b / 2) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (sq_le h1s.le (by linarith))
  refine ⟨?_, ?_, ?_⟩
  · refine (hU x hx).trans ?_
    rw [max_comm, hmax]
    calc C₁ * M / (1 - b / 2) * |x 0| * (1 + max |x 0| |x 1|) ^ (-(b / 2))
        ≤ C₁ * M / (1 - b / 2) ^ 2 * |x 0| * (2 * Y) := by gcongr
      _ = 2 * C₁ / (1 - b / 2) ^ 2 * M * |x 0| * Y := by ring
  · refine hV.trans ?_
    rw [hmax]
    calc C₁ * M / (1 - b / 2) * x 1 * (1 + max |x 0| |x 1|) ^ (-(b / 2))
        ≤ C₁ * M / (1 - b / 2) ^ 2 * x 1 * (2 * Y) := by gcongr
      _ = 2 * C₁ / (1 - b / 2) ^ 2 * M * x 1 * Y := by ring
  · refine hP.trans ?_
    rw [hmax]
    calc C₁ * M / (1 - b / 2) * |x 0| / (1 - b / 2) * x 1 * (1 + max |x 0| |x 1|) ^ (-(b / 2))
        ≤ C₁ * M / (1 - b / 2) * |x 0| / (1 - b / 2) * x 1 * (2 * Y) := by gcongr
      _ = 2 * C₁ / (1 - b / 2) ^ 2 * M * |x 0| * x 1 * Y := by field_simp

end IncompressibleFlow
