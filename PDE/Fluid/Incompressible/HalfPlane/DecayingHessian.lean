/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.HolderHessian
public import PDE.Fluid.Incompressible.HalfPlane.FarHessian

/-!
# Decay and Hölder embeddings of the half-plane Hessian

Chen and Hou, Part I, (6.59a) and (6.60), state the classical embeddings of the inverse Laplacian
of the half-plane for a source `f` odd in `x₀`. With the bracket `⟨y⟩ = 1 + |y|`, equivalent to
`(1 + |y|²)^{1/2}`, we work with the sources satisfying

* `|f(y)| ≤ M ⟨y⟩^{-b}` on the closed upper half-plane, `0 < b ≤ 1`;
* `|⟨y⟩^{-p} f(y) - ⟨z⟩^{-p} f(z)| ≤ M |y - z|^α` on the closed upper half-plane, `p ≥ 0`,
  `0 < α < 1`.

Such a source is a decaying Hölder vorticity (`isHolderVorticity_of_weighted`). Write
`Ψ = GreenFunction.quadrantPotential f`.

Part I states (6.59a) for decay exponents `β ∈ [0, 1/4]`; our version takes `0 < b ≤ 1`. Its (6.60)
has the exponent `1/2` and the norm `‖f‖_{C^{1/2}} + ‖f‖_{L^p}` in the sup part; we take `0 < α < 1`
and decaying sources, with `M + L` in the sup part.

## Main results

* `abs_sub_le_of_weighted`: the weighted Hölder bound gives a local Hölder bound of `f` on bounded
  sets of the closed upper half-plane.
* `isHolderVorticity_of_weighted`: the weighted Hölder class is a decaying Hölder class.
* `exists_abs_hessian_le_of_weighted`: (6.59a), `|∂ₗ∂ₖΨ(x)| ≤ C M ⟨x⟩^{-b/2}` in the open upper
  half-plane, with `C` depending on `α`, `b` and `p` only.
* `exists_abs_hessian_le_of_holder`: (6.60), sup part, `|∂ₗ∂ₖΨ(x)| ≤ C (M + L)` for
  `|f| ≤ M ⟨y⟩^{-b}` and `[f]_α ≤ L` on the closed upper half-plane.
* `exists_abs_hessian_sub_le_of_holder`: (6.60), Hölder part,
  `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ C L |x - z|^α` for a decaying Hölder vorticity with `[f]_α ≤ L` and
  `|f| ≤ B` on the closed upper half-plane; `C` depends on `α` only.

## How it works

For (6.59a) we follow footnote 93 of Part I, with a singular region of radius `δ = ⟨x⟩^{-(p+1)/α}/4`
around `x` in place of `⟨x⟩^{-100-p}`. We apply `exists_abs_hessian_sub_far_le` at this scale and
cut the source at the radius `4⟨x⟩` around the origin. Near `x` we have `|f| ≤ 2M⟨x⟩^{-b}` and, by
`abs_sub_le_of_weighted`, the Hölder constant `(1 + p)(2⟨x⟩)^p M`; since
`δ^α ⟨x⟩^p = 4^{-α} ⟨x⟩^{-1}`, the local Hölder term is of order `M ⟨x⟩^{-1}`. The intermediate
integral of `|f|/|x - y|²` is of order `M ⟨x⟩^{-b} log ⟨x⟩` and the far part, bounded by
`GreenFunction.IsQuadrantFarDensity.abs_hessian_le`, of order `M ⟨x⟩^{-b}`, so every term is at most
a constant times `M ⟨x⟩^{-b/2}`. The sup part of (6.60) is the case `p = 0` with `M + L` in place of
`M`, since `⟨x⟩^{-b/2} ≤ 1`. For the Hölder part we combine `exists_abs_hessian_sub_far_sub_le` and
`GreenFunction.IsQuadrantFarDensity.abs_hessian_sub_le` at every scale `δ ≥ max(2|x - z|, 1)`, with
the radius `4(|x| + |z| + 2δ)`; the bound is `C L |x - z|^α` plus terms of order `δ^{-α}` and
`|x - z|/δ`, and we let `δ → ∞`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, (6.59a), (6.60) and
  footnote 93, p. 108.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

local notation "𝐑" => PDE.Common.coordinateReflection

/-! ### The weighted Hölder class -/

section Weighted

variable {α b p M : ℝ} {f : ℝ^2 → ℝ}

/-- The weight `t ↦ (1 + t)^p`, `p ≥ 0`, is Lipschitz on `[0, ρ]` with constant
`p (1 + ρ)^p`. -/
theorem abs_one_add_rpow_sub_le (hp : 0 ≤ p) {ρ s t : ℝ} (hs : s ∈ Icc 0 ρ) (ht : t ∈ Icc 0 ρ) :
    |(1 + s) ^ p - (1 + t) ^ p| ≤ p * (1 + ρ) ^ p * |s - t| := by
  have hder : ∀ u ∈ Icc 0 ρ, HasDerivWithinAt (fun u : ℝ ↦ (1 + u) ^ p)
      (1 * p * (1 + u) ^ (p - 1)) (Icc 0 ρ) u := fun u hu ↦
    (((hasDerivAt_id u).const_add 1).rpow_const (Or.inl (by
      simp only [id]; linarith [hu.1]))).hasDerivWithinAt
  have hbd : ∀ u ∈ Icc 0 ρ, ‖1 * p * (1 + u) ^ (p - 1)‖ ≤ p * (1 + ρ) ^ p := by
    intro u hu
    have h1 : 1 ≤ 1 + u := by linarith [hu.1]
    rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    calc (1 + u) ^ (p - 1) ≤ (1 + u) ^ p :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ ≤ (1 + ρ) ^ p := Real.rpow_le_rpow (by linarith) (by linarith [hu.2]) hp
  have h := (convex_Icc 0 ρ).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd ht hs
  simpa only [Real.norm_eq_abs] using h

/-- `(1 + |y|)^p (1 + |y|)^{-p} = 1`. -/
theorem one_add_norm_rpow_mul_rpow_neg (p : ℝ) (y : ℝ^2) :
    (1 + ‖y‖) ^ p * (1 + ‖y‖) ^ (-p) = 1 := by
  rw [Real.rpow_neg (by positivity), mul_inv_cancel₀ (by positivity)]

/-- `M ≥ 0` from the size bound at the origin. -/
theorem nonneg_of_abs_le_mul_rpow (hS : ∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) :
    0 ≤ M := by
  have h := (abs_nonneg _).trans (hS 0 (by simp))
  simpa using h

/-- **Local Hölder bound from the weighted Hölder bound.** If `|f| ≤ M ⟨y⟩^{-b}`, `b ≥ 0`, and
`⟨y⟩^{-p} f` is `α`-Hölder with constant `M` on the closed upper half-plane, then for `y, z` there
with `|y|, |z| ≤ ρ` and `|y - z| ≤ 1`, `|f(y) - f(z)| ≤ (1 + p) (1 + ρ)^p M |y - z|^α`. -/
theorem abs_sub_le_of_weighted (hα : 0 < α) (hα1 : α ≤ 1) (hb : 0 ≤ b) (hp : 0 ≤ p)
    (hS : ∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b))
    (hH : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |(1 + ‖y‖) ^ (-p) * f y - (1 + ‖z‖) ^ (-p) * f z| ≤ M * ‖y - z‖ ^ α)
    {ρ : ℝ} {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) (hyρ : ‖y‖ ≤ ρ) (hzρ : ‖z‖ ≤ ρ)
    (hyz : ‖y - z‖ ≤ 1) :
    |f y - f z| ≤ (1 + p) * (1 + ρ) ^ p * M * ‖y - z‖ ^ α := by
  have hM := nonneg_of_abs_le_mul_rpow hS
  set g := fun w : ℝ^2 ↦ (1 + ‖w‖) ^ (-p) * f w
  have hfg (w : ℝ^2) : f w = (1 + ‖w‖) ^ p * g w := by
    simp only [g, ← mul_assoc, one_add_norm_rpow_mul_rpow_neg, one_mul]
  have hgz : |g z| ≤ M := by
    simp only [g, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 + ‖z‖)
      (-p))]
    have h1 : (1 + ‖z‖) ^ (-p) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by linarith)
    have h2 : (1 + ‖z‖) ^ (-b) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by linarith)
    calc (1 + ‖z‖) ^ (-p) * |f z| ≤ 1 * (M * 1) := by
          gcongr
          exact (hS z hz).trans (mul_le_mul_of_nonneg_left h2 hM)
      _ = M := by ring
  have hρ0 : 0 ≤ ρ := (norm_nonneg y).trans hyρ
  have hw : |(1 + ‖y‖) ^ p - (1 + ‖z‖) ^ p| ≤ p * (1 + ρ) ^ p * ‖y - z‖ :=
    (abs_one_add_rpow_sub_le hp ⟨norm_nonneg y, hyρ⟩ ⟨norm_nonneg z, hzρ⟩).trans
      (by gcongr; exact abs_norm_sub_norm_le y z)
  have hyp : (1 + ‖y‖) ^ p ≤ (1 + ρ) ^ p :=
    Real.rpow_le_rpow (by positivity) (by linarith) hp
  have hα' : ‖y - z‖ ≤ ‖y - z‖ ^ α := by
    rcases (norm_nonneg (y - z)).eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow hα.ne']
    · simpa using Real.rpow_le_rpow_of_exponent_ge h0 hyz hα1
  have hρp : 0 ≤ (1 + ρ) ^ p := by positivity
  rw [hfg y, hfg z, show (1 + ‖y‖) ^ p * g y - (1 + ‖z‖) ^ p * g z =
    (1 + ‖y‖) ^ p * (g y - g z) + g z * ((1 + ‖y‖) ^ p - (1 + ‖z‖) ^ p) by ring]
  calc |(1 + ‖y‖) ^ p * (g y - g z) + g z * ((1 + ‖y‖) ^ p - (1 + ‖z‖) ^ p)|
      ≤ (1 + ‖y‖) ^ p * |g y - g z| + |g z| * |(1 + ‖y‖) ^ p - (1 + ‖z‖) ^ p| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 + ‖y‖) ^ p)]
    _ ≤ (1 + ρ) ^ p * (M * ‖y - z‖ ^ α) + M * (p * (1 + ρ) ^ p * ‖y - z‖ ^ α) := by
        gcongr
        · exact hH y z hy hz
        · exact hw.trans (by gcongr)
    _ = (1 + p) * (1 + ρ) ^ p * M * ‖y - z‖ ^ α := by ring

/-- **The weighted Hölder class is a decaying Hölder class.** -/
theorem isHolderVorticity_of_weighted (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b) (hp : 0 ≤ p)
    (hodd : ∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y)
    (hS : ∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b))
    (hH : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |(1 + ‖y‖) ^ (-p) * f y - (1 + ‖z‖) ^ (-p) * f z| ≤ M * ‖y - z‖ ^ α) :
    IsHolderVorticity α f := by
  have hM := nonneg_of_abs_le_mul_rpow hS
  set g := fun w : ℝ^2 ↦ (1 + ‖w‖) ^ (-p) * f w
  have hg : ContinuousOn g {y : ℝ^2 | 0 ≤ y 1} := by
    intro y hy
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun w : ℝ^2 ↦ M * ‖w - y‖ ^ α) (𝓝[{y : ℝ^2 | 0 ≤ y 1}] y)
        (𝓝 (M * ‖y - y‖ ^ α)) :=
      ((continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ ↦ Or.inr hα.le)).tendsto y).mono_left nhdsWithin_le_nhds
    rw [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero] at hlim
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [Real.norm_eq_abs]
    exact hH w y hw hy
  have hfg : EqOn f (fun w ↦ (1 + ‖w‖) ^ p * g w) {y : ℝ^2 | 0 ≤ y 1} := fun w _ ↦ by
    simp only [g, ← mul_assoc, one_add_norm_rpow_mul_rpow_neg, one_mul]
  refine ⟨hα, hα1, ?_, hodd, ⟨M, b, hb, hS⟩, fun ρ ↦ ?_⟩
  · refine ContinuousOn.congr ?_ hfg
    exact ((continuous_const.add continuous_norm).rpow_const fun _ ↦
      Or.inr hp).continuousOn.mul hg
  · refine ⟨(1 + p) * (1 + |ρ|) ^ p * M + 2 * M, fun y z hy hz hyρ hzρ ↦ ?_⟩
    have hyρ' : ‖y‖ ≤ |ρ| := hyρ.trans (le_abs_self ρ)
    have hzρ' : ‖z‖ ≤ |ρ| := hzρ.trans (le_abs_self ρ)
    have hc : 0 ≤ (1 + p) * (1 + |ρ|) ^ p * M := by positivity
    rcases le_or_gt ‖y - z‖ 1 with h1 | h1
    · refine (abs_sub_le_of_weighted hα hα1.le hb.le hp hS hH hy hz hyρ' hzρ' h1).trans ?_
      nlinarith [Real.rpow_nonneg (norm_nonneg (y - z)) α]
    · have h1' : 1 ≤ ‖y - z‖ ^ α := Real.one_le_rpow h1.le hα.le
      have hfy : |f y| ≤ M := (hS y hy).trans (mul_le_of_le_one_right hM
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)))
      have hfz : |f z| ≤ M := (hS z hz).trans (mul_le_of_le_one_right hM
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by linarith)))
      calc |f y - f z| ≤ |f y| + |f z| := abs_sub _ _
        _ ≤ 2 * M * 1 := by linarith
        _ ≤ ((1 + p) * (1 + |ρ|) ^ p * M + 2 * M) * ‖y - z‖ ^ α := by
            nlinarith [mul_le_mul_of_nonneg_left h1' (by positivity : (0 : ℝ) ≤ 2 * M)]

end Weighted

/-! ### The decay bound (6.59a) -/

section Decay

variable {α b p M : ℝ} {f : ℝ^2 → ℝ}

/-- `(1 + t)^{-b} ≤ 2 r^{-b}` when `1 + t ≥ r/2`, `0 ≤ b ≤ 1`. -/
theorem one_add_rpow_neg_le_two_mul (hb : 0 ≤ b) (hb1 : b ≤ 1) {r t : ℝ} (hr : 0 < r)
    (ht : r / 2 ≤ 1 + t) : (1 + t) ^ (-b) ≤ 2 * r ^ (-b) := by
  have h1 : (1 + t) ^ (-b) ≤ (r / 2) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) ht (by linarith)
  have h2 : (r / 2) ^ (-b) = 2 ^ b * r ^ (-b) := by
    rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  have h3 : (2 : ℝ) ^ b ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
  rw [h2] at h1
  exact h1.trans (by gcongr)

/-- The measurable intermediate region of the engine. -/
private theorem measurableSet_middle (x : ℝ^2) (δ R : ℝ) :
    MeasurableSet {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ R} := by
  have h1 : Measurable fun y : ℝ^2 ↦ y 1 := by fun_prop
  exact (measurableSet_lt measurable_const h1).inter ((measurableSet_le measurable_const
    (measurable_const.sub measurable_id).norm).inter (measurableSet_le measurable_norm
      measurable_const))

/-- **The intermediate integral at the scale `δ`.** With `r = 1 + |x|`, `0 < δ ≤ 1/4` and
`|f| ≤ M ⟨y⟩^{-b}`,
`∫⁻_{0 < y₁, δ ≤ |x - y|, |y| ≤ 8r} |f|/|x - y|² ≤ (4M/r²) 2π (9r)^{2-b}/(2-b)
  + 2 M r^{-b} 2π log((r/2)/δ)`. -/
private theorem lintegral_middle_le (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 ≤ M)
    (hS : ∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) {x : ℝ^2} {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * (4 * (1 + ‖x‖))},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2) ≤
      ENNReal.ofReal (4 * M / (1 + ‖x‖) ^ 2 *
          (2 * Real.pi * (9 * (1 + ‖x‖)) ^ (2 - b) / (2 - b)) +
        2 * M * (1 + ‖x‖) ^ (-b) * (2 * Real.pi * Real.log ((1 + ‖x‖) / 2 / δ))) := by
  set r := 1 + ‖x‖ with hr
  have hr1 : 1 ≤ r := by simp [r]
  have hr0 : 0 < r := by linarith
  set S := {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * (4 * r)}
  set T := {y : ℝ^2 | r / 2 ≤ ‖x - y‖}
  have hT : MeasurableSet T := measurableSet_le measurable_const (measurable_const.sub
    measurable_id).norm
  have hSm := measurableSet_middle x δ (2 * (4 * r))
  rw [← lintegral_inter_add_sdiff _ S hT]
  have hP1 : ∫⁻ y in S ∩ T, ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2) ≤
      ENNReal.ofReal (4 * M / r ^ 2 * (2 * Real.pi * (9 * r) ^ (2 - b) / (2 - b))) := by
    rw [← lintegral_ball_zero_rpow (by positivity) (by positivity) (by linarith : 0 < 2 - b)]
    refine (setLIntegral_mono' (hSm.inter hT) fun y hy ↦ ?_).trans
      (lintegral_mono_set fun y hy ↦ ?_)
    · obtain ⟨⟨hy1, -, -⟩, hyT⟩ := hy
      have hy0 : 0 < ‖y‖ := by
        refine norm_pos_iff.mpr fun h ↦ ?_
        rw [h] at hy1; simp at hy1
      have hd : 0 < ‖x - y‖ := lt_of_lt_of_le (by positivity) hyT
      refine ENNReal.ofReal_le_ofReal ?_
      have hfy : |f y| ≤ M * ‖y‖ ^ (-b) := (hS y hy1.le).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)) hM)
      have hinv : 1 / ‖x - y‖ ^ 2 ≤ 4 / r ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul hyT hyT (by positivity) (norm_nonneg _)
        nlinarith
      rw [show (2 - b) - 2 = -b by ring]
      calc |f y| / ‖x - y‖ ^ 2 = |f y| * (1 / ‖x - y‖ ^ 2) := by ring
        _ ≤ M * ‖y‖ ^ (-b) * (4 / r ^ 2) := by gcongr
        _ = 4 * M / r ^ 2 * ‖y‖ ^ (-b) := by ring
    · obtain ⟨⟨-, -, hyR⟩, -⟩ := hy
      rw [mem_ball_zero_iff]
      linarith
  have hP2 : ∫⁻ y in S \ T, ENNReal.ofReal (|f y| / ‖x - y‖ ^ 2) ≤
      ENNReal.ofReal (2 * M * r ^ (-b) * (2 * Real.pi * Real.log (r / 2 / δ))) := by
    rw [← lintegral_annulus_mul_inv_sq x (by positivity) hδ (by linarith : δ ≤ r / 2)]
    refine (setLIntegral_mono' (hSm.diff hT) fun y hy ↦ ?_).trans
      (lintegral_mono_set fun y hy ↦ ?_)
    · obtain ⟨⟨hy1, -, -⟩, hyT⟩ := hy
      simp only [T, mem_ofPred_eq, not_le] at hyT
      refine ENNReal.ofReal_le_ofReal ?_
      have hyr : r / 2 ≤ 1 + ‖y‖ := by
        have := norm_sub_norm_le x y
        simp only [r] at hyT ⊢
        linarith
      have hfy : |f y| ≤ M * (2 * r ^ (-b)) :=
        (hS y hy1.le).trans (mul_le_mul_of_nonneg_left
          (one_add_rpow_neg_le_two_mul hb.le hb1 hr0 hyr) hM)
      rw [div_eq_mul_inv]
      calc |f y| * (‖x - y‖ ^ 2)⁻¹ ≤ M * (2 * r ^ (-b)) * (‖x - y‖ ^ 2)⁻¹ := by gcongr
        _ = 2 * M * r ^ (-b) * (‖x - y‖ ^ 2)⁻¹ := by ring
    · obtain ⟨⟨-, hyδ, -⟩, hyT⟩ := hy
      simp only [T, mem_ofPred_eq, not_le] at hyT
      refine ⟨by rw [mem_ball, dist_comm, dist_eq_norm]; exact hyT, ?_⟩
      rw [mem_ball, dist_comm, dist_eq_norm, not_lt]
      exact hyδ
  have hlog : 0 ≤ Real.log (r / 2 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  rw [ENNReal.ofReal_add (mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith)))
    (mul_nonneg (by positivity) (mul_nonneg (by positivity) hlog))]
  exact add_le_add hP1 hP2

/-- **The far integral.** For `|f| ≤ M ⟨y⟩^{-b}`, `0 < b ≤ 1`, and `R > 0`,
`∫_{ℝ²₊₊} |(1 - χ_R) f|/|y|² ≤ M 2π R^{-b}/b`. -/
private theorem integral_farSource_le (hf : IsHolderVorticity α f) (hb : 0 < b)
    (hM : 0 ≤ M) (hS : ∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) {R : ℝ} (hR : 0 < R) :
    ∫ y in quadrant, |farSource R f y| / ‖y‖ ^ 2 ≤ M * (2 * Real.pi * R ^ (-b) / b) := by
  have hfar := hf.isQuadrantFarDensity_farSource hR
  have hlin : ∫⁻ y in quadrant, ENNReal.ofReal (|farSource R f y| / ‖y‖ ^ 2) ≤
      ENNReal.ofReal (M * (2 * Real.pi * R ^ (-b) / b)) := by
    have h := lintegral_compl_ball_zero_rpow (c := M) (ρ := R) (γ := 1 - b) hM hR (by linarith)
    rw [show (1 - b) - 1 = -b by ring, show 1 - (1 - b) = b by ring] at h
    rw [← h, ← lintegral_indicator measurableSet_ball.compl]
    refine (setLIntegral_mono' measurableSet_quadrant fun y hy ↦ ?_).trans
      (setLIntegral_le_lintegral _ _)
    by_cases hyR : ‖y‖ < R
    · simp [farSource, radialCutoff_eq_one hR hyR.le]
    have hyR' : R ≤ ‖y‖ := not_lt.mp hyR
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hyR'
    rw [indicator_of_mem (by simpa [mem_ball_zero_iff] using hyR')]
    refine ENNReal.ofReal_le_ofReal ?_
    have hχ0 := radialCutoff_nonneg R y
    have hχ1 := radialCutoff_le_one R y
    have hfar1 : |farSource R f y| ≤ |f y| := by
      rw [farSource, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - radialCutoff R y)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    have hfy : |f y| ≤ M * ‖y‖ ^ (-b) := (hS y (le_of_lt hy.2)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hy0 (by linarith) (by linarith)) hM)
    have hpow : ‖y‖ ^ ((1 - b) - 3) = ‖y‖ ^ (-b) / ‖y‖ ^ 2 := by
      rw [show (1 - b) - 3 = -b + -(2 : ℝ) by ring, Real.rpow_add hy0, Real.rpow_neg hy0.le 2,
        Real.rpow_two, div_eq_mul_inv]
    rw [hpow, ← mul_div_assoc]
    gcongr
    exact hfar1.trans hfy
  have hm := (hfar.integrableOn_abs_div_pow le_rfl).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ by positivity) hm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

/-- `|a| ≤ |a - b| + |b|`. -/
private theorem abs_le_abs_sub_add (a b : ℝ) : |a| ≤ |a - b| + |b| := by
  simpa using abs_add_le (a - b) b

/-- `r^{-c} ≤ r^{-d}` for `r ≥ 1` and `d ≤ c`. -/
private theorem rpow_neg_le_rpow_neg {r c d : ℝ} (hr : 1 ≤ r) (hdc : d ≤ c) :
    r ^ (-c) ≤ r ^ (-d) :=
  Real.rpow_le_rpow_of_exponent_le hr (by linarith)

/-- The local Hölder term at the scale `δ = r^{-(p+1)/α}/4`. -/
private theorem scale_mul_holder_le (hα : 0 < α) (hp : 0 ≤ p) (hb1 : b ≤ 1) (hM : 0 ≤ M)
    {r : ℝ} (hr1 : 1 ≤ r) :
    (r ^ (-((p + 1) / α)) / 4) ^ α * ((1 + p) * (2 * r) ^ p * M) ≤
      (1 + p) * 2 ^ p * (M * r ^ (-(b / 2))) := by
  have hr0 : 0 < r := by linarith
  have hδα : (r ^ (-((p + 1) / α)) / 4) ^ α = r ^ (-(p + 1)) / 4 ^ α := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hr0.le]
    congr 2
    field_simp
  have h4 : (1 : ℝ) ≤ 4 ^ α := Real.one_le_rpow (by norm_num) hα.le
  have hrp : r ^ (-(p + 1)) * r ^ p = r ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hr1b : r ^ (-1 : ℝ) ≤ r ^ (-(b / 2)) := rpow_neg_le_rpow_neg hr1 (by linarith)
  have hLr : (2 * r) ^ p = 2 ^ p * r ^ p := Real.mul_rpow (by norm_num) hr0.le
  have hc : 0 ≤ (1 + p) * 2 ^ p * M := by positivity
  calc (r ^ (-((p + 1) / α)) / 4) ^ α * ((1 + p) * (2 * r) ^ p * M)
      = (1 + p) * 2 ^ p * M * (r ^ (-(p + 1)) * r ^ p) / 4 ^ α := by
        rw [hδα, hLr]; ring
    _ ≤ (1 + p) * 2 ^ p * M * (r ^ (-(p + 1)) * r ^ p) := div_le_self (by positivity) h4
    _ = (1 + p) * 2 ^ p * M * r ^ (-1 : ℝ) := by rw [hrp]
    _ ≤ (1 + p) * 2 ^ p * M * r ^ (-(b / 2)) := mul_le_mul_of_nonneg_left hr1b hc
    _ = (1 + p) * 2 ^ p * (M * r ^ (-(b / 2))) := by ring

/-- The outer part of the intermediate integral. -/
private theorem outer_le (hb : 0 < b) (hb1 : b ≤ 1) (hM : 0 ≤ M) {r : ℝ} (hr1 : 1 ≤ r) :
    4 * M / r ^ 2 * (2 * Real.pi * (9 * r) ^ (2 - b) / (2 - b)) ≤
      648 * Real.pi * (M * r ^ (-(b / 2))) := by
  have hr0 : 0 < r := by linarith
  have h9 : (9 * r) ^ (2 - b) = 9 ^ (2 - b) * r ^ (2 - b) := Real.mul_rpow (by norm_num) hr0.le
  have h81 : (9 : ℝ) ^ (2 - b) ≤ 81 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 9) (by linarith : 2 - b ≤ 2)
    rw [show (9 : ℝ) ^ (2 : ℝ) = 81 by norm_num] at this
    exact this
  have hr2 : r ^ (2 - b) = r ^ 2 * r ^ (-b) := by
    rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_two]
  have hdiv0 : 0 ≤ 1 / (2 - b) := div_nonneg zero_le_one (by linarith)
  have hdiv : 1 / (2 - b) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hrb : r ^ (-b) ≤ r ^ (-(b / 2)) := rpow_neg_le_rpow_neg hr1 (by linarith)
  have hc : 0 ≤ 8 * Real.pi * M := by positivity
  calc 4 * M / r ^ 2 * (2 * Real.pi * (9 * r) ^ (2 - b) / (2 - b))
      = 8 * Real.pi * M * 9 ^ (2 - b) * r ^ (-b) * (1 / (2 - b)) := by
        rw [h9, hr2]; field_simp; ring
    _ ≤ 8 * Real.pi * M * 81 * r ^ (-b) * 1 := by
        gcongr
    _ ≤ 8 * Real.pi * M * 81 * r ^ (-(b / 2)) * 1 := by gcongr
    _ = 648 * Real.pi * (M * r ^ (-(b / 2))) := by ring

/-- The annulus part of the intermediate integral at the scale `δ = r^{-(p+1)/α}/4`. -/
private theorem annulus_le (hα : 0 < α) (hp : 0 ≤ p) (hb : 0 < b) (hM : 0 ≤ M) {r : ℝ}
    (hr1 : 1 ≤ r) :
    2 * M * r ^ (-b) * (2 * Real.pi * Real.log (r / 2 / (r ^ (-((p + 1) / α)) / 4))) ≤
      4 * Real.pi * (1 + 2 * (1 + (p + 1) / α) / b) * (M * r ^ (-(b / 2))) := by
  have hr0 : 0 < r := by linarith
  set N := (p + 1) / α
  have hN0 : 0 ≤ N := by positivity
  have hq : r / 2 / (r ^ (-N) / 4) = 2 * r * r ^ N := by
    rw [Real.rpow_neg hr0.le]
    have : r ^ N ≠ 0 := (Real.rpow_pos_of_pos hr0 N).ne'
    field_simp
    ring
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlr := Real.log_le_rpow_div hr0.le (by positivity : 0 < b / 2)
  have hNl : N * Real.log r ≤ N * (r ^ (b / 2) / (b / 2)) := mul_le_mul_of_nonneg_left hlr hN0
  have hlogq : Real.log (r / 2 / (r ^ (-N) / 4)) ≤ 1 + (1 + N) * (r ^ (b / 2) / (b / 2)) := by
    rw [hq, Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hr0.ne',
      Real.log_rpow hr0]
    linarith
  have hcomb : r ^ (-b) * r ^ (b / 2) = r ^ (-(b / 2)) := by
    rw [← Real.rpow_add hr0]; congr 1; ring
  have hrb : r ^ (-b) ≤ r ^ (-(b / 2)) := rpow_neg_le_rpow_neg hr1 (by linarith)
  have hc : 0 ≤ 4 * Real.pi * M := by positivity
  calc 2 * M * r ^ (-b) * (2 * Real.pi * Real.log (r / 2 / (r ^ (-N) / 4)))
      ≤ 2 * M * r ^ (-b) * (2 * Real.pi * (1 + (1 + N) * (r ^ (b / 2) / (b / 2)))) := by
        gcongr
    _ = 4 * Real.pi * M * r ^ (-b) + 4 * Real.pi * M * (2 * (1 + N) / b) *
          (r ^ (-b) * r ^ (b / 2)) := by
        field_simp
        ring
    _ ≤ 4 * Real.pi * M * r ^ (-(b / 2)) + 4 * Real.pi * M * (2 * (1 + N) / b) *
          r ^ (-(b / 2)) := by
        rw [hcomb]
        gcongr
    _ = 4 * Real.pi * (1 + 2 * (1 + N) / b) * (M * r ^ (-(b / 2))) := by ring

/-- The far part at the radius `R = 4r`. -/
private theorem far_le (hb : 0 < b) (hM : 0 ≤ M) {r : ℝ} (hr1 : 1 ≤ r) :
    2 * (M * (2 * Real.pi * (4 * r) ^ (-b) / b)) ≤ 4 * Real.pi / b * (M * r ^ (-(b / 2))) := by
  have hr0 : 0 < r := by linarith
  have hRb : (4 * r) ^ (-b) ≤ r ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos hr0 (by linarith) (by linarith)
  have hrb : r ^ (-b) ≤ r ^ (-(b / 2)) := rpow_neg_le_rpow_neg hr1 (by linarith)
  calc 2 * (M * (2 * Real.pi * (4 * r) ^ (-b) / b)) = 4 * Real.pi / b * (M * (4 * r) ^ (-b)) := by
        ring
    _ ≤ 4 * Real.pi / b * (M * r ^ (-(b / 2))) := by
        gcongr
        exact hRb.trans hrb

/-- **Part I (6.59a), decay of the Hessian.** For `0 < α < 1`, `0 < b ≤ 1` and `p ≥ 0` there is
`C` such that for every source `f` odd in `x₀` on the closed upper half-plane with
`|f(y)| ≤ M ⟨y⟩^{-b}` and `|⟨y⟩^{-p} f(y) - ⟨z⟩^{-p} f(z)| ≤ M |y - z|^α` there, `⟨y⟩ = 1 + |y|`,
the Hessian of `Ψ = quadrantPotential f` satisfies `|∂ₗ∂ₖΨ(x)| ≤ C M ⟨x⟩^{-b/2}` in the open
upper half-plane. -/
theorem exists_abs_hessian_le_of_weighted (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, (∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y) →
      (∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
        |(1 + ‖y‖) ^ (-p) * f y - (1 + ‖z‖) ^ (-p) * f z| ≤ M * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x| ≤ C * M * (1 + ‖x‖) ^ (-(b / 2)) := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_abs_hessian_sub_far_le hα hα1
  refine ⟨C₁ * (2 + (1 + p) * 2 ^ p) +
    C₁ * (648 * Real.pi + 4 * Real.pi * (1 + 2 * (1 + (p + 1) / α) / b)) + 4 * Real.pi / b,
    by positivity, ?_⟩
  intro f M hodd hS hH x hx k l
  have hM := nonneg_of_abs_le_mul_rpow hS
  have hf := isHolderVorticity_of_weighted hα hα1 hb hp hodd hS hH
  have hr1 : 1 ≤ 1 + ‖x‖ := by simp
  have hr0 : 0 < 1 + ‖x‖ := by linarith
  have hN0 : 0 ≤ (p + 1) / α := by positivity
  have hrN : (1 + ‖x‖) ^ (-((p + 1) / α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
  have hδ : 0 < (1 + ‖x‖) ^ (-((p + 1) / α)) / 4 := by positivity
  have hδ4 : (1 + ‖x‖) ^ (-((p + 1) / α)) / 4 ≤ 1 / 4 := by linarith
  have hR : 2 * (‖x‖ + 2 * ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4)) ≤ 4 * (1 + ‖x‖) := by linarith
  have hR0 : 0 < 4 * (1 + ‖x‖) := by positivity
  have hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4) →
      |f y| ≤ 2 * M * (1 + ‖x‖) ^ (-b) := by
    intro y hy hxy
    have hyr : (1 + ‖x‖) / 2 ≤ 1 + ‖y‖ := by
      have := norm_sub_norm_le x y; linarith
    calc |f y| ≤ M * (1 + ‖y‖) ^ (-b) := hS y hy
      _ ≤ M * (2 * (1 + ‖x‖) ^ (-b)) := by
          gcongr; exact one_add_rpow_neg_le_two_mul hb.le hb1 hr0 hyr
      _ = 2 * M * (1 + ‖x‖) ^ (-b) := by ring
  have hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4) →
      ‖x - z‖ ≤ 2 * ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4) →
      |f y - f z| ≤ (1 + p) * (2 * (1 + ‖x‖)) ^ p * M * ‖y - z‖ ^ α := by
    intro y z hy hz hxy hxz
    have hyρ : ‖y‖ ≤ ‖x‖ + 1 / 2 := by
      have := norm_le_norm_add_norm_sub' y x
      rw [norm_sub_rev] at this; linarith
    have hzρ : ‖z‖ ≤ ‖x‖ + 1 / 2 := by
      have := norm_le_norm_add_norm_sub' z x
      rw [norm_sub_rev] at this; linarith
    have hyz : ‖y - z‖ ≤ 1 := by
      have := norm_sub_le_norm_sub_add_norm_sub y x z
      rw [norm_sub_rev y x] at this; linarith
    refine (abs_sub_le_of_weighted hα hα1.le hb.le hp hS hH hy hz hyρ hzρ hyz).trans ?_
    have h2 : (1 + (‖x‖ + 1 / 2)) ^ p ≤ (2 * (1 + ‖x‖)) ^ p :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_nonneg x]) hp
    have := Real.rpow_nonneg (norm_nonneg (y - z)) α
    gcongr
  have hlog : 0 ≤ Real.log ((1 + ‖x‖) / 2 / ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hP₁0 : 0 ≤ 4 * M / (1 + ‖x‖) ^ 2 *
      (2 * Real.pi * (9 * (1 + ‖x‖)) ^ (2 - b) / (2 - b)) :=
    mul_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))
  have hP₂0 : 0 ≤ 2 * M * (1 + ‖x‖) ^ (-b) * (2 * Real.pi *
      Real.log ((1 + ‖x‖) / 2 / ((1 + ‖x‖) ^ (-((p + 1) / α)) / 4))) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlog)
  have hmain := hE hf hx hδ hR hB hL (add_nonneg hP₁0 hP₂0)
    (lintegral_middle_le hb hb1 hM hS hδ hδ4) k l
  have hfar := (hf.isQuadrantFarDensity_farSource hR0).abs_hessian_le k l
    (by linarith [norm_nonneg x] : ‖x‖ < 4 * (1 + ‖x‖) / 2)
  have hfarI := integral_farSource_le hf hb hM hS hR0
  have e1 : 2 * M * (1 + ‖x‖) ^ (-b) ≤ 2 * (M * (1 + ‖x‖) ^ (-(b / 2))) := by
    have := mul_le_mul_of_nonneg_left (rpow_neg_le_rpow_neg hr1 (by linarith : b / 2 ≤ b)) hM
    linarith
  have e2 := scale_mul_holder_le hα hp hb1 hM hr1
  have e3 := outer_le hb hb1 hM hr1
  have e4 := annulus_le hα hp hb hM hr1
  have e5 := far_le hb hM hr1
  have hfar' := hfar.trans ((mul_le_mul_of_nonneg_left hfarI (by norm_num)).trans e5)
  set X := M * (1 + ‖x‖) ^ (-(b / 2))
  calc |(∂[l] (∂[k] (quadrantPotential f))) x|
      ≤ |(∂[l] (∂[k] (quadrantPotential f))) x -
          (∂[l] (∂[k] (quadrantPotential (farSource (4 * (1 + ‖x‖)) f)))) x| +
        |(∂[l] (∂[k] (quadrantPotential (farSource (4 * (1 + ‖x‖)) f)))) x| :=
        abs_le_abs_sub_add _ _
    _ ≤ C₁ * (2 * X + (1 + p) * 2 ^ p * X) +
          C₁ * (648 * Real.pi * X + 4 * Real.pi * (1 + 2 * (1 + (p + 1) / α) / b) * X) +
          4 * Real.pi / b * X := by
        refine add_le_add (hmain.trans (add_le_add ?_ ?_)) hfar'
        · exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) hC₁
        · exact mul_le_mul_of_nonneg_left (add_le_add e3 e4) hC₁
    _ = (C₁ * (2 + (1 + p) * 2 ^ p) +
          C₁ * (648 * Real.pi + 4 * Real.pi * (1 + 2 * (1 + (p + 1) / α) / b)) +
          4 * Real.pi / b) * M * (1 + ‖x‖) ^ (-(b / 2)) := by simp only [X]; ring

end Decay

/-! ### The embeddings (6.60) -/

section Embedding

variable {α b : ℝ} {f : ℝ^2 → ℝ}

/-- A Hölder constant on the closed upper half-plane is nonnegative. -/
theorem nonneg_of_holder_upper {L : ℝ}
    (hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ L * ‖y - z‖ ^ α) : 0 ≤ L := by
  have h := (abs_nonneg _).trans (hL 0 (EuclideanSpace.single 1 1) (by simp) (by simp))
  simpa [PiLp.norm_single] using h

/-- **Part I (6.60), sup part, for decaying sources.** For `0 < α < 1` and `0 < b ≤ 1` there is
`C` such that for every source `f` odd in `x₀` on the closed upper half-plane with
`|f(y)| ≤ M ⟨y⟩^{-b}` and `[f]_{C^α} ≤ L` there, `|∂ₗ∂ₖΨ(x)| ≤ C (M + L)` in the open upper
half-plane, `Ψ = quadrantPotential f`. -/
theorem exists_abs_hessian_le_of_holder (hα : 0 < α) (hα1 : α < 1) (hb : 0 < b) (hb1 : b ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M L : ℝ⦄, (∀ y, 0 ≤ y 1 → f (𝐑 0 y) = -f y) →
      (∀ y, 0 ≤ y 1 → |f y| ≤ M * (1 + ‖y‖) ^ (-b)) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ L * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x| ≤ C * (M + L) := by
  obtain ⟨C, hC, h⟩ := exists_abs_hessian_le_of_weighted hα hα1 hb hb1 le_rfl
  refine ⟨C, hC, fun f M L hodd hS hL x hx k l ↦ ?_⟩
  have hM := nonneg_of_abs_le_mul_rpow hS
  have hL0 := nonneg_of_holder_upper hL
  have hS' : ∀ y, 0 ≤ y 1 → |f y| ≤ (M + L) * (1 + ‖y‖) ^ (-b) := fun y hy ↦
    (hS y hy).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hH' : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |(1 + ‖y‖) ^ (-(0 : ℝ)) * f y - (1 + ‖z‖) ^ (-(0 : ℝ)) * f z| ≤ (M + L) * ‖y - z‖ ^ α := by
    intro y z hy hz
    simp only [neg_zero, Real.rpow_zero, one_mul]
    exact (hL y z hy hz).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hle : (1 + ‖x‖) ^ (-(b / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  calc |(∂[l] (∂[k] (quadrantPotential f))) x| ≤ C * (M + L) * (1 + ‖x‖) ^ (-(b / 2)) :=
        h hodd hS' hH' x hx k l
    _ ≤ C * (M + L) * 1 := by gcongr
    _ = C * (M + L) := mul_one _

/-- The far integral against `|y|^{-3}` for a bounded source. -/
private theorem integral_farSource_cube_le (hf : IsHolderVorticity α f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ y, 0 ≤ y 1 → |f y| ≤ B) {R : ℝ} (hR : 0 < R) :
    ∫ y in quadrant, |farSource R f y| / ‖y‖ ^ 3 ≤ B * (2 * Real.pi * R⁻¹) := by
  have hfar := hf.isQuadrantFarDensity_farSource hR
  have hlin : ∫⁻ y in quadrant, ENNReal.ofReal (|farSource R f y| / ‖y‖ ^ 3) ≤
      ENNReal.ofReal (B * (2 * Real.pi * R⁻¹)) := by
    have h := lintegral_compl_ball_zero_rpow (c := B) (ρ := R) (γ := 0) hB0 hR (by norm_num)
    rw [show (0 : ℝ) - 1 = -1 by ring, Real.rpow_neg_one, sub_zero, div_one] at h
    rw [← h, ← lintegral_indicator measurableSet_ball.compl]
    refine (setLIntegral_mono' measurableSet_quadrant fun y hy ↦ ?_).trans
      (setLIntegral_le_lintegral _ _)
    by_cases hyR : ‖y‖ < R
    · simp [farSource, radialCutoff_eq_one hR hyR.le]
    have hyR' : R ≤ ‖y‖ := not_lt.mp hyR
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le hR hyR'
    rw [indicator_of_mem (by simpa [mem_ball_zero_iff] using hyR')]
    refine ENNReal.ofReal_le_ofReal ?_
    have hχ0 := radialCutoff_nonneg R y
    have hχ1 := radialCutoff_le_one R y
    have hfar1 : |farSource R f y| ≤ |f y| := by
      rw [farSource, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - radialCutoff R y)]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    rw [show (0 : ℝ) - 3 = -(3 : ℕ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast,
      div_eq_mul_inv]
    gcongr
    exact hfar1.trans (hB y (le_of_lt hy.2))
  have hm := (hfar.integrableOn_abs_div_pow (by norm_num : 2 ≤ 3)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y ↦ by positivity) hm]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

/-- **Part I (6.60), Hölder part.** For `0 < α < 1` there is `C` such that for every decaying
Hölder vorticity `f` with `|f| ≤ B` and `|f(y) - f(z)| ≤ L |y - z|^α` on the closed upper
half-plane, `|∂ₗ∂ₖΨ(x) - ∂ₗ∂ₖΨ(z)| ≤ C L |x - z|^α` in the open upper half-plane,
`Ψ = quadrantPotential f`: `[∇²(-Δ)⁻¹ f]_{C^α} ≲ [f]_{C^α}`. -/
theorem exists_abs_hessian_sub_le_of_holder (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃B L : ℝ⦄, IsHolderVorticity α f →
      (∀ y, 0 ≤ y 1 → |f y| ≤ B) →
      (∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ L * ‖y - z‖ ^ α) →
      ∀ x z : ℝ^2, 0 < x 1 → 0 < z 1 → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential f))) z| ≤
          C * L * ‖x - z‖ ^ α := by
  obtain ⟨C₂, hC₂, hE⟩ := exists_abs_hessian_sub_far_sub_le hα hα1
  refine ⟨C₂, hC₂, fun f B L hf hB hL x z hx hz k l ↦ ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (by simp))
  have hL0 := nonneg_of_holder_upper hL
  set d := ‖x - z‖
  set D := fun w : ℝ^2 ↦ (∂[l] (∂[k] (quadrantPotential f))) w
  set Φ := fun δ : ℝ ↦ C₂ * (L + B * δ ^ (-α)) * d ^ α + C₂ * d * (B * (2 * Real.pi * δ⁻¹)) +
    8 * d * (B * (2 * Real.pi * δ⁻¹))
  have hbound : ∀ δ, max (2 * d) 1 ≤ δ → |D x - D z| ≤ Φ δ := by
    intro δ hδm
    have hδ : 0 < δ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hδm)
    have hxz : 2 * ‖x - z‖ ≤ δ := (le_max_left _ _).trans hδm
    set R := 4 * (‖x‖ + ‖z‖ + 2 * δ)
    have hR : 2 * (‖x‖ + 2 * δ) ≤ R := by simp only [R]; linarith [norm_nonneg x, norm_nonneg z]
    have hR0 : 0 < R := by simp only [R]; positivity
    have hI : ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ 3) ≤ ENNReal.ofReal (B * (2 * Real.pi * δ⁻¹)) := by
      have h := MeasureTheory.lintegral_compl_ball_mul_rpow_sub_three x (c := B) (β := 0) hB0 hδ
        (by norm_num)
      rw [show (0 : ℝ) - 1 = -1 by ring, Real.rpow_neg_one, sub_zero, div_one] at h
      rw [← h]
      refine (setLIntegral_mono' (measurableSet_middle x δ (2 * R)) fun y hy ↦ ?_).trans
        (lintegral_mono_set fun y hy ↦ ?_)
      · obtain ⟨hy1, hyδ, -⟩ := hy
        have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hδ hyδ
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show (0 : ℝ) - 3 = -(3 : ℕ) by norm_num, Real.rpow_neg hpos.le, Real.rpow_natCast,
          div_eq_mul_inv]
        gcongr
        exact hB y hy1.le
      · obtain ⟨-, hyδ, -⟩ := hy
        rw [mem_compl_iff, mem_ball, dist_comm, dist_eq_norm, not_lt]
        exact hyδ
    have hmain := hE hf hx hδ hR (fun y hy _ ↦ hB y hy) (fun y z hy hz _ _ ↦ hL y z hy hz)
      (by positivity) hI hz hxz k l
    have hfar := (hf.isQuadrantFarDensity_farSource hR0).abs_hessian_sub_le k l
      (by simp only [R]; linarith [norm_nonneg z] : 4 * ‖x‖ ≤ R)
      (by simp only [R]; linarith [norm_nonneg x] : 4 * ‖z‖ ≤ R)
    have hfarI := integral_farSource_cube_le hf hB0 hB hR0
    have hRδ : R⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (by simp only [R]; linarith [norm_nonneg x, norm_nonneg z])
    have hfar' : |(∂[l] (∂[k] (quadrantPotential (farSource R f)))) x -
        (∂[l] (∂[k] (quadrantPotential (farSource R f)))) z| ≤
        8 * d * (B * (2 * Real.pi * δ⁻¹)) := by
      refine hfar.trans ?_
      have h8 : 0 ≤ 8 * d := by positivity
      exact mul_le_mul_of_nonneg_left (hfarI.trans (by gcongr)) h8
    calc |D x - D z| ≤ |((D x - (∂[l] (∂[k] (quadrantPotential (farSource R f)))) x) -
            (D z - (∂[l] (∂[k] (quadrantPotential (farSource R f)))) z))| +
          |(∂[l] (∂[k] (quadrantPotential (farSource R f)))) x -
            (∂[l] (∂[k] (quadrantPotential (farSource R f)))) z| := by
          refine le_of_eq_of_le ?_ (abs_add_le _ _); ring_nf
      _ ≤ Φ δ := by simp only [Φ]; exact add_le_add hmain hfar'
  have hlim : Tendsto Φ atTop (𝓝 (C₂ * L * d ^ α)) := by
    have h1 : Tendsto (fun δ : ℝ ↦ δ ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
    have h2 : Tendsto (fun δ : ℝ ↦ δ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have := (((tendsto_const_nhds (x := L)).add (h1.const_mul B)).const_mul C₂ |>.mul_const
      (d ^ α)).add ((h2.const_mul (2 * Real.pi)).const_mul B |>.const_mul (C₂ * d)) |>.add
      ((h2.const_mul (2 * Real.pi)).const_mul B |>.const_mul (8 * d))
    simpa [Φ, mul_assoc] using this
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max (2 * d) 1, hbound⟩)

end Embedding

end IncompressibleFlow
