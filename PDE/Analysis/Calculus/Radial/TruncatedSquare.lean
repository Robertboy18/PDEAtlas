/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Integration.WeightedEnergyLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus
import PDE.FDeriv.Euclidean.Laplacian
import PDE.FDeriv.Euclidean.NormSq
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Product

/-!
# A bounded version of the weight `|x|²`

To show that `|x| u` is square integrable one would like to pair an equation for `u` with
`|x|² u`, but that pairing need not converge. The weight

`φ_L = |x|² χ_L + (2L)² (1 - χ_L)`,

with `χ_L` the radial cutoff equal to one for `|x| ≤ L` and to zero for `|x| ≥ 2L`, is a smooth
bounded stand-in. It equals `|x|²` on the ball of radius `L` and `(2L)²` outside the ball of
radius `2L`, it increases along rays, and `|∇φ_L| ≤ C √φ_L` and `|Δφ_L| ≤ C` with a constant
`C` that does not depend on `L`. So estimates proved with `φ_L` pass to the limit `L → ∞`.
Hou, Wang and Yang use a weight of this kind for the weighted estimates in the proof of their
Proposition 4. Every statement here holds for every `L > 0` in every dimension.

## Main results

* `radialCutoff_le_of_norm_le`, `fderiv_radialCutoff_apply_self_nonpos`: the cutoff decreases
  with the norm, and its derivative along rays is nonpositive.
* `truncatedNormSq`: the weight `φ_L`.
* `truncatedNormSq_of_norm_le`, `truncatedNormSq_of_two_mul_le`: its values for `|x| ≤ L` and
  for `|x| ≥ 2L`.
* `truncatedNormSq_nonneg`, `truncatedNormSq_le`, `norm_sq_le_truncatedNormSq`,
  `truncatedNormSq_le_four_mul`: `0 ≤ φ_L ≤ (2L)²`, `|x|² ≤ φ_L` for `|x| ≤ 2L`, and
  `φ_L ≤ 4|x|²`.
* `fderiv_truncatedNormSq_apply_self_nonneg`: `x·∇φ_L ≥ 0`, so `φ_L` increases along rays.
* `exists_norm_fderiv_truncatedNormSq_le`: `|∇φ_L| ≤ C √φ_L`.
* `exists_abs_laplacian_truncatedNormSq_le`: `|Δφ_L| ≤ C`.
* `two_mul_le_fderiv_truncatedNormSq_mul_normSq_apply_self`,
  `exists_norm_fderiv_truncatedNormSq_mul_normSq_le`,
  `exists_abs_laplacian_truncatedNormSq_mul_normSq_le`: the weight `φ_L |x|²` satisfies
  `x·∇(φ_L |x|²) ≥ 2 φ_L |x|²`, `|∇(φ_L |x|²)| ≤ C |x| √(φ_L |x|²)` and
  `|Δ(φ_L |x|²)| ≤ C |x|²`.
* `exists_norm_fderiv_truncatedNormSq_mul_normSq_le_one_add`: for a fixed `L`,
  `|∇(φ_L |x|²)| ≤ C_L (1 + |x|)`.

## How it works

Where `|x| ≤ 2L` the weight is a convex combination of `|x|²` and `(2L)²`, and beyond it is the
constant `(2L)²`. So it lies between `|x|²` and `(2L)²` there, and `φ_L ≤ 4|x|²` everywhere. Its
derivative is `2 χ_L x + (|x|² - (2L)²) ∇χ_L`. Along a ray the first term is nonnegative, and
the second is a product of two nonpositive factors, because the cutoff decreases along rays
(`Real.smoothTransition.monotone`). The derivatives of `χ_L` are `O(1/L)` and `O(1/L²)` and
vanish outside `L ≤ |x| ≤ 2L`, where `|x|² - (2L)²` is `O(L²)` and `L ≤ √φ_L`. This gives the
bounds on `∇φ_L` and `Δφ_L`, with constants that do not depend on `L`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, the weighted
  estimates in the proof of Proposition 4. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open Set Filter SobolevSpace.Approximation
open scoped InnerProductSpace Topology ContDiff

namespace PDE.Analysis

variable {n : ℕ}

/-! ### The radial cutoff decreases along rays -/

/-- The radial cutoff is a nonincreasing function of the norm. -/
theorem radialCutoff_le_of_norm_le (R : ℝ) {x y : ℝ^n} (h : ‖x‖ ≤ ‖y‖) :
    radialCutoff R y ≤ radialCutoff R x := by
  have hn : ‖R⁻¹ • x‖ ≤ ‖R⁻¹ • y‖ := by
    rw [norm_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
  simp only [radialCutoff, ContDiffBumpBase.ofInnerProductSpace]
  exact Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (by linarith) (by norm_num))

/-- The radial cutoff decreases along rays: its derivative along the ray through `x` is
nonpositive, `x·∇χ_R(x) ≤ 0`. -/
theorem fderiv_radialCutoff_apply_self_nonpos {R : ℝ} (hR : 0 < R) (x : ℝ^n) :
    fderiv ℝ (radialCutoff R) x x ≤ 0 := by
  -- The profile along the ray, continued to all `t` as a nonincreasing function.
  let g : ℝ → ℝ := fun t ↦ Real.smoothTransition ((2 - R⁻¹ * ‖x‖ * t) / (2 - 1))
  have ha : 0 ≤ R⁻¹ * ‖x‖ := mul_nonneg (inv_nonneg.mpr hR.le) (norm_nonneg x)
  have hg : Antitone g := fun s t hst ↦ Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left hst ha]) (by norm_num))
  have hd : HasDerivAt (fun t : ℝ ↦ radialCutoff R (t • x)) (fderiv ℝ (radialCutoff R) x x) 1 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have h2 : HasFDerivAt (radialCutoff R) (fderiv ℝ (radialCutoff R) x) ((1 : ℝ) • x) := by
      rw [one_smul]
      exact ((radialCutoff_contDiff R).differentiable (by simp) x).hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (l := radialCutoff (n := n) R) (f := fun t : ℝ ↦ t • x) 1
      h2 h1
  have hev : g =ᶠ[𝓝 1] fun t : ℝ ↦ radialCutoff R (t • x) := by
    filter_upwards [lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with t ht
    simp only [g, radialCutoff, ContDiffBumpBase.ofInnerProductSpace, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, abs_of_pos (inv_pos.mpr hR)]
    ring_nf
  exact (hd.congr_of_eventuallyEq hev).nonpos_of_antitone hg

/-! ### The weight -/

/-- The weight `φ_L = |x|² χ_L + (2L)² (1 - χ_L)`, with `χ_L` the radial cutoff of radius `L`:
a smooth bounded version of `|x|²`, equal to `|x|²` for `|x| ≤ L` and to `(2L)²` for
`|x| ≥ 2L`. -/
def truncatedNormSq (L : ℝ) (x : ℝ^n) : ℝ :=
  ‖x‖ ^ 2 * radialCutoff L x + (2 * L) ^ 2 * (1 - radialCutoff L x)

/-- On the ball of radius `L` the weight is `|x|²`. -/
theorem truncatedNormSq_of_norm_le {L : ℝ} (hL : 0 < L) {x : ℝ^n} (hx : ‖x‖ ≤ L) :
    truncatedNormSq L x = ‖x‖ ^ 2 := by
  rw [truncatedNormSq, radialCutoff_eq_one hL hx]
  ring

/-- Outside the ball of radius `2L` the weight is the constant `(2L)²`. -/
theorem truncatedNormSq_of_two_mul_le {L : ℝ} (hL : 0 < L) {x : ℝ^n} (hx : 2 * L ≤ ‖x‖) :
    truncatedNormSq L x = (2 * L) ^ 2 := by
  rw [truncatedNormSq, radialCutoff_eq_zero_of_le_norm hL hx]
  ring

/-- Where `|x| ≤ 2L` the weight is at least `|x|²`. -/
theorem norm_sq_le_truncatedNormSq {L : ℝ} {x : ℝ^n} (hx : ‖x‖ ≤ 2 * L) :
    ‖x‖ ^ 2 ≤ truncatedNormSq L x := by
  obtain ⟨h0, h1⟩ := radialCutoff_mem_Icc (n := n) L x
  have hsq : ‖x‖ ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  rw [truncatedNormSq]
  nlinarith [mul_nonneg (sub_nonneg.mpr hsq) (sub_nonneg.mpr h1)]

/-- The weight is at most `(2L)²`. -/
theorem truncatedNormSq_le {L : ℝ} (hL : 0 < L) (x : ℝ^n) :
    truncatedNormSq L x ≤ (2 * L) ^ 2 := by
  by_cases hx : ‖x‖ ≤ 2 * L
  · obtain ⟨h0, h1⟩ := radialCutoff_mem_Icc (n := n) L x
    have hsq : ‖x‖ ^ 2 ≤ (2 * L) ^ 2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
    rw [truncatedNormSq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsq) h0]
  · exact (truncatedNormSq_of_two_mul_le hL (not_le.mp hx).le).le

/-- The weight is nonnegative. -/
theorem truncatedNormSq_nonneg {L : ℝ} (hL : 0 < L) (x : ℝ^n) : 0 ≤ truncatedNormSq L x := by
  by_cases hx : ‖x‖ ≤ 2 * L
  · exact (sq_nonneg _).trans (norm_sq_le_truncatedNormSq hx)
  · rw [truncatedNormSq_of_two_mul_le hL (not_le.mp hx).le]
    positivity

/-- The weight is at most `4 |x|²`. -/
theorem truncatedNormSq_le_four_mul {L : ℝ} (hL : 0 < L) (x : ℝ^n) :
    truncatedNormSq L x ≤ 4 * ‖x‖ ^ 2 := by
  by_cases hx : ‖x‖ ≤ L
  · rw [truncatedNormSq_of_norm_le hL hx]
    nlinarith [sq_nonneg ‖x‖]
  · have hLx : L ≤ ‖x‖ := (not_le.mp hx).le
    calc truncatedNormSq L x ≤ (2 * L) ^ 2 := truncatedNormSq_le hL x
      _ = 4 * L ^ 2 := by ring
      _ ≤ 4 * ‖x‖ ^ 2 := by nlinarith [pow_le_pow_left₀ hL.le hLx 2]

/-- The weight is smooth. -/
theorem contDiff_truncatedNormSq (L : ℝ) : ContDiff ℝ ∞ (truncatedNormSq (n := n) L) :=
  ((contDiff_norm_sq ℝ).mul (radialCutoff_contDiff L)).add
    (contDiff_const.mul (contDiff_const.sub (radialCutoff_contDiff L)))

/-- The weight is bounded, so its product with an integrable function is integrable. -/
theorem integrable_truncatedNormSq_mul {L : ℝ} (hL : 0 < L) {g : ℝ^n → ℝ}
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable fun x ↦ truncatedNormSq L x * g x :=
  hg.bdd_mul (contDiff_truncatedNormSq L).continuous.aestronglyMeasurable
    (.of_forall fun x ↦ by
      rw [Real.norm_of_nonneg (truncatedNormSq_nonneg hL x)]
      exact truncatedNormSq_le hL x)

/-- The derivative of the weight: `∇φ_L = (|x|² - (2L)²) ∇χ_L + 2 χ_L x`. -/
theorem fderiv_truncatedNormSq (L : ℝ) (x : ℝ^n) :
    fderiv ℝ (truncatedNormSq L) x =
      (‖x‖ ^ 2 - (2 * L) ^ 2) • fderiv ℝ (radialCutoff L) x +
        radialCutoff L x • ((2 : ℝ) • innerSL ℝ x) := by
  have hχ : DifferentiableAt ℝ (radialCutoff (n := n) L) x :=
    (radialCutoff_contDiff L).differentiable (by simp) x
  have hN : DifferentiableAt ℝ (fun y : ℝ^n ↦ ‖y‖ ^ 2 - (2 * L) ^ 2) x :=
    ((contDiff_norm_sq ℝ).differentiable one_ne_zero x).sub_const _
  have hfun : truncatedNormSq (n := n) L =
      fun y ↦ (2 * L) ^ 2 + (‖y‖ ^ 2 - (2 * L) ^ 2) * radialCutoff L y := by
    funext y
    rw [truncatedNormSq]
    ring
  rw [hfun, fderiv_const_add, fderiv_fun_mul hN hχ, fderiv_sub_const, fderiv_norm_sq_apply,
    two_nsmul, two_smul]

/-- Beyond the outer ball the weight is constant, so its derivative vanishes. -/
theorem fderiv_truncatedNormSq_of_two_mul_lt {L : ℝ} (hL : 0 < L) {x : ℝ^n}
    (hx : 2 * L < ‖x‖) : fderiv ℝ (truncatedNormSq L) x = 0 := by
  have hev : truncatedNormSq (n := n) L =ᶠ[𝓝 x] fun _ ↦ (2 * L) ^ 2 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact truncatedNormSq_of_two_mul_le hL hy.le
  rw [hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply]

/-- The weight increases along rays, `x·∇φ_L(x) ≥ 0`, because the cutoff decreases along
rays. -/
theorem fderiv_truncatedNormSq_apply_self_nonneg {L : ℝ} (hL : 0 < L) (x : ℝ^n) :
    0 ≤ fderiv ℝ (truncatedNormSq L) x x := by
  obtain ⟨h0, -⟩ := radialCutoff_mem_Icc (n := n) L x
  rw [fderiv_truncatedNormSq]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]
  have hsecond : 0 ≤ radialCutoff L x * (2 * ‖x‖ ^ 2) := by positivity
  by_cases hx : ‖x‖ ≤ 2 * L
  · have hsq : ‖x‖ ^ 2 - (2 * L) ^ 2 ≤ 0 :=
      sub_nonpos.mpr (pow_le_pow_left₀ (norm_nonneg x) hx 2)
    have hfirst := mul_nonneg_of_nonpos_of_nonpos hsq (fderiv_radialCutoff_apply_self_nonpos hL x)
    linarith
  · have hnot : x ∉ tsupport (radialCutoff (n := n) L) := fun h ↦ hx (by
      simpa [Metric.mem_closedBall, dist_zero_right] using tsupport_radialCutoff_subset hL h)
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    simpa using hsecond

/-- `|∇φ_L| ≤ C √φ_L` for every `L > 0`, with a constant `C` that does not depend on `L`.
Inside the ball of radius `L` the gradient is `2x`, and on the annulus `L ≤ |x| ≤ 2L` the
derivative of the cutoff is `O(1/L)` while `||x|² - (2L)²| ≤ 4L²`. -/
theorem exists_norm_fderiv_truncatedNormSq_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : ℝ^n,
      ‖fderiv ℝ (truncatedNormSq L) x‖ ≤ C * √(truncatedNormSq L x) := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  refine ⟨2 + 4 * B₁, by positivity, fun L hL x ↦ ?_⟩
  obtain ⟨h0, h1⟩ := radialCutoff_mem_Icc (n := n) L x
  have hinner : ‖radialCutoff L x • ((2 : ℝ) • innerSL ℝ x)‖ ≤ 2 * ‖x‖ := by
    rw [norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_of_nonneg h0,
      Real.norm_ofNat]
    exact mul_le_of_le_one_left (by positivity) h1
  rw [fderiv_truncatedNormSq]
  by_cases hx2 : ‖x‖ ≤ 2 * L
  · have hroot : ‖x‖ ≤ √(truncatedNormSq L x) :=
      Real.le_sqrt_of_sq_le (norm_sq_le_truncatedNormSq hx2)
    by_cases hx1 : ‖x‖ < L
    · -- Inside the inner ball the cutoff is constant.
      have hev : radialCutoff (n := n) L =ᶠ[𝓝 x] fun _ ↦ 1 := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx1] with y hy
        exact radialCutoff_eq_one hL hy.le
      rw [hev.fderiv_eq, fderiv_fun_const, Pi.zero_apply, smul_zero, zero_add]
      exact hinner.trans (by nlinarith [norm_nonneg x])
    · have hLx : L ≤ ‖x‖ := not_lt.mp hx1
      have hfirst : ‖(‖x‖ ^ 2 - (2 * L) ^ 2) • fderiv ℝ (radialCutoff L) x‖ ≤ 4 * B₁ * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        have habs : |‖x‖ ^ 2 - (2 * L) ^ 2| ≤ 4 * L ^ 2 := by
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg ‖x‖, pow_le_pow_left₀ (norm_nonneg x) hx2 2]
        calc |‖x‖ ^ 2 - (2 * L) ^ 2| * ‖fderiv ℝ (radialCutoff L) x‖
            ≤ 4 * L ^ 2 * (B₁ * L⁻¹) :=
              mul_le_mul habs (hB₁ L hL x) (norm_nonneg _) (by positivity)
          _ = 4 * B₁ * L := by
              field_simp
          _ ≤ 4 * B₁ * ‖x‖ := mul_le_mul_of_nonneg_left hLx (by positivity)
      calc ‖(‖x‖ ^ 2 - (2 * L) ^ 2) • fderiv ℝ (radialCutoff L) x +
            radialCutoff L x • ((2 : ℝ) • innerSL ℝ x)‖ ≤ 4 * B₁ * ‖x‖ + 2 * ‖x‖ :=
            (norm_add_le _ _).trans (add_le_add hfirst hinner)
        _ = (2 + 4 * B₁) * ‖x‖ := by ring
        _ ≤ (2 + 4 * B₁) * √(truncatedNormSq L x) :=
            mul_le_mul_of_nonneg_left hroot (by positivity)
  · -- Beyond the outer ball the weight is constant.
    have hx2' : 2 * L < ‖x‖ := not_le.mp hx2
    have hnot : x ∉ tsupport (radialCutoff (n := n) L) := fun h ↦ hx2 (by
      simpa [Metric.mem_closedBall, dist_zero_right] using tsupport_radialCutoff_subset hL h)
    rw [fderiv_of_notMem_tsupport ℝ hnot, radialCutoff_eq_zero_of_le_norm hL hx2'.le]
    simp only [smul_zero, zero_smul, add_zero, norm_zero]
    positivity

/-- `|Δφ_L| ≤ C` for every `L > 0`, with a constant `C` that does not depend on `L`. The
Laplacian of the product has the three terms `2n χ_L`, `4 x·∇χ_L` and `(|x|² - (2L)²) Δχ_L`,
and each is bounded by the cutoff bounds on the annulus `L ≤ |x| ≤ 2L`. -/
theorem exists_abs_laplacian_truncatedNormSq_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : ℝ^n, |laplacian (truncatedNormSq L) x| ≤ C := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_norm_fderiv_radialCutoff_le n
  obtain ⟨B₂, hB₂0, hB₂⟩ := exists_abs_laplacian_radialCutoff_le (n := n)
  refine ⟨2 * n + 8 * B₁ + 4 * B₂, by positivity, fun L hL x ↦ ?_⟩
  obtain ⟨h0, h1⟩ := radialCutoff_mem_Icc (n := n) L x
  have hχc : ContDiff ℝ 2 (radialCutoff (n := n) L) := (radialCutoff_contDiff L).of_le (by simp)
  have hNc : ContDiff ℝ 2 (fun y : ℝ^n ↦ ‖y‖ ^ 2 - (2 * L) ^ 2) :=
    (contDiff_norm_sq ℝ).sub contDiff_const
  have hfun : truncatedNormSq (n := n) L =
      fun y ↦ (fun _ : ℝ^n ↦ (2 * L) ^ 2) y +
        (fun z ↦ (‖z‖ ^ 2 - (2 * L) ^ 2) * radialCutoff L z) y := by
    funext y
    rw [truncatedNormSq]
    ring
  have hΔN : laplacian (fun y : ℝ^n ↦ ‖y‖ ^ 2 - (2 * L) ^ 2) x = 2 * (n : ℝ) := by
    rw [PDE.laplacian_sub _ _ x (contDiff_norm_sq ℝ).contDiffAt contDiffAt_const,
      EuclideanLaplacian.laplacian_norm_sq, PDE.laplacian_const, sub_zero]
  have hgradN : ∀ i : Fin n, ∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ 2 - (2 * L) ^ 2) x = 2 * x i := fun i ↦ by
    rw [partialDeriv_sub ((contDiff_norm_sq ℝ).differentiable one_ne_zero x)
      (differentiableAt_const _), EuclideanLaplacian.partialDeriv_norm_sq, partialDeriv_const,
      sub_zero]
  rw [hfun, PDE.laplacian_add _ _ x contDiffAt_const (hNc.mul hχc).contDiffAt,
    PDE.laplacian_const, zero_add, PDE.laplacian_mul hNc.contDiffAt hχc.contDiffAt, hΔN]
  simp only [hgradN]
  -- The cross term is the derivative of the cutoff along the ray.
  have hcross : ∑ i : Fin n, 2 * x i * ∂[i] (radialCutoff L) x =
      2 * fderiv ℝ (radialCutoff L) x x := by
    rw [fderiv_apply_eq_sum_partialDeriv_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hcross]
  have hray : |fderiv ℝ (radialCutoff L) x x| ≤ 2 * B₁ := by
    by_cases hx2 : ‖x‖ ≤ 2 * L
    · calc |fderiv ℝ (radialCutoff L) x x| ≤ ‖fderiv ℝ (radialCutoff L) x‖ * ‖x‖ :=
            (fderiv ℝ (radialCutoff L) x).le_opNorm x
        _ ≤ B₁ * L⁻¹ * (2 * L) :=
            mul_le_mul (hB₁ L hL x) hx2 (norm_nonneg x) (by positivity)
        _ = 2 * B₁ := by
            field_simp
    · have hnot : x ∉ tsupport (radialCutoff (n := n) L) := fun h ↦ hx2 (by
        simpa [Metric.mem_closedBall, dist_zero_right] using tsupport_radialCutoff_subset hL h)
      rw [fderiv_of_notMem_tsupport ℝ hnot]
      simpa using hB₁0
  have hlast : |(‖x‖ ^ 2 - (2 * L) ^ 2) * laplacian (radialCutoff L) x| ≤ 4 * B₂ := by
    by_cases hx2 : ‖x‖ ≤ 2 * L
    · have habs : |‖x‖ ^ 2 - (2 * L) ^ 2| ≤ 4 * L ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg ‖x‖, pow_le_pow_left₀ (norm_nonneg x) hx2 2]
      rw [abs_mul]
      calc |‖x‖ ^ 2 - (2 * L) ^ 2| * |laplacian (radialCutoff L) x|
          ≤ 4 * L ^ 2 * (B₂ * L⁻¹ ^ 2) :=
            mul_le_mul habs (hB₂ L hL x) (abs_nonneg _) (by positivity)
        _ = 4 * B₂ := by
            field_simp
    · have hnot : x ∉ tsupport (radialCutoff (n := n) L) := fun h ↦ hx2 (by
        simpa [Metric.mem_closedBall, dist_zero_right] using tsupport_radialCutoff_subset hL h)
      rw [EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hnot, mul_zero, abs_zero]
      positivity
  have hfirst : |2 * (n : ℝ) * radialCutoff L x| ≤ 2 * n := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n), abs_of_nonneg h0]
    exact mul_le_of_le_one_right (by positivity) h1
  have e1 := abs_le.mp hfirst
  have e2 := abs_le.mp hray
  have e3 := abs_le.mp hlast
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

/-! ### The weight `φ_L |x|²` -/

/-- The derivative of the weight `φ_L |x|²`: `∇(φ_L |x|²) = 2 φ_L x + |x|² ∇φ_L`. -/
theorem fderiv_truncatedNormSq_mul_normSq (L : ℝ) (x : ℝ^n) :
    fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x =
      truncatedNormSq L x • ((2 : ℝ) • innerSL ℝ x) + ‖x‖ ^ 2 • fderiv ℝ (truncatedNormSq L) x := by
  rw [fderiv_fun_mul ((contDiff_truncatedNormSq L).differentiable (by simp) x)
    ((contDiff_norm_sq ℝ).differentiable one_ne_zero x), fderiv_norm_sq_apply, two_nsmul,
    two_smul]

/-- The weight `φ_L |x|²` grows at least quadratically along rays:
`x·∇(φ_L |x|²) ≥ 2 φ_L |x|²`, because `φ_L` is radially increasing. -/
theorem two_mul_le_fderiv_truncatedNormSq_mul_normSq_apply_self {L : ℝ} (hL : 0 < L)
    (x : ℝ^n) : 2 * (truncatedNormSq L x * ‖x‖ ^ 2) ≤
      fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x x := by
  have hray := fderiv_truncatedNormSq_apply_self_nonneg hL x
  rw [fderiv_truncatedNormSq_mul_normSq]
  simp only [add_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    real_inner_self_eq_norm_sq]
  nlinarith [mul_nonneg (sq_nonneg ‖x‖) hray]

/-- `√φ_L ≤ 2 |x|`. -/
theorem sqrt_truncatedNormSq_le {L : ℝ} (hL : 0 < L) (x : ℝ^n) :
    √(truncatedNormSq L x) ≤ 2 * ‖x‖ := by
  calc √(truncatedNormSq L x) ≤ √((2 * ‖x‖) ^ 2) :=
        Real.sqrt_le_sqrt ((truncatedNormSq_le_four_mul hL x).trans_eq (by ring))
    _ = 2 * ‖x‖ := Real.sqrt_sq (by positivity)

/-- `|∇(φ_L |x|²)| ≤ C |x| √(φ_L |x|²)` for every `L > 0`, with `C` independent of `L`. This is
the bound `|∇φ_L| ≤ C √φ_L` for the weight `φ_L |x|²`. -/
theorem exists_norm_fderiv_truncatedNormSq_mul_normSq_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : ℝ^n,
      ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ ≤
        C * (‖x‖ * √(truncatedNormSq L x * ‖x‖ ^ 2)) := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_norm_fderiv_truncatedNormSq_le n
  refine ⟨4 + Ce, by positivity, fun L hL x ↦ ?_⟩
  have hφ0 := truncatedNormSq_nonneg hL x
  have hs0 : 0 ≤ √(truncatedNormSq L x) := Real.sqrt_nonneg _
  have hs2 : √(truncatedNormSq L x) ^ 2 = truncatedNormSq L x := Real.sq_sqrt hφ0
  have hs := sqrt_truncatedNormSq_le hL x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hroot : √(truncatedNormSq L x * ‖x‖ ^ 2) = √(truncatedNormSq L x) * ‖x‖ := by
    rw [Real.sqrt_mul hφ0, Real.sqrt_sq hx0]
  have h₁ : ‖truncatedNormSq L x • ((2 : ℝ) • innerSL ℝ x)‖ ≤
      4 * (‖x‖ ^ 2 * √(truncatedNormSq L x)) := by
    rw [norm_smul, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg hφ0, Real.norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hs0 hx0)]
  have h₂ : ‖‖x‖ ^ 2 • fderiv ℝ (truncatedNormSq L) x‖ ≤
      Ce * (‖x‖ ^ 2 * √(truncatedNormSq L x)) := by
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg ‖x‖)]
    calc ‖x‖ ^ 2 * ‖fderiv ℝ (truncatedNormSq L) x‖
        ≤ ‖x‖ ^ 2 * (Ce * √(truncatedNormSq L x)) :=
          mul_le_mul_of_nonneg_left (hCe L hL x) (sq_nonneg _)
      _ = Ce * (‖x‖ ^ 2 * √(truncatedNormSq L x)) := by ring
  rw [fderiv_truncatedNormSq_mul_normSq, hroot]
  calc ‖truncatedNormSq L x • ((2 : ℝ) • innerSL ℝ x) +
        ‖x‖ ^ 2 • fderiv ℝ (truncatedNormSq L) x‖
      ≤ 4 * (‖x‖ ^ 2 * √(truncatedNormSq L x)) + Ce * (‖x‖ ^ 2 * √(truncatedNormSq L x)) :=
        (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ = (4 + Ce) * (‖x‖ * (√(truncatedNormSq L x) * ‖x‖)) := by ring

/-- `|∇(φ_L |x|²)| ≤ C_L (1 + |x|)`: for fixed `L` the weight `φ_L |x|²` grows quadratically,
because `φ_L` is constant beyond the ball of radius `2L`. -/
theorem exists_norm_fderiv_truncatedNormSq_mul_normSq_le_one_add {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ^n,
      ‖fderiv ℝ (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x‖ ≤ C * (1 + ‖x‖) := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_norm_fderiv_truncatedNormSq_le n
  refine ⟨8 * Ce * L ^ 3 + 8 * L ^ 2, by positivity, fun x ↦ ?_⟩
  have hφ0 := truncatedNormSq_nonneg hL x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h₁ : ‖truncatedNormSq L x • ((2 : ℝ) • innerSL ℝ x)‖ ≤ 8 * L ^ 2 * ‖x‖ := by
    rw [norm_smul, norm_smul, innerSL_apply_norm, Real.norm_of_nonneg hφ0, Real.norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_right (truncatedNormSq_le hL x) hx0]
  have h₂ : ‖‖x‖ ^ 2 • fderiv ℝ (truncatedNormSq L) x‖ ≤ 8 * Ce * L ^ 3 := by
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg ‖x‖)]
    by_cases hx : ‖x‖ ≤ 2 * L
    · have hroot : √(truncatedNormSq L x) ≤ 2 * L := by
        calc √(truncatedNormSq L x) ≤ √((2 * L) ^ 2) :=
              Real.sqrt_le_sqrt (truncatedNormSq_le hL x)
          _ = 2 * L := Real.sqrt_sq (by positivity)
      calc ‖x‖ ^ 2 * ‖fderiv ℝ (truncatedNormSq L) x‖ ≤ (2 * L) ^ 2 * (Ce * (2 * L)) :=
            mul_le_mul (pow_le_pow_left₀ hx0 hx 2)
              ((hCe L hL x).trans (mul_le_mul_of_nonneg_left hroot hCe0)) (norm_nonneg _)
              (by positivity)
        _ = 8 * Ce * L ^ 3 := by ring
    · rw [fderiv_truncatedNormSq_of_two_mul_lt hL (not_le.mp hx), norm_zero, mul_zero]
      positivity
  rw [fderiv_truncatedNormSq_mul_normSq]
  have hCL : 0 ≤ 8 * Ce * L ^ 3 := by positivity
  calc ‖truncatedNormSq L x • ((2 : ℝ) • innerSL ℝ x) +
        ‖x‖ ^ 2 • fderiv ℝ (truncatedNormSq L) x‖ ≤ 8 * L ^ 2 * ‖x‖ + 8 * Ce * L ^ 3 :=
        (norm_add_le _ _).trans (add_le_add h₁ h₂)
    _ ≤ (8 * Ce * L ^ 3 + 8 * L ^ 2) * (1 + ‖x‖) := by nlinarith [mul_nonneg hCL hx0]

/-- `|Δ(φ_L |x|²)| ≤ C |x|²` for every `L > 0`, with `C` independent of `L`. -/
theorem exists_abs_laplacian_truncatedNormSq_mul_normSq_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ x : ℝ^n,
      |laplacian (fun y : ℝ^n ↦ truncatedNormSq L y * ‖y‖ ^ 2) x| ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_norm_fderiv_truncatedNormSq_le n
  obtain ⟨CΔ, hCΔ0, hCΔ⟩ := exists_abs_laplacian_truncatedNormSq_le n
  refine ⟨CΔ + 8 * Ce + 8 * n, by positivity, fun L hL x ↦ ?_⟩
  have hφc : ContDiff ℝ 2 (truncatedNormSq (n := n) L) :=
    (contDiff_truncatedNormSq L).of_le (by simp)
  have hφ0 := truncatedNormSq_nonneg hL x
  have hφ4 := truncatedNormSq_le_four_mul hL x
  have hs := sqrt_truncatedNormSq_le hL x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  rw [PDE.laplacian_mul hφc.contDiffAt (contDiff_norm_sq ℝ).contDiffAt,
    EuclideanLaplacian.laplacian_norm_sq]
  have hcross : ∑ i : Fin n, ∂[i] (truncatedNormSq L) x * ∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ 2) x =
      2 * fderiv ℝ (truncatedNormSq L) x x := by
    rw [fderiv_apply_eq_sum_partialDeriv_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [EuclideanLaplacian.partialDeriv_norm_sq]
      ring
  rw [hcross]
  have h₁ : |laplacian (truncatedNormSq L) x * ‖x‖ ^ 2| ≤ CΔ * ‖x‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
    exact mul_le_mul_of_nonneg_right (hCΔ L hL x) (sq_nonneg _)
  have h₂ : |fderiv ℝ (truncatedNormSq L) x x| ≤ 2 * Ce * ‖x‖ ^ 2 := by
    calc |fderiv ℝ (truncatedNormSq L) x x| ≤ ‖fderiv ℝ (truncatedNormSq L) x‖ * ‖x‖ :=
          (fderiv ℝ (truncatedNormSq L) x).le_opNorm x
      _ ≤ Ce * (2 * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right ((hCe L hL x).trans (mul_le_mul_of_nonneg_left hs hCe0)) hx0
      _ = 2 * Ce * ‖x‖ ^ 2 := by ring
  have e1 := abs_le.mp h₁
  have e2 := abs_le.mp h₂
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [abs_le]
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, mul_nonneg hn0 hφ0,
    mul_le_mul_of_nonneg_left hφ4 hn0]

end PDE.Analysis
