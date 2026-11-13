/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.HolderHessian
public import PDE.Fluid.Incompressible.HalfPlane.FarHessian
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Weighted Hessian estimates of the quadrant potential

For a vorticity `f` of the Hölder class (`IsHolderVorticity α f`) with the weighted bounds

* `|f(y)| ≤ M min(|y|^a, |y|^(-b))` on the closed upper half-plane, and
* `|f(y) - f(z)| ≤ M min(|x|^γ, |x|^ε) |y - z|^α` for `y, z` in the closed upper half-plane with
  `|x - y|, |x - z| ≤ |x|/2`, for every `x ≠ 0`,

we prove the weighted estimates of Chen and Hou, Part I, Lemma 6.11, for the grouped stream
function `Ψ = quadrantPotential f`, with `c = mixedCoefficient f`, `d = quarticCoefficient f`
and `G(x) = (x₀³ x₁ - x₀ x₁³)/6`.

Our main result is the estimate (6.57) for `|x| ≤ 1`, `exists_abs_hessian_sub_expansion_le`. The
decay for `|x| ≥ 1`, the second estimate of Lemma 6.11, the interior limit at the origin and the
local Hölder increments are proved in the companion modules on Hessian decay and Hölder increments.

## Main results

* `abs_mixedCoefficient_le_of_le_min`: `|c| ≤ 4 (1/a + 1/b) M` for `a, b > 0`.
* `abs_quarticCoefficient_le_of_le_min`: `|d| ≤ 48 (1/(a-2) + 1/(2+b)) M` for `a > 2`, `b > 0`.
* `abs_mixedCoefficient_sub_farSource_le`: the near moment
  `|c(f) - c(farSource R f)| ≤ 4 M (2R)^a / a`.
* `abs_quarticCoefficient_sub_farSource_le`: the near moment
  `|d(f) - d(farSource R f)| ≤ 48 M (2R)^(a-2) / (a - 2)` for `a > 2`.
* `exists_abs_hessian_sub_expansion_le`: (6.57), for `|x| ≤ 1`,
  `|∂ₗ∂ₖ(Ψ - c x₀x₁ - d G)(x)| ≲ M (|x|^a + |x|^(γ+α))`, for `2 < a < 4`.

## How it works

We split the Hessian error at `x` into four parts by the triangle inequality. The first compares the
Hessian with that of the far potential by the engine `exists_abs_hessian_sub_far_le`, applied at the
scale of `x`: the far source is `farSource R f` with `R = 4|x|`, the local radius is `δ = |x|/16`,
so the engine ball `B(x, 2δ)` lies in `B(x, |x|/2)` where the local Hölder bound holds for all
pairs, and the integral of `|f(y)|/|x - y|²` over `δ ≤ |x - y|`, `|y| ≤ 2R` is bounded crudely by
`lintegral_middleRegion_le`. The second is the fourth-order expansion of the far Hessian,
`GreenFunction.IsQuadrantFarDensity.abs_hessian_sub_expansion_le`, whose remainder integral is
bounded by `integral_abs_farSource_div_pow_six_le`. The last two are the near moments, of size
`M R^a` and `M R^(a-2)` (`abs_mixedCoefficient_sub_farSource_le`,
`abs_quarticCoefficient_sub_farSource_le`).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6.3.3, Lemma 6.11 and (6.57),
  p. 107, (6.59a) and footnote 93, p. 108, and Appendix C.3.3, pp. 146-148.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric GreenFunction PotentialTheory PotentialTheory.Planar
open SobolevSpace SobolevSpace.Approximation
open scoped Topology

namespace IncompressibleFlow

/-! ### Lower integrals of radial powers -/

section Lintegral

variable {S : Set (ℝ^2)} {F : ℝ^2 → ℝ} {c ρ γ : ℝ}

/-- A function bounded on a set inside `B(0, ρ)` by `c |y|^(γ-2)`, `γ > 0`, has lower integral at
most `c 2π ρ^γ/γ` over it. -/
theorem setLIntegral_le_of_le_ball (hS : MeasurableSet S) (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (hγ : 0 < γ)
    (hsub : S ⊆ ball (0 : ℝ^2) ρ) (hle : ∀ y ∈ S, F y ≤ c * ‖y‖ ^ (γ - 2)) :
    ∫⁻ y in S, ENNReal.ofReal (F y) ≤ ENNReal.ofReal (c * (2 * Real.pi * ρ ^ γ / γ)) := by
  calc ∫⁻ y in S, ENNReal.ofReal (F y)
      ≤ ∫⁻ y in S, ENNReal.ofReal (c * ‖y‖ ^ (γ - 2)) :=
        setLIntegral_mono' hS fun y hy ↦ ENNReal.ofReal_le_ofReal (hle y hy)
    _ ≤ ∫⁻ y in ball (0 : ℝ^2) ρ, ENNReal.ofReal (c * ‖y‖ ^ (γ - 2)) := lintegral_mono_set hsub
    _ = _ := lintegral_ball_zero_rpow hc hρ hγ

/-- A function bounded on a set outside `B(0, ρ)` by `c |y|^(γ-3)`, `γ < 1`, has lower integral at
most `c 2π ρ^(γ-1)/(1-γ)` over it. -/
theorem setLIntegral_le_of_le_compl_ball (hS : MeasurableSet S) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hγ : γ < 1) (hsub : S ⊆ (ball (0 : ℝ^2) ρ)ᶜ) (hle : ∀ y ∈ S, F y ≤ c * ‖y‖ ^ (γ - 3)) :
    ∫⁻ y in S, ENNReal.ofReal (F y) ≤
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ (γ - 1) / (1 - γ))) := by
  calc ∫⁻ y in S, ENNReal.ofReal (F y)
      ≤ ∫⁻ y in S, ENNReal.ofReal (c * ‖y‖ ^ (γ - 3)) :=
        setLIntegral_mono' hS fun y hy ↦ ENNReal.ofReal_le_ofReal (hle y hy)
    _ ≤ ∫⁻ y in (ball (0 : ℝ^2) ρ)ᶜ, ENNReal.ofReal (c * ‖y‖ ^ (γ - 3)) := lintegral_mono_set hsub
    _ = _ := lintegral_compl_ball_zero_rpow hc hρ hγ

/-- The lower integral over a set is at most the sum over its parts inside and outside a ball. -/
theorem setLIntegral_le_inter_add_diff (S T : Set (ℝ^2)) (G : ℝ^2 → ENNReal) :
    ∫⁻ y in S, G y ≤ (∫⁻ y in S ∩ T, G y) + ∫⁻ y in S ∩ Tᶜ, G y := by
  calc ∫⁻ y in S, G y = ∫⁻ y in S ∩ T ∪ S ∩ Tᶜ, G y := by rw [inter_union_compl]
    _ ≤ _ := lintegral_union_le _ _ _

/-- A function vanishing on `S ∩ B(0, ρ)` and bounded by `c |y|^(γ-3)` on the rest of `S` has
lower integral at most `c 2π ρ^(γ-1)/(1-γ)` over `S`. -/
theorem setLIntegral_le_of_eq_zero_of_le (hS : MeasurableSet S) (hρ : 0 < ρ)
    (hγ : γ < 1) (hz : ∀ y ∈ S, ‖y‖ < ρ → F y ≤ 0)
    (hle : ∀ y ∈ S, ρ ≤ ‖y‖ → F y ≤ c * ‖y‖ ^ (γ - 3)) :
    ∫⁻ y in S, ENNReal.ofReal (F y) ≤
      ENNReal.ofReal (c * (2 * Real.pi * ρ ^ (γ - 1) / (1 - γ))) := by
  rcases le_or_gt 0 c with hc | hc
  swap
  · calc ∫⁻ y in S, ENNReal.ofReal (F y) ≤ ∫⁻ _ in S, (0 : ENNReal) :=
          setLIntegral_mono' hS fun y hy ↦ (ENNReal.ofReal_of_nonpos (by
            rcases lt_or_ge ‖y‖ ρ with h | h
            · exact hz y hy h
            · exact (hle y hy h).trans (mul_nonpos_of_nonpos_of_nonneg hc.le (by positivity)))).le
      _ = 0 := by simp
      _ ≤ _ := zero_le
  refine (setLIntegral_le_inter_add_diff S (ball 0 ρ) _).trans ?_
  have h1 : ∫⁻ y in S ∩ ball 0 ρ, ENNReal.ofReal (F y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in S ∩ ball 0 ρ, ENNReal.ofReal (F y) ≤ ∫⁻ _ in S ∩ ball 0 ρ, (0 : ENNReal) :=
          setLIntegral_mono' (hS.inter measurableSet_ball) fun y hy ↦ by
            rw [ENNReal.ofReal_of_nonpos (hz y hy.1 (mem_ball_zero_iff.mp hy.2))]
      _ = 0 := by simp
  rw [h1, zero_add]
  refine setLIntegral_le_of_le_compl_ball (hS.inter measurableSet_ball.compl) hc hρ hγ
    inter_subset_right fun y hy ↦ hle y hy.1 ?_
  simpa using hy.2

/-- A function vanishing on `S` outside `B(0, ρ)` and bounded by `c |y|^(γ-2)` on the rest of `S`
has lower integral at most `c 2π ρ^γ/γ` over `S`. -/
theorem setLIntegral_le_of_le_of_eq_zero (hS : MeasurableSet S) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hγ : 0 < γ) (hz : ∀ y ∈ S, ρ ≤ ‖y‖ → F y ≤ 0)
    (hle : ∀ y ∈ S, ‖y‖ < ρ → F y ≤ c * ‖y‖ ^ (γ - 2)) :
    ∫⁻ y in S, ENNReal.ofReal (F y) ≤ ENNReal.ofReal (c * (2 * Real.pi * ρ ^ γ / γ)) := by
  refine (setLIntegral_le_inter_add_diff S (ball 0 ρ) _).trans ?_
  have h2 : ∫⁻ y in S ∩ (ball 0 ρ)ᶜ, ENNReal.ofReal (F y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in S ∩ (ball 0 ρ)ᶜ, ENNReal.ofReal (F y) ≤
          ∫⁻ _ in S ∩ (ball 0 ρ)ᶜ, (0 : ENNReal) :=
          setLIntegral_mono' (hS.inter measurableSet_ball.compl) fun y hy ↦ by
            refine (ENNReal.ofReal_of_nonpos (hz y hy.1 ?_)).le
            simpa using hy.2
      _ = 0 := by simp
  rw [h2, add_zero]
  exact setLIntegral_le_of_le_ball (hS.inter measurableSet_ball) hc hρ hγ inter_subset_right
    fun y hy ↦ hle y hy.1 (mem_ball_zero_iff.mp hy.2)

/-- A function bounded on `S` by `c min(|y|^(p-2), |y|^(q-3))`, `p > 0`, `q < 1`, has lower
integral at most `c (2π/p + 2π/(1-q))` over `S`. -/
theorem setLIntegral_le_of_le_min (hS : MeasurableSet S) (hc : 0 ≤ c) {p q : ℝ} (hp : 0 < p)
    (hq : q < 1) (hle : ∀ y ∈ S, F y ≤ c * min (‖y‖ ^ (p - 2)) (‖y‖ ^ (q - 3))) :
    ∫⁻ y in S, ENNReal.ofReal (F y) ≤
      ENNReal.ofReal (c * (2 * Real.pi / p + 2 * Real.pi / (1 - q))) := by
  refine (setLIntegral_le_inter_add_diff S (ball 0 1) _).trans ?_
  have h1 := setLIntegral_le_of_le_ball (F := F) (hS.inter measurableSet_ball) hc zero_le_one hp
    inter_subset_right fun y hy ↦ (hle y hy.1).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hc)
  have h2 := setLIntegral_le_of_le_compl_ball (F := F) (hS.inter measurableSet_ball.compl) hc
    zero_lt_one hq inter_subset_right fun y hy ↦ (hle y hy.1).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hc)
  have h1q : 0 < 1 - q := by linarith
  simp only [Real.one_rpow, mul_one] at h1 h2
  rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add h1 h2

end Lintegral

/-! ### Elementary bounds -/

section Elementary

/-- `|∂ₖ∂ₗG(x)| ≤ |x|²` for `G(x) = (x₀³ x₁ - x₀ x₁³)/6`. -/
theorem abs_quarticHessian_le (k l : Fin 2) (x : ℝ^2) : |quarticHessian k l x| ≤ ‖x‖ ^ 2 := by
  have h1 := abs_mul_coord_le x
  have h2 := abs_sq_sub_sq_coord_le x
  unfold quarticHessian
  split_ifs
  · linarith [sq_nonneg ‖x‖]
  · rw [abs_neg]; linarith [sq_nonneg ‖x‖]
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith [sq_nonneg ‖x‖]

/-- `|∂ₖ∂ₗG(x) - ∂ₖ∂ₗG(z)| ≤ 2 max(|x|, |z|) |x - z|`. -/
theorem abs_quarticHessian_sub_le (k l : Fin 2) (x z : ℝ^2) :
    |quarticHessian k l x - quarticHessian k l z| ≤ 2 * max ‖x‖ ‖z‖ * ‖x - z‖ := by
  have hc (y : ℝ^2) (i : Fin 2) : |y i| ≤ ‖y‖ := EuclideanSpace.abs_apply_le_norm y i
  have hm := le_max_left ‖x‖ ‖z‖
  have hm' := le_max_right ‖x‖ ‖z‖
  have hd0 := hc (x - z) 0
  have hd1 := hc (x - z) 1
  simp only [PiLp.sub_apply] at hd0 hd1
  have hx0 := hc x 0
  have hx1 := hc x 1
  have hz0 := hc z 0
  have hz1 := hc z 1
  have hn : 0 ≤ ‖x - z‖ := norm_nonneg _
  have key1 : |x 0 * x 1 - z 0 * z 1| ≤ 2 * max ‖x‖ ‖z‖ * ‖x - z‖ := by
    rw [show x 0 * x 1 - z 0 * z 1 = x 0 * (x 1 - z 1) + z 1 * (x 0 - z 0) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    nlinarith [abs_nonneg (x 0), abs_nonneg (z 1), abs_nonneg (x 1 - z 1),
      abs_nonneg (x 0 - z 0)]
  unfold quarticHessian
  split_ifs
  · exact key1
  · rw [show -(x 0 * x 1) - -(z 0 * z 1) = -(x 0 * x 1 - z 0 * z 1) by ring, abs_neg]
    exact key1
  · rw [show (x 0 ^ 2 - x 1 ^ 2) / 2 - (z 0 ^ 2 - z 1 ^ 2) / 2 =
      ((x 0 - z 0) * (x 0 + z 0) - (x 1 - z 1) * (x 1 + z 1)) / 2 by ring, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs0 : |x 0 + z 0| ≤ 2 * max ‖x‖ ‖z‖ := (abs_add_le _ _).trans (by linarith)
    have hs1 : |x 1 + z 1| ≤ 2 * max ‖x‖ ‖z‖ := (abs_add_le _ _).trans (by linarith)
    have := abs_sub ((x 0 - z 0) * (x 0 + z 0)) ((x 1 - z 1) * (x 1 + z 1))
    rw [abs_mul, abs_mul] at this
    nlinarith [abs_nonneg (x 0 + z 0), abs_nonneg (x 1 + z 1), abs_nonneg (x 1 - z 1),
      abs_nonneg (x 0 - z 0)]

end Elementary

/-! ### Weighted vorticities -/

section Weighted

variable {f : ℝ^2 → ℝ} {M a b : ℝ}

/-- The weighted bound `|f(y)| ≤ M min(|y|^a, |y|^(-b))` forces `M ≥ 0`. -/
theorem nonneg_of_abs_le_min (hS : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) :
    0 ≤ M := by
  have h := hS (EuclideanSpace.single 1 1) (by simp)
  rw [PiLp.norm_single, norm_one, Real.one_rpow, Real.one_rpow, min_self,
    mul_one] at h
  exact (abs_nonneg _).trans h

variable (hS : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b)))
include hS

/-- `|f(y)| ≤ M |y|^a`. -/
theorem abs_le_mul_rpow_of_le_min {y : ℝ^2} (hy : 0 ≤ y 1) : |f y| ≤ M * ‖y‖ ^ a :=
  (hS y hy).trans (mul_le_mul_of_nonneg_left (min_le_left _ _) (nonneg_of_abs_le_min hS))

/-- `|f(y)| ≤ M |y|^(-b)`. -/
theorem abs_le_mul_rpow_neg_of_le_min {y : ℝ^2} (hy : 0 ≤ y 1) : |f y| ≤ M * ‖y‖ ^ (-b) :=
  (hS y hy).trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (nonneg_of_abs_le_min hS))

/-- `|f(y)| ≤ M` when `a, b ≥ 0`. -/
theorem abs_le_of_le_min (ha : 0 ≤ a) (hb : 0 ≤ b) {y : ℝ^2} (hy : 0 ≤ y 1) : |f y| ≤ M := by
  refine (hS y hy).trans (mul_le_of_le_one_right (nonneg_of_abs_le_min hS) ?_)
  rcases le_total ‖y‖ 1 with h1 | h1
  · exact (min_le_left _ _).trans (Real.rpow_le_one (norm_nonneg _) h1 ha)
  · exact (min_le_right _ _).trans (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))

/-- On the quadrant, `|K₁ f| ≤ (M/2) min(|y|^(a-2), |y|^((1-b)-3))`. -/
theorem abs_hessianKernel_mul_le_min {y : ℝ^2} (hy : y ∈ quadrant) :
    |hessianKernel 0 1 y * f y| ≤ M / 2 * min (‖y‖ ^ (a - 2)) (‖y‖ ^ ((1 - b) - 3)) := by
  have hM := nonneg_of_abs_le_min hS
  have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
  have e1 : ‖y‖ ^ a / ‖y‖ ^ 2 = ‖y‖ ^ (a - 2) := by
    rw [← Real.rpow_sub_natCast hy0.ne']; norm_num
  have e2 : ‖y‖ ^ (-b) / ‖y‖ ^ 2 = ‖y‖ ^ ((1 - b) - 3) := by
    rw [← Real.rpow_sub_natCast hy0.ne']; congr 1; push_cast; ring
  rw [abs_mul, ← e1, ← e2, min_div_div_right (by positivity)]
  calc |hessianKernel 0 1 y| * |f y| ≤ 1 / (2 * ‖y‖ ^ 2) * (M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) :=
        mul_le_mul (abs_hessianKernel_le 0 1 y) (hS y hy.2.le) (abs_nonneg _)
          (by positivity)
    _ = M / 2 * (min (‖y‖ ^ a) (‖y‖ ^ (-b)) / ‖y‖ ^ 2) := by field_simp

/-- On the quadrant, `|q f| ≤ 6 M min(|y|^((a-2)-2), |y|^((-1-b)-3))`. -/
theorem abs_quarticKernel_mul_le_min {y : ℝ^2} (hy : y ∈ quadrant) :
    |quarticKernel y * f y| ≤ 6 * M * min (‖y‖ ^ ((a - 2) - 2)) (‖y‖ ^ ((-1 - b) - 3)) := by
  have hM := nonneg_of_abs_le_min hS
  have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
  have e1 : ‖y‖ ^ a / ‖y‖ ^ 4 = ‖y‖ ^ ((a - 2) - 2) := by
    rw [← Real.rpow_sub_natCast hy0.ne']; congr 1; push_cast; ring
  have e2 : ‖y‖ ^ (-b) / ‖y‖ ^ 4 = ‖y‖ ^ ((-1 - b) - 3) := by
    rw [← Real.rpow_sub_natCast hy0.ne']; congr 1; push_cast; ring
  rw [abs_mul, ← e1, ← e2, min_div_div_right (by positivity)]
  calc |quarticKernel y| * |f y| ≤ 6 / ‖y‖ ^ 4 * (M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) :=
        mul_le_mul (abs_quarticKernel_le y) (hS y hy.2.le) (abs_nonneg _) (by positivity)
    _ = 6 * M * (min (‖y‖ ^ a) (‖y‖ ^ (-b)) / ‖y‖ ^ 4) := by field_simp

/-- **Size of the mixed coefficient** (Part I, Lemma 6.11):
`|c| ≤ 4 (1/a + 1/b) M` for `a, b > 0`. -/
theorem abs_mixedCoefficient_le_of_le_min (ha : 0 < a) (hb : 0 < b) :
    |mixedCoefficient f| ≤ 4 * (1 / a + 1 / b) * M := by
  have hM := nonneg_of_abs_le_min hS
  have hl := setLIntegral_le_of_le_min (F := fun y ↦ |hessianKernel 0 1 y * f y|)
    measurableSet_quadrant (by positivity : 0 ≤ M / 2) ha (by linarith : 1 - b < 1)
    fun y hy ↦ abs_hessianKernel_mul_le_min hS hy
  rw [show 1 - (1 - b) = b by ring] at hl
  have h := abs_setIntegral_le_of_lintegral_le measurableSet_quadrant subset_rfl (by positivity)
    (fun _ _ ↦ le_rfl) hl
  unfold mixedCoefficient
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
  calc 4 / Real.pi * |∫ y in quadrant, hessianKernel 0 1 y * f y|
      ≤ 4 / Real.pi * (M / 2 * (2 * Real.pi / a + 2 * Real.pi / b)) := by gcongr
    _ = 4 * (1 / a + 1 / b) * M := by field_simp

/-- **Size of the quartic coefficient** (Part I, Lemma 6.11):
`|d| ≤ 48 (1/(a-2) + 1/(2+b)) M` for `a > 2`, `b > 0`. -/
theorem abs_quarticCoefficient_le_of_le_min (ha : 2 < a) (hb : 0 < b) :
    |quarticCoefficient f| ≤ 48 * (1 / (a - 2) + 1 / (2 + b)) * M := by
  have hM := nonneg_of_abs_le_min hS
  have ha2 : 0 < a - 2 := by linarith
  have hl := setLIntegral_le_of_le_min (F := fun y ↦ |quarticKernel y * f y|)
    measurableSet_quadrant (by positivity : 0 ≤ 6 * M) ha2 (by linarith : -1 - b < 1)
    fun y hy ↦ abs_quarticKernel_mul_le_min hS hy
  rw [show 1 - (-1 - b) = 2 + b by ring] at hl
  have h := abs_setIntegral_le_of_lintegral_le measurableSet_quadrant subset_rfl (by positivity)
    (fun _ _ ↦ le_rfl) hl
  unfold quarticCoefficient
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
  calc 4 / Real.pi * |∫ y in quadrant, quarticKernel y * f y|
      ≤ 4 / Real.pi * (6 * M * (2 * Real.pi / (a - 2) + 2 * Real.pi / (2 + b))) := by gcongr
    _ = 48 * (1 / (a - 2) + 1 / (2 + b)) * M := by field_simp; ring

end Weighted

/-! ### The far source and the near moments -/

section FarSource

variable {α : ℝ} {f : ℝ^2 → ℝ} {M a b R : ℝ}
variable (hS : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b)))
include hS

/-- `K₁ f` is integrable on the quadrant for a weighted Hölder vorticity, `a, b > 0`. -/
theorem integrableOn_hessianKernel_mul_of_le_min (hf : IsHolderVorticity α f) (ha : 0 < a)
    (hb : 0 < b) : IntegrableOn (fun y ↦ hessianKernel 0 1 y * f y) quadrant := by
  have hM := nonneg_of_abs_le_min hS
  have hK : Measurable (hessianKernel 0 1 : ℝ^2 → ℝ) := by
    rw [show (hessianKernel 0 1 : ℝ^2 → ℝ) = fun z ↦ z 0 * z 1 / ‖z‖ ^ 4 from
      funext hessianKernel_zero_one]
    fun_prop
  have hfm : AEStronglyMeasurable f (volume.restrict quadrant) :=
    (hf.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _)).aestronglyMeasurable
      measurableSet_quadrant
  exact integrableOn_of_abs_le_of_lintegral_le measurableSet_quadrant subset_rfl
    (hK.aestronglyMeasurable.mul hfm) (fun y hy ↦ abs_hessianKernel_mul_le_min hS hy)
    (setLIntegral_le_of_le_min measurableSet_quadrant (by positivity : 0 ≤ M / 2) ha
      (by linarith : 1 - b < 1) fun _ _ ↦ le_rfl)

/-- `q f` is integrable on the quadrant for a weighted Hölder vorticity, `a > 2`, `b > 0`. -/
theorem integrableOn_quarticKernel_mul_of_le_min (hf : IsHolderVorticity α f) (ha : 2 < a)
    (hb : 0 < b) : IntegrableOn (fun y ↦ quarticKernel y * f y) quadrant := by
  have hM := nonneg_of_abs_le_min hS
  have hK : Measurable quarticKernel := by unfold quarticKernel; fun_prop
  have hfm : AEStronglyMeasurable f (volume.restrict quadrant) :=
    (hf.continuousOn.mono fun _ hy ↦ (le_of_lt hy.2 : (0 : ℝ) ≤ _)).aestronglyMeasurable
      measurableSet_quadrant
  exact integrableOn_of_abs_le_of_lintegral_le measurableSet_quadrant subset_rfl
    (hK.aestronglyMeasurable.mul hfm) (fun y hy ↦ abs_quarticKernel_mul_le_min hS hy)
    (setLIntegral_le_of_le_min measurableSet_quadrant (by positivity : 0 ≤ 6 * M)
      (by linarith : 0 < a - 2) (by linarith : -1 - b < 1) fun _ _ ↦ le_rfl)

omit hS in
/-- The far source is at most `|f|`. -/
theorem abs_farSource_le (y : ℝ^2) : |farSource R f y| ≤ |f y| := by
  have hc := radialCutoff_mem_Icc (n := 2) R y
  rw [farSource, abs_mul, abs_of_nonneg (by linarith [hc.2] : (0 : ℝ) ≤ 1 - _)]
  exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hc.1])

omit hS in
/-- The far source vanishes on `B̄(0, R)`. -/
theorem farSource_eq_zero (hR : 0 < R) {y : ℝ^2} (hy : ‖y‖ ≤ R) : farSource R f y = 0 := by
  simp [farSource, radialCutoff_eq_one hR hy]

/-- The near part of a kernel `K` with `|K(y)| ≤ C |y|^{-m}`:
`|∫_{ℝ²₊₊} K χ_R f| ≤ C M 2π (2R)^p / p` for `p = a + 2 - m > 0`. -/
private theorem abs_setIntegral_mul_radialCutoff_le {K : ℝ^2 → ℝ} {C p : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hp : 0 < p) (hpa : a - m = p - 2) (hK : ∀ y, |K y| ≤ C / ‖y‖ ^ m)
    (hR : 0 < R) :
    |∫ y in quadrant, K y * (radialCutoff R y * f y)| ≤
      C * M * (2 * Real.pi * (2 * R) ^ p / p) := by
  have hM := nonneg_of_abs_le_min hS
  refine abs_setIntegral_le_of_lintegral_le measurableSet_quadrant subset_rfl
    (mul_nonneg (by positivity) (div_nonneg (by positivity) hp.le)) (fun _ _ ↦ le_rfl) ?_
  refine setLIntegral_le_of_le_of_eq_zero measurableSet_quadrant (by positivity)
    (by positivity : 0 ≤ 2 * R) hp
    (fun y _ hy ↦ by simp [radialCutoff_eq_zero_of_le_norm hR hy]) fun y hy _ ↦ ?_
  have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
  have hc := radialCutoff_mem_Icc (n := 2) R y
  rw [abs_mul, abs_mul, abs_of_nonneg hc.1, ← hpa, Real.rpow_sub hy0, Real.rpow_natCast]
  calc |K y| * (radialCutoff R y * |f y|) ≤ C / ‖y‖ ^ m * (1 * (M * ‖y‖ ^ a)) :=
        mul_le_mul (hK y) (mul_le_mul hc.2 (abs_le_mul_rpow_of_le_min hS hy.2.le) (abs_nonneg _)
          zero_le_one) (mul_nonneg hc.1 (abs_nonneg _)) (by positivity)
    _ = C * M * (‖y‖ ^ a / ‖y‖ ^ m) := by ring

/-- **The near moment of the mixed coefficient**:
`|c(f) - c(farSource R f)| ≤ 4 M (2R)^a / a`. -/
theorem abs_mixedCoefficient_sub_farSource_le (hf : IsHolderVorticity α f) (ha : 0 < a)
    (hb : 0 < b) (hR : 0 < R) :
    |mixedCoefficient f - mixedCoefficient (farSource R f)| ≤ 4 * M * (2 * R) ^ a / a := by
  have h1 := integrableOn_hessianKernel_mul_of_le_min hS hf ha hb
  have h2 := (hf.isQuadrantFarDensity_farSource hR).integrableOn_hessianKernel_mul
  have heq : mixedCoefficient f - mixedCoefficient (farSource R f) =
      4 / Real.pi * ∫ y in quadrant, hessianKernel 0 1 y * (radialCutoff R y * f y) := by
    unfold mixedCoefficient
    rw [← mul_sub, ← integral_sub h1 h2]
    congr 1
    refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
    simp only [farSource]
    ring
  have h := abs_setIntegral_mul_radialCutoff_le hS (m := 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) ha
    (by push_cast; ring) (fun y ↦ (abs_hessianKernel_le 0 1 y).trans_eq (by ring)) hR
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
  calc _ ≤ 4 / Real.pi * (1 / 2 * M * (2 * Real.pi * (2 * R) ^ a / a)) := by gcongr
    _ = 4 * M * (2 * R) ^ a / a := by field_simp

/-- **The near moment of the quartic coefficient**:
`|d(f) - d(farSource R f)| ≤ 48 M (2R)^(a-2) / (a - 2)` for `a > 2`. -/
theorem abs_quarticCoefficient_sub_farSource_le (hf : IsHolderVorticity α f) (ha : 2 < a)
    (hb : 0 < b) (hR : 0 < R) :
    |quarticCoefficient f - quarticCoefficient (farSource R f)| ≤
      48 * M * (2 * R) ^ (a - 2) / (a - 2) := by
  have h1 := integrableOn_quarticKernel_mul_of_le_min hS hf ha hb
  have h2 := (hf.isQuadrantFarDensity_farSource hR).integrableOn_quarticKernel_mul
  have heq : quarticCoefficient f - quarticCoefficient (farSource R f) =
      4 / Real.pi * ∫ y in quadrant, quarticKernel y * (radialCutoff R y * f y) := by
    unfold quarticCoefficient
    rw [← mul_sub, ← integral_sub h1 h2]
    congr 1
    refine setIntegral_congr_fun measurableSet_quadrant fun y _ ↦ ?_
    simp only [farSource]
    ring
  have h := abs_setIntegral_mul_radialCutoff_le hS (m := 4) (by norm_num : (0 : ℝ) ≤ 6)
    (by linarith : 0 < a - 2) (by push_cast; ring) abs_quarticKernel_le hR
  rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi)]
  calc _ ≤ 4 / Real.pi * (6 * M * (2 * Real.pi * (2 * R) ^ (a - 2) / (a - 2))) := by gcongr
    _ = 48 * M * (2 * R) ^ (a - 2) / (a - 2) := by field_simp; ring

/-- `∫_{ℝ²₊₊} |farSource R f|/|y|⁶ ≤ 2π M R^(a-4)/(4-a)` for `a < 4`. -/
theorem integral_abs_farSource_div_pow_six_le (ha : a < 4) (hR : 0 < R) :
    ∫ y in quadrant, |farSource R f y| / ‖y‖ ^ 6 ≤ M * (2 * Real.pi * R ^ (a - 4) / (4 - a)) := by
  have hM := nonneg_of_abs_le_min hS
  have hl := setLIntegral_le_of_eq_zero_of_le (F := fun y ↦ |(|farSource R f y| / ‖y‖ ^ 6)|)
    measurableSet_quadrant hR (by linarith : a - 3 < 1)
    (fun y _ hy ↦ by simp [farSource_eq_zero hR hy.le]) fun y hy hyR ↦ by
      have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
      rw [abs_of_nonneg (by positivity)]
      have e1 : ‖y‖ ^ a / ‖y‖ ^ 6 = ‖y‖ ^ ((a - 3) - 3) := by
        rw [← Real.rpow_sub_natCast hy0.ne']; congr 1; push_cast; ring
      calc |farSource R f y| / ‖y‖ ^ 6 ≤ M * ‖y‖ ^ a / ‖y‖ ^ 6 := by
            gcongr; exact (abs_farSource_le y).trans (abs_le_mul_rpow_of_le_min hS hy.2.le)
        _ = M * ‖y‖ ^ ((a - 3) - 3) := by rw [mul_div_assoc, e1]
  rw [show a - 3 - 1 = a - 4 by ring, show 1 - (a - 3) = 4 - a by ring] at hl
  have h4 : 0 < 4 - a := by linarith
  exact (le_abs_self _).trans (abs_setIntegral_le_of_lintegral_le measurableSet_quadrant
    subset_rfl (by positivity) (fun _ _ ↦ le_rfl) hl)

/-- `∫_{ℝ²₊₊} |farSource R f|/|y|² ≤ 2π M R^(-b)/b` for `b > 0`. -/
theorem integral_abs_farSource_div_sq_le (hb : 0 < b) (hR : 0 < R) :
    ∫ y in quadrant, |farSource R f y| / ‖y‖ ^ 2 ≤ M * (2 * Real.pi * R ^ (-b) / b) := by
  have hM := nonneg_of_abs_le_min hS
  have hl := setLIntegral_le_of_eq_zero_of_le (F := fun y ↦ |(|farSource R f y| / ‖y‖ ^ 2)|)
    measurableSet_quadrant hR (by linarith : 1 - b < 1)
    (fun y _ hy ↦ by simp [farSource_eq_zero hR hy.le]) fun y hy hyR ↦ by
      have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
      rw [abs_of_nonneg (by positivity)]
      have e1 : ‖y‖ ^ (-b) / ‖y‖ ^ 2 = ‖y‖ ^ ((1 - b) - 3) := by
        rw [← Real.rpow_sub_natCast hy0.ne']; congr 1; push_cast; ring
      calc |farSource R f y| / ‖y‖ ^ 2 ≤ M * ‖y‖ ^ (-b) / ‖y‖ ^ 2 := by
            gcongr
            exact (abs_farSource_le y).trans (abs_le_mul_rpow_neg_of_le_min hS hy.2.le)
        _ = M * ‖y‖ ^ ((1 - b) - 3) := by rw [mul_div_assoc, e1]
  rw [show 1 - b - 1 = -b by ring, show 1 - (1 - b) = b by ring] at hl
  exact (le_abs_self _).trans (abs_setIntegral_le_of_lintegral_le measurableSet_quadrant
    subset_rfl (by positivity) (fun _ _ ↦ le_rfl) hl)

/-- `∫_{ℝ²₊₊} |farSource R f|/|y|³ ≤ 2π M / R` for `a, b ≥ 0`. -/
theorem integral_abs_farSource_div_pow_three_le (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 < R) :
    ∫ y in quadrant, |farSource R f y| / ‖y‖ ^ 3 ≤ M * (2 * Real.pi / R) := by
  have hM := nonneg_of_abs_le_min hS
  have hl := setLIntegral_le_of_eq_zero_of_le (F := fun y ↦ |(|farSource R f y| / ‖y‖ ^ 3)|)
    measurableSet_quadrant hR (by norm_num : (0 : ℝ) < 1)
    (fun y _ hy ↦ by simp [farSource_eq_zero hR hy.le]) fun y hy hyR ↦ by
      have hy0 : 0 < ‖y‖ := norm_pos_of_mem_quadrant hy
      rw [abs_of_nonneg (by positivity)]
      have e1 : 1 / ‖y‖ ^ 3 = ‖y‖ ^ ((0 : ℝ) - 3) := by
        rw [zero_sub, Real.rpow_neg hy0.le, one_div]; norm_cast
      calc |farSource R f y| / ‖y‖ ^ 3 ≤ M / ‖y‖ ^ 3 := by
            gcongr; exact (abs_farSource_le y).trans (abs_le_of_le_min hS ha hb hy.2.le)
        _ = M * ‖y‖ ^ ((0 : ℝ) - 3) := by rw [← e1, mul_one_div]
  rw [show (0 : ℝ) - 1 = -1 by ring, show (1 : ℝ) - 0 = 1 by ring, Real.rpow_neg_one,
    div_one] at hl
  exact (le_abs_self _).trans (abs_setIntegral_le_of_lintegral_le measurableSet_quadrant
    subset_rfl (by positivity) (fun _ _ ↦ le_rfl) (hl.trans_eq (by rw [div_eq_mul_inv])))

omit hS in
/-- The region of the intermediate integrals of the engine is measurable. -/
theorem measurableSet_middleRegion (x : ℝ^2) (δ R : ℝ) :
    MeasurableSet {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R} := by
  have h1 : MeasurableSet {y : ℝ^2 | 0 < y 1} := measurableSet_lt measurable_const (by fun_prop)
  have h2 : MeasurableSet {y : ℝ^2 | δ ≤ ‖x - y‖} := measurableSet_le measurable_const (by fun_prop)
  have h3 : MeasurableSet {y : ℝ^2 | ‖y‖ ≤ 2 * R} := measurableSet_le (by fun_prop) measurable_const
  exact h1.inter (h2.inter h3)

/-- **The crude intermediate integral**: with `|f| ≤ M |y|^a`, `a ≥ 0`,
`∫⁻_{0 < y₁, δ ≤ |x - y|, |y| ≤ 2R} |f|/|x - y|^p ≤ 16π M (2R)^a R² / δ^p`. -/
theorem lintegral_middleRegion_le (ha : 0 ≤ a) {x : ℝ^2} {δ : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (p : ℕ) :
    ∫⁻ y in {y : ℝ^2 | 0 < y 1 ∧ δ ≤ ‖x - y‖ ∧ ‖y‖ ≤ 2 * R},
        ENNReal.ofReal (|f y| / ‖x - y‖ ^ p) ≤
      ENNReal.ofReal (16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ p) := by
  have hM := nonneg_of_abs_le_min hS
  have h := setLIntegral_le_of_le_ball (F := fun y ↦ |f y| / ‖x - y‖ ^ p)
    (measurableSet_middleRegion x δ R) (by positivity : 0 ≤ M * (2 * R) ^ a / δ ^ p)
    (by positivity : 0 ≤ 4 * R) (by norm_num : (0 : ℝ) < 2)
    (fun y hy ↦ by rw [mem_ball_zero_iff]; linarith [hy.2.2]) fun y hy ↦ by
      rw [sub_self, Real.rpow_zero, mul_one]
      have hxy : 0 < ‖x - y‖ := lt_of_lt_of_le hδ hy.2.1
      calc |f y| / ‖x - y‖ ^ p ≤ M * (2 * R) ^ a / δ ^ p := by
            gcongr
            · exact (abs_le_mul_rpow_of_le_min hS hy.1.le).trans (by gcongr; exact hy.2.2)
            · exact hy.2.1
        _ = M * (2 * R) ^ a / δ ^ p := rfl
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [Real.rpow_two]
  field_simp
  ring

end FarSource

/-! ### Lemma 6.11 near the origin -/

section Expansion

variable {α a b γ ε : ℝ}

/-- `t^(p - n) t^n = t^p` for `t > 0`. -/
private theorem rpow_sub_mul_pow {t : ℝ} (ht : 0 < t) (p : ℝ) (n : ℕ) :
    t ^ (p - n) * t ^ n = t ^ p := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]; congr 1; ring

/-- **Part I, Lemma 6.11, (6.57).** For a Hölder vorticity with
`|f(y)| ≤ M min(|y|^a, |y|^(-b))` (`2 < a < 4`, `b > 0`) and local Hölder constant
`M min(|x|^γ, |x|^ε)` on `B(x, |x|/2)`, the Hessian of the grouped stream function satisfies, for
`|x| ≤ 1` in the open upper half-plane,
`|∂ₗ∂ₖΨ(x) - (c mₖₗ + d ∂ₖ∂ₗG(x))| ≤ C M (|x|^a + |x|^(γ+α))`, `c = mixedCoefficient f`,
`d = quarticCoefficient f`, `mₖₗ = 1 - δₖₗ`. With the `X₁` weights, `a = 29/10`, `γ = 2`,
`α = 1/2`, this is `C M |x|^(5/2)`. -/
theorem exists_abs_hessian_sub_expansion_le (hα : 0 < α) (hα1 : α < 1) (ha : 2 < a)
    (ha4 : a < 4) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ⦃f : ℝ^2 → ℝ⦄ ⦃M : ℝ⦄, IsHolderVorticity α f →
      (∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) →
      (∀ x : ℝ^2, x ≠ 0 → ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ ‖x‖ / 2 →
        ‖x - z‖ ≤ ‖x‖ / 2 → |f y - f z| ≤ M * min (‖x‖ ^ γ) (‖x‖ ^ ε) * ‖y - z‖ ^ α) →
      ∀ x : ℝ^2, 0 < x 1 → ‖x‖ ≤ 1 → ∀ k l : Fin 2,
        |(∂[l] (∂[k] (quadrantPotential f))) x -
            (mixedCoefficient f * (if k = l then 0 else 1) +
              quarticCoefficient f * quarticHessian k l x)| ≤
          C * M * (‖x‖ ^ a + ‖x‖ ^ (γ + α)) := by
  obtain ⟨C₁, hC₁, hE⟩ := exists_abs_hessian_sub_far_le hα hα1
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < a - 2 := by linarith
  have h4a : 0 < 4 - a := by linarith
  set KI : ℝ := 65536 * Real.pi * 8 ^ a
  set KF : ℝ := 368 / 9 * 4 ^ (a - 4) / (4 - a)
  set Kc : ℝ := 4 * 8 ^ a / a
  set Kd : ℝ := 48 * 8 ^ (a - 2) / (a - 2)
  have hKI : 0 ≤ KI := by positivity
  have hKF : 0 ≤ KF := by positivity
  have hKc : 0 ≤ Kc := by positivity
  have hKd : 0 ≤ Kd := by positivity
  refine ⟨C₁ * 2 ^ a + C₁ + C₁ * KI + KF + Kc + Kd, by positivity, ?_⟩
  intro f M hf hS hH x hx hx1 k l
  have hM := nonneg_of_abs_le_min hS
  have hx0 : x ≠ 0 := fun h ↦ by rw [h] at hx; simp at hx
  set r := ‖x‖ with hr_def
  have hr : 0 < r := norm_pos_iff.mpr hx0
  set δ := r / 16 with hδ_def
  set R := 4 * r with hR_def
  have hδ : 0 < δ := by positivity
  have hR : 0 < R := by positivity
  set F := farSource R f
  have hfar := hf.isQuadrantFarDensity_farSource hR
  -- the engine
  have hB : ∀ y, 0 ≤ y 1 → ‖x - y‖ ≤ 2 * δ → |f y| ≤ M * (2 * r) ^ a := fun y hy hxy ↦ by
    refine (abs_le_mul_rpow_of_le_min hS hy).trans (mul_le_mul_of_nonneg_left ?_ hM)
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ ha0.le
    have := norm_le_norm_add_norm_sub' y x
    rw [norm_sub_rev] at this
    linarith
  have hL : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → ‖x - y‖ ≤ 2 * δ → ‖x - z‖ ≤ 2 * δ →
      |f y - f z| ≤ M * min (r ^ γ) (r ^ ε) * ‖y - z‖ ^ α := fun y z hy hz hxy hxz ↦
    hH x hx0 y z hy hz (by linarith) (by linarith)
  have hI := lintegral_middleRegion_le hS ha0.le (x := x) hδ hR 2
  have h1 := hE hf hx hδ (by linarith) hB hL (by positivity) hI k l
  -- the far part
  have h2 := hfar.abs_hessian_sub_expansion_le k l (x := x) (by linarith)
  have h2' := integral_abs_farSource_div_pow_six_le hS ha4 hR
  -- the near moments
  have h3 := abs_mixedCoefficient_sub_farSource_le hS hf ha0 hb hR
  have h4 := abs_quarticCoefficient_sub_farSource_le hS hf ha hb hR
  have hQ := abs_quarticHessian_le k l x
  have hm : |(if k = l then (0 : ℝ) else 1)| ≤ 1 := by split_ifs <;> simp
  -- arithmetic
  set u := M * r ^ a
  set v := M * r ^ (γ + α)
  have hu : 0 ≤ u := by positivity
  have hv : 0 ≤ v := by positivity
  have e2r : (2 * r) ^ a = 2 ^ a * r ^ a := Real.mul_rpow (by norm_num) hr.le
  have e8r : (2 * R) ^ a = 8 ^ a * r ^ a := by
    rw [show 2 * R = 8 * r by rw [hR_def]; ring]; exact Real.mul_rpow (by norm_num) hr.le
  have hT1 : C₁ * (M * (2 * r) ^ a + δ ^ α * (M * min (r ^ γ) (r ^ ε))) +
      C₁ * (16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ 2) ≤
        C₁ * (2 ^ a * u + v) + C₁ * (KI * u) := by
    have hδα : δ ^ α * (M * min (r ^ γ) (r ^ ε)) ≤ v := by
      calc δ ^ α * (M * min (r ^ γ) (r ^ ε)) ≤ r ^ α * (M * r ^ γ) := by
            gcongr
            · linarith
            · exact min_le_left _ _
        _ = v := by
            simp only [v]; rw [Real.rpow_add hr]; ring
    have hI' : 16 * Real.pi * M * (2 * R) ^ a * R ^ 2 / δ ^ 2 = KI * u := by
      rw [e8r]; simp only [KI, u, δ, R]; field_simp; ring
    rw [hI', e2r]
    have h' : M * (2 ^ a * r ^ a) + δ ^ α * (M * min (r ^ γ) (r ^ ε)) ≤ 2 ^ a * u + v := by
      rw [show M * (2 ^ a * r ^ a) = 2 ^ a * u by simp only [u]; ring]; linarith
    exact add_le_add_left (mul_le_mul_of_nonneg_left h' hC₁) _
  have hT2 : 184 / (9 * Real.pi) * r ^ 4 * ∫ y in quadrant, |F y| / ‖y‖ ^ 6 ≤ KF * u := by
    calc 184 / (9 * Real.pi) * r ^ 4 * ∫ y in quadrant, |F y| / ‖y‖ ^ 6
        ≤ 184 / (9 * Real.pi) * r ^ 4 * (M * (2 * Real.pi * R ^ (a - 4) / (4 - a))) := by
          gcongr
      _ = KF * u := by
          rw [show R ^ (a - 4) = 4 ^ (a - 4) * r ^ (a - 4) from Real.mul_rpow (by norm_num) hr.le]
          have e := rpow_sub_mul_pow hr a 4
          push_cast at e
          simp only [KF, u]
          rw [← e]
          field_simp
          ring
  have hT3 : |mixedCoefficient f - mixedCoefficient F| * |(if k = l then (0 : ℝ) else 1)| ≤
      Kc * u := by
    calc |mixedCoefficient f - mixedCoefficient F| * |(if k = l then (0 : ℝ) else 1)|
        ≤ 4 * M * (2 * R) ^ a / a * 1 := by gcongr
      _ = Kc * u := by rw [e8r]; simp only [Kc, u]; field_simp
  have hT4 : |quarticCoefficient f - quarticCoefficient F| * |quarticHessian k l x| ≤ Kd * u := by
    calc |quarticCoefficient f - quarticCoefficient F| * |quarticHessian k l x|
        ≤ 48 * M * (2 * R) ^ (a - 2) / (a - 2) * r ^ 2 := by gcongr
      _ = Kd * u := by
          rw [show 2 * R = 8 * r by rw [hR_def]; ring,
            Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hr.le]
          have e := rpow_sub_mul_pow hr a 2
          push_cast at e
          simp only [Kd, u]
          rw [← e]
          field_simp
  have htri : |(∂[l] (∂[k] (quadrantPotential f))) x -
      (mixedCoefficient f * (if k = l then 0 else 1) +
        quarticCoefficient f * quarticHessian k l x)| ≤
      |(∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential F))) x| +
        |(∂[l] (∂[k] (quadrantPotential F))) x - (mixedCoefficient F * (if k = l then 0 else 1) +
          quarticCoefficient F * quarticHessian k l x)| +
        |mixedCoefficient f - mixedCoefficient F| * |(if k = l then (0 : ℝ) else 1)| +
        |quarticCoefficient f - quarticCoefficient F| * |quarticHessian k l x| := by
    rw [← abs_mul, ← abs_mul]
    calc _ = |((∂[l] (∂[k] (quadrantPotential f))) x - (∂[l] (∂[k] (quadrantPotential F))) x) +
          ((∂[l] (∂[k] (quadrantPotential F))) x - (mixedCoefficient F *
            (if k = l then 0 else 1) + quarticCoefficient F * quarticHessian k l x)) -
          ((mixedCoefficient f - mixedCoefficient F) * (if k = l then 0 else 1)) -
          ((quarticCoefficient f - quarticCoefficient F) * quarticHessian k l x)| := by
            congr 1; ring
      _ ≤ _ := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add
          (abs_add_le _ _) le_rfl)) le_rfl)
  have hCu : (C₁ * 2 ^ a + C₁ + C₁ * KI + KF + Kc + Kd) * M * (r ^ a + r ^ (γ + α)) =
      (C₁ * 2 ^ a + C₁ + C₁ * KI + KF + Kc + Kd) * (u + v) := by simp only [u, v]; ring
  rw [hCu]
  have hC1u : 0 ≤ C₁ * u := mul_nonneg hC₁ hu
  have hrest : 0 ≤ (C₁ * 2 ^ a + C₁ * KI + KF + Kc + Kd) * v := by positivity
  linear_combination htri + h1 + hT1 + h2 + hT2 + hT3 + hT4 + hC1u + hrest

end Expansion

end IncompressibleFlow
