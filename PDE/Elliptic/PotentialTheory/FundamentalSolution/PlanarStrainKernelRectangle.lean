/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarStrainKernelTaylor
public import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Integrals of the strain kernel against separable sums on rectangles

On a closed rectangle `R = [x₀, x₁] × [y₀, y₁]` whose points satisfy `|y - c| ≤ ρ |c|` with
`ρ < 1`, the strain kernel `K₁ = hessianKernel 0 1` is its Taylor polynomial about `c` up to
`|c|⁻² ∑_{m > n} (m + 1) ρ^m / 2` (`abs_hessianKernel_zero_one_sub_strainTaylor_le`). For a sum of
separable functions `f(y) = ∑_j g_j(y₀) k_j(y₁)` on `R` the integral of the polynomial part is a
finite sum of products of one-dimensional moments, and the remainder is bounded by the products of
the one-dimensional `L¹` norms:

`|∫_R K₁ f - ∑_{m ≤ n} ∑_{s ≤ m} κ_{m,s} ∑_j (∫ ξ^s g_j)(∫ η^{m-s} k_j)|
  ≤ |c|⁻² ∑_{m > n} (m + 1) ρ^m / 2 · ∑_j (∫ |g_j|)(∫ |k_j|)`,

with `ξ = (y₀ - Re c)/h₁`, `η = (y₁ - Im c)/h₂` and the real Taylor coefficients
`κ_{m,s} = -Im ((m + 1) (-1)^m C(m, s) h₁^s (i h₂)^{m-s} c^{-(m+2)}) / 2`.

## Main definitions

* `strainTaylorCoeff`: the real Taylor coefficient `κ_{m,s}` of `ξ^s η^{m-s}` in
  `strainTaylor c h₁ h₂`.

## Main results

* `strainTaylor_eq_sum`: the Taylor polynomial expanded in the monomials `ξ^s η^{m-s}`.
* `setIntegral_coordinateRectangle_mul`: a product of one-dimensional functions continuous on the
  sides of a rectangle integrates to the product of the one-dimensional integrals.
* `abs_setIntegral_hessianKernel_mul_sub_le`: the displayed bound for `K₁` against a separable sum
  on a rectangle.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory Set PDE.Analysis
open scoped Interval

namespace PotentialTheory.Planar

/-- The real Taylor coefficient of `ξ^s η^{m-s}` in `strainTaylor c h₁ h₂`. -/
def strainTaylorCoeff (c : ℂ) (h₁ h₂ : ℝ) (m s : ℕ) : ℝ :=
  -(((m + 1 : ℕ) : ℂ) * (-1) ^ m * ((m.choose s : ℕ) : ℂ) * (h₁ : ℂ) ^ s *
      (Complex.I * (h₂ : ℂ)) ^ (m - s) * ((c ^ (m + 2))⁻¹)).im / 2

/-- The Taylor polynomial expanded in the monomials `ξ^s η^{m-s}`. -/
theorem strainTaylor_eq_sum (c : ℂ) (h₁ h₂ : ℝ) (n : ℕ) (ξ η : ℝ) :
    strainTaylor c h₁ h₂ n ξ η =
      ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
        strainTaylorCoeff c h₁ h₂ m s * (ξ ^ s * η ^ (m - s)) := by
  unfold strainTaylor strainTaylorCoeff
  rw [Complex.im_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro m _
  rw [add_pow, mul_sum, Finset.sum_mul, Complex.im_sum, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply sum_congr rfl
  intro s _
  have hfac : ((m + 1 : ℕ) : ℂ) * (-1) ^ m * ((((h₁ * ξ : ℝ) : ℂ)) ^ s *
      (Complex.I * ((h₂ * η : ℝ) : ℂ)) ^ (m - s) * ((m.choose s : ℕ) : ℂ)) *
        ((c ^ (m + 2))⁻¹) =
      (((m + 1 : ℕ) : ℂ) * (-1) ^ m * ((m.choose s : ℕ) : ℂ) * (h₁ : ℂ) ^ s *
        (Complex.I * (h₂ : ℂ)) ^ (m - s) * ((c ^ (m + 2))⁻¹)) *
          ((ξ ^ s * η ^ (m - s) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfac, Complex.im_mul_ofReal]
  ring

/-- A product of one-dimensional functions continuous on the sides of a rectangle integrates to the
product of the one-dimensional integrals. -/
theorem setIntegral_coordinateRectangle_mul {A B : ℝ → ℝ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁)
    (hy : y₀ ≤ y₁) (hA : ContinuousOn A (Icc x₀ x₁)) (hB : ContinuousOn B (Icc y₀ y₁)) :
    ∫ y in coordinateRectangle x₀ x₁ y₀ y₁, A (y 0) * B (y 1) =
      (∫ x in x₀..x₁, A x) * ∫ y in y₀..y₁, B y := by
  have hc : ContinuousOn (fun y : ℝ^2 ↦ A (y 0) * B (y 1)) (coordinateRectangle x₀ x₁ y₀ y₁) := by
    have h0 : Continuous fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous
    have h1 : Continuous fun y : ℝ^2 ↦ y 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (hA.comp h0.continuousOn fun y hy ↦ hy.1).mul (hB.comp h1.continuousOn fun y hy ↦ hy.2)
  rw [setIntegral_coordinateRectangle hx hy hc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro p _
  simp only
  rw [intervalIntegral.integral_const_mul]

/-- A point between `a` and `b` is no farther from `m` than the farther endpoint, in squares. -/
theorem sq_sub_le_of_mem_Icc {a b t m D : ℝ} (ht : t ∈ Icc a b) (ha : (a - m) ^ 2 ≤ D)
    (hb : (b - m) ^ 2 ≤ D) : (t - m) ^ 2 ≤ D := by
  obtain ⟨h1, h2⟩ := ht
  rcases le_total 0 (t - m) with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℝ) ≤ b + t - 2 * m)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) (by linarith : (0 : ℝ) ≤ 2 * m - a - t)]

/-- The corner distances bound the distance of every point of the rectangle to `c`. -/
theorem sq_dist_le_of_corners {x₀ x₁ y₀ y₁ : ℝ} {c : ℂ} {D₁ D₂ : ℝ}
    (hx0 : (x₀ - c.re) ^ 2 ≤ D₁) (hx1 : (x₁ - c.re) ^ 2 ≤ D₁)
    (hy0 : (y₀ - c.im) ^ 2 ≤ D₂) (hy1 : (y₁ - c.im) ^ 2 ≤ D₂) {y : ℝ^2}
    (hy : y ∈ coordinateRectangle x₀ x₁ y₀ y₁) :
    (y 0 - c.re) ^ 2 + (y 1 - c.im) ^ 2 ≤ D₁ + D₂ :=
  add_le_add (sq_sub_le_of_mem_Icc hy.1 hx0 hx1) (sq_sub_le_of_mem_Icc hy.2 hy0 hy1)

/-- The Taylor polynomial in the scaled coordinates is continuous. -/
theorem continuous_strainTaylor (c : ℂ) (h₁ h₂ : ℝ) (n : ℕ) :
    Continuous fun y : ℝ^2 ↦ strainTaylor c h₁ h₂ n ((y 0 - c.re) / h₁) ((y 1 - c.im) / h₂) := by
  simp_rw [strainTaylor_eq_sum]
  fun_prop

/-- The strain kernel is continuous away from the origin. -/
theorem continuousOn_hessianKernel_zero_one {s : Set (ℝ^2)} (hs : ∀ y ∈ s, y ≠ 0) :
    ContinuousOn (hessianKernel 0 1) s := by
  have h : ContinuousOn (fun z : ℝ^2 ↦ z 0 * z 1 / ‖z‖ ^ 4) s := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun y hy ↦ ?_
    exact pow_ne_zero 4 (norm_ne_zero_iff.mpr (hs y hy))
  exact h.congr fun y _ ↦ hessianKernel_zero_one y

/-- **The strain kernel against a separable sum on a rectangle**: the Taylor part is a sum of
products of one-dimensional moments, and the remainder is at most
`|c|⁻² ∑_{m > n} (m + 1) ρ^m / 2` times the sum of the products of the one-dimensional `L¹`
norms. -/
theorem abs_setIntegral_hessianKernel_mul_sub_le {ι : Type*} (J : Finset ι) (g k : ι → ℝ → ℝ)
    {f : ℝ^2 → ℝ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hg : ∀ j ∈ J, ContinuousOn (g j) (Icc x₀ x₁)) (hk : ∀ j ∈ J, ContinuousOn (k j) (Icc y₀ y₁))
    (hf : ∀ y ∈ coordinateRectangle x₀ x₁ y₀ y₁, f y = ∑ j ∈ J, g j (y 0) * k j (y 1))
    {c : ℂ} (hc : c ≠ 0) {h₁ h₂ ρ : ℝ} (h₁0 : h₁ ≠ 0) (h₂0 : h₂ ≠ 0) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (hR : ∀ y ∈ coordinateRectangle x₀ x₁ y₀ y₁,
      (y 0 - c.re) ^ 2 + (y 1 - c.im) ^ 2 ≤ ρ ^ 2 * ‖c‖ ^ 2) (n : ℕ) :
    |(∫ y in coordinateRectangle x₀ x₁ y₀ y₁, hessianKernel 0 1 y * f y) -
        ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1), strainTaylorCoeff c h₁ h₂ m s *
          ∑ j ∈ J, (∫ x in x₀..x₁, ((x - c.re) / h₁) ^ s * g j x) *
            ∫ y in y₀..y₁, ((y - c.im) / h₂) ^ (m - s) * k j y| ≤
      (‖c‖ ^ 2)⁻¹ * inverseSquareTail n ρ / 2 *
        ∑ j ∈ J, (∫ x in x₀..x₁, |g j x|) * ∫ y in y₀..y₁, |k j y| := by
  set R := coordinateRectangle x₀ x₁ y₀ y₁ with hRdef
  have hRc : IsCompact R := isCompact_coordinateRectangle x₀ x₁ y₀ y₁
  have hRm : MeasurableSet R := measurableSet_coordinateRectangle x₀ x₁ y₀ y₁
  set F : ℝ^2 → ℝ := fun y ↦ ∑ j ∈ J, g j (y 0) * k j (y 1) with hFdef
  set T : ℝ^2 → ℝ := fun y ↦ strainTaylor c h₁ h₂ n ((y 0 - c.re) / h₁) ((y 1 - c.im) / h₂)
    with hTdef
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hne : ∀ y ∈ R, y ≠ 0 := by
    rintro y hyR rfl
    have h := hR 0 hyR
    have hc2 : c.re ^ 2 + c.im ^ 2 = ‖c‖ ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [PiLp.zero_apply, zero_sub, neg_sq, hc2] at h
    nlinarith [pow_lt_one₀ hρ0 hρ two_ne_zero, pow_pos hcn 2]
  have hgc : ∀ j ∈ J, ContinuousOn (fun y : ℝ^2 ↦ g j (y 0)) R := fun j hj ↦
    (hg j hj).comp (PiLp.continuous_apply _ _ 0).continuousOn fun y hy ↦ hy.1
  have hkc : ∀ j ∈ J, ContinuousOn (fun y : ℝ^2 ↦ k j (y 1)) R := fun j hj ↦
    (hk j hj).comp (PiLp.continuous_apply _ _ 1).continuousOn fun y hy ↦ hy.2
  have hFc : ContinuousOn F R := continuousOn_finsetSum J fun j hj ↦ (hgc j hj).mul (hkc j hj)
  have hKc : ContinuousOn (hessianKernel 0 1) R := continuousOn_hessianKernel_zero_one hne
  have hTc : ContinuousOn T R := (continuous_strainTaylor c h₁ h₂ n).continuousOn
  have hint : ∀ {u : ℝ^2 → ℝ}, ContinuousOn u R → IntegrableOn u R := fun hu ↦
    hu.integrableOn_compact hRc
  have hfF : ∫ y in R, hessianKernel 0 1 y * f y = ∫ y in R, hessianKernel 0 1 y * F y :=
    setIntegral_congr_fun hRm fun y hy ↦ by rw [hf y hy]
  have hTF : ∫ y in R, T y * F y = ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
      strainTaylorCoeff c h₁ h₂ m s * ∑ j ∈ J, (∫ x in x₀..x₁, ((x - c.re) / h₁) ^ s * g j x) *
        ∫ y in y₀..y₁, ((y - c.im) / h₂) ^ (m - s) * k j y := by
    have hpt : ∀ y, T y * F y = ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
        strainTaylorCoeff c h₁ h₂ m s * ∑ j ∈ J,
          (((y 0 - c.re) / h₁) ^ s * g j (y 0)) * (((y 1 - c.im) / h₂) ^ (m - s) * k j (y 1)) := by
      intro y
      simp only [T, F, strainTaylor_eq_sum, Finset.sum_mul]
      refine sum_congr rfl fun m _ ↦ sum_congr rfl fun s _ ↦ ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact sum_congr rfl fun j _ ↦ by ring
    simp_rw [hpt]
    have hterm : ∀ m s j, j ∈ J → IntegrableOn (fun y : ℝ^2 ↦
        (((y 0 - c.re) / h₁) ^ s * g j (y 0)) * (((y 1 - c.im) / h₂) ^ (m - s) * k j (y 1))) R :=
      fun m s j hj ↦ hint
        (((((PiLp.continuous_apply _ _ 0).sub continuous_const).div_const _).pow s).continuousOn.mul
          (hgc j hj) |>.mul
          (((((PiLp.continuous_apply _ _ 1).sub continuous_const).div_const _).pow (m -
              s)).continuousOn.mul
            (hkc j hj)))
    rw [integral_finsetSum _ fun m _ ↦ integrable_finsetSum _ fun s _ ↦
      (integrable_finsetSum _ fun j hj ↦ hterm m s j hj).const_mul _]
    refine sum_congr rfl fun m _ ↦ ?_
    rw [integral_finsetSum _ fun s _ ↦
      (integrable_finsetSum _ fun j hj ↦ hterm m s j hj).const_mul _]
    refine sum_congr rfl fun s _ ↦ ?_
    rw [integral_const_mul, integral_finsetSum _ fun j hj ↦ hterm m s j hj]
    refine congrArg _ (sum_congr rfl fun j hj ↦ ?_)
    exact setIntegral_coordinateRectangle_mul hx hy
      (((continuous_id.sub continuous_const).div_const _ |>.pow s).continuousOn.mul (hg j hj))
      (((continuous_id.sub continuous_const).div_const _ |>.pow (m - s)).continuousOn.mul (hk j hj))
  set B := (‖c‖ ^ 2)⁻¹ * inverseSquareTail n ρ / 2 with hBdef
  have hpt : ∀ y ∈ R, |hessianKernel 0 1 y - T y| ≤ B := fun y hy ↦
    abs_hessianKernel_zero_one_sub_strainTaylor_le hc h₁0 h₂0 hρ0 hρ n (hR y hy)
  have hsplit : ∫ y in R, hessianKernel 0 1 y * F y =
      (∫ y in R, T y * F y) + ∫ y in R, (hessianKernel 0 1 y - T y) * F y := by
    have hIT : IntegrableOn (fun y ↦ T y * F y) R := hint (hTc.mul hFc)
    have hIR : IntegrableOn (fun y ↦ (hessianKernel 0 1 y - T y) * F y) R :=
      hint ((hKc.sub hTc).mul hFc)
    rw [← integral_add hIT hIR]
    congr 1; funext y; ring
  have hrem : |∫ y in R, (hessianKernel 0 1 y - T y) * F y| ≤
      B * ∑ j ∈ J, (∫ x in x₀..x₁, |g j x|) * ∫ y in y₀..y₁, |k j y| := by
    have habsF : ∀ y ∈ R, |F y| ≤ ∑ j ∈ J, |g j (y 0)| * |k j (y 1)| := fun y _ ↦
      (abs_sum_le_sum_abs _ _).trans_eq (sum_congr rfl fun j _ ↦ abs_mul _ _)
    calc |∫ y in R, (hessianKernel 0 1 y - T y) * F y|
        ≤ ∫ y in R, |(hessianKernel 0 1 y - T y) * F y| := abs_integral_le_integral_abs
      _ ≤ ∫ y in R, B * ∑ j ∈ J, |g j (y 0)| * |k j (y 1)| := by
          refine setIntegral_mono_on (hint ((hKc.sub hTc).mul hFc).abs)
            (hint (continuousOn_const.mul (continuousOn_finsetSum J fun j hj ↦
              ((hgc j hj).abs).mul ((hkc j hj).abs)))) hRm fun y hy ↦ ?_
          rw [abs_mul]
          exact mul_le_mul (hpt y hy) (habsF y hy) (abs_nonneg _)
            ((abs_nonneg _).trans (hpt y hy))
      _ = B * ∑ j ∈ J, (∫ x in x₀..x₁, |g j x|) * ∫ y in y₀..y₁, |k j y| := by
          have hI : ∀ j ∈ J, IntegrableOn (fun y : ℝ^2 ↦ |g j (y 0)| * |k j (y 1)|) R :=
            fun j hj ↦ hint (((hgc j hj).abs).mul ((hkc j hj).abs))
          rw [integral_const_mul, integral_finsetSum _ hI]
          exact congrArg _ (sum_congr rfl fun j hj ↦
            setIntegral_coordinateRectangle_mul hx hy (hg j hj).abs (hk j hj).abs)
  rw [hfF, hsplit, hTF, add_sub_cancel_left]
  exact hrem

end PotentialTheory.Planar
