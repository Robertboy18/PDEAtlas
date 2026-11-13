/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarKernelOneHalfPower
public import PDE.Analysis.Integration.Rectangle.Tonelli

/-!
# The strain kernel on a singular square

Chen and Hou II, Supplementary material II, Section 6.1.1, bound the most singular part of `u_x`,

`S = P.V. ∫_{[-δ,δ]²} K₁(y) F(x + y) dy`,  `K₁(y) = y₁ y₂ / |y|⁴` (without `1/π`),

for a function `F = W ψ` that is `1/2`-Hölder along the first coordinate on `x + [-δ,δ]²` with
constant `A₁` and along the second coordinate on the strip `x + [-δ,δ] × (-t, t)` with constant
`A₂` (`t = min(x₂, δ)`; the strip lies in the upper half-plane, where `W` is Hölder in `x₂`). The
oddness of `K₁` in each coordinate pairs `y` with its reflection: on `|y₂| ≥ t` the horizontal
differences of `F` are at most `A₁ (2|y₁|)^{1/2}`, on `|y₂| < t` the vertical ones at most
`A₂ (2|y₂|)^{1/2}`, and the remaining integrals of `|K₁|` against a half power are the closed forms
of `PlanarKernelOneHalfPower`. The bound is stated for every measurable set `E ⊆ [-δ,δ]²` that is
symmetric under both coordinate reflections and on which `K₁ F(x + ·)` is integrable, with the
Hölder hypotheses on `x + E` only. For the principal value over the truncations `[-δ,δ]² \ B_ε`
the hypotheses are needed on `x + G` for a symmetric set `G` of full measure in `[-δ,δ]²`, so `F`
may be arbitrary on null sets such as the boundary line `{y₂ = -x₂}`, where the odd extension of
the vorticity takes its trace.

## Main results

* `abs_setIntegral_hessianKernel_zero_one_mul_le`: for `0 < t ≤ δ`,
  `|∫_E K₁(y) F(x + y) dy| ≤ √2 (A₁ (√t f_h(δ/t) - √δ f_h(1)) + A₂ (2√t - √δ f_h(t/δ)))`,
  the estimate of Supp. 6.1 for `u_x` with `I₁(t/δ)`, `I₂(t/δ)`;
* `abs_setIntegral_hessianKernel_zero_one_mul_le_of_horizontal`: with the first hypothesis
  alone, `|∫_E K₁(y) F(x + y) dy| ≤ √2 A₁ √δ (2 - f_h(1)) = 2 √(2δ) A₁ (1 - f_h(1)/2)`, the first
  estimate of Supp. 6.1, used when the square touches the boundary.
* `abs_setIntegral_hessianKernel_zero_one_mul_le_interior`: when `F` is Hölder in both directions
  on the whole square (`x₂ ≥ δ`), `0 < A₂ ≤ A₁`,
  `|∫_E K₁(y) F(x + y) dy| ≤ √2 √δ (2A₂ - A₁ f_h(A₂²/A₁²) - A₂ f_h(1))`, the "improvement for
  `x₂ ≥ δ`" of Supp. 6.1, from the four reflections and the two wedges `y₁ ≤ M y₂`,
  `M y₂ ≤ y₁` of `[0, δ]²`, `M = A₂²/A₁²`.
* `abs_le_of_tendsto_hessianKernel_zero_one_of_horizontal`,
  `abs_le_of_tendsto_hessianKernel_zero_one`,
  `abs_le_of_tendsto_hessianKernel_zero_one_interior`: the three bounds for the principal value
  `lim_{ε → 0⁺} ∫_{[-δ,δ]² \ B_ε}`, when that limit exists, with the Hölder hypotheses on a
  symmetric set of full measure.

The kernel `K₂` of `u_y` and `v_x`, whose singular-region bounds involve the principal value of
`K₂` on quadrants and the constant `C_{K₂,up}`, is not treated here.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II, Section 5.1.2, (5.13)-(5.14), and Section 6.1.1.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis PDE.Common
open scoped ENNReal

namespace PotentialTheory.Planar

/-! ### Reflections and the kernel on a quadrant -/

/-- If `D` is invariant under the reflection `coordinateReflection i`, then
`coordinateReflection i y ∈ D` if and only if `y ∈ D`. -/
private theorem reflection_mem_iff {i : Fin 2} {D : Set (ℝ^2)}
    (h : ∀ y ∈ D, coordinateReflection i y ∈ D) (y : ℝ^2) :
    coordinateReflection i y ∈ D ↔ y ∈ D := by
  refine ⟨fun hy ↦ ?_, h y⟩
  have := h _ hy
  rwa [coordinateReflection_involutive i y] at this

/-- The kernel `K₁(y) = y₁ y₂ / |y|⁴` is nonnegative on the closed first quadrant. -/
private theorem hessianKernel_zero_one_nonneg {y : ℝ^2} (h0 : 0 ≤ y 0) (h1 : 0 ≤ y 1) :
    0 ≤ hessianKernel 0 1 y := by
  rw [hessianKernel_zero_one]; positivity

/-- The function `y ↦ K₁(y) √y₁` is measurable. -/
private theorem measurable_kernel_mul_sqrt :
    Measurable fun y : ℝ^2 ↦ hessianKernel 0 1 y * √(y 0) :=
  (measurable_hessianKernel 0 1).mul
    (Real.continuous_sqrt.measurable.comp (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable)

/-- The bound integral over `[0, a] × [c, d]`:
`∫⁻ A |K₁(y)| √y₁ = A ∫₀^a (∫_c^d K₁(u, v) dv) √u du`. -/
theorem lintegral_abs_hessianKernel_zero_one_mul_sqrt {a c d A : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcd : c ≤ d) (hA : 0 ≤ A) :
    ∫⁻ y in coordinateRectangle 0 a c d, ENNReal.ofReal (A * (|hessianKernel 0 1 y| * √(y 0))) =
      ENNReal.ofReal (A * ∫ u in (0 : ℝ)..a, (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u) := by
  have hcongr : ∀ y ∈ coordinateRectangle 0 a c d,
      ENNReal.ofReal (A * (|hessianKernel 0 1 y| * √(y 0))) =
        ENNReal.ofReal (A * (hessianKernel 0 1 y * √(y 0))) := fun y hy ↦ by
    rw [abs_of_nonneg (hessianKernel_zero_one_nonneg hy.1.1 (hc.trans hy.2.1))]
  have hin : ∀ p ∈ Ioo 0 a, IntervalIntegrable
      (fun q ↦ A * (hessianKernel 0 1 !₂[p, q] * √((!₂[p, q] : ℝ^2) 0))) volume c d := by
    intro p hp
    have e : (fun q ↦ A * (hessianKernel 0 1 !₂[p, q] * √((!₂[p, q] : ℝ^2) 0))) =
        fun q ↦ A * (hessianKernel 0 1 !₂[p, q] * √p) := rfl
    rw [e]
    exact ((continuous_hessianKernel_zero_one_slice hp.1.ne').mul continuous_const
      |>.const_mul A).intervalIntegrable c d
  have hinner : ∀ p, ∫ q in c..d, A * (hessianKernel 0 1 !₂[p, q] * √((!₂[p, q] : ℝ^2) 0)) =
      A * ((∫ q in c..d, hessianKernel 0 1 !₂[p, q]) * √p) := fun p ↦ by
    have e : (fun q ↦ A * (hessianKernel 0 1 !₂[p, q] * √((!₂[p, q] : ℝ^2) 0))) =
        fun q ↦ A * (hessianKernel 0 1 !₂[p, q] * √p) := rfl
    rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  have hout : IntervalIntegrable (fun p ↦ ∫ q in c..d,
      A * (hessianKernel 0 1 !₂[p, q] * √((!₂[p, q] : ℝ^2) 0))) volume 0 a := by
    simp_rw [hinner]
    exact (intervalIntegrable_integral_hessianKernel_zero_one_mul_sqrt ha hc hcd).const_mul A
  rw [setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _) hcongr,
    lintegral_coordinateRectangle_eq ha hcd (measurable_kernel_mul_sqrt.const_mul A)
      (fun y hy ↦ mul_nonneg hA (mul_nonneg
        (hessianKernel_zero_one_nonneg hy.1.1 (hc.trans hy.2.1)) (Real.sqrt_nonneg _))) hin hout]
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]

/-- For `0 ≤ a` and `0 ≤ c ≤ d`, the bound integral `∫₀^a (∫_c^d K₁(u, v) dv) √u du` is nonnegative.
-/
private theorem integral_integral_hessianKernel_zero_one_mul_sqrt_nonneg {a c d : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hcd : c ≤ d) :
    0 ≤ ∫ u in (0 : ℝ)..a, (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u :=
  intervalIntegral.integral_nonneg ha fun _ hu ↦ mul_nonneg
    (intervalIntegral.integral_nonneg hcd fun _ hv ↦
      hessianKernel_zero_one_nonneg hu.1 (hc.trans hv.1)) (Real.sqrt_nonneg _)

/-- **The horizontal estimate.** Let `D` be a measurable set symmetric under `y₁ ↦ -y₁` with
`|y₁| ≤ a` and `c ≤ |y₂| ≤ d` on `D`, and let `K₁ F(x + ·)` be integrable on `D`. If
`|F(x + y) - F(x + R₁ y)| ≤ A √(2 y₁)` for `y ∈ D` with `y₁ > 0`, then
`|∫_D K₁(y) F(x + y) dy| ≤ 2 √2 A ∫₀^a (∫_c^d K₁(u, v) dv) √u du`. -/
theorem abs_setIntegral_hessianKernel_zero_one_mul_le_horizontal {a c d A : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hA : 0 ≤ A) {x : ℝ^2} {F : ℝ^2 → ℝ} {D : Set (ℝ^2)}
    (hD : MeasurableSet D) (hD0 : ∀ y ∈ D, coordinateReflection 0 y ∈ D)
    (hDsub : ∀ y ∈ D, |y 0| ≤ a ∧ c ≤ |y 1| ∧ |y 1| ≤ d)
    (hint : IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y)) D)
    (hF : ∀ y ∈ D, 0 < y 0 → |F (x + y) - F (x + coordinateReflection 0 y)| ≤ A * √(2 * y 0)) :
    |∫ y in D, hessianKernel 0 1 y * F (x + y)| ≤
      2 * √2 * A * ∫ u in (0 : ℝ)..a, (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u := by
  set K := hessianKernel 0 1 with hK
  set g : ℝ^2 → ℝ := fun y ↦ K y * F (x + y) with hg
  set I := ∫ u in (0 : ℝ)..a, (∫ v in c..d, K !₂[u, v]) * √u with hI
  set R : Set (ℝ^2) := coordinateRectangle 0 a c d with hR
  set B : ℝ^2 → ℝ := fun y ↦ √2 * A * (|K y| * √(y 0)) with hB
  have hI0 : 0 ≤ I := integral_integral_hessianKernel_zero_one_mul_sqrt_nonneg ha hc hcd
  -- symmetrize along the first coordinate
  have hsym : ∫ y in D, g y = ∫ y in D ∩ {y | 0 < y 0}, (g y + g (coordinateReflection 0 y)) :=
    GreenFunction.setIntegral_eq_setIntegral_pos_add_reflect 0 hD (reflection_mem_iff hD0) hint
  have hpt : ∀ y ∈ D ∩ {y | 0 < y 0}, ‖g y + g (coordinateReflection 0 y)‖ₑ ≤
      ENNReal.ofReal (B y) := by
    rintro y ⟨hyD, hy0⟩
    simp only [mem_ofPred_eq] at hy0
    have hKR : K (coordinateReflection 0 y) = -K y :=
      hessianKernel_zero_one_coordinateReflection 0 y
    have e : g y + g (coordinateReflection 0 y) =
        K y * (F (x + y) - F (x + coordinateReflection 0 y)) := by
      simp only [hg, hKR]; ring
    rw [e, Real.enorm_eq_ofReal_abs, abs_mul]
    simp only [hB]
    exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (hF y hyD hy0)
      (abs_nonneg _)).trans_eq (by rw [Real.sqrt_mul (by norm_num)]; ring))
  -- the region `D ∩ {y₁ > 0}` lies in `R ∪ R₂⁻¹ R`
  have hsub : D ∩ {y | 0 < y 0} ⊆ R ∪ coordinateReflection 1 ⁻¹' R := by
    rintro y ⟨hyD, hy0⟩
    simp only [mem_ofPred_eq] at hy0
    obtain ⟨h0, h1, h2⟩ := hDsub y hyD
    rcases le_total 0 (y 1) with hy1 | hy1
    · left
      rw [abs_of_nonneg hy1] at h1 h2
      exact ⟨⟨hy0.le, (le_abs_self _).trans h0⟩, h1, h2⟩
    · right
      rw [abs_of_nonpos hy1] at h1 h2
      simp only [mem_preimage, hR, mem_coordinateRectangle, mem_Icc,
        coordinateReflection_apply_same,
        coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)]
      exact ⟨⟨hy0.le, (le_abs_self _).trans h0⟩, h1, h2⟩
  have hBR : ∀ y, B (coordinateReflection 1 y) = B y := fun y ↦ by
    simp only [hB, hK, hessianKernel_zero_one_coordinateReflection, abs_neg,
      coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)]
  have hrefl : ∫⁻ y in coordinateReflection 1 ⁻¹' R, ENNReal.ofReal (B y) =
      ∫⁻ y in R, ENNReal.ofReal (B y) := by
    have := (measurePreserving_coordinateReflection (n := 2) 1).setLIntegral_comp_preimage_emb
      (coordinateReflectionLinearIsometryEquiv (n := 2) 1).toMeasurableEquiv.measurableEmbedding
      (fun y ↦ ENNReal.ofReal (B y)) R
    simpa only [hBR] using this
  have hRval : ∫⁻ y in R, ENNReal.ofReal (B y) = ENNReal.ofReal (√2 * A * I) :=
    lintegral_abs_hessianKernel_zero_one_mul_sqrt ha hc hcd (by positivity)
  have hmain : ‖∫ y in D, g y‖ₑ ≤ ENNReal.ofReal (2 * √2 * A * I) := by
    calc ‖∫ y in D, g y‖ₑ
        = ‖∫ y in D ∩ {y | 0 < y 0}, (g y + g (coordinateReflection 0 y))‖ₑ := by rw [hsym]
      _ ≤ ∫⁻ y in D ∩ {y | 0 < y 0}, ‖g y + g (coordinateReflection 0 y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y in D ∩ {y | 0 < y 0}, ENNReal.ofReal (B y) :=
          setLIntegral_mono' (hD.inter (measurableSet_lt measurable_const
            (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable)) hpt
      _ ≤ ∫⁻ y in R ∪ coordinateReflection 1 ⁻¹' R, ENNReal.ofReal (B y) :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ y in R, ENNReal.ofReal (B y)) +
            ∫⁻ y in coordinateReflection 1 ⁻¹' R, ENNReal.ofReal (B y) :=
          lintegral_union_le _ _ _
      _ = ENNReal.ofReal (2 * √2 * A * I) := by
          rw [hrefl, hRval, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  rw [Real.enorm_eq_ofReal_abs] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain

/-! ### The vertical estimate, by the coordinate swap -/

/-- The coordinate swap `(y₁, y₂) ↦ (y₂, y₁)`. -/
private abbrev swap : ℝ^2 ≃ₗᵢ[ℝ] ℝ^2 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

/-- The coordinate swap is an involution. -/
private theorem swap_swap (z : ℝ^2) : swap (swap z) = z := by
  ext i; fin_cases i <;> simp [(coordinateSwap_apply _).1, (coordinateSwap_apply _).2]

/-- The coordinate swap turns the reflection `y₁ ↦ -y₁` into the reflection `y₂ ↦ -y₂`:
`swap (R₁ z) = R₂ (swap z)`. -/
private theorem swap_reflection_zero (z : ℝ^2) :
    swap (coordinateReflection 0 z) = coordinateReflection 1 (swap z) := by
  ext i; fin_cases i <;>
    simp [(coordinateSwap_apply _).1, (coordinateSwap_apply _).2,
      coordinateReflection_apply_same]

/-- **The vertical estimate.** Let `D` be a measurable set symmetric under `y₂ ↦ -y₂` with
`|y₂| ≤ a` and `c ≤ |y₁| ≤ d` on `D`, and let `K₁ F(x + ·)` be integrable on `D`. If
`|F(x + y) - F(x + R₂ y)| ≤ A √(2 y₂)` for `y ∈ D` with `y₂ > 0`, then
`|∫_D K₁(y) F(x + y) dy| ≤ 2 √2 A ∫₀^a (∫_c^d K₁(u, v) dv) √u du`. -/
theorem abs_setIntegral_hessianKernel_zero_one_mul_le_vertical {a c d A : ℝ} (ha : 0 ≤ a)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hA : 0 ≤ A) {x : ℝ^2} {F : ℝ^2 → ℝ} {D : Set (ℝ^2)}
    (hD : MeasurableSet D) (hD1 : ∀ y ∈ D, coordinateReflection 1 y ∈ D)
    (hDsub : ∀ y ∈ D, |y 1| ≤ a ∧ c ≤ |y 0| ∧ |y 0| ≤ d)
    (hint : IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y)) D)
    (hF : ∀ y ∈ D, 0 < y 1 → |F (x + y) - F (x + coordinateReflection 1 y)| ≤ A * √(2 * y 1)) :
    |∫ y in D, hessianKernel 0 1 y * F (x + y)| ≤
      2 * √2 * A * ∫ u in (0 : ℝ)..a, (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u := by
  have hmp : MeasurePreserving (swap : ℝ^2 → ℝ^2) volume volume := swap.measurePreserving
  have hemb : MeasurableEmbedding (swap : ℝ^2 → ℝ^2) :=
    swap.toMeasurableEquiv.measurableEmbedding
  have hS0 : ∀ z : ℝ^2, swap z 0 = z 1 := fun z ↦ (coordinateSwap_apply z).1
  have hS1 : ∀ z : ℝ^2, swap z 1 = z 0 := fun z ↦ (coordinateSwap_apply z).2
  have hadd : ∀ z : ℝ^2, x + swap z = swap (swap x + z) := fun z ↦ by
    rw [map_add, swap_swap]
  set F' : ℝ^2 → ℝ := fun z ↦ F (swap z) with hF'
  have hfun : ∀ z, hessianKernel 0 1 (swap z) * F (x + swap z) =
      hessianKernel 0 1 z * F' (swap x + z) := fun z ↦ by
    rw [hessianKernel_zero_one_swap, hadd]
  have hchange : ∫ y in D, hessianKernel 0 1 y * F (x + y) =
      ∫ z in swap ⁻¹' D, hessianKernel 0 1 z * F' (swap x + z) := by
    rw [← hmp.setIntegral_preimage_emb hemb]
    simp only [hfun]
  rw [hchange]
  refine abs_setIntegral_hessianKernel_zero_one_mul_le_horizontal ha hc hcd hA
    (hD.preimage swap.continuous.measurable) (fun z hz ↦ ?_) (fun z hz ↦ ?_) ?_ (fun z hz hz0 ↦ ?_)
  · simp only [mem_preimage, swap_reflection_zero] at hz ⊢
    exact hD1 _ hz
  · obtain ⟨h1, h2, h3⟩ := hDsub _ hz
    rw [hS1] at h1
    rw [hS0] at h2 h3
    exact ⟨h1, h2, h3⟩
  · have := (hmp.integrableOn_comp_preimage hemb).2 hint
    refine this.congr_fun (fun z _ ↦ ?_) (hD.preimage swap.continuous.measurable)
    simp only [Function.comp_apply]
    exact hfun z
  · simp only [mem_preimage] at hz
    have h := hF _ hz (by rw [hS1]; exact hz0)
    rw [hS1] at h
    simp only [hF']
    rw [← hadd z, ← hadd (coordinateReflection 0 z), swap_reflection_zero]
    exact h

/-! ### The estimates of Supplementary Section 6.1 -/

/-- The square `[-δ,δ]²` is invariant under `y₁ ↦ -y₁`. -/
private theorem reflection_zero_mem_square {δ : ℝ} {y : ℝ^2}
    (hy : y ∈ coordinateRectangle (-δ) δ (-δ) δ) :
    coordinateReflection 0 y ∈ coordinateRectangle (-δ) δ (-δ) δ := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [coordinateReflection_apply_same,
      coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide)] <;> linarith

/-- The square `[-δ,δ]²` is invariant under `y₂ ↦ -y₂`. -/
private theorem reflection_one_mem_square {δ : ℝ} {y : ℝ^2}
    (hy : y ∈ coordinateRectangle (-δ) δ (-δ) δ) :
    coordinateReflection 1 y ∈ coordinateRectangle (-δ) δ (-δ) δ := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [coordinateReflection_apply_same,
      coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)] <;> linarith

/-- Both coordinates of a point of `[-δ,δ]²` have absolute value at most `δ`. -/
private theorem abs_le_of_mem_square {δ : ℝ} {y : ℝ^2}
    (hy : y ∈ coordinateRectangle (-δ) δ (-δ) δ) : |y 0| ≤ δ ∧ |y 1| ≤ δ :=
  ⟨abs_le.2 hy.1, abs_le.2 hy.2⟩

/-- If `D` is invariant under `y₁ ↦ -y₁` and `F` is `1/2`-Hölder along `x₁` on `x + D` with constant
`A`, then `|F(x + y) - F(x + R₁ y)| ≤ A √(2 y₁)` for `y ∈ D` with `y₁ > 0`. -/
private theorem horizontal_holder {A : ℝ} {x : ℝ^2} {F : ℝ^2 → ℝ} {D : Set (ℝ^2)}
    (hD : ∀ y ∈ D, coordinateReflection 0 y ∈ D)
    (hF : ∀ y ∈ D, ∀ y' ∈ D, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A * √|y 0 - y' 0|)
    {y : ℝ^2} (hy : y ∈ D) (hy0 : 0 < y 0) :
    |F (x + y) - F (x + coordinateReflection 0 y)| ≤ A * √(2 * y 0) := by
  have h := hF y hy _ (hD y hy)
    (by rw [coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide)])
  rwa [coordinateReflection_apply_same, sub_neg_eq_add, ← two_mul,
    abs_of_pos (show 0 < 2 * y 0 by linarith)] at h

/-- **The singular square for `u_x` at the boundary**, Chen and Hou II, Supp. 6.1, first
estimate: for a measurable `E ⊆ [-δ,δ]²` symmetric under `y₁ ↦ -y₁` on which `K₁ F(x + ·)` is
integrable, if `F` is `1/2`-Hölder along `x₁` on `x + E` with constant `A`, then
`|∫_E K₁(y) F(x + y) dy| ≤ √2 A √δ (2 - f_h(1))`, that is `2 √(2δ) A (1 - f_h(1)/2)`. -/
theorem abs_setIntegral_hessianKernel_zero_one_mul_le_of_horizontal {δ A : ℝ} (hδ : 0 < δ)
    (hA : 0 ≤ A) {x : ℝ^2} {F : ℝ^2 → ℝ} {E : Set (ℝ^2)} (hE : MeasurableSet E)
    (hEQ : E ⊆ coordinateRectangle (-δ) δ (-δ) δ)
    (hE0 : ∀ y ∈ E, coordinateReflection 0 y ∈ E)
    (hint : IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y)) E)
    (hF : ∀ y ∈ E, ∀ y' ∈ E, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A * √|y 0 - y' 0|) :
    |∫ y in E, hessianKernel 0 1 y * F (x + y)| ≤
      √2 * A * (√δ * (2 - threeHalvesPowerIntegral 1)) := by
  have h := abs_setIntegral_hessianKernel_zero_one_mul_le_horizontal hδ.le le_rfl hδ.le hA hE hE0
    (fun y hy ↦ ⟨(abs_le_of_mem_square (hEQ hy)).1, abs_nonneg _,
      (abs_le_of_mem_square (hEQ hy)).2⟩) hint
    (fun y hy hy0 ↦ horizontal_holder hE0 hF hy hy0)
  rw [integral_integral_hessianKernel_zero_one_mul_sqrt_self hδ] at h
  linarith

/-- By the symmetry `K₁(u, v) = K₁(v, u)`, the bound integral `∫₀^a (∫_c^d K₁(u, v) dv) √u du`
equals `∫₀^a (∫_c^d K₁(u, v) du) √v dv`. -/
private theorem integral_integral_hessianKernel_zero_one_mul_sqrt_comm (a c d : ℝ) :
    ∫ u in (0 : ℝ)..a, (∫ v in c..d, hessianKernel 0 1 !₂[u, v]) * √u =
      ∫ v in (0 : ℝ)..a, (∫ u in c..d, hessianKernel 0 1 !₂[u, v]) * √v := by
  congr 1; ext w; congr 1; congr 1; ext z
  simp only [hessianKernel_zero_one_toLp]; ring

/-- **The singular square for `u_x`**, Chen and Hou II, Supp. 6.1: let `0 < t ≤ δ` and let
`E ⊆ [-δ,δ]²` be measurable, symmetric under both coordinate reflections, with `K₁ F(x + ·)`
integrable on `E`. If `F` is `1/2`-Hölder along `x₁` on `x + E` with constant `A₁ ≥ 0` and along
`x₂` on `x + (E ∩ {|y₂| < t})` with constant `A₂ ≥ 0`, then
`|∫_E K₁(y) F(x + y) dy| ≤ √2 (A₁ (√t f_h(δ/t) - √δ f_h(1)) + A₂ (2√t - √δ f_h(t/δ)))`,
that is `2 √(2δ) (A₁ I₁(t/δ) + A₂ I₂(t/δ))` with the integrals `I₁`, `I₂` of the supplement.
For `t = min(x₂, δ)` the strip `x + [-δ,δ] × (-t, t)` lies in the open upper half-plane, where
`[F]_{C_y}` is available. -/
theorem abs_setIntegral_hessianKernel_zero_one_mul_le {δ t A₁ A₂ : ℝ} (ht : 0 < t) (htδ : t ≤ δ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) {x : ℝ^2} {F : ℝ^2 → ℝ} {E : Set (ℝ^2)}
    (hE : MeasurableSet E) (hEQ : E ⊆ coordinateRectangle (-δ) δ (-δ) δ)
    (hE0 : ∀ y ∈ E, coordinateReflection 0 y ∈ E) (hE1 : ∀ y ∈ E, coordinateReflection 1 y ∈ E)
    (hint : IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y)) E)
    (hF₀ : ∀ y ∈ E, ∀ y' ∈ E, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A₁ * √|y 0 - y' 0|)
    (hF₁ : ∀ y ∈ E, ∀ y' ∈ E, |y 1| < t → |y' 1| < t → y 0 = y' 0 →
      |F (x + y) - F (x + y')| ≤ A₂ * √|y 1 - y' 1|) :
    |∫ y in E, hessianKernel 0 1 y * F (x + y)| ≤
      √2 * (A₁ * (√t * threeHalvesPowerIntegral (δ / t) - √δ * threeHalvesPowerIntegral 1) +
        A₂ * (2 * √t - √δ * threeHalvesPowerIntegral (t / δ))) := by
  have hδ : 0 < δ := ht.trans_le htδ
  set S : Set (ℝ^2) := {y | |y 1| < t} with hS
  have hmS : MeasurableSet S :=
    measurableSet_lt (continuous_abs.comp (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous).measurable
      measurable_const
  have hsplit := integral_inter_add_sdiff (μ := volume) hmS hint
  rw [← hsplit]
  -- the outer part `|y₂| ≥ t`, by horizontal pairs
  have h1 := abs_setIntegral_hessianKernel_zero_one_mul_le_horizontal hδ.le ht.le htδ hA₁
    (hE.diff hmS) (fun y hy ↦ ⟨hE0 _ hy.1, by
      simpa [hS, coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide)] using hy.2⟩)
    (fun y hy ↦ ⟨(abs_le_of_mem_square (hEQ hy.1)).1, by simpa [hS] using hy.2,
      (abs_le_of_mem_square (hEQ hy.1)).2⟩) (hint.mono_set sdiff_subset)
    (fun y hy hy0 ↦ horizontal_holder hE0 hF₀ hy.1 hy0)
  rw [integral_integral_hessianKernel_zero_one_mul_sqrt ht htδ] at h1
  -- the strip `|y₂| < t`, by vertical pairs
  have h2 := abs_setIntegral_hessianKernel_zero_one_mul_le_vertical ht.le le_rfl hδ.le hA₂
    (hE.inter hmS) (fun y hy ↦ ⟨hE1 _ hy.1, by
      simpa [hS, coordinateReflection_apply_same] using hy.2⟩)
    (fun y hy ↦ ⟨hy.2.le, abs_nonneg _, (abs_le_of_mem_square (hEQ hy.1)).1⟩)
    (hint.mono_set inter_subset_left) (fun y hy hy1 ↦ ?_)
  · rw [integral_integral_hessianKernel_zero_one_mul_sqrt_comm,
      integral_integral_hessianKernel_zero_one_mul_sqrt_left hδ ht.le] at h2
    calc |(∫ y in E ∩ S, hessianKernel 0 1 y * F (x + y)) +
          ∫ y in E \ S, hessianKernel 0 1 y * F (x + y)|
        ≤ |∫ y in E ∩ S, hessianKernel 0 1 y * F (x + y)| +
            |∫ y in E \ S, hessianKernel 0 1 y * F (x + y)| := abs_add_le _ _
      _ ≤ _ := by linarith
  · have hyS : |y 1| < t := hy.2
    have h := hF₁ y hy.1 _ (hE1 _ hy.1) hyS
      (by rwa [coordinateReflection_apply_same, abs_neg])
      (by rw [coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)])
    rwa [coordinateReflection_apply_same, sub_neg_eq_add, ← two_mul,
      abs_of_pos (show 0 < 2 * y 1 by linarith)] at h

/-! ### The interior square -/

/-- The wedge `{y ∈ [0, δ]² | m y₁ ≤ y₂}`. -/
private def wedge (δ m : ℝ) : Set (ℝ^2) := {y | y ∈ coordinateRectangle 0 δ 0 δ ∧ m * y 0 ≤ y 1}

/-- The wedge `{y ∈ [0, δ]² | m y₁ ≤ y₂}` is measurable. -/
private theorem measurableSet_wedge (δ m : ℝ) : MeasurableSet (wedge δ m) :=
  (measurableSet_coordinateRectangle 0 δ 0 δ).inter (measurableSet_le
    (measurable_const.mul (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable)
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.measurable)

/-- The inner integral over the wedge: `∫_{m u}^δ K₁(u, v) dv · √u` in closed form. -/
private theorem integral_wedge_mul_sqrt_eq {δ m u : ℝ} (hδ : 0 < δ) (hm : 0 < m) (hu : 0 ≤ u) :
    (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      1 / (1 + m ^ 2) * (1 / (2 * √u)) - (u * √u / (δ ^ 2 + u ^ 2)) / 2 := by
  rcases hu.eq_or_lt with rfl | hu
  · simp [hessianKernel_zero_one_toLp]
  have hmu : 0 < m * u := mul_pos hm hu
  rw [integral_hessianKernel_zero_one_right fun v hv ↦ by
    have : 0 < v := by
      rcases le_total (m * u) δ with h | h
      · rw [uIcc_of_le h] at hv; linarith [hv.1]
      · rw [uIcc_of_ge h] at hv; linarith [hv.1]
    positivity]
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 < r ∧ u = r ^ 2 :=
    ⟨√u, Real.sqrt_pos.mpr hu, (Real.sq_sqrt hu.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  field_simp
  ring

/-- The wedge integral `∫₀^a (∫_{m u}^δ K₁(u, v) dv) √u du = √a/(1 + m²) - √δ f_h(a/δ)/2`. -/
private theorem integral_integral_wedge {δ m a : ℝ} (hδ : 0 < δ) (hm : 0 < m) (ha : 0 ≤ a) :
    ∫ u in (0 : ℝ)..a, (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u =
      √a / (1 + m ^ 2) - √δ * threeHalvesPowerIntegral (a / δ) / 2 := by
  have hcongr : EqOn (fun u ↦ (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u)
      (fun u ↦ 1 / (1 + m ^ 2) * (1 / (2 * √u)) - (u * √u / (δ ^ 2 + u ^ 2)) / 2) (uIcc 0 a) :=
    fun u hu ↦ integral_wedge_mul_sqrt_eq hδ hm (by rw [uIcc_of_le ha] at hu; exact hu.1)
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_sub
      ((intervalIntegrable_inv_two_sqrt ha).const_mul _)
      (((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 a).div_const 2),
    intervalIntegral.integral_const_mul, integral_inv_two_sqrt ha, intervalIntegral.integral_div,
    integral_mul_sqrt_div_sq_add_sq hδ]
  ring

/-- For `δ, m > 0` and `a ≥ 0`, the function `u ↦ (∫_{m u}^δ K₁(u, v) dv) √u` is interval integrable
on `[0, a]`. -/
private theorem intervalIntegrable_integral_wedge {δ m a : ℝ} (hδ : 0 < δ) (hm : 0 < m)
    (ha : 0 ≤ a) :
    IntervalIntegrable (fun u ↦ (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u) volume 0 a := by
  have h := ((intervalIntegrable_inv_two_sqrt ha).const_mul (1 / (1 + m ^ 2))).sub
    (((continuous_mul_sqrt_div_sq_add_sq hδ.ne').intervalIntegrable 0 a).div_const 2)
  refine h.congr_ae ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  refine Filter.Eventually.of_forall fun u hu ↦ ?_
  rw [uIoc_of_le ha] at hu
  exact (integral_wedge_mul_sqrt_eq hδ hm hu.1.le).symm

/-- **The wedge**: for `δ, m > 0` and `C ≥ 0`, with `a = min δ (δ/m)`,
`∫⁻_{y ∈ [0,δ]², m y₁ ≤ y₂} C K₁(y) √y₁ = C ∫₀^a (∫_{m u}^δ K₁(u, v) dv) √u du`. -/
private theorem lintegral_wedge {δ m C : ℝ} (hδ : 0 < δ) (hm : 0 < m) (hC : 0 ≤ C) :
    ∫⁻ y in wedge δ m, ENNReal.ofReal (C * (hessianKernel 0 1 y * √(y 0))) =
      ENNReal.ofReal (C * ∫ u in (0 : ℝ)..min δ (δ / m),
        (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u) := by
  set a := min δ (δ / m) with ha
  have ha0 : 0 ≤ a := le_min hδ.le (div_nonneg hδ.le hm.le)
  have haδ : a ≤ δ := min_le_left _ _
  have hma : m * a ≤ δ :=
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hm.le).trans_eq (mul_div_cancel₀ _ hm.ne')
  set g : ℝ^2 → ℝ := fun y ↦ C * (hessianKernel 0 1 y * √(y 0)) with hg
  set R := coordinateRectangle 0 a 0 δ with hR
  have hWR : wedge δ m ⊆ R := by
    rintro y ⟨⟨⟨h0, h1⟩, h2, h3⟩, h4⟩
    refine ⟨⟨h0, le_min h1 ?_⟩, h2, h3⟩
    rw [le_div_iff₀ hm, mul_comm]; exact h4.trans h3
  have hind : ∀ y, (wedge δ m).indicator (fun y ↦ ENNReal.ofReal (g y)) y =
      ENNReal.ofReal ((wedge δ m).indicator g y) := fun y ↦ by
    by_cases hy : y ∈ wedge δ m <;> simp [hy]
  have hstep : ∫⁻ y in wedge δ m, ENNReal.ofReal (g y) =
      ∫⁻ y in R, ENNReal.ofReal ((wedge δ m).indicator g y) := by
    rw [← funext hind, setLIntegral_indicator (measurableSet_wedge δ m), inter_eq_left.2 hWR]
  rw [hstep]
  -- the inner integrals
  have hmem : ∀ p q : ℝ, p ∈ Icc 0 a → q ∈ Icc 0 δ →
      ((!₂[p, q] : ℝ^2) ∈ wedge δ m ↔ m * p ≤ q) := fun p q hp hq ↦
    ⟨fun h ↦ h.2, fun h ↦ ⟨⟨⟨hp.1, hp.2.trans haδ⟩, hq⟩, h⟩⟩
  have hinner : ∀ p ∈ Icc 0 a,
      IntervalIntegrable (fun q ↦ (wedge δ m).indicator g !₂[p, q]) volume 0 δ ∧
      ∫ q in (0 : ℝ)..δ, (wedge δ m).indicator g !₂[p, q] =
        C * ((∫ q in m * p..δ, hessianKernel 0 1 !₂[p, q]) * √p) := by
    intro p hp
    have hmp0 : 0 ≤ m * p := mul_nonneg hm.le hp.1
    have hmpδ : m * p ≤ δ := (mul_le_mul_of_nonneg_left hp.2 hm.le).trans hma
    have hzero : ∀ᵐ q, q ∈ uIoc 0 (m * p) → (wedge δ m).indicator g !₂[p, q] = 0 := by
      filter_upwards [Measure.ae_ne volume (m * p)] with q hq hqI
      rw [uIoc_of_le hmp0] at hqI
      exact Set.indicator_of_notMem (fun hw ↦ (not_le.2 (lt_of_le_of_ne hqI.2 hq))
        ((hmem p q hp ⟨hqI.1.le, hqI.2.trans hmpδ⟩).1 hw)) _
    have h1 : ∫ q in (0 : ℝ)..m * p, (wedge δ m).indicator g !₂[p, q] = 0 :=
      intervalIntegral.integral_zero_ae hzero
    have h2 : ∫ q in m * p..δ, (wedge δ m).indicator g !₂[p, q] =
        ∫ q in m * p..δ, C * (hessianKernel 0 1 !₂[p, q] * √p) := by
      refine intervalIntegral.integral_congr fun q hq ↦ ?_
      rw [uIcc_of_le hmpδ] at hq
      rw [Set.indicator_of_mem ((hmem p q hp ⟨hmp0.trans hq.1, hq.2⟩).2 hq.1)]
      rfl
    have hint1 :
        IntervalIntegrable (fun q ↦ (wedge δ m).indicator g !₂[p, q]) volume 0 (m * p) := by
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      exact hzero.mono fun q h hq ↦ (h hq).symm
    have hint2 :
        IntervalIntegrable (fun q ↦ (wedge δ m).indicator g !₂[p, q]) volume (m * p) δ := by
      rcases hp.1.eq_or_lt with hp0 | hp0
      · subst hp0
        refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun q _ ↦ ?_
        by_cases hw : (!₂[(0 : ℝ), q] : ℝ^2) ∈ wedge δ m
        · simp [Set.indicator_of_mem hw, hg]
        · simp [Set.indicator_of_notMem hw]
      refine (((continuous_hessianKernel_zero_one_slice hp0.ne').mul
        (continuous_const (y := √p)) |>.const_mul C).intervalIntegrable (m * p) δ).congr
        fun q hq ↦ ?_
      rw [uIoc_of_le hmpδ] at hq
      simp only [Pi.mul_apply]
      rw [Set.indicator_of_mem ((hmem p q hp ⟨hmp0.trans hq.1.le, hq.2⟩).2 hq.1.le)]
      rfl
    refine ⟨hint1.trans hint2, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2, h1, zero_add, h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const]
  have hgR : ∀ y ∈ R, 0 ≤ (wedge δ m).indicator g y := fun y _ ↦ Set.indicator_nonneg
    (fun a ha ↦ mul_nonneg hC (mul_nonneg (hessianKernel_zero_one_nonneg ha.1.1.1 ha.1.2.1)
      (Real.sqrt_nonneg _))) y
  have hmeas : Measurable ((wedge δ m).indicator g) :=
    (measurable_kernel_mul_sqrt.const_mul C).indicator (measurableSet_wedge δ m)
  have hout : IntervalIntegrable (fun p ↦ ∫ q in (0 : ℝ)..δ, (wedge δ m).indicator g !₂[p, q])
      volume 0 a := by
    refine ((intervalIntegrable_integral_wedge hδ hm ha0).const_mul C).congr fun p hp ↦ ?_
    rw [uIoc_of_le ha0] at hp
    exact ((hinner p ⟨hp.1.le, hp.2⟩).2).symm
  rw [lintegral_coordinateRectangle_eq ha0 hδ.le hmeas hgR
    (fun p hp ↦ (hinner p ⟨hp.1.le, hp.2.le⟩).1) hout]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun p hp ↦ ?_
  rw [uIcc_of_le ha0] at hp
  exact (hinner p hp).2

/-- For `m > 0`, `a ≥ 0` and `m a ≤ δ`, the wedge integral `∫₀^a (∫_{m u}^δ K₁(u, v) dv) √u du` is
nonnegative. -/
private theorem integral_integral_wedge_nonneg {δ m a : ℝ} (hm : 0 < m) (ha : 0 ≤ a)
    (hma : m * a ≤ δ) :
    0 ≤ ∫ u in (0 : ℝ)..a, (∫ v in m * u..δ, hessianKernel 0 1 !₂[u, v]) * √u :=
  intervalIntegral.integral_nonneg ha fun _ hu ↦ mul_nonneg
    (intervalIntegral.integral_nonneg ((mul_le_mul_of_nonneg_left hu.2 hm.le).trans hma)
      fun _ hv ↦ hessianKernel_zero_one_nonneg hu.1
        ((mul_nonneg hm.le hu.1).trans hv.1)) (Real.sqrt_nonneg _)

/-- If `D` is invariant under `y₂ ↦ -y₂` and `F` is `1/2`-Hölder along `x₂` on `x + D` with constant
`A`, then `|F(x + y) - F(x + R₂ y)| ≤ A √(2 y₂)` for `y ∈ D` with `y₂ > 0`. -/
private theorem vertical_holder {A : ℝ} {x : ℝ^2} {F : ℝ^2 → ℝ} {D : Set (ℝ^2)}
    (hD : ∀ y ∈ D, coordinateReflection 1 y ∈ D)
    (hF : ∀ y ∈ D, ∀ y' ∈ D, y 0 = y' 0 → |F (x + y) - F (x + y')| ≤ A * √|y 1 - y' 1|)
    {y : ℝ^2} (hy : y ∈ D) (hy1 : 0 < y 1) :
    |F (x + y) - F (x + coordinateReflection 1 y)| ≤ A * √(2 * y 1) := by
  have h := hF y hy _ (hD y hy)
    (by rw [coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide)])
  rwa [coordinateReflection_apply_same, sub_neg_eq_add, ← two_mul,
    abs_of_pos (show 0 < 2 * y 1 by linarith)] at h

/-- **The singular square for `u_x` away from the boundary**, Chen and Hou II, Supp. 6.1,
"Improvement for `x₂ ≥ δ`": for a measurable `E ⊆ [-δ,δ]²` symmetric under both coordinate
reflections on which `K₁ F(x + ·)` is integrable, if `F` is `1/2`-Hölder on `x + E` along `x₁`
with constant `A₁` and along `x₂` with constant `A₂`, `0 < A₂ ≤ A₁`, then
`|∫_E K₁(y) F(x + y) dy| ≤ √2 √δ (2A₂ - A₁ f_h(A₂²/A₁²) - A₂ f_h(1))`. The four reflections of
`y` give differences of `F` at most `2 √2 min(A₁ √y₁, A₂ √y₂)`; the two wedges of `[0,δ]²` where
each term is the smaller one carry the closed forms. -/
theorem abs_setIntegral_hessianKernel_zero_one_mul_le_interior {δ A₁ A₂ : ℝ} (hδ : 0 < δ)
    (hA₂ : 0 < A₂) (hA : A₂ ≤ A₁) {x : ℝ^2} {F : ℝ^2 → ℝ} {E : Set (ℝ^2)}
    (hE : MeasurableSet E) (hEQ : E ⊆ coordinateRectangle (-δ) δ (-δ) δ)
    (hE0 : ∀ y ∈ E, coordinateReflection 0 y ∈ E) (hE1 : ∀ y ∈ E, coordinateReflection 1 y ∈ E)
    (hint : IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y)) E)
    (hF₀ : ∀ y ∈ E, ∀ y' ∈ E, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A₁ * √|y 0 - y' 0|)
    (hF₁ : ∀ y ∈ E, ∀ y' ∈ E, y 0 = y' 0 → |F (x + y) - F (x + y')| ≤ A₂ * √|y 1 - y' 1|) :
    |∫ y in E, hessianKernel 0 1 y * F (x + y)| ≤
      √2 * √δ * (2 * A₂ - A₁ * threeHalvesPowerIntegral (A₂ ^ 2 / A₁ ^ 2) -
        A₂ * threeHalvesPowerIntegral 1) := by
  set K := hessianKernel 0 1 with hK
  set g : ℝ^2 → ℝ := fun y ↦ K y * F (x + y) with hg
  set R0 := coordinateReflection (n := 2) 0
  set R1 := coordinateReflection (n := 2) 1
  have hA₁ : 0 < A₁ := hA₂.trans_le hA
  set M := A₂ ^ 2 / A₁ ^ 2 with hM
  have hM0 : 0 < M := by positivity
  have hM1 : M ≤ 1 := by rw [hM, div_le_one (by positivity)]; nlinarith
  have hsM : √M = A₂ / A₁ := by
    rw [hM, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hA₂.le, Real.sqrt_sq hA₁.le]
  have hR0b : ∀ y : ℝ^2, R0 y 1 = y 1 := fun y ↦
    coordinateReflection_apply_of_ne (n := 2) 0 1 (by decide) y
  have hR1b : ∀ y : ℝ^2, R1 y 0 = y 0 := fun y ↦
    coordinateReflection_apply_of_ne (n := 2) 1 0 (by decide) y
  -- first symmetrization
  have hs0 : ∫ y in E, g y = ∫ y in E ∩ {y | 0 < y 0}, (g y + g (R0 y)) :=
    GreenFunction.setIntegral_eq_setIntegral_pos_add_reflect 0 hE (reflection_mem_iff hE0) hint
  set D := E ∩ {y : ℝ^2 | 0 < y 0} with hDdef
  have hD : MeasurableSet D := hE.inter
    (measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.measurable)
  have hD1 : ∀ y ∈ D, R1 y ∈ D := fun y hy ↦
    ⟨hE1 _ hy.1, by simpa only [mem_ofPred_eq, hR1b] using hy.2⟩
  have hgR0 : IntegrableOn (fun y ↦ g (R0 y)) D :=
    ((measurePreserving_coordinateReflection (n := 2) 0).integrableOn_comp_preimage
      (coordinateReflectionLinearIsometryEquiv (n := 2) 0).toMeasurableEquiv.measurableEmbedding
      |>.2 hint).mono_set fun y hy ↦ hE0 _ hy.1
  have hs1 : ∫ y in D, (g y + g (R0 y)) =
      ∫ y in D ∩ {y | 0 < y 1}, (g y + g (R0 y) + (g (R1 y) + g (R0 (R1 y)))) :=
    GreenFunction.setIntegral_eq_setIntegral_pos_add_reflect 1 hD (reflection_mem_iff hD1)
      ((hint.mono_set inter_subset_left).add hgR0)
  rw [hs0, hs1]
  -- the pointwise bound
  set B : ℝ^2 → ℝ := fun y ↦ 2 * √2 * (K y * min (A₁ * √(y 0)) (A₂ * √(y 1))) with hB
  have hpt : ∀ y ∈ D ∩ {y : ℝ^2 | 0 < y 1},
      ‖g y + g (R0 y) + (g (R1 y) + g (R0 (R1 y)))‖ₑ ≤ ENNReal.ofReal (B y) := by
    rintro y ⟨⟨hyE, hy0⟩, hy1⟩
    simp only [mem_ofPred_eq] at hy0 hy1
    have e : g y + g (R0 y) + (g (R1 y) + g (R0 (R1 y))) =
        K y * ((F (x + y) - F (x + R0 y)) - (F (x + R1 y) - F (x + R0 (R1 y)))) := by
      simp only [hg, hK, R0, R1, hessianKernel_zero_one_coordinateReflection]; ring
    have hh1 : |F (x + y) - F (x + R0 y)| ≤ A₁ * √(2 * y 0) := horizontal_holder hE0 hF₀ hyE hy0
    have hh2 : |F (x + R1 y) - F (x + R0 (R1 y))| ≤ A₁ * √(2 * y 0) := by
      have := horizontal_holder hE0 hF₀ (hE1 _ hyE) (by rw [hR1b]; exact hy0)
      rwa [hR1b] at this
    have hv1 : |F (x + y) - F (x + R1 y)| ≤ A₂ * √(2 * y 1) := vertical_holder hE1 hF₁ hyE hy1
    have hv2 : |F (x + R0 y) - F (x + R0 (R1 y))| ≤ A₂ * √(2 * y 1) := by
      have := vertical_holder hE1 hF₁ (hE0 _ hyE) (by rw [hR0b]; exact hy1)
      rwa [hR0b, ← GreenFunction.coordinateReflection_comm] at this
    rw [Real.sqrt_mul (by norm_num)] at hh1 hh2 hv1 hv2
    have hbr : |(F (x + y) - F (x + R0 y)) - (F (x + R1 y) - F (x + R0 (R1 y)))| ≤
        2 * √2 * min (A₁ * √(y 0)) (A₂ * √(y 1)) := by
      rw [mul_min_of_nonneg _ _ (by positivity)]
      refine le_min ((abs_sub _ _).trans (by linarith)) ?_
      rw [show (F (x + y) - F (x + R0 y)) - (F (x + R1 y) - F (x + R0 (R1 y))) =
        (F (x + y) - F (x + R1 y)) - (F (x + R0 y) - F (x + R0 (R1 y))) by ring]
      exact (abs_sub _ _).trans (by linarith)
    have hKy : 0 ≤ K y := hessianKernel_zero_one_nonneg hy0.le hy1.le
    rw [e, Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hKy]
    exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left hbr hKy).trans_eq (by ring))
  -- cover by two wedges
  have hcov : D ∩ {y : ℝ^2 | 0 < y 1} ⊆ wedge δ (1 / M) ∪ swap ⁻¹' wedge δ M := by
    rintro y ⟨⟨hyE, hy0⟩, hy1⟩
    simp only [mem_ofPred_eq] at hy0 hy1
    obtain ⟨⟨_, h2⟩, _, h4⟩ := hEQ hyE
    rcases le_total (y 0) (M * y 1) with h | h
    · left
      refine ⟨⟨⟨hy0.le, h2⟩, hy1.le, h4⟩, ?_⟩
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hM0]; linarith
    · right
      simp only [mem_preimage, wedge, mem_ofPred_eq, mem_coordinateRectangle, mem_Icc,
        (coordinateSwap_apply _).1, (coordinateSwap_apply _).2]
      exact ⟨⟨⟨hy1.le, h4⟩, hy0.le, h2⟩, h⟩
  have hKnn : ∀ y : ℝ^2, 0 ≤ y 0 → 0 ≤ y 1 → 0 ≤ K y := fun y h0 h1 ↦
    hessianKernel_zero_one_nonneg h0 h1
  have hb1 : ∀ y ∈ wedge δ (1 / M),
      ENNReal.ofReal (B y) ≤ ENNReal.ofReal (2 * √2 * A₁ * (K y * √(y 0))) := fun y hy ↦
    ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (min_le_left _ _) (hKnn y hy.1.1.1 hy.1.2.1)) (by positivity)).trans_eq (by ring))
  have hb2 : ∀ y ∈ swap ⁻¹' wedge δ M,
      ENNReal.ofReal (B y) ≤ ENNReal.ofReal (2 * √2 * A₂ * (K y * √(y 1))) := by
    intro y hy
    simp only [mem_preimage, wedge, mem_ofPred_eq, mem_coordinateRectangle, mem_Icc,
      (coordinateSwap_apply _).1, (coordinateSwap_apply _).2] at hy
    exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (min_le_right _ _) (hKnn y hy.1.2.1 hy.1.1.1)) (by positivity)).trans_eq (by ring))
  have hswapW : ∫⁻ y in swap ⁻¹' wedge δ M, ENNReal.ofReal (2 * √2 * A₂ * (K y * √(y 1))) =
      ∫⁻ z in wedge δ M, ENNReal.ofReal (2 * √2 * A₂ * (K z * √(z 0))) := by
    have := swap.measurePreserving.setLIntegral_comp_preimage_emb
      swap.toMeasurableEquiv.measurableEmbedding
      (fun z ↦ ENNReal.ofReal (2 * √2 * A₂ * (K z * √(z 0)))) (wedge δ M)
    simp only [hK, hessianKernel_zero_one_swap, (coordinateSwap_apply _).1] at this
    exact this
  have hmin1 : min δ (δ / (1 / M)) = δ * M := by
    rw [one_div, div_inv_eq_mul]; exact min_eq_right (mul_le_of_le_one_right hδ.le hM1)
  have hmin2 : min δ (δ / M) = δ := min_eq_left (le_div_self hδ.le hM0 hM1)
  have hW1 := lintegral_wedge (C := 2 * √2 * A₁) hδ (one_div_pos.2 hM0) (by positivity)
  have hW2 := lintegral_wedge (C := 2 * √2 * A₂) hδ hM0 (by positivity)
  rw [hmin1] at hW1
  rw [hmin2] at hW2
  have hI1 := integral_integral_wedge_nonneg (δ := δ) (one_div_pos.2 hM0)
    (a := δ * M) (by positivity) (le_of_eq (by field_simp))
  have hI2 := integral_integral_wedge_nonneg (δ := δ) hM0 (a := δ) hδ.le
    (mul_le_of_le_one_left hδ.le hM1)
  rw [integral_integral_wedge hδ (one_div_pos.2 hM0) (by positivity)] at hW1 hI1
  rw [integral_integral_wedge hδ hM0 hδ.le] at hW2 hI2
  set X := 2 * √2 * A₁ * (√(δ * M) / (1 + (1 / M) ^ 2) -
    √δ * threeHalvesPowerIntegral (δ * M / δ) / 2) with hX
  set Y := 2 * √2 * A₂ * (√δ / (1 + M ^ 2) - √δ * threeHalvesPowerIntegral (δ / δ) / 2) with hY
  have hX0 : 0 ≤ X := mul_nonneg (by positivity) hI1
  have hY0 : 0 ≤ Y := mul_nonneg (by positivity) hI2
  have hval : X + Y = √2 * √δ * (2 * A₂ - A₁ * threeHalvesPowerIntegral M -
      A₂ * threeHalvesPowerIntegral 1) := by
    rw [hX, hY, mul_div_cancel_left₀ _ hδ.ne', div_self hδ.ne', Real.sqrt_mul hδ.le, hsM]
    have hA0 : A₁ ≠ 0 := hA₁.ne'
    have hMeq : M = (A₂ / A₁) ^ 2 := by rw [hM, div_pow]
    rw [hMeq]
    field_simp
    ring
  have hmain : ‖∫ y in D ∩ {y : ℝ^2 | 0 < y 1},
      (g y + g (R0 y) + (g (R1 y) + g (R0 (R1 y))))‖ₑ ≤ ENNReal.ofReal (X + Y) := by
    calc _ ≤ ∫⁻ y in D ∩ {y : ℝ^2 | 0 < y 1}, ‖g y + g (R0 y) + (g (R1 y) + g (R0 (R1 y)))‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y in D ∩ {y : ℝ^2 | 0 < y 1}, ENNReal.ofReal (B y) :=
          setLIntegral_mono' (hD.inter (measurableSet_lt measurable_const
            (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.measurable)) hpt
      _ ≤ ∫⁻ y in wedge δ (1 / M) ∪ swap ⁻¹' wedge δ M, ENNReal.ofReal (B y) :=
          lintegral_mono_set hcov
      _ ≤ (∫⁻ y in wedge δ (1 / M), ENNReal.ofReal (B y)) +
            ∫⁻ y in swap ⁻¹' wedge δ M, ENNReal.ofReal (B y) := lintegral_union_le _ _ _
      _ ≤ (∫⁻ y in wedge δ (1 / M), ENNReal.ofReal (2 * √2 * A₁ * (K y * √(y 0)))) +
            ∫⁻ y in swap ⁻¹' wedge δ M, ENNReal.ofReal (2 * √2 * A₂ * (K y * √(y 1))) :=
          add_le_add (setLIntegral_mono' (measurableSet_wedge _ _) hb1)
            (setLIntegral_mono' ((measurableSet_wedge _ _).preimage swap.continuous.measurable)
              hb2)
      _ = ENNReal.ofReal (X + Y) := by
          rw [hswapW, hW1, hW2, ← ENNReal.ofReal_add hX0 hY0]
  rw [Real.enorm_eq_ofReal_abs, hval] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (hval ▸ add_nonneg hX0 hY0)).1 hmain

/-! ### Principal values -/

/-- The truncated square `[-δ,δ]² \ B_ε` is invariant under each coordinate reflection. -/
private theorem truncation_symm (k : Fin 2) {δ ε : ℝ} {y : ℝ^2}
    (hy : y ∈ coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε) :
    coordinateReflection k y ∈ coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε := by
  refine ⟨?_, ?_⟩
  · fin_cases k
    · exact reflection_zero_mem_square hy.1
    · exact reflection_one_mem_square hy.1
  · simpa [Metric.mem_ball, dist_zero_right, norm_coordinateReflection] using hy.2

/-- The truncated square `[-δ,δ]² \ B_ε` is measurable. -/
private theorem measurableSet_truncation (δ ε : ℝ) :
    MeasurableSet (coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε) :=
  (measurableSet_coordinateRectangle _ _ _ _).diff measurableSet_ball

/-- If `G` contains almost every point of `[-δ,δ]²`, then `([-δ,δ]² \ B_ε) ∩ G` agrees with
`[-δ,δ]² \ B_ε` up to a null set. -/
private theorem truncation_ae_eq {δ ε : ℝ} {G : Set (ℝ^2)}
    (hG : volume (coordinateRectangle (-δ) δ (-δ) δ \ G) = 0) :
    (coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε) ∩ G =ᵐ[volume]
      coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε := by
  refine ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 inter_subset_left, measure_empty], ?_⟩
  rw [sdiff_self_inter]
  exact measure_mono_null (sdiff_subset_sdiff_left sdiff_subset) hG

/-- **The principal value at the boundary.** Let `G` be a measurable set, symmetric under
`y₁ ↦ -y₁`, containing almost every point of `[-δ,δ]²`. If the integrals of `K₁ F(x + ·)` over the
truncations `[-δ,δ]² \ B_ε` tend to `S` as `ε → 0⁺` and `F` is `1/2`-Hölder along `x₁` on `x + G`
with constant `A`, then `|S| ≤ √2 A √δ (2 - f_h(1))`, the first estimate of Supp. 6.1. -/
theorem abs_le_of_tendsto_hessianKernel_zero_one_of_horizontal {δ A S : ℝ} (hδ : 0 < δ)
    (hA : 0 ≤ A) {x : ℝ^2} {F : ℝ^2 → ℝ} {G : Set (ℝ^2)} (hG : MeasurableSet G)
    (hG0 : ∀ y ∈ G, coordinateReflection 0 y ∈ G)
    (hGQ : volume (coordinateRectangle (-δ) δ (-δ) δ \ G) = 0)
    (hint : ∀ ε > 0, IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y))
      (coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε))
    (hlim : Tendsto (fun ε ↦ ∫ y in coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε,
      hessianKernel 0 1 y * F (x + y)) (nhdsWithin 0 (Ioi 0)) (nhds S))
    (hF : ∀ y ∈ G, ∀ y' ∈ G, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A * √|y 0 - y' 0|) :
    |S| ≤ √2 * A * (√δ * (2 - threeHalvesPowerIntegral 1)) := by
  refine le_of_tendsto (continuous_abs.tendsto S |>.comp hlim) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Function.comp_apply, ← setIntegral_congr_set (truncation_ae_eq hGQ)]
  exact abs_setIntegral_hessianKernel_zero_one_mul_le_of_horizontal hδ hA
    ((measurableSet_truncation δ ε).inter hG) (fun y hy ↦ hy.1.1)
    (fun y hy ↦ ⟨truncation_symm 0 hy.1, hG0 _ hy.2⟩) ((hint ε hε).mono_set inter_subset_left)
    (fun y hy y' hy' ↦ hF y hy.2 y' hy'.2)

/-- **The principal value of the singular square for `u_x`**: for `G` as in
`abs_le_of_tendsto_hessianKernel_zero_one_of_horizontal`, symmetric under both reflections, if the
integrals of `K₁ F(x + ·)` over `[-δ,δ]² \ B_ε` tend to `S` as `ε → 0⁺` and `F` satisfies the
Hölder bounds on `x + G`, the estimate of Supp. 6.1 with the split at `0 < t ≤ δ` holds for `S`. -/
theorem abs_le_of_tendsto_hessianKernel_zero_one {δ t A₁ A₂ S : ℝ} (ht : 0 < t) (htδ : t ≤ δ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) {x : ℝ^2} {F : ℝ^2 → ℝ} {G : Set (ℝ^2)} (hG : MeasurableSet G)
    (hG0 : ∀ y ∈ G, coordinateReflection 0 y ∈ G) (hG1 : ∀ y ∈ G, coordinateReflection 1 y ∈ G)
    (hGQ : volume (coordinateRectangle (-δ) δ (-δ) δ \ G) = 0)
    (hint : ∀ ε > 0, IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y))
      (coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε))
    (hlim : Tendsto (fun ε ↦ ∫ y in coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε,
      hessianKernel 0 1 y * F (x + y)) (nhdsWithin 0 (Ioi 0)) (nhds S))
    (hF₀ : ∀ y ∈ G, ∀ y' ∈ G, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A₁ * √|y 0 - y' 0|)
    (hF₁ : ∀ y ∈ G, ∀ y' ∈ G, |y 1| < t → |y' 1| < t → y 0 = y' 0 →
      |F (x + y) - F (x + y')| ≤ A₂ * √|y 1 - y' 1|) :
    |S| ≤ √2 * (A₁ * (√t * threeHalvesPowerIntegral (δ / t) - √δ * threeHalvesPowerIntegral 1) +
      A₂ * (2 * √t - √δ * threeHalvesPowerIntegral (t / δ))) := by
  refine le_of_tendsto (continuous_abs.tendsto S |>.comp hlim) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Function.comp_apply, ← setIntegral_congr_set (truncation_ae_eq hGQ)]
  exact abs_setIntegral_hessianKernel_zero_one_mul_le ht htδ hA₁ hA₂
    ((measurableSet_truncation δ ε).inter hG) (fun y hy ↦ hy.1.1)
    (fun y hy ↦ ⟨truncation_symm 0 hy.1, hG0 _ hy.2⟩)
    (fun y hy ↦ ⟨truncation_symm 1 hy.1, hG1 _ hy.2⟩) ((hint ε hε).mono_set inter_subset_left)
    (fun y hy y' hy' ↦ hF₀ y hy.2 y' hy'.2) (fun y hy y' hy' ↦ hF₁ y hy.2 y' hy'.2)

/-- **The principal value of the interior square**: for `G` as in
`abs_le_of_tendsto_hessianKernel_zero_one`, if the integrals of `K₁ F(x + ·)` over
`[-δ,δ]² \ B_ε` tend to `S` as `ε → 0⁺` and `F` satisfies both Hölder bounds on `x + G`, the
interior estimate of Supp. 6.1 holds for `S`. -/
theorem abs_le_of_tendsto_hessianKernel_zero_one_interior {δ A₁ A₂ S : ℝ} (hδ : 0 < δ)
    (hA₂ : 0 < A₂) (hA : A₂ ≤ A₁) {x : ℝ^2} {F : ℝ^2 → ℝ} {G : Set (ℝ^2)} (hG : MeasurableSet G)
    (hG0 : ∀ y ∈ G, coordinateReflection 0 y ∈ G) (hG1 : ∀ y ∈ G, coordinateReflection 1 y ∈ G)
    (hGQ : volume (coordinateRectangle (-δ) δ (-δ) δ \ G) = 0)
    (hint : ∀ ε > 0, IntegrableOn (fun y ↦ hessianKernel 0 1 y * F (x + y))
      (coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε))
    (hlim : Tendsto (fun ε ↦ ∫ y in coordinateRectangle (-δ) δ (-δ) δ \ Metric.ball (0 : ℝ^2) ε,
      hessianKernel 0 1 y * F (x + y)) (nhdsWithin 0 (Ioi 0)) (nhds S))
    (hF₀ : ∀ y ∈ G, ∀ y' ∈ G, y 1 = y' 1 → |F (x + y) - F (x + y')| ≤ A₁ * √|y 0 - y' 0|)
    (hF₁ : ∀ y ∈ G, ∀ y' ∈ G, y 0 = y' 0 → |F (x + y) - F (x + y')| ≤ A₂ * √|y 1 - y' 1|) :
    |S| ≤ √2 * √δ * (2 * A₂ - A₁ * threeHalvesPowerIntegral (A₂ ^ 2 / A₁ ^ 2) -
      A₂ * threeHalvesPowerIntegral 1) := by
  refine le_of_tendsto (continuous_abs.tendsto S |>.comp hlim) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Function.comp_apply, ← setIntegral_congr_set (truncation_ae_eq hGQ)]
  exact abs_setIntegral_hessianKernel_zero_one_mul_le_interior hδ hA₂ hA
    ((measurableSet_truncation δ ε).inter hG) (fun y hy ↦ hy.1.1)
    (fun y hy ↦ ⟨truncation_symm 0 hy.1, hG0 _ hy.2⟩)
    (fun y hy ↦ ⟨truncation_symm 1 hy.1, hG1 _ hy.2⟩) ((hint ε hε).mono_set inter_subset_left)
    (fun y hy y' hy' ↦ hF₀ y hy.2 y' hy'.2) (fun y hy y' hy' ↦ hF₁ y hy.2 y' hy'.2)

end PotentialTheory.Planar
