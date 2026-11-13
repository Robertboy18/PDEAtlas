/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarRectangleIntegrals

/-!
# The planar velocity kernel on a box about its pole

The planar Biot-Savart velocity kernels without `1/π` are `s₂ / (2|s|²)` and `-s₁ / (2|s|²)`. On the
box `[-A, A] × [-B, B]` about the pole their absolute values have the closed-form integrals

`∫ |s₂| / (2|s|²) ds = A log(1 + B²/A²) + 2 B arctan(A/B)`,

and the same with `(A, B)` exchanged for `|s₁| / (2|s|²)`. On each half of the box where the
coordinate has a sign, the absolute value is `∓π ∂ⱼG`, whose rectangle integrals are corner sums of
explicit primitives (`integral_rectangle_gradientKernel_zero_eq_cornerSum`,
`integral_rectangle_gradientKernel_one_eq_cornerSum`); the box is covered by the two halves.

## Main definitions

* `velocityBoxIntegral`: `velocityBoxIntegral A B = A log(1 + B²/A²) + 2 B arctan(A/B)`.

## Main results

* `lintegral_velocityBox_le`: for `A, B > 0`, the integral over the box `x + [-A, A] × [-B, B]` of
  `|y₂ - x₂| / (2|x - y|²)` is at most `velocityBoxIntegral A B`.
* `lintegral_velocityBox_swap_le`: the integral over the same box of `|y₁ - x₁| / (2|x - y|²)` is
  at most `velocityBoxIntegral B A`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis

namespace PotentialTheory.Planar

/-- `A log(1 + B²/A²) + 2 B arctan(A/B)`, the integral of `|s₂| / (2|s|²)` over
`[-A, A] × [-B, B]`. -/
def velocityBoxIntegral (A B : ℝ) : ℝ :=
  A * Real.log (1 + B ^ 2 / A ^ 2) + 2 * B * Real.arctan (A / B)

/-- For `A > 0`, `log(A² + B²) - log A² = log(1 + B²/A²)`. -/
private theorem log_sq_add_sq_sub {A B : ℝ} (hA : 0 < A) :
    Real.log (A ^ 2 + B ^ 2) - Real.log (A ^ 2) = Real.log (1 + B ^ 2 / A ^ 2) := by
  have hA2 : A ^ 2 ≠ 0 := by positivity
  have h1 : 0 < 1 + B ^ 2 / A ^ 2 := by positivity
  rw [show A ^ 2 + B ^ 2 = A ^ 2 * (1 + B ^ 2 / A ^ 2) by field_simp,
    Real.log_mul hA2 h1.ne']
  ring

/-- The gradient kernel `∂ᵢG` is integrable on every closed rectangle, including one containing the
pole. -/
private theorem integrableOn_gradientKernel (i : Fin 2) (a b c d : ℝ) :
    IntegrableOn (gradientKernel i) (coordinateRectangle a b c d) :=
  (locallyIntegrable_gradientKernel i).integrableOn_isCompact
    (isCompact_coordinateRectangle a b c d)

/-- `π ∂ⱼG(s) = -sⱼ / (2|s|²)`, also at the pole. -/
private theorem pi_mul_gradientKernel (i : Fin 2) (s : ℝ^2) :
    Real.pi * gradientKernel i s = -(s i / (2 * ‖s‖ ^ 2)) := by
  rw [gradientKernel_eq_div]
  have := Real.pi_pos.ne'
  by_cases h : ‖s‖ ^ 2 = 0
  · simp [h]
  · field_simp

/-- The integral of `ofReal (σ π ∂ⱼG)` over a rectangle on which it is nonnegative. -/
private theorem lintegral_rectangle_eq {i : Fin 2} {σ : ℝ} {a b c d : ℝ}
    (h0 : ∀ s ∈ coordinateRectangle a b c d, 0 ≤ σ * (Real.pi * gradientKernel i s)) :
    ∫⁻ s in coordinateRectangle a b c d, ENNReal.ofReal (σ * (Real.pi * gradientKernel i s)) =
      ENNReal.ofReal (σ * (Real.pi * ∫ s in coordinateRectangle a b c d, gradientKernel i s)) := by
  have hint := ((integrableOn_gradientKernel i a b c d).const_mul Real.pi).const_mul σ
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' (measurableSet_coordinateRectangle a b c d)).2
      (Filter.Eventually.of_forall h0)), integral_const_mul, integral_const_mul]

/-- The half box `[-A, A] × [0, B]`. -/
private theorem lintegral_upper {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ s in coordinateRectangle (-A) A 0 B, ENNReal.ofReal (|s 1| / (2 * ‖s‖ ^ 2)) =
      ENNReal.ofReal (velocityBoxIntegral A B / 2) := by
  have hcongr : ∀ s ∈ coordinateRectangle (-A) A 0 B,
      |s 1| / (2 * ‖s‖ ^ 2) = -1 * (Real.pi * gradientKernel 1 s) := by
    intro s hs
    rw [pi_mul_gradientKernel, abs_of_nonneg hs.2.1]
    ring
  rw [setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _)
      (fun s hs ↦ by rw [hcongr s hs]),
    lintegral_rectangle_eq (fun s hs ↦ by rw [← hcongr s hs]; positivity),
    integral_rectangle_gradientKernel_one_eq_cornerSum (by linarith) hB.le]
  congr 1
  simp only [cornerSum]
  have e1 : Real.arctan (-A / B) = -Real.arctan (A / B) := by rw [neg_div, Real.arctan_neg]
  have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [e1, neg_sq A, e0, add_zero]
  unfold velocityBoxIntegral
  rw [← log_sq_add_sq_sub hA]
  ring

/-- The half box `[-A, A] × [-B, 0]`. -/
private theorem lintegral_lower {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ s in coordinateRectangle (-A) A (-B) 0, ENNReal.ofReal (|s 1| / (2 * ‖s‖ ^ 2)) =
      ENNReal.ofReal (velocityBoxIntegral A B / 2) := by
  have hcongr : ∀ s ∈ coordinateRectangle (-A) A (-B) 0,
      |s 1| / (2 * ‖s‖ ^ 2) = 1 * (Real.pi * gradientKernel 1 s) := by
    intro s hs
    rw [pi_mul_gradientKernel, abs_of_nonpos hs.2.2]
    ring
  rw [setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _)
      (fun s hs ↦ by rw [hcongr s hs]),
    lintegral_rectangle_eq (fun s hs ↦ by rw [← hcongr s hs]; positivity),
    integral_rectangle_gradientKernel_one_eq_cornerSum (by linarith) (by linarith)]
  congr 1
  simp only [cornerSum]
  have e1 : Real.arctan (A / -B) = -Real.arctan (A / B) := by rw [div_neg, Real.arctan_neg]
  have e2 : Real.arctan (-A / -B) = Real.arctan (A / B) := by rw [neg_div_neg_eq]
  have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  rw [e1, e2, neg_sq A, neg_sq B, e0, add_zero]
  unfold velocityBoxIntegral
  rw [← log_sq_add_sq_sub hA]
  ring

/-- The half box `[0, A] × [-B, B]`, for the kernel of the other coordinate. -/
private theorem lintegral_right {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ s in coordinateRectangle 0 A (-B) B, ENNReal.ofReal (|s 0| / (2 * ‖s‖ ^ 2)) =
      ENNReal.ofReal (velocityBoxIntegral B A / 2) := by
  have hcongr : ∀ s ∈ coordinateRectangle 0 A (-B) B,
      |s 0| / (2 * ‖s‖ ^ 2) = -1 * (Real.pi * gradientKernel 0 s) := by
    intro s hs
    rw [pi_mul_gradientKernel, abs_of_nonneg hs.1.1]
    ring
  rw [setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _)
      (fun s hs ↦ by rw [hcongr s hs]),
    lintegral_rectangle_eq (fun s hs ↦ by rw [← hcongr s hs]; positivity),
    integral_rectangle_gradientKernel_zero_eq_cornerSum hA.le (by linarith)]
  congr 1
  simp only [cornerSum]
  have e1 : Real.arctan (-B / A) = -Real.arctan (B / A) := by rw [neg_div, Real.arctan_neg]
  have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  have hlog : Real.log (1 + A ^ 2 / B ^ 2) = Real.log (A ^ 2 + B ^ 2) - Real.log (B ^ 2) := by
    rw [← log_sq_add_sq_sub hB, add_comm]
  rw [e1, neg_sq B, e0, zero_add]
  unfold velocityBoxIntegral
  rw [hlog]
  ring

/-- The half box `[-A, 0] × [-B, B]`, for the kernel of the other coordinate. -/
private theorem lintegral_left {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ s in coordinateRectangle (-A) 0 (-B) B, ENNReal.ofReal (|s 0| / (2 * ‖s‖ ^ 2)) =
      ENNReal.ofReal (velocityBoxIntegral B A / 2) := by
  have hcongr : ∀ s ∈ coordinateRectangle (-A) 0 (-B) B,
      |s 0| / (2 * ‖s‖ ^ 2) = 1 * (Real.pi * gradientKernel 0 s) := by
    intro s hs
    rw [pi_mul_gradientKernel, abs_of_nonpos hs.1.2]
    ring
  rw [setLIntegral_congr_fun (measurableSet_coordinateRectangle _ _ _ _)
      (fun s hs ↦ by rw [hcongr s hs]),
    lintegral_rectangle_eq (fun s hs ↦ by rw [← hcongr s hs]; positivity),
    integral_rectangle_gradientKernel_zero_eq_cornerSum (by linarith) (by linarith)]
  congr 1
  simp only [cornerSum]
  have e1 : Real.arctan (B / -A) = -Real.arctan (B / A) := by rw [div_neg, Real.arctan_neg]
  have e2 : Real.arctan (-B / -A) = Real.arctan (B / A) := by rw [neg_div_neg_eq]
  have e0 : (0 : ℝ) ^ 2 = 0 := by norm_num
  have hlog : Real.log (1 + A ^ 2 / B ^ 2) = Real.log (A ^ 2 + B ^ 2) - Real.log (B ^ 2) := by
    rw [← log_sq_add_sq_sub hB, add_comm]
  rw [e1, e2, neg_sq A, neg_sq B, e0, zero_add]
  unfold velocityBoxIntegral
  rw [hlog]
  ring

/-- The box `x + [-A, A] × [-B, B]` as a translate of the centered box. -/
private theorem lintegral_box_eq (x : ℝ^2) (A B : ℝ) (j : Fin 2) :
    ∫⁻ y in {y : ℝ^2 | |y 0 - x 0| ≤ A ∧ |y 1 - x 1| ≤ B},
        ENNReal.ofReal (|y j - x j| / (2 * ‖x - y‖ ^ 2)) =
      ∫⁻ s in coordinateRectangle (-A) A (-B) B, ENNReal.ofReal (|s j| / (2 * ‖s‖ ^ 2)) := by
  have hc : ∀ i : Fin 2, Continuous fun y : ℝ^2 ↦ |y i - x i| := fun i ↦
    ((EuclideanSpace.proj i).continuous.sub continuous_const).abs
  have hS : MeasurableSet {y : ℝ^2 | |y 0 - x 0| ≤ A ∧ |y 1 - x 1| ≤ B} :=
    ((isClosed_le (hc 0) continuous_const).inter
      (isClosed_le (hc 1) continuous_const)).measurableSet
  rw [← lintegral_indicator hS, ← lintegral_indicator (measurableSet_coordinateRectangle _ _ _ _),
    ← lintegral_add_right_eq_self _ x]
  congr 1
  funext s
  have hmem : s + x ∈ {y : ℝ^2 | |y 0 - x 0| ≤ A ∧ |y 1 - x 1| ≤ B} ↔
      s ∈ coordinateRectangle (-A) A (-B) B := by
    simp only [mem_ofPred_eq, mem_coordinateRectangle, mem_Icc, PiLp.add_apply,
      add_sub_cancel_right, abs_le]
  by_cases h : s ∈ coordinateRectangle (-A) A (-B) B
  · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
    simp only [PiLp.add_apply, add_sub_cancel_right]
    rw [show x - (s + x) = -s by abel, norm_neg]
  · rw [indicator_of_notMem (fun h' ↦ h (hmem.1 h')), indicator_of_notMem h]

/-- **The direct velocity kernel on a box about its pole**: for `A, B > 0`,
`∫_{x + [-A, A] × [-B, B]} |y₂ - x₂| / (2|x - y|²) dy ≤ A log(1 + B²/A²) + 2 B arctan(A/B)`. -/
theorem lintegral_velocityBox_le (x : ℝ^2) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ y in {y : ℝ^2 | |y 0 - x 0| ≤ A ∧ |y 1 - x 1| ≤ B},
        ENNReal.ofReal (|y 1 - x 1| / (2 * ‖x - y‖ ^ 2)) ≤
      ENNReal.ofReal (velocityBoxIntegral A B) := by
  rw [lintegral_box_eq]
  have hsub : coordinateRectangle (-A) A (-B) B ⊆
      coordinateRectangle (-A) A 0 B ∪ coordinateRectangle (-A) A (-B) 0 := by
    intro s hs
    rcases le_total 0 (s 1) with h | h
    · exact Or.inl ⟨hs.1, h, hs.2.2⟩
    · exact Or.inr ⟨hs.1, hs.2.1, h⟩
  refine (lintegral_mono_set hsub).trans ((lintegral_union_le _ _ _).trans (le_of_eq ?_))
  rw [lintegral_upper hA hB, lintegral_lower hA hB, ← ENNReal.ofReal_add]
  · ring_nf
  all_goals
    unfold velocityBoxIntegral
    have : 0 ≤ Real.log (1 + B ^ 2 / A ^ 2) := Real.log_nonneg (by
      have : 0 ≤ B ^ 2 / A ^ 2 := by positivity
      linarith)
    have : 0 ≤ Real.arctan (A / B) := Real.arctan_nonneg.mpr (by positivity)
    positivity

/-- **The direct velocity kernel of the other coordinate on a box about its pole**: for
`A, B > 0`, `∫_{x + [-A, A] × [-B, B]} |y₁ - x₁| / (2|x - y|²) dy ≤
B log(1 + A²/B²) + 2 A arctan(B/A)`. -/
theorem lintegral_velocityBox_swap_le (x : ℝ^2) {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∫⁻ y in {y : ℝ^2 | |y 0 - x 0| ≤ A ∧ |y 1 - x 1| ≤ B},
        ENNReal.ofReal (|y 0 - x 0| / (2 * ‖x - y‖ ^ 2)) ≤
      ENNReal.ofReal (velocityBoxIntegral B A) := by
  rw [lintegral_box_eq]
  have hsub : coordinateRectangle (-A) A (-B) B ⊆
      coordinateRectangle 0 A (-B) B ∪ coordinateRectangle (-A) 0 (-B) B := by
    intro s hs
    rcases le_total 0 (s 0) with h | h
    · exact Or.inl ⟨⟨h, hs.1.2⟩, hs.2⟩
    · exact Or.inr ⟨⟨hs.1.1, h⟩, hs.2⟩
  refine (lintegral_mono_set hsub).trans ((lintegral_union_le _ _ _).trans (le_of_eq ?_))
  rw [lintegral_right hA hB, lintegral_left hA hB, ← ENNReal.ofReal_add]
  · ring_nf
  all_goals
    unfold velocityBoxIntegral
    have : 0 ≤ Real.log (1 + A ^ 2 / B ^ 2) := Real.log_nonneg (by
      have : 0 ≤ A ^ 2 / B ^ 2 := by positivity
      linarith)
    have : 0 ≤ Real.arctan (B / A) := Real.arctan_nonneg.mpr (by positivity)
    positivity

end PotentialTheory.Planar
