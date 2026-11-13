/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarSingularIntegral
import PDE.Analysis.Integration.Rectangle.MixedPrimitive
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Hölder estimates of the image part of half-plane singular integrals

For a point `x` of the open upper half-plane `{x₁ > 0}`, the integral

`R f(x) = ∫_{y₁<0} K(x - y) f(y) dy`

over the lower half-plane is absolutely convergent, because `|x - y| ≥ x₁` there. It is the
image part of a singular integral of an odd extension across `{y₁ = 0}`. Its Hölder estimate
uses, in place of the cancellation on circles, the cancellation of `K` on horizontal lines
(`HasLineCancellation`). None of the constants depends on the distance of `x` to the boundary.

## Main results

* `integral_lower_sub_eq_zero`: `∫_{y₁<0} (K(x - y) - K(x' - y)) dy = 0` (Fubini over
  horizontal lines).
* `abs_setIntegral_rectangle_le`: `|∫_Q K(p - y) dy| ≤ 2A h/η` for a rectangle `Q` of height
  `h` below the boundary whose horizontal sides contain `(p₀ - η, p₀ + η)`.
* `abs_integral_lower_sub_le`: `|R f(x) - R f(x')| ≤ 16π/(α(1-α)) · A M |x - x'|^α` for a
  Hölder integrable density, `0 < α < 1`.
* `abs_integral_lower_le`: `|R f(x)| ≤ A (4πM/α + 2B + ‖f‖₁)` when `|f| ≤ B`.
* `abs_integral_lower_le_log`: `|R f(x)| ≤ (4πA/α)(1 + B log(2 + M)) + 2AB + A ‖f‖₁` when
  `|f| ≤ B`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PotentialTheory.Planar

section Fubini

open PDE.Analysis (planeEquiv planeEquiv_symm_apply measurePreserving_planeEquiv)

/-- **Fubini over horizontal lines.** For integrable `F` on the plane,
`∫ F = ∫_t ∫_s F(s, t) ds dt`. -/
theorem integral_eq_integral_integral_vec {F : ℝ^2 → ℝ} (hF : Integrable F) :
    ∫ y, F y = ∫ t, ∫ s, F !₂[s, t] := by
  have hmp := measurePreserving_planeEquiv.symm
  have h1 : ∫ p, F (planeEquiv.symm p) = ∫ y, F y := hmp.integral_comp' F
  have hint : Integrable (fun p ↦ F (planeEquiv.symm p)) (volume : Measure (ℝ × ℝ)) :=
    (hmp.integrable_comp_emb planeEquiv.symm.measurableEmbedding).mpr hF
  rw [← h1, Measure.volume_eq_prod] at *
  rw [integral_prod_symm _ hint]
  simp only [planeEquiv_symm_apply]

end Fubini

/-- The open rectangle `{t₀ < y₁ < 0, a < y₀ < b}` is measurable. -/
private theorem measurableSet_rectangle (t₀ a b : ℝ) :
    MeasurableSet {y : ℝ^2 | t₀ < y 1 ∧ y 1 < 0 ∧ a < y 0 ∧ y 0 < b} := by
  measurability

/-- The rectangle of half-width `r` below a point `x` of the upper half-plane lies in the ball
of radius `3r/2` around `x`. -/
private theorem rectangle_subset_ball {x : ℝ^2} (hx : 0 < x 1) {r : ℝ} (hr : 0 < r) :
    {y : ℝ^2 | min (x 1 - r) 0 < y 1 ∧ y 1 < 0 ∧ x 0 - r < y 0 ∧ y 0 < x 0 + r} ⊆
      ball x (3 / 2 * r) := fun y ⟨h1, h2, h3, h4⟩ ↦ by
  have h1' : x 1 - r < y 1 := (min_lt_iff.mp h1).resolve_right (by linarith)
  rw [mem_ball, dist_eq_norm, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
    EuclideanSpace.norm_sq_fin_two, PiLp.sub_apply, PiLp.sub_apply]
  nlinarith

/-- Off the rectangle of half-width `r` below `x`, the lower half-plane is at distance at least
`r` from `x`. -/
private theorem le_norm_sub_of_mem_lower_diff_rectangle {x : ℝ^2} {r : ℝ} :
    ∀ y ∈ {y : ℝ^2 | y 1 < 0} \
      {y : ℝ^2 | min (x 1 - r) 0 < y 1 ∧ y 1 < 0 ∧ x 0 - r < y 0 ∧ y 0 < x 0 + r},
      r ≤ ‖x - y‖ := by
  rintro y ⟨hyL, hyN⟩
  have e0 : |x 0 - y 0| ≤ ‖x - y‖ := by simpa using PiLp.norm_apply_le (x - y) 0
  have e1 : |x 1 - y 1| ≤ ‖x - y‖ := by simpa using PiLp.norm_apply_le (x - y) 1
  simp only [Set.mem_ofPred_eq, not_and_or, not_lt] at hyN
  rcases hyN with h | h | h | h
  · linarith [le_abs_self (x 1 - y 1), min_le_left (x 1 - r) 0]
  · exact absurd hyL (not_lt.2 h)
  · linarith [le_abs_self (x 0 - y 0)]
  · linarith [neg_abs_le (x 0 - y 0)]

/-- A set integral is at most `V` when a pointwise bound of its integrand has lintegral
`ENNReal.ofReal V` over a larger set. -/
private theorem norm_setIntegral_le_of_lintegral_eq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {S T : Set X} {F g : X → ℝ} {V : ℝ} (hS : MeasurableSet S) (hST : S ⊆ T)
    (hle : ∀ y ∈ S, ‖F y‖ ≤ g y) (hval : ∫⁻ y in T, ENNReal.ofReal (g y) ∂μ = ENNReal.ofReal V)
    (hV : 0 ≤ V) : ‖∫ y in S, F y ∂μ‖ ≤ V := by
  have hmono := lintegral_mono_set (μ := μ) (f := fun y ↦ ENNReal.ofReal (g y)) hST
  rw [hval] at hmono
  refine (norm_setIntegral_le_of_norm_le hS hle
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmono)).trans ?_
  rw [← ENNReal.toReal_ofReal hV]
  exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono

/-- The open lower half-plane is measurable. -/
theorem measurableSet_lower : MeasurableSet {y : ℝ^2 | y 1 < 0} :=
  measurableSet_lt (by fun_prop) measurable_const

/-- A point of the lower half-plane is at distance at least `x₁` from `x`. -/
theorem le_norm_sub_of_lower {x y : ℝ^2} (hy : y 1 < 0) : x 1 ≤ ‖x - y‖ := by
  have h := PiLp.norm_apply_le (x - y) 1
  rw [PiLp.sub_apply, Real.norm_eq_abs] at h
  have := le_abs_self (x 1 - y 1)
  linarith

variable {K : ℝ^2 → ℝ} {A : ℝ} {f : ℝ^2 → ℝ} {M α : ℝ}

namespace IsSingularKernel

variable (hK : IsSingularKernel K A)
include hK

/-- The image integral at a point of the upper half-plane is absolutely convergent. -/
theorem integrableOn_lower_mul (hf : Integrable f) {x : ℝ^2} (hx : 0 < x 1) :
    IntegrableOn (fun y ↦ K (x - y) * f y) {y : ℝ^2 | y 1 < 0} :=
  hK.integrableOn_mul_of_le hf x measurableSet_lower hx fun _ hy ↦ le_norm_sub_of_lower hy

/-- The difference of two kernels centred in the upper half-plane is integrable on the lower
half-plane. -/
theorem integrableOn_lower_sub {x x' : ℝ^2} (hx : 0 < x 1) (hx' : 0 < x' 1) :
    IntegrableOn (fun y ↦ K (x - y) - K (x' - y)) {y : ℝ^2 | y 1 < 0} := by
  rcases eq_or_ne x x' with rfl | hxx'
  · simp only [sub_self]
    exact integrableOn_zero
  have hball : MeasurableSet ({y : ℝ^2 | y 1 < 0} ∩ ball x (2 * ‖x - x'‖)) :=
    measurableSet_lower.inter measurableSet_ball
  have hfin : volume ({y : ℝ^2 | y 1 < 0} ∩ ball x (2 * ‖x - x'‖)) ≠ ⊤ :=
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  have h1 : IntegrableOn (fun y ↦ K (x - y) - K (x' - y))
      ({y : ℝ^2 | y 1 < 0} ∩ ball x (2 * ‖x - x'‖)) :=
    (hK.integrableOn_of_le x hball hfin hx fun _ hy ↦ le_norm_sub_of_lower hy.1).sub
      (hK.integrableOn_of_le x' hball hfin hx' fun _ hy ↦ le_norm_sub_of_lower hy.1)
  have h2 : IntegrableOn (fun y ↦ K (x - y) - K (x' - y))
      ({y : ℝ^2 | y 1 < 0} ∩ (ball x (2 * ‖x - x'‖))ᶜ) :=
    (hK.integrableOn_compl_ball_sub hxx').mono_set inter_subset_right
  have := h1.union h2
  rwa [← inter_union_distrib_left, union_compl_self, inter_univ] at this

/-- **Zero mean on the lower half-plane.** For `x, x'` in the upper half-plane,
`∫_{y₁<0} (K(x - y) - K(x' - y)) dy = 0`. -/
theorem integral_lower_sub_eq_zero (hL : HasLineCancellation K) {x x' : ℝ^2} (hx : 0 < x 1)
    (hx' : 0 < x' 1) :
    ∫ y in {y : ℝ^2 | y 1 < 0}, (K (x - y) - K (x' - y)) = 0 := by
  rw [← integral_indicator measurableSet_lower,
    integral_eq_integral_integral_vec ((hK.integrableOn_lower_sub hx hx').integrable_indicator
      measurableSet_lower)]
  have hinner : ∀ t : ℝ, ∫ s : ℝ, {y : ℝ^2 | y 1 < 0}.indicator
      (fun y ↦ K (x - y) - K (x' - y)) !₂[s, t] = 0 := by
    intro t
    by_cases ht : t < 0
    · have hmem : ∀ s : ℝ, (!₂[s, t] : ℝ^2) ∈ {y : ℝ^2 | y 1 < 0} := fun s ↦ by simpa using ht
      simp_rw [indicator_of_mem (hmem _)]
      rw [integral_sub (hK.integrable_sub_vec x (by linarith))
        (hK.integrable_sub_vec x' (by linarith)), hL.integral_sub_vec x (by linarith),
        hL.integral_sub_vec x' (by linarith), sub_zero]
    · have hmem : ∀ s : ℝ, (!₂[s, t] : ℝ^2) ∉ {y : ℝ^2 | y 1 < 0} := fun s ↦ by simpa using ht
      simp_rw [indicator_of_notMem (hmem _)]
      simp
  simp [hinner]

/-- **The rectangle bound.** Let `p₁ > 0`, `t₀ ≤ 0`, `η > 0` and `a ≤ p₀ - η`, `p₀ + η ≤ b`.
Over the rectangle `Q = (a, b) × (t₀, 0)` below the boundary,
`|∫_Q K(p - y) dy| ≤ 2A (-t₀)/η`. -/
theorem abs_setIntegral_rectangle_le (hL : HasLineCancellation K) {p : ℝ^2} (hp : 0 < p 1)
    {a b t₀ η : ℝ} (hη : 0 < η) (ha : a ≤ p 0 - η) (hb : p 0 + η ≤ b) (ht₀ : t₀ ≤ 0) :
    |∫ y in {y : ℝ^2 | t₀ < y 1 ∧ y 1 < 0 ∧ a < y 0 ∧ y 0 < b}, K (p - y)| ≤
      2 * A * (-t₀) / η := by
  have hA := hK.nonneg
  set Q := {y : ℝ^2 | t₀ < y 1 ∧ y 1 < 0 ∧ a < y 0 ∧ y 0 < b} with hQdef
  have hQm : MeasurableSet Q := measurableSet_rectangle t₀ a b
  have hQb : Q ⊆ ball 0 (|a| + |b| + |t₀| + 1) := fun y ⟨h1, h2, h3, h4⟩ ↦ by
    have hy0 : |y 0| ≤ |a| + |b| := _root_.abs_le.2
      ⟨by linarith [neg_abs_le a, abs_nonneg b], by linarith [le_abs_self b, abs_nonneg a]⟩
    have hy1 : |y 1| ≤ |t₀| :=
      _root_.abs_le.2 ⟨by linarith [neg_abs_le t₀], by linarith [abs_nonneg t₀]⟩
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
      EuclideanSpace.norm_sq_fin_two, ← sq_abs (y 0), ← sq_abs (y 1)]
    nlinarith [mul_le_mul hy0 hy0 (abs_nonneg _) (by positivity),
      mul_le_mul hy1 hy1 (abs_nonneg _) (abs_nonneg _), abs_nonneg a, abs_nonneg b, abs_nonneg t₀]
  have hQint : IntegrableOn (fun y ↦ K (p - y)) Q :=
    hK.integrableOn_of_le p hQm ((measure_mono hQb).trans_lt measure_ball_lt_top).ne hp
      fun _ hy ↦ le_norm_sub_of_lower hy.2.1
  set φ : ℝ → ℝ := fun t ↦ ∫ s in Ioo a b, K (p - !₂[s, t]) with hφdef
  have hslice : ∀ t ∈ Ioo t₀ 0, ‖φ t‖ ≤ 2 * A / η := by
    intro t ht
    have htp : t ≠ p 1 := by linarith [ht.2]
    have hsplit : φ t = -∫ s in (Ioo a b)ᶜ, K (p - !₂[s, t]) := by
      have := integral_add_compl (measurableSet_Ioo (a := a) (b := b)) (hK.integrable_sub_vec p htp)
      rw [hL.integral_sub_vec p htp] at this
      linarith
    have hsub : (Ioo a b)ᶜ ⊆ {s : ℝ | η ≤ |s - p 0|} := fun s hs ↦ by
      simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hs
      rcases hs with hs | hs
      · exact le_abs.2 (.inr (by linarith : η ≤ -(s - p 0)))
      · exact le_abs.2 (.inl (by linarith : η ≤ s - p 0))
    have hle : ∀ s ∈ (Ioo a b)ᶜ, ‖K (p - !₂[s, t])‖ ≤ A * ((s - p 0) ^ 2)⁻¹ := fun s hs ↦ by
      have hpos : 0 < (s - p 0) ^ 2 := by rw [← sq_abs]; exact pow_pos (hη.trans_le (hsub hs)) 2
      rw [Real.norm_eq_abs, sub_vec, ← div_eq_mul_inv]
      exact (hK.abs_vec_le _ _).trans
        (div_le_div_of_nonneg_left hA hpos (by nlinarith [sq_nonneg (p 1 - t)]))
    rw [hsplit, norm_neg, show 2 * A / η = A * (2 / η) by ring]
    refine norm_setIntegral_le_of_lintegral_eq measurableSet_Ioo.compl hsub hle ?_ (by positivity)
    simp_rw [ENNReal.ofReal_mul hA]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_abs_sub_ge_inv_sq _ hη]
  -- Fubini on the rectangle
  have hfub : ∫ y in Q, K (p - y) = ∫ t in Ioo t₀ 0, φ t := by
    rw [← integral_indicator hQm, integral_eq_integral_integral_vec
      (hQint.integrable_indicator hQm), ← integral_indicator measurableSet_Ioo]
    congr 1 with t
    by_cases ht : t ∈ Ioo t₀ 0
    · rw [indicator_of_mem ht]
      change _ = ∫ s in Ioo a b, K (p - !₂[s, t])
      rw [← integral_indicator measurableSet_Ioo]
      congr 1 with s
      simp only [indicator, hQdef, Set.mem_ofPred_eq, mem_Ioo, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, ht.1, ht.2, true_and]
    · rw [indicator_of_notMem ht]
      exact integral_eq_zero_of_ae (ae_of_all _ fun s ↦ indicator_of_notMem (fun h ↦ ht
        ⟨by simpa using h.1, by simpa using h.2.1⟩) _)
  rw [hfub, ← Real.norm_eq_abs]
  refine (norm_setIntegral_le_of_norm_le_const (by simp) hslice).trans (le_of_eq ?_)
  rw [Real.volume_real_Ioo_of_le ht₀]
  ring

omit hK in
/-- The arithmetic of the four pieces of the image Hölder estimate. -/
private theorem image_constant_le {δ α : ℝ} (hδ : 0 < δ) (hα : 0 < α) (hα1 : α < 1) :
    2 * Real.pi * (3 * δ) ^ α / α + 2 * Real.pi * (4 * δ) ^ α / α + 4 * δ ^ α +
        δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) ≤
      16 * Real.pi / (α * (1 - α)) * δ ^ α := by
  have h1α : 0 < 1 - α := by linarith
  have e3 : (3 * δ) ^ α = 3 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
  have e4 : (4 * δ) ^ α = 4 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
  have e2' : (2 * δ) ^ (α - 1) = 2 ^ (α - 1) * δ ^ (α - 1) := Real.mul_rpow (by norm_num) hδ.le
  have eδ : δ * δ ^ (α - 1) = δ ^ α := by
    rw [show α = 1 + (α - 1) by ring, Real.rpow_add hδ, Real.rpow_one]
    ring_nf
  have b3 : (3 : ℝ) ^ α ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα1.le
  have b4 : (4 : ℝ) ^ α ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hα1.le
  have b2' : (2 : ℝ) ^ (α - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have ht : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  set t := δ ^ α
  have hpi := Real.two_le_pi
  calc 2 * Real.pi * (3 * δ) ^ α / α + 2 * Real.pi * (4 * δ) ^ α / α + 4 * t +
        δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))
      = t * (2 * Real.pi * 3 ^ α / α + 2 * Real.pi * 4 ^ α / α + 4 +
          2 * Real.pi * 2 ^ (α - 1) / (1 - α)) := by
        rw [e3, e4, e2', show δ * (2 * Real.pi * (2 ^ (α - 1) * δ ^ (α - 1)) / (1 - α)) =
          2 * Real.pi * 2 ^ (α - 1) * (δ * δ ^ (α - 1)) / (1 - α) by ring, eδ]
        ring
    _ ≤ t * (2 * Real.pi * 3 / α + 2 * Real.pi * 4 / α + 4 + 2 * Real.pi * 1 / (1 - α)) := by
        gcongr
    _ ≤ t * (16 * Real.pi / (α * (1 - α))) := by
        gcongr
        have key : 2 * Real.pi * 3 / α + 2 * Real.pi * 4 / α + 4 + 2 * Real.pi * 1 / (1 - α) =
            (14 * Real.pi * (1 - α) + 4 * α * (1 - α) + 2 * Real.pi * α) / (α * (1 - α)) := by
          field_simp
          ring
        rw [key]
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [mul_pos hα h1α, sq_nonneg (α - 1 / 2)]
    _ = 16 * Real.pi / (α * (1 - α)) * t := by ring

/-- **Hölder continuity of the image integral.** For a singular kernel with zero mean on
horizontal lines and an integrable density with `|f(y) - f(z)| ≤ M |y - z|^α`, `0 < α < 1`, and
`x, x'` in the upper half-plane,
`|R f(x) - R f(x')| ≤ 16π/(α(1-α)) · A M |x - x'|^α`. -/
theorem abs_integral_lower_sub_le (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α < 1)
    (hf : Integrable f) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) {x x' : ℝ^2}
    (hx : 0 < x 1) (hx' : 0 < x' 1) :
    |(∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * f y) -
        ∫ y in {y : ℝ^2 | y 1 < 0}, K (x' - y) * f y| ≤
      16 * Real.pi / (α * (1 - α)) * A * M * ‖x - x'‖ ^ α := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  have hfm := hf.aestronglyMeasurable
  rcases eq_or_ne x x' with rfl | hxx'
  · rw [sub_self, abs_zero]
    have : 0 < α * (1 - α) := mul_pos hα (by linarith)
    positivity
  set δ := ‖x - x'‖ with hδdef
  have hδ : 0 < δ := norm_pos_iff.mpr (sub_ne_zero.mpr hxx')
  set L := {y : ℝ^2 | y 1 < 0} with hLdef
  set N := {y : ℝ^2 | min (x 1 - 2 * δ) 0 < y 1 ∧ y 1 < 0 ∧ x 0 - 2 * δ < y 0 ∧
    y 0 < x 0 + 2 * δ} with hNdef
  have hNm : MeasurableSet N := measurableSet_rectangle _ _ _
  have hNL : N ⊆ L := fun y hy ↦ hy.2.1
  have hx0 : |x 0 - x' 0| ≤ δ := by simpa using PiLp.norm_apply_le (x - x') 0
  have hN3 : N ⊆ ball x (3 * δ) :=
    (rectangle_subset_ball hx (by positivity)).trans (ball_subset_ball (by linarith))
  have hN4 : N ⊆ ball x' (4 * δ) :=
    hN3.trans (ball_subset_ball' (by rw [dist_eq_norm, ← hδdef]; linarith))
  have hfar : ∀ y ∈ L \ N, 2 * δ ≤ ‖x - y‖ := le_norm_sub_of_mem_lower_diff_rectangle
  -- integrability
  have iKf := hK.integrableOn_lower_mul hf hx
  have iK'f := hK.integrableOn_lower_mul hf hx'
  have iD := hK.integrableOn_lower_sub hx hx'
  have iDf : IntegrableOn (fun y ↦ (K (x - y) - K (x' - y)) * (f y - f x)) L :=
    ((iKf.sub iK'f).sub (iD.mul_const (f x))).congr_fun
      (fun y _ ↦ by simp only [Pi.sub_apply]; ring) measurableSet_lower
  have hNfin : volume N ≠ ⊤ := ((measure_mono hN3).trans_lt measure_ball_lt_top).ne
  have i1 : IntegrableOn (fun y ↦ K (x - y) * (f y - f x)) N :=
    hK.integrableOn_mul_sub hα hfm hM x hNm (by linarith) hN3
  have i2 : IntegrableOn (fun y ↦ K (x' - y) * (f y - f x')) N :=
    hK.integrableOn_mul_sub hα hfm hM x' hNm (by linarith) hN4
  have i3 : IntegrableOn (fun y ↦ K (x' - y)) N :=
    hK.integrableOn_of_le x' hNm hNfin hx' fun _ hy ↦ le_norm_sub_of_lower hy.2.1
  set c := ∫ y in N, K (x' - y) with hcdef
  -- the decomposition
  have s1 : (∫ y in L, K (x - y) * f y) - ∫ y in L, K (x' - y) * f y =
      ∫ y in L, (K (x - y) - K (x' - y)) * (f y - f x) := by
    have iKK : IntegrableOn (fun y ↦ K (x - y) * f y - K (x' - y) * f y) L := iKf.sub iK'f
    rw [show (fun y ↦ (K (x - y) - K (x' - y)) * (f y - f x)) =
        fun y ↦ (K (x - y) * f y - K (x' - y) * f y) - (K (x - y) - K (x' - y)) * f x by
      funext y; ring, integral_sub iKK (iD.mul_const _), integral_mul_const,
      hK.integral_lower_sub_eq_zero hL hx hx', zero_mul, sub_zero, integral_sub iKf iK'f]
  have s2 : ∫ y in L, (K (x - y) - K (x' - y)) * (f y - f x) =
      (∫ y in N, (K (x - y) - K (x' - y)) * (f y - f x)) +
        ∫ y in L \ N, (K (x - y) - K (x' - y)) * (f y - f x) := by
    rw [← setIntegral_union disjoint_sdiff_right (measurableSet_lower.diff hNm)
      (iDf.mono_set hNL) (iDf.mono_set sdiff_subset), union_sdiff_cancel hNL]
  have s3 : ∫ y in N, (K (x - y) - K (x' - y)) * (f y - f x) =
      (∫ y in N, K (x - y) * (f y - f x)) - (∫ y in N, K (x' - y) * (f y - f x')) -
        (f x' - f x) * c := by
    have i23 : IntegrableOn
        (fun y ↦ K (x' - y) * (f y - f x') + (f x' - f x) * K (x' - y)) N :=
      i2.add (i3.const_mul _)
    rw [show (fun y ↦ (K (x - y) - K (x' - y)) * (f y - f x)) = fun y ↦ K (x - y) * (f y - f x) -
        (K (x' - y) * (f y - f x') + (f x' - f x) * K (x' - y)) by funext y; ring,
      integral_sub i1 i23, integral_add i2 (i3.const_mul _), integral_const_mul]
    ring
  -- the bounds
  have b1 := hK.abs_setIntegral_mul_sub_le hα hM x hNm (by linarith : (0 : ℝ) ≤ 3 * δ) hN3
  have b2 := hK.abs_setIntegral_mul_sub_le hα hM x' hNm (by linarith : (0 : ℝ) ≤ 4 * δ) hN4
  have b3 : |c| ≤ 4 * A := by
    have ht : -(2 * δ) ≤ min (x 1 - 2 * δ) 0 := le_min (by linarith) (by linarith)
    refine (hK.abs_setIntegral_rectangle_le hL hx' (a := x 0 - 2 * δ) (b := x 0 + 2 * δ) hδ
      (by linarith [(_root_.abs_le.mp hx0).2]) (by linarith [(_root_.abs_le.mp hx0).1])
      (min_le_right _ _)).trans ((div_le_iff₀ hδ).2 (by nlinarith))
  have b4 : |f x' - f x| ≤ M * δ ^ α := by simpa [norm_sub_rev] using hM x' x
  have b5 := (hK.integrableOn_sub_mul_sub_and_abs_le (p := x) hα hα1 hfm hM hxx'
    (measurableSet_lower.diff hNm) hfar le_rfl (fun y _ ↦ by
      rw [one_mul, norm_sub_rev])).2
  rw [s1, s2, s3]
  have hsum := image_constant_le hδ hα hα1
  calc |(∫ y in N, K (x - y) * (f y - f x)) - (∫ y in N, K (x' - y) * (f y - f x')) -
          (f x' - f x) * c + ∫ y in L \ N, (K (x - y) - K (x' - y)) * (f y - f x)|
      ≤ |∫ y in N, K (x - y) * (f y - f x)| + |∫ y in N, K (x' - y) * (f y - f x')| +
          |f x' - f x| * |c| + |∫ y in L \ N, (K (x - y) - K (x' - y)) * (f y - f x)| := by
        rw [← abs_mul]
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ A * M * (2 * Real.pi * (3 * δ) ^ α / α) + A * M * (2 * Real.pi * (4 * δ) ^ α / α) +
          M * δ ^ α * (4 * A) + 1 * A * M * δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α)) := by
        gcongr
    _ = A * M * (2 * Real.pi * (3 * δ) ^ α / α + 2 * Real.pi * (4 * δ) ^ α / α + 4 * δ ^ α +
          δ * (2 * Real.pi * (2 * δ) ^ (α - 1) / (1 - α))) := by ring
    _ ≤ A * M * (16 * Real.pi / (α * (1 - α)) * δ ^ α) := by gcongr
    _ = 16 * Real.pi / (α * (1 - α)) * A * M * δ ^ α := by ring

/-- **Size of the image integral at a radius.** For `|f| ≤ B` and `0 < ρ ≤ 1`,
`|R f(x)| ≤ A M · 2π(2ρ)^α/α + 2AB + AB · 2π log(1/ρ) + A ‖f‖₁`. -/
theorem abs_integral_lower_le_of_radius (hL : HasLineCancellation K) (hα : 0 < α)
    (hf : Integrable f) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) {x : ℝ^2} (hx : 0 < x 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    |∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * f y| ≤
      A * M * (2 * Real.pi * (2 * ρ) ^ α / α) + 2 * A * B +
        A * B * (2 * Real.pi * Real.log (1 / ρ)) + A * ∫ y, |f y| := by
  have hA := hK.nonneg
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hfm := hf.aestronglyMeasurable
  set L := {y : ℝ^2 | y 1 < 0} with hLdef
  set N := {y : ℝ^2 | min (x 1 - ρ) 0 < y 1 ∧ y 1 < 0 ∧ x 0 - ρ < y 0 ∧ y 0 < x 0 + ρ} with hNdef
  have hNm : MeasurableSet N := measurableSet_rectangle _ _ _
  have hNL : N ⊆ L := fun y hy ↦ hy.2.1
  have hN2 : N ⊆ ball x (2 * ρ) :=
    (rectangle_subset_ball hx hρ).trans (ball_subset_ball (by linarith))
  have hfar : ∀ y ∈ L \ N, ρ ≤ ‖x - y‖ := le_norm_sub_of_mem_lower_diff_rectangle
  have iKf := hK.integrableOn_lower_mul hf hx
  have hNfin : volume N ≠ ⊤ := ((measure_mono hN2).trans_lt measure_ball_lt_top).ne
  have i1 : IntegrableOn (fun y ↦ K (x - y) * (f y - f x)) N :=
    hK.integrableOn_mul_sub hα hfm hM x hNm (by linarith) hN2
  have i3 : IntegrableOn (fun y ↦ K (x - y)) N :=
    hK.integrableOn_of_le x hNm hNfin hx fun _ hy ↦ le_norm_sub_of_lower hy.2.1
  have hLN : MeasurableSet (L \ N) := measurableSet_lower.diff hNm
  -- the decomposition
  have s1 : ∫ y in L, K (x - y) * f y =
      (∫ y in N, K (x - y) * f y) + ∫ y in L \ N, K (x - y) * f y := by
    rw [← setIntegral_union disjoint_sdiff_right hLN (iKf.mono_set hNL) (iKf.mono_set sdiff_subset),
      union_sdiff_cancel hNL]
  have s2 : ∫ y in N, K (x - y) * f y =
      (∫ y in N, K (x - y) * (f y - f x)) + f x * ∫ y in N, K (x - y) := by
    rw [show (fun y ↦ K (x - y) * f y) = fun y ↦ K (x - y) * (f y - f x) + f x * K (x - y) by
      funext y; ring, integral_add i1 (i3.const_mul _), integral_const_mul]
  have s3 : ∫ y in L \ N, K (x - y) * f y =
      (∫ y in (L \ N) ∩ ball x 1, K (x - y) * f y) +
        ∫ y in (L \ N) \ ball x 1, K (x - y) * f y := by
    rw [← setIntegral_union (disjoint_sdiff_inter.symm.mono_left le_rfl)
      (hLN.diff measurableSet_ball) (iKf.mono_set (inter_subset_left.trans sdiff_subset))
      (iKf.mono_set (sdiff_subset.trans sdiff_subset)), inter_union_sdiff]
  -- the bounds
  have b1 := hK.abs_setIntegral_mul_sub_le hα hM x hNm (by linarith : (0 : ℝ) ≤ 2 * ρ) hN2
  have b2 : |f x * ∫ y in N, K (x - y)| ≤ B * (2 * A) := by
    have ht : -ρ ≤ min (x 1 - ρ) 0 := le_min (by linarith) (by linarith)
    rw [abs_mul]
    exact mul_le_mul (hB x) ((hK.abs_setIntegral_rectangle_le hL hx (a := x 0 - ρ)
      (b := x 0 + ρ) hρ le_rfl le_rfl (min_le_right _ _)).trans ((div_le_iff₀ hρ).2 (by nlinarith)))
      (abs_nonneg _) hB0
  have b3 : |∫ y in (L \ N) ∩ ball x 1, K (x - y) * f y| ≤
      A * B * (2 * Real.pi * Real.log (1 / ρ)) := by
    have hsub : (L \ N) ∩ ball x 1 ⊆ ball x 1 \ ball x ρ := fun y hy ↦
      ⟨hy.2, fun h ↦ by
        have := hfar y hy.1
        rw [mem_ball, dist_eq_norm, norm_sub_rev] at h
        linarith⟩
    have hle : ∀ y ∈ (L \ N) ∩ ball x 1, ‖K (x - y) * f y‖ ≤ A * B * (‖x - y‖ ^ 2)⁻¹ := by
      intro y hy
      have hn : 0 < ‖x - y‖ := hρ.trans_le (hfar y hy.1)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_right_comm, ← div_eq_mul_inv]
      exact mul_le_mul (hK.abs_le _) (hB y) (abs_nonneg _) (by positivity) |>.trans_eq
        (by ring)
    rw [← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_lintegral_eq (hLN.inter measurableSet_ball) hsub hle
      (lintegral_annulus_mul_inv_sq x (mul_nonneg hA hB0) hρ hρ1)
      (by have := Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith : 1 ≤ 1 / ρ); positivity)
  have b4 := hK.abs_setIntegral_mul_le hf x ((hLN.diff measurableSet_ball)) one_pos
    fun y hy ↦ le_norm_sub_of_mem_compl_ball hy.2
  rw [one_pow, div_one] at b4
  rw [s1, s2, s3]
  calc |(∫ y in N, K (x - y) * (f y - f x)) + f x * (∫ y in N, K (x - y)) +
        ((∫ y in (L \ N) ∩ ball x 1, K (x - y) * f y) +
          ∫ y in (L \ N) \ ball x 1, K (x - y) * f y)|
      ≤ |∫ y in N, K (x - y) * (f y - f x)| + |f x * ∫ y in N, K (x - y)| +
          (|∫ y in (L \ N) ∩ ball x 1, K (x - y) * f y| +
            |∫ y in (L \ N) \ ball x 1, K (x - y) * f y|) :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ A * M * (2 * Real.pi * (2 * ρ) ^ α / α) + B * (2 * A) +
          (A * B * (2 * Real.pi * Real.log (1 / ρ)) + A * ∫ y, |f y|) := by
        gcongr
    _ = _ := by ring

/-- **Size of the image integral.** For `|f| ≤ B`,
`|R f(x)| ≤ A (4πM/α + 2B + ‖f‖₁)` at every point of the upper half-plane. -/
theorem abs_integral_lower_le (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Integrable f) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) {x : ℝ^2} (hx : 0 < x 1) :
    |∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * f y| ≤
      A * (4 * Real.pi * M / α + 2 * B + ∫ y, |f y|) := by
  have hA := hK.nonneg
  have hM0 := nonneg_of_holder hM
  refine (hK.abs_integral_lower_le_of_radius hL hα hf hM hB hx one_pos le_rfl).trans ?_
  have h2 : (2 * (1 : ℝ)) ^ α ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
  rw [div_one, Real.log_one, mul_zero, mul_zero, add_zero]
  have : A * M * (2 * Real.pi * (2 * 1) ^ α / α) ≤ A * (4 * Real.pi * M / α) := by
    rw [show A * (4 * Real.pi * M / α) = A * M * (2 * Real.pi * 2 / α) by ring]
    gcongr
  nlinarith

/-- **Logarithmic size bound of the image integral.** For `|f| ≤ B`,
`|R f(x)| ≤ (4πA/α)(1 + B log(2 + M)) + 2AB + A ‖f‖₁`. -/
theorem abs_integral_lower_le_log (hL : HasLineCancellation K) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Integrable f) (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) {x : ℝ^2} (hx : 0 < x 1) :
    |∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * f y| ≤
      4 * Real.pi * A / α * (1 + B * Real.log (2 + M)) + 2 * A * B + A * ∫ y, |f y| := by
  have hA := hK.nonneg
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hlog2 : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith [nonneg_of_holder hM])
  have key (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
      |∫ y in {y : ℝ^2 | y 1 < 0}, K (x - y) * f y| ≤
        4 * Real.pi * A / α * (M * ρ ^ α) + 2 * A * B +
          A * B * (2 * Real.pi * Real.log (1 / ρ)) + A * ∫ y, |f y| := by
    refine (hK.abs_integral_lower_le_of_radius hL hα hf hM hB hx hρ hρ1).trans ?_
    have h2 : (2 * ρ) ^ α ≤ 2 * ρ ^ α := by
      rw [Real.mul_rpow (by norm_num) hρ.le]
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
    have : A * M * (2 * Real.pi * (2 * ρ) ^ α / α) ≤
        A * M * (2 * Real.pi * (2 * ρ ^ α) / α) := by
      have := nonneg_of_holder hM
      gcongr
    have e : 4 * Real.pi * A / α * (M * ρ ^ α) = A * M * (2 * Real.pi * (2 * ρ ^ α) / α) := by
      ring
    linarith
  have hc : 0 ≤ 2 * Real.pi * A / α := by positivity
  have hc4 : 4 * Real.pi * A / α = 2 * (2 * Real.pi * A / α) := by ring
  have hlogB := mul_nonneg hc (mul_nonneg hB0 hlog2)
  rcases le_or_gt M 1 with hM1 | hM1
  · refine (key 1 one_pos le_rfl).trans ?_
    rw [Real.one_rpow, mul_one, div_one, Real.log_one, mul_zero, mul_zero, add_zero, mul_add,
      mul_one, hc4]
    nlinarith [mul_le_mul_of_nonneg_left hM1 hc]
  · have hMpos : 0 < M := by linarith
    set ρ := M ^ (-1 / α) with hρdef
    have hρα : M * ρ ^ α = 1 := by
      rw [hρdef, ← Real.rpow_mul hMpos.le, show -1 / α * α = -1 by field_simp,
        Real.rpow_neg_one, mul_inv_cancel₀ hMpos.ne']
    have hlog : Real.log (1 / ρ) = Real.log M / α := by
      rw [one_div, Real.log_inv, hρdef, Real.log_rpow hMpos]
      ring
    refine (key ρ (Real.rpow_pos_of_pos hMpos _) (Real.rpow_le_one_of_one_le_of_nonpos hM1.le
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) hα.le))).trans ?_
    rw [hρα, hlog]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (Real.log_le_log hMpos (by linarith : M ≤ 2 + M)) hB0) hc
    have : A * B * (2 * Real.pi * (Real.log M / α)) = 2 * Real.pi * A / α * (B * Real.log M) := by
      ring
    rw [mul_add, mul_one, hc4]
    nlinarith

end IsSingularKernel

end PotentialTheory.Planar
