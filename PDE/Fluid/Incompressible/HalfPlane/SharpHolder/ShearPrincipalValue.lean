/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarPrincipalValue
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearTransport
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainVertical
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Strip and disc truncations of the kernel `K₂`

For the kernel `K₂(y) = (y₁² - y₂²) / (2 |y|⁴)`, a point `x` inside a rectangle
`Q = [x₁ - a, x₁ + a] × [x₂ - b₁, x₂ + b₂]` and a function `W` Hölder at `x` on `Q`, the
truncations of `∫_Q K₂(x - y) W(y) dy` removing the vertical strip `|y₁ - x₁| < ε` converge to the
disc principal value plus `(π/2) W(x)`. This is Lemma B.1 of Chen and Hou, Part I, summed over
the four quadrants at `x`: the region of the strip outside the disc carries the mass
`∫ K₂ → -π/2`, since on the line through `x` the kernel is `-1/(2 t²)`.

For the localized velocity gradients of Part I, (3.4), `u_y = π⁻¹ P.V. ∫ K₂ W + W(x)/2`, so `u_y(x)`
is `π⁻¹` times the limit of the strip truncations, with no local term.

## Main results

* `integral_shearKernel_strip_diff_ball`: the mass of `K₂` on the strip outside the disc,
  `∫_{-ε}^{ε} (b₁/(2(s² + b₁²)) + b₂/(2(s² + b₂²))) ds - π/2`.
* `exists_tendsto_setIntegral_box_diff_ball`: the disc principal value exists.
* `tendsto_setIntegral_box_inter_strip`: the strip truncations converge to the principal value
  plus `(π/2) W(x)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (3.4), p. 27, and Appendix B.1,
  Lemma B.1, p. 130.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open PDE.Analysis (planeEquiv planeEquiv_symm_apply measurePreserving_planeEquiv)
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

variable {K : ℝ^2 → ℝ} {a b₁ b₂ : ℝ}

/-- `K₂` in coordinates. -/
theorem shearKernel_apply (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) (v : ℝ^2) :
    K v = shearDensity (v 0) (v 1) := by
  rw [hK, shearDensity_eq, show ‖v‖ ^ 4 = (‖v‖ ^ 2) ^ 2 by ring, EuclideanSpace.norm_sq_fin_two]

/-- `K₂` is even. -/
theorem shearKernel_neg (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) (v : ℝ^2) :
    K (-v) = K v := by
  rw [hK, hK, norm_neg]
  simp only [PiLp.neg_apply, neg_sq]

/-- `|K₂(v)| ≤ 1 / (2 |v|²)`. -/
theorem abs_shearKernel_le (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) (v : ℝ^2) :
    |K v| ≤ 1 / (2 * ‖v‖ ^ 2) := by
  rw [shearKernel_apply hK]
  have h := EuclideanSpace.norm_sq_fin_two v
  simp only [shearDensity_eq]
  rcases eq_or_ne (v 0 ^ 2 + v 1 ^ 2) 0 with h0 | h0
  · rw [h0]
    simp
  · have hp : 0 < v 0 ^ 2 + v 1 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (v 0 ^ 2 + v 1 ^ 2) ^ 2), h,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have : |v 0 ^ 2 - v 1 ^ 2| ≤ v 0 ^ 2 + v 1 ^ 2 :=
      abs_le.2 ⟨by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)],
        by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]⟩
    nlinarith

/-- `K₂` is measurable. -/
theorem measurable_shearKernel (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) :
    Measurable K := by
  have : K = PotentialTheory.Planar.hessianKernel 0 0 := funext fun y ↦ by
    rw [hK, PotentialTheory.Planar.hessianKernel_zero_zero]
  rw [this]
  exact PotentialTheory.Planar.measurable_hessianKernel 0 0

/-- `∫_{-ε}^{ε} (ε² - s²)^{1/2} ds = π ε² / 2`. -/
theorem integral_sqrt_sq_sub_sq {ε : ℝ} (hε : 0 < ε) :
    ∫ s in (-ε)..ε, Real.sqrt (ε ^ 2 - s ^ 2) = Real.pi / 2 * ε ^ 2 := by
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
    (fun s ↦ Real.sqrt (ε ^ 2 - s ^ 2)) hε.ne'
  simp only [mul_neg, mul_one, smul_eq_mul] at h
  have e : ∀ v : ℝ, Real.sqrt (ε ^ 2 - (ε * v) ^ 2) = ε * Real.sqrt (1 - v ^ 2) := fun v ↦ by
    rw [show ε ^ 2 - (ε * v) ^ 2 = ε ^ 2 * (1 - v ^ 2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hε.le]
  simp only [e, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq] at h
  field_simp at h
  linarith

/-- On a vertical line `s ≠ 0`, the mass of `K₂(s, ·)` on `[-b₁, b₂]` outside `|t| < r`. -/
private theorem integral_shearDensity_diff {s r : ℝ} (hs : s ≠ 0) (hr : 0 ≤ r) (hb₁ : r ≤ b₁)
    (hb₂ : r ≤ b₂) :
    ∫ t in Icc (-b₁) b₂ \ Ioo (-r) r, shearDensity s t =
      b₁ / (2 * (s ^ 2 + b₁ ^ 2)) + b₂ / (2 * (s ^ 2 + b₂ ^ 2)) - r / (s ^ 2 + r ^ 2) := by
  have hc := (continuous_shearDensity_right hs).continuousOn (s := Icc (-b₁) b₂)
  rw [setIntegral_sdiff measurableSet_Ioo hc.integrableOn_Icc
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith) hb₂)),
    setIntegral_Icc_eq_sub_of_hasDerivAt (by linarith) hc
      fun t _ ↦ hasDerivAt_shearPrimitive hs t,
    ← integral_Icc_eq_integral_Ioo,
    setIntegral_Icc_eq_sub_of_hasDerivAt (by linarith)
      (continuous_shearDensity_right hs).continuousOn fun t _ ↦ hasDerivAt_shearPrimitive hs t]
  have h₁ : s ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h₂ : s ^ 2 + b₁ ^ 2 ≠ 0 := by positivity
  have h₃ : s ^ 2 + b₂ ^ 2 ≠ 0 := by positivity
  simp only [neg_sq]
  field_simp
  ring

/-- The mass of `K₂` on the part of the strip `|u₁| < ε` of `ℝ × [-b₁, b₂]` outside the disc
`|u| < ε` (`ε ≤ b₁, b₂`):
`∫_{-ε}^{ε} (b₁/(2(s² + b₁²)) + b₂/(2(s² + b₂²))) ds - π/2`. -/
theorem integral_shearKernel_strip_diff_ball
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {ε : ℝ} (hε : 0 < ε) (hb₁ : ε ≤ b₁)
    (hb₂ : ε ≤ b₂) :
    ∫ u in {u : ℝ^2 | |u 0| < ε ∧ -b₁ ≤ u 1 ∧ u 1 ≤ b₂ ∧ ε ≤ ‖u‖}, K u =
      (∫ s in (-ε)..ε, (b₁ / (2 * (s ^ 2 + b₁ ^ 2)) + b₂ / (2 * (s ^ 2 + b₂ ^ 2)))) -
        Real.pi / 2 := by
  set S : Set (ℝ^2) := {u | |u 0| < ε ∧ -b₁ ≤ u 1 ∧ u 1 ≤ b₂ ∧ ε ≤ ‖u‖} with hS
  have h₀ : Measurable fun u : ℝ^2 ↦ u 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  have hSm : MeasurableSet S :=
    (measurableSet_lt (continuous_abs.measurable.comp h₀) measurable_const).inter
      ((measurableSet_le measurable_const h₁).inter ((measurableSet_le h₁ measurable_const).inter
        (measurableSet_le measurable_const measurable_norm)))
  have hKm := measurable_shearKernel hK
  -- integrability: `K` is bounded on `S`, which is bounded
  have hSb : S ⊆ closedBall 0 (ε + b₁ + b₂) := fun u hu ↦ by
    rw [mem_closedBall, dist_zero_right]
    refine (EuclideanSpace.norm_le_abs_add_abs_fin_two u).trans ?_
    have : |u 1| ≤ b₁ + b₂ := abs_le.2 ⟨by linarith [hu.2.1], by linarith [hu.2.2.1]⟩
    linarith [hu.1]
  have hKi : IntegrableOn K S := by
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2))
      ((measure_mono hSb).trans_lt measure_closedBall_lt_top).ne hKm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hSm] with u hu
    rw [Real.norm_eq_abs]
    refine (abs_shearKernel_le hK u).trans ?_
    have := hu.2.2.2
    gcongr
  -- Fubini in the coordinates `(abscissa, height)`
  have hmp := measurePreserving_planeEquiv.symm
  have hFi : Integrable (S.indicator K) := (integrable_indicator_iff hSm).2 hKi
  have hFi' : Integrable fun q : ℝ × ℝ ↦ S.indicator K (planeEquiv.symm q) :=
    hmp.integrable_comp_emb planeEquiv.symm.measurableEmbedding |>.2 hFi
  have hprod : ∫ u in S, K u = ∫ s, ∫ t, S.indicator K !₂[s, t] := by
    rw [← integral_indicator hSm, ← hmp.integral_comp' (S.indicator K), Measure.volume_eq_prod,
      integral_prod _ (by rwa [← Measure.volume_eq_prod])]
    simp only [planeEquiv_symm_apply]
  -- the vertical lines
  set f : ℝ → ℝ := fun s ↦ b₁ / (2 * (s ^ 2 + b₁ ^ 2)) + b₂ / (2 * (s ^ 2 + b₂ ^ 2)) -
    Real.sqrt (ε ^ 2 - s ^ 2) / ε ^ 2 with hf
  have hline : ∀ s, s ≠ 0 → ∫ t, S.indicator K !₂[s, t] = (Ioo (-ε) ε).indicator f s := by
    intro s hs
    by_cases hsε : |s| < ε
    · rw [indicator_of_mem (show s ∈ Ioo (-ε) ε from abs_lt.1 hsε)]
      set r := Real.sqrt (ε ^ 2 - s ^ 2) with hr
      have hrsq : r ^ 2 = ε ^ 2 - s ^ 2 :=
        Real.sq_sqrt (by linarith [sq_lt_sq' (abs_lt.1 hsε).1 (abs_lt.1 hsε).2])
      have hrε : r ≤ ε := Real.sqrt_le_iff.2 ⟨hε.le, by nlinarith [sq_nonneg s]⟩
      have hslice : (fun t ↦ S.indicator K !₂[s, t]) =
          (Icc (-b₁) b₂ \ Ioo (-r) r).indicator (shearDensity s) := by
        ext t
        have hn : ‖!₂[s, t]‖ ^ 2 = s ^ 2 + t ^ 2 := by
          rw [EuclideanSpace.norm_sq_fin_two]
          simp
        have key : ε ≤ ‖!₂[s, t]‖ ↔ t ∉ Ioo (-r) r := by
          rw [mem_Ioo, ← abs_lt, not_lt, hr, ← Real.sqrt_sq (abs_nonneg t),
            Real.sqrt_le_sqrt_iff (sq_nonneg _), sq_abs, sub_le_iff_le_add', ← hn,
            pow_le_pow_iff_left₀ hε.le (norm_nonneg _) two_ne_zero]
        have hmem : !₂[s, t] ∈ S ↔ t ∈ Icc (-b₁) b₂ \ Ioo (-r) r := by
          rw [Set.mem_sdiff, mem_Icc, ← key]
          simp only [hS, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.cons_val_fin_one, hsε, true_and, and_assoc]
        simp [indicator_apply, hmem, shearKernel_apply hK]
      rw [hslice, integral_indicator (measurableSet_Icc.diff measurableSet_Ioo),
        integral_shearDensity_diff hs (Real.sqrt_nonneg _) (hrε.trans hb₁) (hrε.trans hb₂), hf,
        show s ^ 2 + r ^ 2 = ε ^ 2 by rw [hrsq]; ring]
    · rw [indicator_of_notMem (fun h : s ∈ Ioo (-ε) ε ↦ hsε (abs_lt.2 h))]
      have : (fun t ↦ S.indicator K !₂[s, t]) = fun _ ↦ 0 := by
        ext t
        refine indicator_of_notMem (fun h ↦ hsε ?_) _
        simpa [hS] using h.1
      rw [this, integral_zero]
  have hae : (fun s ↦ ∫ t, S.indicator K !₂[s, t]) =ᵐ[volume] (Ioo (-ε) ε).indicator f := by
    filter_upwards [Measure.ae_ne volume 0] with s hs using hline s hs
  rw [hprod, integral_congr_ae hae, integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith), hf]
  have hc₁ : Continuous fun s : ℝ ↦ b₁ / (2 * (s ^ 2 + b₁ ^ 2)) + b₂ / (2 * (s ^ 2 + b₂ ^ 2)) := by
    have hb₁' : 0 < b₁ := hε.trans_le hb₁
    have hb₂' : 0 < b₂ := hε.trans_le hb₂
    exact (continuous_const.div (by fun_prop) fun s ↦ by positivity).add
      (continuous_const.div (by fun_prop) fun s ↦ by positivity)
  have hc₂ : Continuous fun s : ℝ ↦ Real.sqrt (ε ^ 2 - s ^ 2) / ε ^ 2 := by fun_prop
  rw [intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₂.intervalIntegrable _ _),
    intervalIntegral.integral_div, integral_sqrt_sq_sub_sq hε]
  field_simp

/-- `K₂(x - y) (W(y) - W(x))` is integrable on a bounded measurable set `S` when `W` is Hölder at
`x` on `S`. -/
theorem integrableOn_shearKernel_mul_sub (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {S : Set (ℝ^2)} (hSm : MeasurableSet S) (hSb : Bornology.IsBounded S) {x : ℝ^2}
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W (volume.restrict S)) {M α : ℝ} (hα : 0 < α)
    (hhol : ∀ y ∈ S, |W y - W x| ≤ M * ‖y - x‖ ^ α) :
    IntegrableOn (fun y ↦ K (x - y) * (W y - W x)) S := by
  have hKx : Measurable fun y ↦ K (x - y) :=
    (measurable_shearKernel hK).comp (measurable_const.sub measurable_id)
  have hGm : AEStronglyMeasurable (S.indicator fun y ↦ K (x - y) * (W y - W x)) :=
    (aestronglyMeasurable_indicator_iff hSm).2
      (hKx.aestronglyMeasurable.mul (hWm.sub aestronglyMeasurable_const))
  obtain ⟨r, hr⟩ := hSb.subset_closedBall x
  set F : ℝ^2 → ℝ := fun v ↦ S.indicator (fun y ↦ K (x - y) * (W y - W x)) (v + x)
  have hFb : ∀ v, ‖F v‖ ≤ |M| / 2 * ‖v‖ ^ (-(2 - α)) := fun v ↦ by
    by_cases hv : v + x ∈ S
    · simp only [F, indicator_of_mem hv, Real.norm_eq_abs]
      have e : x - (v + x) = -v := by abel
      rw [e, abs_mul, shearKernel_neg hK]
      have h := hhol _ hv
      rw [add_sub_cancel_right] at h
      by_cases hv0 : v = 0
      · rw [hv0, zero_add, sub_self, abs_zero, mul_zero]
        positivity
      have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      calc |K v| * |W (v + x) - W x| ≤ 1 / (2 * ‖v‖ ^ 2) * (|M| * ‖v‖ ^ α) :=
            mul_le_mul (abs_shearKernel_le hK v) (h.trans (mul_le_mul_of_nonneg_right
              (le_abs_self M) (by positivity))) (abs_nonneg _) (by positivity)
        _ = |M| / 2 * ‖v‖ ^ (-(2 - α)) := by
            rw [show -(2 - α) = α - 2 by ring, Real.rpow_sub hn, Real.rpow_two]
            field_simp
    · simp only [F, indicator_of_notMem hv, norm_zero]
      positivity
  have hFm : AEStronglyMeasurable F :=
    hGm.comp_measurePreserving (measurePreserving_add_right volume x)
  have hFball : IntegrableOn F (ball 0 (r + 1)) :=
    integrableOn_ball_of_norm_le_rpow (by simp) (by simp; linarith) (ae_of_all _ hFb) hFm
  have hsupp : Function.support F ⊆ ball 0 (r + 1) := by
    intro v hv
    by_contra hvb
    apply hv
    have : v + x ∉ S := fun h ↦ by
      have := hr h
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right] at this
      exact hvb (mem_ball_zero_iff.2 (by linarith))
    simp only [F, indicator_of_notMem this]
  have hFint : Integrable F := (integrableOn_iff_integrable_of_support_subset hsupp).1 hFball
  have h := hFint.comp_sub_right x
  simp only [F, sub_add_cancel] at h
  exact (integrable_indicator_iff hSm).1 h

/-- A function Hölder at `x` on a bounded set is bounded there. -/
theorem exists_bound_of_holder {S : Set (ℝ^2)} (hS : Bornology.IsBounded S) {x : ℝ^2}
    {W : ℝ^2 → ℝ} {M α : ℝ} (hα : 0 < α) (hhol : ∀ y ∈ S, |W y - W x| ≤ M * ‖y - x‖ ^ α) :
    ∃ C, ∀ y ∈ S, |W y| ≤ C := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall x
  refine ⟨|W x| + |M| * max R 0 ^ α, fun y hy ↦ ?_⟩
  have h1 := hhol y hy
  have h2 : ‖y - x‖ ≤ max R 0 := by
    have := hR hy
    rw [mem_closedBall, dist_eq_norm] at this
    exact this.trans (le_max_left _ _)
  have h3 : ‖y - x‖ ^ α ≤ max R 0 ^ α := Real.rpow_le_rpow (norm_nonneg _) h2 hα.le
  have h4 : M * ‖y - x‖ ^ α ≤ |M| * max R 0 ^ α :=
    (mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg M))
  calc |W y| = |W x + (W y - W x)| := by ring_nf
    _ ≤ |W x| + |W y - W x| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- `|y₁ - x₁| ≤ |y - x|`, so the disc `|y - x| < ε` lies in the strip `|y₁ - x₁| < ε`. -/
theorem abs_sub_apply_le_norm (x y : ℝ^2) (i : Fin 2) : |y i - x i| ≤ ‖y - x‖ := by
  have := PiLp.norm_apply_le (y - x) i
  simpa using this

/-- **Strip and disc truncations.** Let `x` lie inside the box `Q = Q_{a,b₁,b₂}(x)`
(`a, b₁, b₂ > 0`) and let `W` be measurable and Hölder at `x` on `Q`. If the disc truncations
`∫_{Q ∖ B(x, ε)} K₂(x - y) W(y) dy` converge to `v`, the strip truncations
`∫_{Q, |y₁ - x₁| ≥ ε} K₂(x - y) W(y) dy` converge to `v + (π/2) W(x)` (Chen and Hou, Part I,
Lemma B.1, over the four quadrants at `x`). -/
theorem tendsto_setIntegral_box_inter_strip (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {x : ℝ^2} (ha : 0 < a) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {M α : ℝ} (hα : 0 < α)
    (hhol : ∀ y ∈ box a b₁ b₂ x, |W y - W x| ≤ M * ‖y - x‖ ^ α) {v : ℝ}
    (hv : Tendsto (fun ε ↦ ∫ y in box a b₁ b₂ x \ ball x ε, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 v)) :
    Tendsto (fun ε ↦ ∫ y in box a b₁ b₂ x ∩ {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 (v + Real.pi / 2 * W x)) := by
  set Q := box a b₁ b₂ x with hQ
  have hQm : MeasurableSet Q := measurableSet_box x
  have hQb : Bornology.IsBounded Q := isBounded_box x
  have hKm := measurable_shearKernel hK
  have hKx : Measurable fun y ↦ K (x - y) := hKm.comp (measurable_const.sub measurable_id)
  have hG := integrableOn_shearKernel_mul_sub hK hQm hQb hWm.restrict hα hhol
  -- `W` is bounded on `Q`
  obtain ⟨Mw, hWb⟩ := exists_bound_of_holder hQb hα hhol
  have hQfin : volume Q < ⊤ := hQb.measure_lt_top
  -- integrability of `K₂(x - y) W(y)` away from `x`
  have hKW : ∀ ε, 0 < ε → ∀ T ⊆ Q, MeasurableSet T → (∀ y ∈ T, ε ≤ ‖x - y‖) →
      IntegrableOn (fun y ↦ K (x - y) * W y) T := by
    intro ε hε T hTQ hTm hTε
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2) * Mw)
      ((measure_mono hTQ).trans_lt hQfin).ne
      (hKx.aestronglyMeasurable.mul hWm) ?_
    filter_upwards [ae_restrict_mem hTm] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ((abs_shearKernel_le hK _).trans ?_) (hWb y (hTQ hy)) (abs_nonneg _)
      (by positivity)
    have := hTε y hy
    gcongr
  have h₀ : Measurable fun y : ℝ^2 ↦ y 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  set S : ℝ → Set (ℝ^2) := fun ε ↦ (Q ∩ {y | |y 0 - x 0| < ε}) \ ball x ε with hS
  have hSm (ε : ℝ) : MeasurableSet (S ε) := (hQm.inter (measurableSet_lt
    (continuous_abs.measurable.comp (h₀.sub measurable_const)) measurable_const)).diff
      measurableSet_ball
  have hSQ (ε : ℝ) : S ε ⊆ Q := fun y hy ↦ hy.1.1
  have hfar (ε : ℝ) (y : ℝ^2) (hy : y ∉ ball x ε) : ε ≤ ‖x - y‖ :=
    dist_eq_norm x y ▸ not_lt.1 (mt mem_ball'.2 hy)
  -- the decomposition of the disc truncation
  have hdec (ε : ℝ) (hε : 0 < ε) : ∫ y in Q \ ball x ε, K (x - y) * W y =
      (∫ y in Q ∩ {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y) + ∫ y in S ε, K (x - y) * W y := by
    have hsub : Q ∩ {y | ε ≤ |y 0 - x 0|} ⊆ Q \ ball x ε := fun y hy ↦ ⟨hy.1, fun hb ↦
      not_le.2 (mem_ball_iff_norm.1 hb) (hy.2.trans (abs_sub_apply_le_norm x y 0))⟩
    have hunion : Q \ ball x ε = (Q ∩ {y | ε ≤ |y 0 - x 0|}) ∪ S ε :=
      Subset.antisymm (fun y hy ↦ (le_or_gt ε |y 0 - x 0|).imp (⟨hy.1, ·⟩) (⟨⟨hy.1, ·⟩, hy.2⟩))
        (union_subset hsub fun y h ↦ ⟨h.1.1, h.2⟩)
    have hKWb := hKW ε hε _ sdiff_subset (hQm.diff measurableSet_ball) fun y hy ↦ hfar ε y hy.2
    rw [hunion, setIntegral_union
      (disjoint_left.2 fun y h₁ h₂ ↦ (h₂.1.2 : |y 0 - x 0| < ε).not_ge h₁.2) (hSm ε)
      (hKWb.mono_set (hunion ▸ subset_union_left)) (hKWb.mono_set (hunion ▸ subset_union_right))]
  -- the region between the strip and the disc
  have hval : ∀ ε, 0 < ε → ε ≤ a → ε ≤ b₁ → ε ≤ b₂ → ∫ y in S ε, K (x - y) =
      (∫ s in (-ε)..ε, (b₂ / (2 * (s ^ 2 + b₂ ^ 2)) + b₁ / (2 * (s ^ 2 + b₁ ^ 2)))) -
        Real.pi / 2 := by
    intro ε hε hεa hεb₁ hεb₂
    set S' : Set (ℝ^2) := {u | |u 0| < ε ∧ -b₂ ≤ u 1 ∧ u 1 ≤ b₁ ∧ ε ≤ ‖u‖} with hS'
    have h₁ : Measurable fun u : ℝ^2 ↦ u 1 :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
    have hS'm : MeasurableSet S' :=
      (measurableSet_lt (continuous_abs.measurable.comp h₀) measurable_const).inter
        ((measurableSet_le measurable_const h₁).inter ((measurableSet_le h₁ measurable_const).inter
          (measurableSet_le measurable_const measurable_norm)))
    rw [← integral_shearKernel_strip_diff_ball hK hε hεb₂ hεb₁, ← integral_indicator (hSm ε),
      ← integral_indicator hS'm,
      ← integral_sub_left_eq_self (fun y ↦ (S ε).indicator (fun y ↦ K (x - y)) y) volume x]
    congr 1
    ext u
    have hmem : x - u ∈ S ε ↔ u ∈ S' := by
      simp only [hS, hS', hQ, box, Set.mem_sdiff, Set.mem_inter_iff, mem_ofPred_eq,
        Metric.mem_ball, dist_eq_norm, PiLp.sub_apply, sub_sub_cancel_left, norm_neg, not_lt]
      rw [abs_neg]
      constructor
      · rintro ⟨⟨⟨_, _, h₃, h₄⟩, h₅⟩, h₆⟩
        exact ⟨h₅, by linarith, by linarith, h₆⟩
      · rintro ⟨h₅, h₃, h₄, h₆⟩
        have := abs_lt.1 h₅
        exact ⟨⟨⟨by linarith, by linarith, by linarith, by linarith⟩, h₅⟩, h₆⟩
    by_cases hu : u ∈ S'
    · rw [indicator_of_mem (hmem.2 hu), indicator_of_mem hu, sub_sub_cancel]
    · rw [indicator_of_notMem (fun h ↦ hu (hmem.1 h)), indicator_of_notMem hu]
  -- the subtracted part over the shrinking region tends to zero
  have hGS : Tendsto (fun ε ↦ ∫ y in S ε, K (x - y) * (W y - W x)) (𝓝[>] 0) (𝓝 0) := by
    have h : ∀ ε, ∫ y in S ε, K (x - y) * (W y - W x) =
        ∫ y in Q, (S ε).indicator (fun y ↦ K (x - y) * (W y - W x)) y := fun ε ↦ by
      rw [setIntegral_indicator (hSm ε), inter_eq_right.2 (hSQ ε)]
    simp_rw [h]
    have hdom := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := volume.restrict Q) (f := fun _ ↦ (0 : ℝ))
      (F := fun ε ↦ (S ε).indicator (fun y ↦ K (x - y) * (W y - W x)))
      (fun y ↦ ‖K (x - y) * (W y - W x)‖)
      (Eventually.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hSm ε))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self _ y)
      hG.norm ?_
    · rwa [integral_zero] at hdom
    have hae : ∀ᵐ y : ℝ^2, y 0 ≠ x 0 :=
      measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))
    filter_upwards [ae_restrict_of_ae hae] with y hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hy)))] with ε hε
    rw [indicator_of_notMem fun h ↦ (not_lt.2 hε.le) h.1.2]
  -- the strip integral of the regular part tends to zero
  set f : ℝ → ℝ := fun s ↦ b₂ / (2 * (s ^ 2 + b₂ ^ 2)) + b₁ / (2 * (s ^ 2 + b₁ ^ 2)) with hf
  have hI : Tendsto (fun ε ↦ ∫ s in (-ε)..ε, f s) (𝓝[>] 0) (𝓝 0) := by
    have hb (b : ℝ) (hb : 0 < b) (s : ℝ) : b / (2 * (s ^ 2 + b ^ 2)) ≤ 1 / (2 * b) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg s]
    have hfb (s : ℝ) : ‖f s‖ ≤ 1 / (2 * b₂) + 1 / (2 * b₁) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith [hb b₂ hb₂ s, hb b₁ hb₁ s]
    have hb : ∀ ε, ‖∫ s in (-ε)..ε, f s‖ ≤ (1 / (2 * b₂) + 1 / (2 * b₁)) * |ε - -ε| := fun ε ↦
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ ↦ hfb s
    have hlim : Tendsto (fun ε : ℝ ↦ (1 / (2 * b₂) + 1 / (2 * b₁)) * |ε - -ε|) (𝓝[>] 0)
        (𝓝 0) := by
      have hc : Continuous fun ε : ℝ ↦ (1 / (2 * b₂) + 1 / (2 * b₁)) * |ε - -ε| := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm hb hlim
  -- assembling
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ y in Q \ ball x ε, K (x - y) * W y) -
      (W x * ((∫ s in (-ε)..ε, f s) - Real.pi / 2) +
        ∫ y in S ε, K (x - y) * (W y - W x)) =
      ∫ y in Q ∩ {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (lt_min ha (lt_min hb₁ hb₂)))] with ε (hε : 0 < ε) hεm
    have hεa : ε ≤ a := hεm.trans (min_le_left _ _)
    have hεb₁ : ε ≤ b₁ := hεm.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεb₂ : ε ≤ b₂ := hεm.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hsplit : ∫ y in S ε, K (x - y) * W y =
        W x * (∫ y in S ε, K (x - y)) + ∫ y in S ε, K (x - y) * (W y - W x) := by
      rw [← integral_const_mul, ← sub_eq_iff_eq_add, ← integral_sub
        (hKW ε hε _ (hSQ ε) (hSm ε) fun y hy ↦ hfar ε y hy.2) (hG.mono_set (hSQ ε))]
      congr 1 with y
      ring
    rw [hdec ε hε, hsplit, hval ε hε hεa hεb₁ hεb₂]
    ring
  refine Tendsto.congr' heq ?_
  have := hv.sub ((tendsto_const_nhds (x := W x)).mul
    (hI.sub (tendsto_const_nhds (x := Real.pi / 2))) |>.add hGS)
  convert this using 2
  ring

/-- **Existence of the disc principal value** of `∫_Q K₂(x - y) W(y) dy` for `x` inside the box
`Q = Q_{a,b₁,b₂}(x)` and `W` measurable and Hölder at `x` on `Q`. -/
theorem exists_tendsto_setIntegral_box_diff_ball
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {x : ℝ^2} (ha : 0 < a) (hb₁ : 0 < b₁)
    (hb₂ : 0 < b₂) {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {M α : ℝ} (hα : 0 < α)
    (hhol : ∀ y ∈ box a b₁ b₂ x, |W y - W x| ≤ M * ‖y - x‖ ^ α) :
    ∃ v, Tendsto (fun ε ↦ ∫ y in box a b₁ b₂ x \ ball x ε, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 v) := by
  have hKe : K = PotentialTheory.Planar.hessianKernel 0 0 := funext fun y ↦ by
    rw [hK, PotentialTheory.Planar.hessianKernel_zero_zero]
  set Q := box a b₁ b₂ x with hQ
  have hQm : MeasurableSet Q := measurableSet_box x
  have hQb : Bornology.IsBounded Q := isBounded_box x
  set r := min a (min b₁ b₂) with hr
  have hr0 : 0 < r := lt_min ha (lt_min hb₁ hb₂)
  have hball : ball x r ⊆ Q := fun y hy ↦ by
    have h0 := abs_lt.1 ((abs_sub_apply_le_norm x y 0).trans_lt (mem_ball_iff_norm.1 hy))
    have h1 := abs_lt.1 ((abs_sub_apply_le_norm x y 1).trans_lt (mem_ball_iff_norm.1 hy))
    simp only [hQ, box, mem_ofPred_eq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [min_le_left a (min b₁ b₂), min_le_right a (min b₁ b₂),
      min_le_left b₁ b₂, min_le_right b₁ b₂]
  obtain ⟨Mw, hWb⟩ := exists_bound_of_holder hQb hα hhol
  have hKm := measurable_shearKernel hK
  have hfar : IntegrableOn (fun y ↦ K (x - y) * W y) (Q \ ball x r) := by
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * r ^ 2) * Mw)
      ((measure_mono sdiff_subset).trans_lt hQb.measure_lt_top).ne
      ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hWm) ?_
    filter_upwards [ae_restrict_mem (hQm.diff measurableSet_ball)] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ((abs_shearKernel_le hK _).trans ?_) (hWb y hy.1) (abs_nonneg _)
      (by positivity)
    have := hy.2
    rw [mem_ball, not_lt, dist_eq_norm, norm_sub_rev] at this
    gcongr
  have hpv := PotentialTheory.Planar.hasPrincipalValueAt_hessianKernel_of_holder 0 0 hQm hr0 hα
    hball hWm (fun y hy ↦ by rw [norm_sub_rev]; exact hhol y (hball hy)) (by rwa [← hKe])
  refine ⟨_, hpv.2.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [PDE.Analysis.principalValueTruncation, hKe]
  refine setIntegral_congr_set ?_
  have hsph : volume (sphere x ε) = 0 := Measure.addHaar_sphere volume x ε
  refine (ae_eq_set.2 ⟨?_, ?_⟩)
  · refine measure_mono_null (fun y hy ↦ ?_) hsph
    rw [mem_sphere, dist_eq_norm, norm_sub_rev]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
      not_and, not_lt] at hy
    have := hy.2 hy.1.1
    rw [norm_sub_rev] at this
    linarith [hy.1.2]
  · refine measure_mono_null (fun y hy ↦ ?_) hsph
    rw [mem_sphere, dist_eq_norm, norm_sub_rev]
    simp only [Set.mem_sdiff, Set.mem_inter_iff, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
      not_and, not_lt] at hy
    have := hy.2 hy.1.1
    rw [norm_sub_rev] at hy
    linarith [hy.1.2]

end IncompressibleFlow.SharpHolder
