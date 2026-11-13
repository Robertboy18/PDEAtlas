/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientSmoothing

/-!
# Forward Duhamel integrals with square-root singularities

Let a kernel satisfy `‖K r‖ ≤ M * r ^ (-1/2)` for positive lag and let a forcing satisfy
`‖f s‖ ≤ D * s ^ (-1/2) * exp (ω * s)` for positive time. The forward integral
`∫₀ᵗ K (t - s) (f s) ds` then converges at every positive time, depends continuously on `t`,
and the weight `√t * exp (-ω t)` makes it at most a multiple of `M * D / √ω`.

On bounded continuous paths over positive times, the forcing is decoded by the weight
`s ^ (-1/2) * exp (ω * s)`. For a family `A s : E →L F` with `‖A s‖ ≤ a` and jointly
continuous action, the weighted perturbation operator
`w ↦ √t e^{-ωt} ∫₀ᵗ K (t - s) (A s (w s)) ds` has norm at most
`forwardSmoothingConstant * M * a / √ω`. With `A s` the identity this is the forward
smoothing operator, of norm at most `forwardSmoothingConstant * M / √ω`, so a large
exponential weight makes it a contraction and `1 + V` is invertible. This is the Volterra
iteration that perturbs a smoothing semigroup by a first-order operator. A path with a
singular bound `C s^(-1/2) exp (ω s)` is encoded with any weight above `ω`, so the contraction
also shows that the forward Volterra equation has at most one solution with a singular bound,
whatever its rate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-! ## Real estimates -/

/-- The inverse square root as a real power. -/
theorem rpow_neg_one_half_eq_inv_sqrt {r : ℝ} (hr : 0 ≤ r) :
    r ^ (-(1 / 2 : ℝ)) = (Real.sqrt r)⁻¹ := by
  rw [Real.rpow_neg hr, Real.sqrt_eq_rpow]

/-- Two square-root singularities at the ends of `[0, t]` are dominated by their sum. -/
theorem singularPair_le {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) ≤
      (t / 2) ^ (-(1 / 2 : ℝ)) * (s ^ (-(1 / 2 : ℝ)) + (t - s) ^ (-(1 / 2 : ℝ))) := by
  have hts : 0 < t - s := sub_pos.mpr hst
  have h1 := Real.rpow_nonneg hs.le (-(1 / 2 : ℝ))
  have h2 := Real.rpow_nonneg hts.le (-(1 / 2 : ℝ))
  have h3 := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t / 2) (-(1 / 2 : ℝ))
  rcases le_total s (t / 2) with h | h
  · have hle : (t - s) ^ (-(1 / 2 : ℝ)) ≤ (t / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
    calc
      _ ≤ (t / 2) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hle h1
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h2) h3
  · have hle : s ^ (-(1 / 2 : ℝ)) ≤ (t / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h (by norm_num)
    calc
      _ ≤ (t - s) ^ (-(1 / 2 : ℝ)) * (t / 2) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hle h2
      _ = (t / 2) ^ (-(1 / 2 : ℝ)) * (t - s) ^ (-(1 / 2 : ℝ)) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h1) h3

/-- The inverse square root is integrable on every bounded interval. -/
theorem intervalIntegrable_rpow_neg_one_half (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ s ^ (-(1 / 2 : ℝ))) volume a b :=
  intervalIntegral.intervalIntegrable_rpow' (by norm_num)

/-- The inverse square root of the remaining time is integrable on `[0, t]`. -/
theorem intervalIntegrable_sub_rpow_neg_one_half (t : ℝ) :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  have h := (intervalIntegrable_rpow_neg_one_half t 0).comp_sub_left t
  simpa only [sub_self, sub_zero] using h

/-- The product of the two end singularities is integrable on `[0, t]`. -/
theorem intervalIntegrable_singularPair {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)))
      volume 0 t := by
  have hsum := ((intervalIntegrable_rpow_neg_one_half 0 t).add
    (intervalIntegrable_sub_rpow_neg_one_half t)).const_mul ((t / 2) ^ (-(1 / 2 : ℝ)))
  refine hsum.mono_fun ?_ ?_
  · exact (((measurable_const.sub measurable_id).pow_const _).mul
      (measurable_id.pow_const _)).aestronglyMeasurable
  · rw [uIoc_of_le ht.le]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hpos := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t / 2) (-(1 / 2 : ℝ))
    have hsum_nonneg : 0 ≤ (t / 2) ^ (-(1 / 2 : ℝ)) *
        (s ^ (-(1 / 2 : ℝ)) + (t - s) ^ (-(1 / 2 : ℝ))) :=
      mul_nonneg hpos (add_nonneg (Real.rpow_nonneg hs.1.le _)
        (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    rcases eq_or_lt_of_le hs.2 with h | h
    · calc
        _ = (0 : ℝ) := by rw [h, sub_self, Real.zero_rpow (by norm_num), zero_mul, abs_zero]
        _ ≤ _ := hsum_nonneg
    · rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
        (Real.rpow_nonneg hs.1.le _))]
      exact singularPair_le hs.1 h

/-- The inverse square root against an exponential weight is integrable on `[0, t]`. -/
theorem intervalIntegrable_singularPair_mul_exp {t : ℝ} (ht : 0 < t) (ω : ℝ) :
    IntervalIntegrable
      (fun s : ℝ ↦ (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
      volume 0 t :=
  (intervalIntegrable_singularPair ht).mul_continuousOn (by fun_prop)

/-- A square root is absorbed by half of an exponential weight. -/
theorem sqrt_mul_exp_neg_half_le (t : ℝ) {ω : ℝ} (hω : 0 < ω) :
    Real.sqrt t * Real.exp (-(ω * t / 2)) ≤ (Real.sqrt ω)⁻¹ := by
  have hsω := Real.sqrt_pos.mpr hω
  have hmain : Real.sqrt ω * Real.sqrt t ≤ Real.exp (ω * t / 2) := by
    rw [← Real.sqrt_mul hω.le, show Real.exp (ω * t / 2) = Real.sqrt (Real.exp (ω * t)) by
      rw [← Real.exp_half]]
    exact Real.sqrt_le_sqrt (by linarith [Real.add_one_le_exp (ω * t)])
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc
    Real.sqrt t = (Real.sqrt ω)⁻¹ * (Real.sqrt ω * Real.sqrt t) := by
      rw [← mul_assoc, inv_mul_cancel₀ hsω.ne', one_mul]
    _ ≤ (Real.sqrt ω)⁻¹ * Real.exp (ω * t / 2) :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hsω.le)

/-- The constant in the weighted square-root convolution bound. -/
def forwardSmoothingConstant : ℝ :=
  2 * Real.sqrt 2 + Real.sqrt 2 * Real.sqrt Real.pi

theorem forwardSmoothingConstant_nonneg : 0 ≤ forwardSmoothingConstant := by
  unfold forwardSmoothingConstant
  positivity

private theorem weighted_singularPair_le {s t ω : ℝ} (hω : 0 ≤ ω) (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sqrt t * Real.exp (-(ω * t)) *
        ((t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) ≤
      Real.sqrt 2 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * t / 2))) +
        Real.sqrt 2 * ((t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * (t - s)))) := by
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have hA : 0 ≤ Real.sqrt 2 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * t / 2))) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le)
  have hB : 0 ≤ Real.sqrt 2 * ((t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * (t - s)))) :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.rpow_nonneg hts _) (Real.exp_pos _).le)
  rcases eq_or_lt_of_le hs with h0 | h0
  · calc
      _ = (0 : ℝ) := by rw [← h0, Real.zero_rpow (by norm_num)]; ring
      _ ≤ _ := add_nonneg hA hB
  rcases eq_or_lt_of_le hst with h1 | h1
  · calc
      _ = (0 : ℝ) := by rw [h1, sub_self, Real.zero_rpow (by norm_num)]; ring
      _ ≤ _ := add_nonneg hA hB
  have hts' : 0 < t - s := sub_pos.mpr h1
  simp only [rpow_neg_one_half_eq_inv_sqrt hts, rpow_neg_one_half_eq_inv_sqrt hs] at hA hB ⊢
  have hsq_s := Real.sqrt_pos.mpr h0
  have hsq_ts := Real.sqrt_pos.mpr hts'
  have hexp : Real.exp (-(ω * t)) * Real.exp (ω * s) = Real.exp (-(ω * (t - s))) := by
    rw [← Real.exp_add]
    ring_nf
  rcases le_total s (t / 2) with h | h
  · calc
      _ = Real.sqrt t / Real.sqrt (t - s) * (Real.sqrt s)⁻¹ *
          (Real.exp (-(ω * t)) * Real.exp (ω * s)) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt s)⁻¹ * Real.exp (-(ω * t / 2)) := by
        gcongr ?_ * _ * ?_
        · rw [div_le_iff₀ hsq_ts, ← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt (by linarith)
        · exact hexp ▸ Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_left h hω])
      _ = Real.sqrt 2 * ((Real.sqrt s)⁻¹ * Real.exp (-(ω * t / 2))) := by ring
      _ ≤ _ := le_add_of_nonneg_right hB
  · calc
      _ = Real.sqrt t / Real.sqrt s * (Real.sqrt (t - s))⁻¹ *
          (Real.exp (-(ω * t)) * Real.exp (ω * s)) := by ring
      _ ≤ Real.sqrt 2 * (Real.sqrt (t - s))⁻¹ * Real.exp (-(ω * (t - s))) := by
        rw [hexp]
        gcongr
        rw [div_le_iff₀ hsq_s, ← Real.sqrt_mul (by norm_num)]
        exact Real.sqrt_le_sqrt (by linarith)
      _ = Real.sqrt 2 * ((Real.sqrt (t - s))⁻¹ * Real.exp (-(ω * (t - s)))) := by ring
      _ ≤ _ := le_add_of_nonneg_left hA

/-- The integral of the inverse square root from zero. -/
theorem integral_rpow_neg_one_half (t : ℝ) :
    ∫ s in (0 : ℝ)..t, s ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt t := by
  rw [integral_rpow (Or.inl (by norm_num)), show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num,
    Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow]
  ring

/-- The inverse square root against exponential decay has at most the full Gamma mass. -/
theorem integral_rpow_neg_one_half_mul_exp_le {t ω : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) :
    ∫ r in (0 : ℝ)..t, r ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * r)) ≤
      Real.sqrt Real.pi / Real.sqrt ω := by
  rw [intervalIntegral.integral_of_le ht, ← smoothingMass_one_half,
    ← integral_smoothingWeight (by norm_num) hω]
  apply setIntegral_mono_set (integrableOn_smoothingWeight (by norm_num) hω)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hr) _) (Real.exp_pos _).le
  · exact Ioc_subset_Ioi_self.eventuallyLE

/-- The weighted convolution of two square-root singularities is uniformly small
for a large exponential weight. -/
theorem sqrt_mul_exp_mul_integral_singularPair_le {t ω : ℝ} (ht : 0 < t) (hω : 0 < ω) :
    Real.sqrt t * Real.exp (-(ω * t)) *
        (∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) ≤
      forwardSmoothingConstant / Real.sqrt ω := by
  rw [← intervalIntegral.integral_const_mul]
  have hf1 : IntervalIntegrable
      (fun s : ℝ ↦ Real.sqrt 2 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * t / 2)))) volume 0 t :=
    ((intervalIntegrable_rpow_neg_one_half 0 t).mul_const _).const_mul _
  have hf2 : IntervalIntegrable
      (fun s : ℝ ↦ Real.sqrt 2 *
        ((t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * (t - s))))) volume 0 t :=
    ((intervalIntegrable_sub_rpow_neg_one_half t).mul_continuousOn
      (by fun_prop)).const_mul _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t,
        (Real.sqrt 2 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * t / 2))) +
          Real.sqrt 2 * ((t - s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * (t - s))))) := by
      apply intervalIntegral.integral_mono_on ht.le
        ((intervalIntegrable_singularPair_mul_exp ht ω).const_mul _) (hf1.add hf2)
      intro s hs
      exact weighted_singularPair_le hω.le hs.1 hs.2
    _ = Real.sqrt 2 * Real.exp (-(ω * t / 2)) * (2 * Real.sqrt t) +
        Real.sqrt 2 * ∫ r in (0 : ℝ)..t, r ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * r)) := by
      rw [intervalIntegral.integral_add hf1 hf2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
        integral_rpow_neg_one_half t]
      have hshift := intervalIntegral.integral_comp_sub_left
        (fun r : ℝ ↦ r ^ (-(1 / 2 : ℝ)) * Real.exp (-(ω * r))) t (a := 0) (b := t)
      simp only [sub_self, sub_zero] at hshift
      rw [hshift]
      ring
    _ ≤ Real.sqrt 2 * 2 * (Real.sqrt ω)⁻¹ +
        Real.sqrt 2 * (Real.sqrt Real.pi / Real.sqrt ω) := by
      have h := mul_le_mul_of_nonneg_left (sqrt_mul_exp_neg_half_le t hω)
        (by positivity : (0 : ℝ) ≤ Real.sqrt 2 * 2)
      exact add_le_add (by linarith) (mul_le_mul_of_nonneg_left
        (integral_rpow_neg_one_half_mul_exp_le ht.le hω) (Real.sqrt_nonneg _))
    _ = forwardSmoothingConstant / Real.sqrt ω := by
      unfold forwardSmoothingConstant
      ring

/-! ## Forward integrals -/

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The forward Duhamel integral `∫₀ᵗ K (t - s) (f s) ds`. The kernel may gain regularity,
so it maps the forcing space `F` to the solution space `E`. -/
def forwardDuhamel (K : ℝ → F →L[ℝ] E) (f : ℝ → F) (t : ℝ) : E :=
  ∫ s in (0 : ℝ)..t, K (t - s) (f s)

omit [NormedSpace ℝ E] in
/-- A forward integrand that is continuous inside `(0, t)` and dominated by an integrable
function is integrable on `[0, t]`. -/
theorem intervalIntegrable_of_continuousOn_Ioo {G : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn G (Ioo 0 t)) {g : ℝ → ℝ} (hg : IntervalIntegrable g volume 0 t)
    (hbound : ∀ s ∈ Ioo 0 t, ‖G s‖ ≤ g s) :
    IntervalIntegrable G volume 0 t := by
  refine hg.mono_fun ?_ ?_
  · rw [uIoc_of_le ht, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · rw [uIoc_of_le ht, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (hbound s hs).trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)

variable {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {M D ω : ℝ}

/-- Joint continuity of the kernel action and continuity of the forcing on positive times
make the forward integrand continuous inside `(0, t)`. -/
theorem continuousOn_forwardIntegrand
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hfc : ContinuousOn f (Ioi 0)) (t : ℝ) :
    ContinuousOn (fun s ↦ K (t - s) (f s)) (Ioo 0 t) := by
  refine hKc.comp ((continuousOn_const.sub continuousOn_id).prodMk
    (hfc.mono fun s hs ↦ hs.1)) ?_
  intro s hs
  exact ⟨sub_pos.mpr hs.2, mem_univ _⟩

/-- At a time `s ∈ (0, t)` where the forcing has the singular bound, the singular kernel bound
dominates the integrand by the product of the two end singularities. -/
theorem norm_forwardIntegrand_le_of_le
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) {s t : ℝ} (hs : s ∈ Ioo 0 t)
    (hfs : ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    ‖K (t - s) (f s)‖ ≤
      M * D * ((t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) := by
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  calc
    _ ≤ ‖K (t - s)‖ * ‖f s‖ := (K (t - s)).le_opNorm _
    _ ≤ (M * (t - s) ^ (-(1 / 2 : ℝ))) * (D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
      mul_le_mul (hK _ (sub_pos.mpr hs.2)) hfs (norm_nonneg _)
        (mul_nonneg hM (Real.rpow_nonneg (sub_nonneg.mpr hs.2.le) _))
    _ = _ := by ring

/-- The singular kernel and forcing bounds dominate the integrand by the product of the two
end singularities. -/
theorem norm_forwardIntegrand_le
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {s t : ℝ} (hs : s ∈ Ioo 0 t) :
    ‖K (t - s) (f s)‖ ≤
      M * D * ((t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
  norm_forwardIntegrand_le_of_le hK hs (hf s hs.1)

/-- For `t ≤ T`, the forward integrand is integrable on `[0, t]` when the forcing is
continuous on `(0, T]` and has a singular bound there. -/
theorem intervalIntegrable_forwardIntegrand_of_le {T : ℝ}
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hfc : ContinuousOn f (Ioc 0 T))
    (hf : ∀ s ∈ Ioc 0 T, ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    IntervalIntegrable (fun s ↦ K (t - s) (f s)) volume 0 t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst h
    exact IntervalIntegrable.refl
  have hcont : ContinuousOn (fun s ↦ K (t - s) (f s)) (Ioo 0 t) := by
    refine hKc.comp ((continuousOn_const.sub continuousOn_id).prodMk
      (hfc.mono fun s hs ↦ ⟨hs.1, hs.2.le.trans htT⟩)) ?_
    intro s hs
    exact ⟨sub_pos.mpr hs.2, mem_univ _⟩
  exact intervalIntegrable_of_continuousOn_Ioo ht hcont
    ((intervalIntegrable_singularPair_mul_exp h ω).const_mul (M * D))
    fun s hs ↦ norm_forwardIntegrand_le_of_le hK hs (hf s ⟨hs.1, hs.2.le.trans htT⟩)

/-- The forward integrand of a singular kernel and a singular forcing is integrable. -/
theorem intervalIntegrable_forwardIntegrand
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hfc : ContinuousOn f (Ioi 0))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s ↦ K (t - s) (f s)) volume 0 t :=
  intervalIntegrable_forwardIntegrand_of_le hKc hK (hfc.mono Ioc_subset_Ioi_self)
    (fun s hs ↦ hf s hs.1) ht le_rfl

/-- A singular bound of the forcing on `(0, t)` bounds the forward integral at time `t` by
the convolution of the two singularities. -/
theorem norm_forwardDuhamel_le_of_le
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) {t : ℝ} (ht : 0 < t)
    (hf : ∀ s ∈ Ioo 0 t, ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    ‖forwardDuhamel K f t‖ ≤ M * D *
      ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) := by
  rw [forwardDuhamel, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le ht.le
  · filter_upwards [Measure.ae_ne volume t] with s hst hs
    have hs' : s ∈ Ioo 0 t := ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    exact norm_forwardIntegrand_le_of_le hK hs' (hf s hs')
  · exact (intervalIntegrable_singularPair_mul_exp ht ω).const_mul _

/-- The forward integral is bounded by the convolution of the two singularities. -/
theorem norm_forwardDuhamel_le
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {t : ℝ} (ht : 0 < t) :
    ‖forwardDuhamel K f t‖ ≤ M * D *
      ∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) :=
  norm_forwardDuhamel_le_of_le hK ht fun s hs ↦ hf s hs.1

/-- With the weight `√t * exp (-ω t)`, the forward integral is at most a multiple of
`M * D / √ω`, uniformly in positive time. -/
theorem weighted_norm_forwardDuhamel_le
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hω : 0 < ω) {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * Real.exp (-(ω * t)) * ‖forwardDuhamel K f t‖ ≤
      forwardSmoothingConstant * M * D / Real.sqrt ω := by
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hf 1 one_pos)
    rw [Real.one_rpow, mul_one] at h
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  have hweight : 0 ≤ Real.sqrt t * Real.exp (-(ω * t)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ Real.sqrt t * Real.exp (-(ω * t)) * (M * D *
        ∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
      mul_le_mul_of_nonneg_left (norm_forwardDuhamel_le hK hf ht) hweight
    _ = M * D * (Real.sqrt t * Real.exp (-(ω * t)) *
        ∫ s in (0 : ℝ)..t,
          (t - s) ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) := by ring
    _ ≤ M * D * (forwardSmoothingConstant / Real.sqrt ω) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_exp_mul_integral_singularPair_le ht hω)
        (mul_nonneg hM hD)
    _ = _ := by ring

/-- A bounded kernel against a singular forcing gives an integrable forward integrand. -/
theorem intervalIntegrable_forwardIntegrand_of_bounded
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M)
    (hfc : ContinuousOn f (Ioi 0))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s ↦ K (t - s) (f s)) volume 0 t := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hK 1 one_pos)
  refine intervalIntegrable_of_continuousOn_Ioo ht (continuousOn_forwardIntegrand hKc hfc t)
    (((intervalIntegrable_rpow_neg_one_half 0 t).mul_continuousOn
      (g := fun s ↦ Real.exp (ω * s)) (by fun_prop)).const_mul (M * D)) ?_
  intro s hs
  calc
    ‖K (t - s) (f s)‖ ≤ ‖K (t - s)‖ * ‖f s‖ := (K (t - s)).le_opNorm _
    _ ≤ M * (D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
      mul_le_mul (hK _ (sub_pos.mpr hs.2)) (hf s hs.1) (norm_nonneg _) hM
    _ = M * D * (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) := by ring

/-- A bounded kernel against a singular forcing gives a forward integral of order `√t`. -/
theorem norm_forwardDuhamel_le_of_bounded
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M)
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hω : 0 ≤ ω) {t : ℝ} (ht : 0 ≤ t) :
    ‖forwardDuhamel K f t‖ ≤ 2 * M * D * Real.exp (ω * t) * Real.sqrt t := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hK 1 one_pos)
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hf 1 one_pos)
    rw [Real.one_rpow, mul_one] at h
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  rw [forwardDuhamel]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, M * D * Real.exp (ω * t) * s ^ (-(1 / 2 : ℝ)) := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht
      · filter_upwards [Measure.ae_ne volume t] with s hst ⟨hs0, hs⟩
        calc ‖K (t - s) (f s)‖ ≤ M * (D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
              (K _).le_of_opNorm_le_of_le (hK _ (sub_pos.mpr (hs.lt_of_ne hst))) (hf s hs0)
          _ ≤ M * (D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * t)) := by gcongr
          _ = _ := by ring
      · exact (intervalIntegrable_rpow_neg_one_half 0 t).const_mul _
    _ = 2 * M * D * Real.exp (ω * t) * Real.sqrt t := by
      rw [intervalIntegral.integral_const_mul, integral_rpow_neg_one_half]
      ring

/-- Rescaling time to `[0, 1]` fixes the positions of both singularities. -/
theorem forwardDuhamel_eq_smul_integral (K : ℝ → F →L[ℝ] E) (f : ℝ → F) {t : ℝ}
    (ht : t ≠ 0) :
    forwardDuhamel K f t = t • ∫ σ in (0 : ℝ)..1, K (t - t * σ) (f (t * σ)) := by
  have h := intervalIntegral.integral_comp_mul_left (fun s ↦ K (t - s) (f s)) ht
    (a := 0) (b := 1)
  simp only [mul_zero, mul_one] at h
  rw [h, smul_inv_smul₀ ht]
  rfl

/-- The forward integral is continuous at positive times. Dominated convergence applies
after rescaling to `[0, 1]`, where the two singularities are fixed. -/
theorem continuousOn_forwardDuhamel
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hfc : ContinuousOn f (Ioi 0))
    (hf : ∀ s, 0 < s → ‖f s‖ ≤ D * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    ContinuousOn (forwardDuhamel K f) (Ioi 0) := by
  intro t₀ ht₀
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  have hD : 0 ≤ D := by
    have h := (norm_nonneg _).trans (hf 1 one_pos)
    rw [Real.one_rpow, mul_one] at h
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  apply ContinuousAt.continuousWithinAt
  have hsub : ContinuousAt (fun t ↦ ∫ σ in (0 : ℝ)..1, K (t - t * σ) (f (t * σ))) t₀ := by
    apply intervalIntegral.continuousAt_of_dominated_interval
      (bound := fun σ ↦ M * D * (t₀ / 2)⁻¹ * Real.exp (|ω| * (2 * t₀)) *
        ((1 - σ) ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ))))
    · filter_upwards [lt_mem_nhds ht₀'] with t ht
      rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact ContinuousOn.aestronglyMeasurable (hKc.comp ((continuousOn_const.sub
        (continuousOn_const.mul continuousOn_id)).prodMk (hfc.comp (continuousOn_const.mul
          continuousOn_id) fun σ hσ ↦ mul_pos ht hσ.1)) fun σ hσ ↦
        ⟨(by nlinarith [hσ.2] : 0 < t - t * σ), mem_univ _⟩) measurableSet_Ioo
    · filter_upwards [Ioo_mem_nhds (half_lt_self ht₀') (by linarith : t₀ < 2 * t₀)] with t ht
      filter_upwards [Measure.ae_ne volume 1] with σ hσ1 hσ
      rw [uIoc_of_le zero_le_one] at hσ
      have hσ' : σ < 1 := lt_of_le_of_ne hσ.2 hσ1
      have htpos : 0 < t := lt_trans (half_pos ht₀') ht.1
      have hmem : t * σ ∈ Ioo 0 t := ⟨mul_pos htpos hσ.1, by nlinarith⟩
      have hle := norm_forwardIntegrand_le hK hf hmem
      have hrpow : (t - t * σ) ^ (-(1 / 2 : ℝ)) * (t * σ) ^ (-(1 / 2 : ℝ)) =
          t⁻¹ * ((1 - σ) ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ))) := by
        rw [show t - t * σ = t * (1 - σ) by ring, Real.mul_rpow htpos.le (by linarith),
          Real.mul_rpow htpos.le hσ.1.le, mul_mul_mul_comm, ← Real.rpow_add htpos,
          show -(1 / 2 : ℝ) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
      have hinv : t⁻¹ ≤ (t₀ / 2)⁻¹ := inv_anti₀ (half_pos ht₀') ht.1.le
      have hexp : Real.exp (ω * (t * σ)) ≤ Real.exp (|ω| * (2 * t₀)) :=
        Real.exp_le_exp.mpr <| (mul_le_mul_of_nonneg_right (le_abs_self ω)
          (mul_pos htpos hσ.1).le).trans
          (mul_le_mul_of_nonneg_left (by nlinarith [ht.2]) (abs_nonneg ω))
      have hpair : 0 ≤ (1 - σ) ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ)) :=
        mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hσ.1.le _)
      calc
        ‖K (t - t * σ) (f (t * σ))‖ ≤ M * D * t⁻¹ * Real.exp (ω * (t * σ)) *
            ((1 - σ) ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ))) :=
          hle.trans_eq (by rw [hrpow]; ring)
        _ ≤ M * D * (t₀ / 2)⁻¹ * Real.exp (|ω| * (2 * t₀)) *
            ((1 - σ) ^ (-(1 / 2 : ℝ)) * σ ^ (-(1 / 2 : ℝ))) := by gcongr
    · simpa only [mul_comm] using (intervalIntegrable_singularPair one_pos).const_mul
        (M * D * (t₀ / 2)⁻¹ * Real.exp (|ω| * (2 * t₀)))
    · filter_upwards [Measure.ae_ne volume 1] with σ hσ1 hσ
      rw [uIoc_of_le zero_le_one] at hσ
      have hσ' : σ < 1 := lt_of_le_of_ne hσ.2 hσ1
      have hmul : ContinuousAt (fun t : ℝ ↦ t * σ) t₀ := continuousAt_id.mul continuousAt_const
      have hfσ : ContinuousAt f (t₀ * σ) := hfc.continuousAt (Ioi_mem_nhds (mul_pos ht₀' hσ.1))
      have hpair : ContinuousAt (fun t : ℝ ↦ (t - t * σ, f (t * σ))) t₀ :=
        (continuousAt_id.sub hmul).prodMk (ContinuousAt.comp (g := f) hfσ hmul)
      have hK' : ContinuousAt (fun p : ℝ × F ↦ K p.1 p.2) (t₀ - t₀ * σ, f (t₀ * σ)) :=
        hKc.continuousAt (prod_mem_nhds (Ioi_mem_nhds (by nlinarith)) univ_mem)
      exact ContinuousAt.comp (x := t₀) hK' hpair
  have heq : forwardDuhamel K f =ᶠ[𝓝 t₀]
      fun t ↦ t • ∫ σ in (0 : ℝ)..1, K (t - t * σ) (f (t * σ)) := by
    filter_upwards [lt_mem_nhds ht₀'] with t ht
    exact forwardDuhamel_eq_smul_integral K f ht.ne'
  exact (continuousAt_id.smul hsub).congr heq.symm

/-- The forward integral is additive in integrable forcings. -/
theorem forwardDuhamel_add {g : ℝ → F} {t : ℝ}
    (hf : IntervalIntegrable (fun s ↦ K (t - s) (f s)) volume 0 t)
    (hg : IntervalIntegrable (fun s ↦ K (t - s) (g s)) volume 0 t) :
    forwardDuhamel K (f + g) t = forwardDuhamel K f t + forwardDuhamel K g t := by
  simp only [forwardDuhamel, Pi.add_apply, map_add]
  exact intervalIntegral.integral_add hf hg

/-- The forward integral is homogeneous in the forcing. -/
theorem forwardDuhamel_smul (c : ℝ) (t : ℝ) :
    forwardDuhamel K (c • f) t = c • forwardDuhamel K f t := by
  simp only [forwardDuhamel, Pi.smul_apply, map_smul]
  exact intervalIntegral.integral_smul c _

/-! ## Fubini on a triangle -/

/-- A continuous linear image of an interval integrable function is interval integrable. -/
theorem IntervalIntegrable.continuousLinearMap_comp {g : ℝ → F} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (L : F →L[ℝ] E) :
    IntervalIntegrable (fun s ↦ L (g s)) volume a b :=
  ⟨L.integrable_comp hg.1, L.integrable_comp hg.2⟩

/-- Fubini's theorem on the triangle `a < r ≤ s ≤ b`. -/
theorem intervalIntegral_triangle_swap {G : ℝ → ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (h : IntegrableOn (fun p : ℝ × ℝ ↦ if p.2 ≤ p.1 then G p.1 p.2 else 0)
      (Ioc a b ×ˢ Ioc a b)) :
    ∫ s in a..b, ∫ r in a..s, G s r = ∫ r in a..b, ∫ s in r..b, G s r := by
  have hin : ∀ s ∈ uIcc a b,
      ∫ r in a..s, G s r = ∫ r in a..b, (if r ≤ s then G s r else 0) := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have hind : (fun r ↦ if r ≤ s then G s r else 0) = (Iic s).indicator (G s) := by
      funext r
      simp only [Set.indicator_apply, mem_Iic]
    rw [hind, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hs.1,
      setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hs.2]
  have hout : ∀ r ∈ uIcc a b,
      ∫ s in a..b, (if r ≤ s then G s r else 0) = ∫ s in r..b, G s r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    have hind : (fun s ↦ if r ≤ s then G s r else 0) = (Ici r).indicator (fun s ↦ G s r) := by
      funext s
      simp only [Set.indicator_apply, mem_Ici]
    rw [hind, intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hr.2,
      setIntegral_indicator measurableSet_Ici]
    apply setIntegral_congr_set
    rcases eq_or_lt_of_le hr.1 with rfl | h0
    · rw [inter_eq_left.2 fun x hx ↦ hx.1.le]
    · rw [show Ioc a b ∩ Ici r = Icc r b from
        Set.ext fun x ↦ ⟨fun hx ↦ ⟨hx.2, hx.1.2⟩, fun hx ↦ ⟨⟨h0.trans_le hx.1, hx.2⟩, hx.1⟩⟩]
      exact Ioc_ae_eq_Icc.symm
  calc
    _ = ∫ s in a..b, ∫ r in a..b, (if r ≤ s then G s r else 0) :=
      intervalIntegral.integral_congr hin
    _ = ∫ r in a..b, ∫ s in a..b, (if r ≤ s then G s r else 0) := by
      apply intervalIntegral_intervalIntegral_swap
      rw [uIoc_of_le hab]
      exact h
    _ = _ := intervalIntegral.integral_congr hout

/-! ## Weighted paths over positive times -/

/-- Decode a weighted path over positive times by the singular weight
`s ^ (-1/2) * exp (ω * s)`, extended by zero to nonpositive times. -/
def forwardDecode (ω : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) (s : ℝ) : E :=
  if hs : 0 < s then (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) • w ⟨s, hs⟩ else 0

theorem forwardDecode_of_pos (ω : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) {s : ℝ} (hs : 0 < s) :
    forwardDecode ω w s = (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) • w ⟨s, hs⟩ :=
  dite_eq_left hs

theorem forwardDecode_of_nonpos (ω : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) {s : ℝ} (hs : s ≤ 0) :
    forwardDecode ω w s = 0 :=
  dite_eq_right (not_lt.mpr hs)

/-- The decoded path has the singular bound with the path norm as constant. -/
theorem norm_forwardDecode_le (ω : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) {s : ℝ} (hs : 0 < s) :
    ‖forwardDecode ω w s‖ ≤ ‖w‖ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) := by
  have hweight : 0 ≤ s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le
  rw [forwardDecode_of_pos ω w hs, norm_smul, Real.norm_eq_abs, abs_of_nonneg hweight]
  calc
    _ ≤ (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) * ‖w‖ :=
      mul_le_mul_of_nonneg_left (w.norm_coe_le_norm _) hweight
    _ = _ := by ring

/-- The decoded path is continuous at positive times. -/
theorem continuousOn_forwardDecode (ω : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) :
    ContinuousOn (forwardDecode ω w) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (Ioi (0 : ℝ)).domRestrict (forwardDecode ω w) =
      fun s : Ioi (0 : ℝ) ↦ ((s : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) • w s := by
    funext s
    exact forwardDecode_of_pos ω w s.2
  rw [h]
  refine Continuous.smul ?_ w.continuous
  exact (continuous_subtype_val.rpow_const fun s ↦ Or.inl s.2.ne').mul (by fun_prop)

theorem forwardDecode_add (ω : ℝ) (w₁ w₂ : Ioi (0 : ℝ) →ᵇ E) :
    forwardDecode ω (w₁ + w₂) = forwardDecode ω w₁ + forwardDecode ω w₂ := by
  funext s
  by_cases hs : 0 < s
  · simp only [forwardDecode_of_pos _ _ hs, Pi.add_apply, BoundedContinuousFunction.coe_add,
      smul_add]
  · simp only [forwardDecode_of_nonpos _ _ (not_lt.mp hs), Pi.add_apply, add_zero]

theorem forwardDecode_smul (ω c : ℝ) (w : Ioi (0 : ℝ) →ᵇ E) :
    forwardDecode ω (c • w) = c • forwardDecode ω w := by
  funext s
  by_cases hs : 0 < s
  · simp only [forwardDecode_of_pos _ _ hs, Pi.smul_apply, BoundedContinuousFunction.coe_smul,
      smul_comm c]
  · simp only [forwardDecode_of_nonpos _ _ (not_lt.mp hs), Pi.smul_apply, smul_zero]

/-- The decoding weight `s ^ (-1/2) * exp (ω * s)` inverts the path weight
`√s * exp (-ω s)`. -/
theorem rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp {s : ℝ} (hs : 0 < s) (ω : ℝ) :
    s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) * (Real.sqrt s * Real.exp (-(ω * s))) = 1 := by
  rw [rpow_neg_one_half_eq_inv_sqrt hs.le]
  have h1 := (Real.sqrt_pos.mpr hs).ne'
  calc
    _ = ((Real.sqrt s)⁻¹ * Real.sqrt s) * (Real.exp (ω * s) * Real.exp (-(ω * s))) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ h1, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- A singular bound persists for a nonnegative constant and a larger rate. -/
theorem mul_rpow_neg_one_half_mul_exp_le {C ω ω' s : ℝ} (hs : 0 < s) (hω : ω ≤ ω') :
    C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) ≤
      max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * s) := by
  have hp := Real.rpow_nonneg hs.le (-(1 / 2 : ℝ))
  have he : Real.exp (ω * s) ≤ Real.exp (ω' * s) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hω hs.le)
  calc
    _ ≤ max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
        (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left he (mul_nonneg (le_max_right _ _) hp)

/-- The weight `√s * exp (-ω' s)` turns the singular bound `C s^(-1/2) exp (ω s)` with
`ω ≤ ω'` into the uniform bound `max C 0`. -/
theorem norm_sqrt_mul_exp_smul_le {C ω ω' s : ℝ} (hω : ω ≤ ω') (hs : 0 < s) {x : E}
    (hx : ‖x‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    ‖(Real.sqrt s * Real.exp (-(ω' * s))) • x‖ ≤ max C 0 := by
  have hw : 0 ≤ Real.sqrt s * Real.exp (-(ω' * s)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  calc
    _ ≤ Real.sqrt s * Real.exp (-(ω' * s)) *
        (max C 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * s)) :=
      mul_le_mul_of_nonneg_left (hx.trans (mul_rpow_neg_one_half_mul_exp_le hs hω)) hw
    _ = max C 0 * (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * s) *
        (Real.sqrt s * Real.exp (-(ω' * s)))) := by ring
    _ = max C 0 := by rw [rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp hs, mul_one]

/-- Encode a path that is continuous at positive times and has the singular bound
`C s^(-1/2) exp (ω s)` as a bounded continuous path over positive times, with the weight
`√s * exp (-ω' s)` for a rate `ω' ≥ ω`. -/
def forwardEncode (ω' : ℝ) {ω C : ℝ} (hω : ω ≤ ω') {v : ℝ → E} (hvc : ContinuousOn v (Ioi 0))
    (hvb : ∀ s, 0 < s → ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    Ioi (0 : ℝ) →ᵇ E :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s : Ioi (0 : ℝ) ↦ (Real.sqrt s * Real.exp (-(ω' * s))) • v s)
    ((show Continuous fun s : Ioi (0 : ℝ) ↦ Real.sqrt s * Real.exp (-(ω' * s)) by
      fun_prop).smul (hvc.comp_continuous continuous_subtype_val fun s ↦ s.2))
    (max C 0) (fun s ↦ norm_sqrt_mul_exp_smul_le hω s.2 (hvb s s.2))

theorem forwardEncode_apply (ω' : ℝ) {ω C : ℝ} (hω : ω ≤ ω') {v : ℝ → E}
    (hvc : ContinuousOn v (Ioi 0))
    (hvb : ∀ s, 0 < s → ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (s : Ioi (0 : ℝ)) :
    forwardEncode ω' hω hvc hvb s = (Real.sqrt s * Real.exp (-(ω' * s))) • v s :=
  rfl

theorem norm_forwardEncode_le (ω' : ℝ) {ω C : ℝ} (hω : ω ≤ ω') {v : ℝ → E}
    (hvc : ContinuousOn v (Ioi 0))
    (hvb : ∀ s, 0 < s → ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :
    ‖forwardEncode ω' hω hvc hvb‖ ≤ max C 0 :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (le_max_right _ _) _

/-- Decoding an encoded path recovers it at positive times. -/
theorem forwardDecode_forwardEncode (ω' : ℝ) {ω C : ℝ} (hω : ω ≤ ω') {v : ℝ → E}
    (hvc : ContinuousOn v (Ioi 0))
    (hvb : ∀ s, 0 < s → ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) {s : ℝ}
    (hs : 0 < s) :
    forwardDecode ω' (forwardEncode ω' hω hvc hvb) s = v s := by
  rw [forwardDecode_of_pos _ _ hs]
  change (s ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * s)) •
    ((Real.sqrt s * Real.exp (-(ω' * s))) • v s) = v s
  rw [smul_smul, rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp hs, one_smul]

section Perturbation

variable (K : ℝ → F →L[ℝ] E) (A : ℝ → E →L[ℝ] F) {a : ℝ}

/-- The weighted perturbation operator
`w ↦ √t e^{-ωt} ∫₀ᵗ K (t - s) (A s (decode w s)) ds` on bounded continuous paths over
positive times. -/
def forwardPerturbationOperator (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Ioi 0 ×ˢ univ))
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ a) :
    (Ioi (0 : ℝ) →ᵇ E) →L[ℝ] (Ioi (0 : ℝ) →ᵇ E) := by
  let C := forwardSmoothingConstant * M * a / Real.sqrt ω
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA 1 one_pos)
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (mul_nonneg forwardSmoothingConstant_nonneg hM) ha)
    (Real.sqrt_nonneg _)
  have hfc (w : Ioi (0 : ℝ) →ᵇ E) :
      ContinuousOn (fun s ↦ A s (forwardDecode ω w s)) (Ioi 0) :=
    hAc.comp (continuousOn_id.prodMk (continuousOn_forwardDecode ω w))
      fun s hs ↦ ⟨hs, mem_univ _⟩
  have hfb (w : Ioi (0 : ℝ) →ᵇ E) : ∀ s, 0 < s →
      ‖A s (forwardDecode ω w s)‖ ≤ (a * ‖w‖) * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s) := by
    intro s hs
    calc
      _ ≤ ‖A s‖ * ‖forwardDecode ω w s‖ := (A s).le_opNorm _
      _ ≤ a * (‖w‖ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s)) :=
        mul_le_mul (hA s hs) (norm_forwardDecode_le ω w hs) (norm_nonneg _) ha
      _ = _ := by ring
  let I (w : Ioi (0 : ℝ) →ᵇ E) : C(Ioi (0 : ℝ), E) :=
    { toFun t := (Real.sqrt t * Real.exp (-(ω * t))) •
        forwardDuhamel K (fun s ↦ A s (forwardDecode ω w s)) t
      continuous_toFun := by
        apply Continuous.smul (by fun_prop)
        exact (continuousOn_forwardDuhamel hKc hK (hfc w) (hfb w)).comp_continuous
          continuous_subtype_val (fun t ↦ t.2) }
  have hI (w : Ioi (0 : ℝ) →ᵇ E) (t : Ioi (0 : ℝ)) : ‖I w t‖ ≤ C * ‖w‖ := by
    change ‖(Real.sqrt t * Real.exp (-(ω * t))) •
      forwardDuhamel K (fun s ↦ A s (forwardDecode ω w s)) t‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
    calc
      _ ≤ forwardSmoothingConstant * M * (a * ‖w‖) / Real.sqrt ω :=
        weighted_norm_forwardDuhamel_le hK (hfb w) hω t.2
      _ = C * ‖w‖ := by ring
  have hint (w : Ioi (0 : ℝ) →ᵇ E) (t : Ioi (0 : ℝ)) :
      IntervalIntegrable (fun s ↦ K (t - s) (A s (forwardDecode ω w s))) volume 0 t :=
    intervalIntegrable_forwardIntegrand hKc hK (hfc w) (hfb w) t.2.le
  let L : (Ioi (0 : ℝ) →ᵇ E) →ₗ[ℝ] (Ioi (0 : ℝ) →ᵇ E) :=
    { toFun w := BoundedContinuousFunction.ofNormedAddCommGroup (I w) (I w).continuous
        (C * ‖w‖) (hI w)
      map_add' w₁ w₂ := by
        ext t
        change (Real.sqrt t * Real.exp (-(ω * t))) •
            forwardDuhamel K (fun s ↦ A s (forwardDecode ω (w₁ + w₂) s)) t =
          (Real.sqrt t * Real.exp (-(ω * t))) •
              forwardDuhamel K (fun s ↦ A s (forwardDecode ω w₁ s)) t +
            (Real.sqrt t * Real.exp (-(ω * t))) •
              forwardDuhamel K (fun s ↦ A s (forwardDecode ω w₂ s)) t
        have hsum : (fun s ↦ A s (forwardDecode ω (w₁ + w₂) s)) =
            (fun s ↦ A s (forwardDecode ω w₁ s)) + (fun s ↦ A s (forwardDecode ω w₂ s)) := by
          funext s
          simp only [forwardDecode_add, Pi.add_apply, map_add]
        rw [hsum, forwardDuhamel_add (hint w₁ t) (hint w₂ t), smul_add]
      map_smul' c w := by
        ext t
        change (Real.sqrt t * Real.exp (-(ω * t))) •
            forwardDuhamel K (fun s ↦ A s (forwardDecode ω (c • w) s)) t =
          c • ((Real.sqrt t * Real.exp (-(ω * t))) •
            forwardDuhamel K (fun s ↦ A s (forwardDecode ω w s)) t)
        have hsmul : (fun s ↦ A s (forwardDecode ω (c • w) s)) =
            c • (fun s ↦ A s (forwardDecode ω w s)) := by
          funext s
          simp only [forwardDecode_smul, Pi.smul_apply, map_smul]
        rw [hsmul, forwardDuhamel_smul, smul_comm] }
  exact L.mkContinuous C fun w ↦ BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg hC (norm_nonneg w)) (hI w)

/-- The operator evaluates to the weighted forward integral of the perturbed decoded path. -/
theorem forwardPerturbationOperator_apply (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Ioi 0 ×ˢ univ))
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ a) (w : Ioi (0 : ℝ) →ᵇ E) (t : Ioi (0 : ℝ)) :
    forwardPerturbationOperator K A hω hKc hK hAc hA w t =
      (Real.sqrt t * Real.exp (-(ω * t))) •
        forwardDuhamel K (fun s ↦ A s (forwardDecode ω w s)) t :=
  rfl

/-- The perturbation operator has norm at most `(2√2 + √(2π)) M a / √ω`. -/
theorem norm_forwardPerturbationOperator_le (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (hAc : ContinuousOn (fun p : ℝ × E ↦ A p.1 p.2) (Ioi 0 ×ˢ univ))
    (hA : ∀ s, 0 < s → ‖A s‖ ≤ a) :
    ‖forwardPerturbationOperator K A hω hKc hK hAc hA‖ ≤
      forwardSmoothingConstant * M * a / Real.sqrt ω := by
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  have ha : 0 ≤ a := (norm_nonneg _).trans (hA 1 one_pos)
  unfold forwardPerturbationOperator
  apply LinearMap.mkContinuous_norm_le
  exact div_nonneg (mul_nonneg (mul_nonneg forwardSmoothingConstant_nonneg hM) ha)
    (Real.sqrt_nonneg _)

end Perturbation

section Operator

variable (K : ℝ → E →L[ℝ] E) {M ω : ℝ}

/-- The weighted forward smoothing operator `w ↦ √t e^{-ωt} ∫₀ᵗ K (t - s) (decode w s) ds`
on bounded continuous paths over positive times: the perturbation operator with the identity
as perturbation. -/
def forwardSmoothingOperator (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) :
    (Ioi (0 : ℝ) →ᵇ E) →L[ℝ] (Ioi (0 : ℝ) →ᵇ E) :=
  forwardPerturbationOperator K (fun _ ↦ ContinuousLinearMap.id ℝ E) hω hKc hK
    ((ContinuousLinearMap.id ℝ E).continuous.comp continuous_snd).continuousOn
    (fun _ _ ↦ ContinuousLinearMap.norm_id_le)

/-- The operator evaluates to the weighted forward integral of the decoded path. -/
theorem forwardSmoothingOperator_apply (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    (w : Ioi (0 : ℝ) →ᵇ E) (t : Ioi (0 : ℝ)) :
    forwardSmoothingOperator K hω hKc hK w t =
      (Real.sqrt t * Real.exp (-(ω * t))) • forwardDuhamel K (forwardDecode ω w) t :=
  rfl

/-- A large exponential weight makes the forward smoothing operator small. -/
theorem norm_forwardSmoothingOperator_le (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) :
    ‖forwardSmoothingOperator K hω hKc hK‖ ≤ forwardSmoothingConstant * M / Real.sqrt ω := by
  have h := norm_forwardPerturbationOperator_le K (fun _ ↦ ContinuousLinearMap.id ℝ E) hω hKc
    hK ((ContinuousLinearMap.id ℝ E).continuous.comp continuous_snd).continuousOn
    (fun _ _ ↦ ContinuousLinearMap.norm_id_le)
  rwa [mul_one] at h

/-- Uniqueness for the forward Volterra equation. A path that is continuous at positive times,
has a singular bound `C s^(-1/2) exp (ω s)` for some rate `ω`, and satisfies
`v t + ∫₀ᵗ K (t - s) (v s) ds = 0` for `t > 0` vanishes at positive times. With a rate
`ω' ≥ ω` large enough, the weighted path is a fixed point of a forward smoothing operator of
norm at most one half. -/
theorem eq_zero_of_add_forwardDuhamel_eq_zero
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    {v : ℝ → E} (hvc : ContinuousOn v (Ioi 0)) {C : ℝ}
    (hvb : ∀ s, 0 < s → ‖v s‖ ≤ C * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω * s))
    (hv : ∀ t, 0 < t → v t + forwardDuhamel K v t = 0) {t : ℝ} (ht : 0 < t) : v t = 0 := by
  have hM : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hK 1 one_pos)
    rwa [Real.one_rpow, mul_one] at h
  have hc := forwardSmoothingConstant_nonneg
  have ha : 0 ≤ 2 * forwardSmoothingConstant * M := by positivity
  set a := 2 * forwardSmoothingConstant * M + 1 with ha_def
  set ω' := max ω (a ^ 2) with hω'_def
  have ha1 : 0 < a := by linarith
  have hω' : 0 < ω' := lt_of_lt_of_le (pow_pos ha1 2) (le_max_right _ _)
  have hsqrt : a ≤ Real.sqrt ω' :=
    (Real.sqrt_sq (by linarith)).symm.le.trans (Real.sqrt_le_sqrt (le_max_right _ _))
  set V := forwardSmoothingOperator K hω' hKc hK with hV_def
  have hV : ‖V‖ ≤ 1 / 2 := by
    refine (norm_forwardSmoothingOperator_le K hω' hKc hK).trans ?_
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hω')]
    linarith
  set w := forwardEncode ω' (le_max_left ω (a ^ 2)) hvc hvb with hw_def
  have hw_apply (τ : Ioi (0 : ℝ)) : w τ = (Real.sqrt τ * Real.exp (-(ω' * τ))) • v τ := rfl
  have hdec (r : ℝ) (hr : 0 < r) : forwardDecode ω' w r = v r :=
    forwardDecode_forwardEncode _ _ _ _ hr
  have hw : w + V w = 0 := by
    refine BoundedContinuousFunction.ext fun τ ↦ ?_
    have hτ : (0 : ℝ) < τ := τ.2
    have hint : forwardDuhamel K (forwardDecode ω' w) τ = forwardDuhamel K v τ :=
      intervalIntegral.integral_congr_ae (.of_forall fun r hr ↦ by
        rw [hdec r (uIoc_of_le hτ.le ▸ hr : r ∈ Ioc 0 (τ : ℝ)).1])
    rw [BoundedContinuousFunction.add_apply, hV_def, forwardSmoothingOperator_apply, hint,
      hw_apply, ← smul_add, hv τ hτ, smul_zero, BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  have hw0 : w = 0 := by
    have hle : ‖w‖ ≤ 1 / 2 * ‖w‖ := ((congrArg norm (eq_neg_of_add_eq_zero_left hw)).trans
      (norm_neg _)).trans_le (V.le_of_opNorm_le hV w)
    exact norm_le_zero_iff.mp (by linarith [norm_nonneg w])
  have h : (Real.sqrt t * Real.exp (-(ω' * t))) • v t = 0 := by
    simpa only [hw0, BoundedContinuousFunction.coe_zero, Pi.zero_apply] using
      (hw_apply ⟨t, ht⟩).symm
  calc
    v t = (t ^ (-(1 / 2 : ℝ)) * Real.exp (ω' * t)) •
        ((Real.sqrt t * Real.exp (-(ω' * t))) • v t) := by
      rw [smul_smul, rpow_neg_one_half_mul_exp_mul_sqrt_mul_exp ht, one_smul]
    _ = 0 := by rw [h, smul_zero]

/-- Two paths that are continuous at positive times, have singular bounds
`Cᵢ s^(-1/2) exp (ωᵢ s)` with any rates `ωᵢ`, and satisfy the same forward Volterra equation
`v t + ∫₀ᵗ K (t - s) (v s) ds = g t` for `t > 0` agree at positive times. -/
theorem eq_of_add_forwardDuhamel_eq
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ)))
    {v₁ v₂ : ℝ → E} (hc₁ : ContinuousOn v₁ (Ioi 0)) (hc₂ : ContinuousOn v₂ (Ioi 0))
    {C₁ C₂ ω₁ ω₂ : ℝ}
    (hb₁ : ∀ s, 0 < s → ‖v₁ s‖ ≤ C₁ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω₁ * s))
    (hb₂ : ∀ s, 0 < s → ‖v₂ s‖ ≤ C₂ * s ^ (-(1 / 2 : ℝ)) * Real.exp (ω₂ * s))
    (h : ∀ t, 0 < t → v₁ t + forwardDuhamel K v₁ t = v₂ t + forwardDuhamel K v₂ t)
    {t : ℝ} (ht : 0 < t) : v₁ t = v₂ t := by
  have hb : ∀ s, 0 < s → ‖(v₁ - v₂) s‖ ≤
      (max C₁ 0 + max C₂ 0) * s ^ (-(1 / 2 : ℝ)) * Real.exp (max ω₁ ω₂ * s) := by
    intro s hs
    calc
      ‖(v₁ - v₂) s‖ ≤ ‖v₁ s‖ + ‖v₂ s‖ := norm_sub_le _ _
      _ ≤ max C₁ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (max ω₁ ω₂ * s) +
          max C₂ 0 * s ^ (-(1 / 2 : ℝ)) * Real.exp (max ω₁ ω₂ * s) :=
        add_le_add ((hb₁ s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs (le_max_left _ _)))
          ((hb₂ s hs).trans (mul_rpow_neg_one_half_mul_exp_le hs (le_max_right _ _)))
      _ = _ := by ring
  have hv : ∀ τ, 0 < τ → (v₁ - v₂) τ + forwardDuhamel K (v₁ - v₂) τ = 0 := by
    intro τ hτ
    have hsub : forwardDuhamel K (v₁ - v₂) τ =
        forwardDuhamel K v₁ τ - forwardDuhamel K v₂ τ := by
      simp only [forwardDuhamel, Pi.sub_apply, map_sub]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_forwardIntegrand hKc hK hc₁ hb₁ hτ.le)
        (intervalIntegrable_forwardIntegrand hKc hK hc₂ hb₂ hτ.le)
    rw [Pi.sub_apply, hsub, sub_add_sub_comm, h τ hτ, sub_self]
  exact sub_eq_zero.mp
    (eq_zero_of_add_forwardDuhamel_eq_zero K hKc hK (v := v₁ - v₂) (hc₁.sub hc₂) hb hv ht)

/-- Each weighted path is contracted by the factor `forwardSmoothingConstant * M / √ω`. -/
theorem norm_forwardSmoothingOperator_apply_le (hω : 0 < ω)
    (hKc : ContinuousOn (fun p : ℝ × E ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-(1 / 2 : ℝ))) (w : Ioi (0 : ℝ) →ᵇ E) :
    ‖forwardSmoothingOperator K hω hKc hK w‖ ≤
      forwardSmoothingConstant * M / Real.sqrt ω * ‖w‖ :=
  (forwardSmoothingOperator K hω hKc hK).le_of_opNorm_le
    (norm_forwardSmoothingOperator_le K hω hKc hK) w

end Operator

/-! ## Inverting `1 + V` -/

section Inverse

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The inverse of `1 + V` for an operator of norm less than one, given by the Neumann
series. -/
def inverseOneAdd (V : X →L[ℝ] X) (hV : ‖V‖ < 1) : X →L[ℝ] X :=
  ↑(Units.oneSub (-V) (by rwa [norm_neg]))⁻¹

/-- The inverse solves the perturbed equation `w + V w = g`. -/
theorem inverseOneAdd_add_apply (V : X →L[ℝ] X) (hV : ‖V‖ < 1) (g : X) :
    inverseOneAdd V hV g + V (inverseOneAdd V hV g) = g := by
  have h := congrArg (fun L : X →L[ℝ] X ↦ L g)
    (Units.oneSub (-V) (by rwa [norm_neg])).mul_inv
  simp only [Units.val_oneSub, sub_neg_eq_add, mul_apply_eq_comp, add_apply,
    one_apply_eq_self] at h
  exact h

/-- Every solution of `w + V w = g` is the value of the inverse at `g`. -/
theorem eq_inverseOneAdd (V : X →L[ℝ] X) (hV : ‖V‖ < 1) {w g : X} (h : w + V w = g) :
    w = inverseOneAdd V hV g := by
  have h' := congrArg (fun L : X →L[ℝ] X ↦ L w)
    (Units.oneSub (-V) (by rwa [norm_neg])).inv_mul
  simp only [Units.val_oneSub, sub_neg_eq_add, mul_apply_eq_comp, add_apply,
    one_apply_eq_self, h] at h'
  exact h'.symm

/-- A solution of `w + v = g` with `‖v‖ ≤ ‖w‖ / 2` has at most twice the norm of `g`. -/
theorem norm_le_two_mul_of_add_eq {Y : Type*} [SeminormedAddCommGroup Y] {w v g : Y}
    (h : w + v = g) (hv : ‖v‖ ≤ 1 / 2 * ‖w‖) : ‖w‖ ≤ 2 * ‖g‖ := by
  have hw : w = g - v := eq_sub_of_add_eq h
  have hbound : ‖w‖ ≤ ‖g‖ + 1 / 2 * ‖w‖ :=
    calc
      ‖w‖ = ‖g - v‖ := by rw [← hw]
      _ ≤ ‖g‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl hv
  linarith

/-- A perturbation of norm at most one half at most doubles the norm. -/
theorem norm_inverseOneAdd_apply_le (V : X →L[ℝ] X) (hV : ‖V‖ < 1) (hhalf : ‖V‖ ≤ 1 / 2)
    (g : X) : ‖inverseOneAdd V hV g‖ ≤ 2 * ‖g‖ :=
  norm_le_two_mul_of_add_eq (inverseOneAdd_add_apply V hV g) (V.le_of_opNorm_le hhalf _)

theorem norm_inverseOneAdd_le (V : X →L[ℝ] X) (hV : ‖V‖ < 1) (hhalf : ‖V‖ ≤ 1 / 2) :
    ‖inverseOneAdd V hV‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (norm_inverseOneAdd_apply_le V hV hhalf)

end Inverse

end PDE.Analysis.Evolution
