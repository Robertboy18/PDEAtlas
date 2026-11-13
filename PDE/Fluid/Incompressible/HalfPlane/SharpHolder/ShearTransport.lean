/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Rearrangement.Transport1D
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearMap

/-!
# Vertical transport on the columns of the horizontal Hölder estimate of `u_y`

Chen and Hou, Part I, Appendix B.1: for two points `(∓1, h)` at unit half-distance, the
difference of the localized kernels `K₂` is, on the column at abscissa `p`, the kernel
`Δ_B(p, t) = 1{|p + 1| ≤ B} K₂(p + 1, t) - 1{|p - 1| ≤ B} K₂(p - 1, t)` in the vertical offset
`t`. It is even in `t`, odd in `p`, negative below the threshold `s_c(p)` and positive above it.
On `[0, A]`, `A = min(h, B)`, the part above `T(p, A)` has zero mass and is transported
vertically by the map `T` (the map (B.66) inside, `(p - 1)²/t` near the edge of the boxes); the
rest is nonpositive and is compared with the column at `-p`; the part above `h` reads the odd
extension at the two heights `h ± t`.

## Main results

* `abs_setIntegral_mul_le_of_hasDerivAt`: the transport lemma (Part I, Lemma 3.6) on a balanced
  interval `[T A, A]` for a kernel with an explicit primitive.
* `abs_integral_sub_integral_le_of_hasDerivAt`: the column estimate for an abstract kernel.
* `localShearDifference`, `localShearThreshold`, `localShearMap`, `shearCost`, `shearMass`: the
  localized kernel, threshold, map, vertical cost and column mass `Δ_{1D}`.
* `abs_integral_localShearDifference_add_le`: the column estimate for `Δ_B`.
* `shearMassCost`, `shearUpperCost`, `shearOuterCost`: the constants `S̃_{1D}`, `S_up`, `S_out` of
  Part I, (B.39) and (B.40).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.6, p. 29, Appendix B.1,
  pp. 129-136, and Appendix B.3.2, (B.66), p. 142.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter PDE.Analysis.Rearrangement
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

section Column

variable {k Ψ T : ℝ → ℝ} {c A : ℝ}

/-- The fundamental theorem of calculus on `[s, t]` for a continuous density `k` with primitive
`Ψ`. -/
theorem setIntegral_Icc_eq_sub_of_hasDerivAt {s t : ℝ} (hst : s ≤ t) (hk : ContinuousOn k (Icc s t))
    (hΨ : ∀ x ∈ Icc s t, HasDerivAt Ψ (k x) x) : ∫ x in Icc s t, k x = Ψ t - Ψ s := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx ↦ hΨ x ?_) ?_
  · rwa [uIcc_of_le hst] at hx
  · exact (hk.mono fun x hx ↦ by rwa [uIcc_of_le hst] at hx).intervalIntegrable

/-- **Transport on a balanced interval.** Let `k` be continuous on `[0, A]` with primitive `Ψ`
there, nonpositive on `[0, c)` and nonnegative on `(c, ∞)`, and let `T` be a measurable map from
`(c, ∞)` to `(0, c)`, nonincreasing, with `Ψ(T t) = Ψ(t)`. For `c < A` the kernel `k` has zero
mass on `[T A, A]`, and a function `H` that is `1/2`-Hölder with constant `C` there satisfies
`|∫_{T A}^{A} k H| ≤ C ∫_c^A |k(t)| |t - T t|^{1/2} dt` (Chen and Hou, Part I, Lemma 3.6). -/
theorem abs_setIntegral_mul_le_of_hasDerivAt (hcA : c < A) (hk : ContinuousOn k (Icc 0 A))
    (hΨ : ∀ t ∈ Icc 0 A, HasDerivAt Ψ (k t) t) (hneg : ∀ t, 0 ≤ t → t < c → k t ≤ 0)
    (hpos : ∀ t, c < t → 0 ≤ k t) (hTm : Measurable T) (hT0 : ∀ t, c < t → 0 < T t)
    (hTc : ∀ t, c < t → T t < c) (hTanti : AntitoneOn T (Ioi c))
    (hmass : ∀ t, c < t → Ψ (T t) = Ψ t) {H : ℝ → ℝ} {C : ℝ≥0}
    (hH : HolderOnWith C (1 / 2) H (Icc (T A) A)) :
    ENNReal.ofReal |∫ t in Icc (T A) A, k t * H t| ≤
      C * ∫⁻ t in Ioc c A, ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ)) := by
  have hTA0 : 0 < T A := hT0 A hcA
  have hTAc : T A < c := hTc A hcA
  set S : Set ℝ := Icc (T A) A with hS
  set κ : ℝ → ℝ := S.indicator k with hκ
  have hS0 : ∀ x ∈ S, 0 ≤ x := fun x hx ↦ hTA0.le.trans hx.1
  have hSA : S ⊆ Icc 0 A := fun x hx ↦ ⟨hS0 x hx, hx.2⟩
  have hkS : ContinuousOn k S := hk.mono hSA
  have hki : IntegrableOn k S := hkS.integrableOn_Icc
  have hκi : Integrable κ := (integrable_indicator_iff measurableSet_Icc).2 hki
  have hzero : ∫ x, κ x = 0 := by
    rw [hκ, integral_indicator measurableSet_Icc,
      setIntegral_Icc_eq_sub_of_hasDerivAt (hTAc.trans hcA).le hkS (fun x hx ↦ hΨ x (hSA hx)),
      hmass A hcA, sub_self]
  have hκneg : ∀ᵐ x, x < c → κ x ≤ 0 :=
    Eventually.of_forall fun x hx ↦ indicator_apply_nonpos fun h ↦ hneg x (hS0 x h) hx
  have hκpos : ∀ᵐ x, c < x → 0 ≤ κ x :=
    Eventually.of_forall fun x hx ↦ indicator_apply_nonneg fun _ ↦ hpos x hx
  have hint : Integrable fun x ↦ κ x * |x - c| ^ ((1 / 2 : ℝ≥0) : ℝ) := by
    rw [show (fun x ↦ κ x * _) = S.indicator fun x ↦ k x * |x - c| ^ ((1 / 2 : ℝ≥0) : ℝ) by
      ext x; simp only [hκ, indicator_mul_left], integrable_indicator_iff measurableSet_Icc]
    exact (hkS.mul (Continuous.continuousOn (by fun_prop (disch := positivity)))).integrableOn_Icc
  have hTeq : ∀ᵐ y ∂volume.restrict (Ioi c), κ y ≠ 0 → ∫ x in T y..y, κ x = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : c < y) hκy
    have hyS : y ∈ S := mem_of_indicator_ne_zero hκy
    have hTy : T A ≤ T y := hTanti hy (hcA : A ∈ Ioi c) hyS.2
    have hTyy : T y ≤ y := ((hTc y hy).trans hy).le
    rw [intervalIntegral.integral_of_le hTyy, ← integral_Icc_eq_integral_Ioc]
    have hsub : Icc (T y) y ⊆ S := Icc_subset_Icc hTy hyS.2
    rw [setIntegral_congr_fun measurableSet_Icc (fun x hx ↦ by
        rw [hκ, indicator_of_mem (hsub hx)] : EqOn κ k (Icc (T y) y)),
      setIntegral_Icc_eq_sub_of_hasDerivAt hTyy (hkS.mono hsub) (fun x hx ↦ hΨ x (hSA (hsub hx))),
      hmass y hy, sub_self]
  have hmain := abs_integral_mul_le_of_integral_eq_zero hκi hκneg hκpos hzero hint
    hTm.aemeasurable (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : c < y) _ using hTc y hy)
    hTeq
    (by norm_num) measurableSet_Icc
    (Eventually.of_forall fun x hx ↦ mem_of_indicator_ne_zero hx) ⟨hTAc.le, hcA.le⟩ hH
  have hlhs : ∫ x, κ x * H x = ∫ t in S, k t * H t := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1 with x
    simp only [hκ, hS, indicator_mul_left]
  have hrhs : ∫ y in Ioi c, |κ y| * |y - T y| ^ ((1 / 2 : ℝ≥0) : ℝ) =
      ∫ y in Ioc c A, |k y| * |y - T y| ^ (1 / 2 : ℝ) := by
    rw [show Ioc c A = Ioi c ∩ S from Subset.antisymm (fun y hy ↦ ⟨hy.1, (hTAc.trans hy.1).le,
      hy.2⟩) fun y hy ↦ ⟨hy.1, hy.2.2⟩, ← setIntegral_indicator measurableSet_Icc]
    congr 1 with y
    simp only [hκ, hS, indicator_mul_left, ← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
    norm_num
  rw [hlhs, hrhs] at hmain
  have hnn : 0 ≤ ∫ y in Ioc c A, |k y| * |y - T y| ^ (1 / 2 : ℝ) :=
    setIntegral_nonneg measurableSet_Ioc fun y _ ↦ by positivity
  calc ENNReal.ofReal |∫ t in S, k t * H t|
      ≤ ENNReal.ofReal (C * ∫ y in Ioc c A, |k y| * |y - T y| ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = C * ENNReal.ofReal (∫ y in Ioc c A, |k y| * |y - T y| ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
    _ ≤ C * ∫⁻ t in Ioc c A, ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ)) := by
        gcongr
        rw [← abs_of_nonneg hnn, ← Real.enorm_eq_ofReal_abs]
        refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
        refine setLIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ |t - T t| ^ (1 / 2 : ℝ)),
          Real.enorm_eq_ofReal_abs]

/-- A function that is `1/2`-Hölder on `[-B, min(h, B)]` and odd about `h` on `(h, B]` is
integrable on `[-B, B]`. -/
theorem integrableOn_of_holderOnWith_of_odd {B h : ℝ} (hh : 0 ≤ h) {g : ℝ → ℝ} {C : ℝ≥0}
    (hg : HolderOnWith C (1 / 2) g (Icc (-B) (min h B)))
    (hodd : ∀ t ∈ Ioc h B, g t = -g (2 * h - t)) : IntegrableOn g (Icc (-B) B) := by
  have hc := hg.continuousOn (by norm_num)
  have hsub : Icc (-B) B ⊆ Icc (-B) (min h B) ∪ Ioc h B := fun t ht ↦ by
    by_cases hth : t ≤ h
    · exact Or.inl ⟨ht.1, le_min hth ht.2⟩
    · exact Or.inr ⟨lt_of_not_ge hth, ht.2⟩
  refine IntegrableOn.mono_set (IntegrableOn.union hc.integrableOn_Icc ?_) hsub
  have hr : ContinuousOn (fun t ↦ -g (2 * h - t)) (Icc h B) := by
    refine (hc.comp (continuous_const.sub continuous_id).continuousOn fun t ht ↦ ?_).neg
    simp only [Pi.sub_apply, id]
    exact ⟨by linarith [ht.2], le_min (by linarith [ht.1]) (by linarith [ht.1, ht.2])⟩
  exact (hr.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
    (fun t ht ↦ (hodd t ht).symm) measurableSet_Ioc

/-- The two halves of a function integrable on `[-B, B]`, the left one reflected onto `[0, B]`. -/
private theorem intervalIntegrable_halves {B : ℝ} (hB : 0 ≤ B) {f : ℝ → ℝ}
    (hi : IntegrableOn f (Icc (-B) B)) : IntervalIntegrable f volume (-B) 0 ∧
      IntervalIntegrable f volume 0 B ∧ IntervalIntegrable (fun t ↦ f (-t)) volume 0 B := by
  have hii : IntervalIntegrable f volume (-B) B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 hi
  have h₁ := hii.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le (by linarith) hB))
  refine ⟨h₁, hii.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le (by linarith) hB)), ?_⟩
  simpa using ((IntervalIntegrable.iff_comp_neg (f := f)).mp h₁).symm

/-- Folding a symmetric interval: for an even `k`,
`∫_{-B}^{B} k g = ∫_0^B k(t) (g(t) + g(-t)) dt`. -/
theorem setIntegral_Icc_neg_eq {B : ℝ} (hB : 0 ≤ B) {k g : ℝ → ℝ} (heven : ∀ t, k (-t) = k t)
    (hi : IntegrableOn (fun t ↦ k t * g t) (Icc (-B) B)) :
    ∫ t in Icc (-B) B, k t * g t = ∫ t in (0 : ℝ)..B, k t * (g t + g (-t)) := by
  obtain ⟨h₁, h₂, h₃⟩ := intervalIntegrable_halves hB hi
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_add_adjacent_intervals h₁ h₂, show ∫ t in -B..0, k t * g t =
      ∫ t in (0 : ℝ)..B, k (-t) * g (-t) by
      rw [intervalIntegral.integral_comp_neg (fun t ↦ k t * g t), neg_zero],
    ← intervalIntegral.integral_add h₃ h₂]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [heven]
  ring

/-- The folded integrand `k(t) (g(t) + g(-t))` of an even `k` is interval integrable on `[0, B]`
when `k g` is integrable on `[-B, B]`. -/
theorem intervalIntegrable_fold {B : ℝ} (hB : 0 ≤ B) {k g : ℝ → ℝ} (heven : ∀ t, k (-t) = k t)
    (hi : IntegrableOn (fun t ↦ k t * g t) (Icc (-B) B)) :
    IntervalIntegrable (fun t ↦ k t * (g t + g (-t))) volume 0 B := by
  obtain ⟨-, h₂, h₃⟩ := intervalIntegrable_halves hB hi
  simpa only [heven, mul_add] using h₂.add h₃

/-- `ofReal |x + y| ≤ ofReal |x| + ofReal |y|`. -/
theorem ofReal_abs_add_le (x y : ℝ) :
    ENNReal.ofReal |x + y| ≤ ENNReal.ofReal |x| + ENNReal.ofReal |y| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)

/-- `ofReal |x - y| ≤ ofReal |x| + ofReal |y|`. -/
private theorem ofReal_abs_sub_le (x y : ℝ) :
    ENNReal.ofReal |x - y| ≤ ENNReal.ofReal |x| + ENNReal.ofReal |y| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub _ _)

/-- The fold `g(t) + g(-t)` of a `1/2`-Hölder function on `[-B, A]` (`A ≤ B`) is `1/2`-Hölder on
`[0, A]` with twice the constant. -/
theorem holderOnWith_fold {A B : ℝ} (hAB : A ≤ B) {g : ℝ → ℝ} {C : ℝ≥0}
    (hg : HolderOnWith C (1 / 2) g (Icc (-B) A)) :
    HolderOnWith (2 * C) (1 / 2) (fun t ↦ g t + g (-t)) (Icc 0 A) := by
  intro t ht t' ht'
  have h₁ : t ∈ Icc (-B) A := ⟨by linarith [ht.1, ht.2], ht.2⟩
  have h₁' : t' ∈ Icc (-B) A := ⟨by linarith [ht'.1, ht'.2], ht'.2⟩
  have h₂ : -t ∈ Icc (-B) A := ⟨by linarith [ht.2], by linarith [ht.1, ht.2]⟩
  have h₂' : -t' ∈ Icc (-B) A := ⟨by linarith [ht'.2], by linarith [ht'.1, ht'.2]⟩
  calc edist (g t + g (-t)) (g t' + g (-t'))
      ≤ edist (g t) (g t') + edist (g (-t)) (g (-t')) := edist_add_add_le _ _ _ _
    _ ≤ C * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) + C * edist (-t) (-t') ^ ((1 / 2 : ℝ≥0) : ℝ) :=
        add_le_add (hg t h₁ t' h₁') (hg (-t) h₂ (-t') h₂')
    _ = (2 * C : ℝ≥0) * edist t t' ^ ((1 / 2 : ℝ≥0) : ℝ) := by
        rw [edist_neg_neg, ENNReal.coe_mul, ENNReal.coe_ofNat]
        ring

/-- The lower end `m` of the balanced interval `[m, A]` of a column, `T A` for `c < A` and `A`
otherwise, lies in `[0, A]`. -/
private theorem balancedEnd_mem (hA0 : 0 < A) (hT0 : ∀ t, c < t → 0 < T t)
    (hTc : ∀ t, c < t → T t < c) :
    0 ≤ (if c < A then T A else A) ∧ (if c < A then T A else A) ≤ A := by
  split_ifs with hcA
  exacts [⟨(hT0 A hcA).le, ((hTc A hcA).trans hcA).le⟩, ⟨hA0.le, le_rfl⟩]

/-- The balanced part `[m, A]` of a column, transported vertically by `T`. -/
private theorem abs_integral_balanced_le (hk : ContinuousOn k (Icc 0 A))
    (hΨ : ∀ t ∈ Icc 0 A, HasDerivAt Ψ (k t) t) (hneg : ∀ t, 0 ≤ t → t < c → k t ≤ 0)
    (hpos : ∀ t, c < t → 0 ≤ k t) (hTm : Measurable T) (hT0 : ∀ t, c < t → 0 < T t)
    (hTc : ∀ t, c < t → T t < c) (hTanti : AntitoneOn T (Ioi c))
    (hmass : ∀ t, c < t → Ψ (T t) = Ψ t) {G : ℝ → ℝ} {C : ℝ≥0}
    (hG : HolderOnWith (2 * C) (1 / 2) G (Icc 0 A)) :
    ENNReal.ofReal |∫ t in (if c < A then T A else A)..A, k t * G t| ≤
      2 * C * ∫⁻ t in Ioc c A, ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ)) := by
  split_ifs with hcA
  · rw [intervalIntegral.integral_of_le ((hTc A hcA).trans hcA).le,
      ← integral_Icc_eq_integral_Ioc]
    have h := abs_setIntegral_mul_le_of_hasDerivAt hcA hk hΨ hneg hpos hTm hT0 hTc hTanti
      hmass (hG.mono (Icc_subset_Icc (hT0 A hcA).le le_rfl))
    rwa [ENNReal.coe_mul, ENNReal.coe_ofNat] at h
  · simp

/-- The part of a column above `h`: the oddness of `G` about `h` pairs the heights `-t` and
`2h - t`. -/
private theorem abs_integral_odd_le {B h : ℝ} (hh : 0 < h) {G : ℝ → ℝ} {C : ℝ≥0}
    (hG : HolderOnWith C (1 / 2) G (Icc (-B) (min h B)))
    (hGodd : ∀ t ∈ Ioc h B, G t = -G (2 * h - t)) :
    ENNReal.ofReal |∫ t in min h B..B, k t * (G t + G (-t))| ≤
      C * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * ∫⁻ t in Ioc h B, ‖k t‖ₑ := by
  rcases le_or_gt B h with hBh | hhB
  · rw [min_eq_right hBh, intervalIntegral.integral_same, abs_zero, ENNReal.ofReal_zero]
    exact zero_le
  rw [min_eq_left hhB.le] at hG ⊢
  rw [intervalIntegral.integral_of_le hhB.le, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
  rw [enorm_mul, mul_comm (C * _ : ℝ≥0∞)]
  gcongr
  rw [hGodd t ht, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_mul (NNReal.coe_nonneg _), neg_add_eq_sub]
  refine ENNReal.ofReal_le_ofReal ?_
  have hd := hG.dist_le (x := -t) (y := 2 * h - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  rwa [Real.dist_eq, Real.dist_eq, show -t - (2 * h - t) = -(2 * h) by ring, abs_neg,
    abs_of_pos (by linarith : (0 : ℝ) < 2 * h), show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at hd

/-- For an even `k` continuous on `[-A, A]`, `∫_{-A}^{A} k = 2 ∫_0^A k`. -/
private theorem integral_Icc_neg_eq_two_mul (hA : 0 ≤ A) (heven : ∀ t, k (-t) = k t)
    (hk : ContinuousOn k (Icc (-A) A)) : ∫ t in Icc (-A) A, k t = 2 * ∫ t in (0 : ℝ)..A, k t := by
  have h := setIntegral_Icc_neg_eq hA heven (g := fun _ ↦ 1)
    (hk.integrableOn_Icc.congr_fun (fun t _ ↦ (mul_one (k t)).symm) measurableSet_Icc)
  simp only [mul_one, one_add_one_eq_two, intervalIntegral.integral_mul_const] at h
  rw [h, mul_comm]

/-- **The column estimate** of Chen and Hou, Part I, Appendix B.1 (the estimate of `u_y`). Let `k`
be even and continuous on `[-B, B]` with primitive `Ψ` on `[0, B]`, nonpositive on `[0, c)`,
nonnegative on `(c, ∞)`, with a transport map `T` as in `abs_setIntegral_mul_le_of_hasDerivAt`.
Let `A = min(h, B)` and let `g`, `g'` be `1/2`-Hölder with constant `C_y` on `[-B, A]`, odd about
`h` on `(h, B]`, and at distance at most `C_x (2p)^{1/2}` on `[-A, A]`. Then

`|∫_{-B}^{B} k g - ∫_{-B}^{B} k g'| ≤ 4 C_y ∫_c^A |k(t)| |t - T t|^{1/2} dt
  + C_x (2p)^{1/2} |∫_{-A}^{A} k| + 2 C_y (2h)^{1/2} ∫_h^B |k|`.

The part of `[0, A]` above `T A` is balanced and transported vertically; on `[0, T A]` the kernel
is nonpositive and `g` is compared with `g'`; above `h` the oddness of `g` about `h` pairs the
heights `-t` and `2h - t`. -/
theorem abs_integral_sub_integral_le_of_hasDerivAt {B h p : ℝ} (hB : 0 < B) (hh : 0 < h)
    (hk : ContinuousOn k (Icc (-B) B)) (heven : ∀ t, k (-t) = k t)
    (hΨ : ∀ t ∈ Icc 0 B, HasDerivAt Ψ (k t) t) (hneg : ∀ t, 0 ≤ t → t < c → k t ≤ 0)
    (hpos : ∀ t, c < t → 0 ≤ k t) (hTm : Measurable T) (hT0 : ∀ t, c < t → 0 < T t)
    (hTc : ∀ t, c < t → T t < c) (hTanti : AntitoneOn T (Ioi c))
    (hmass : ∀ t, c < t → Ψ (T t) = Ψ t) {g g' : ℝ → ℝ} {Cx Cy : ℝ≥0}
    (hgy : HolderOnWith Cy (1 / 2) g (Icc (-B) (min h B)))
    (hg'y : HolderOnWith Cy (1 / 2) g' (Icc (-B) (min h B)))
    (hodd : ∀ t ∈ Ioc h B, g t = -g (2 * h - t)) (hodd' : ∀ t ∈ Ioc h B, g' t = -g' (2 * h - t))
    (hx : ∀ t ∈ Icc (-min h B) (min h B), |g t - g' t| ≤ Cx * (2 * p) ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal |(∫ t in Icc (-B) B, k t * g t) - ∫ t in Icc (-B) B, k t * g' t| ≤
      4 * Cy * (∫⁻ t in Ioc c (min h B), ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ))) +
      Cx * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |∫ t in Icc (-min h B) (min h B), k t|) +
      2 * Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * ∫⁻ t in Ioc h B, ‖k t‖ₑ := by
  set A := min h B with hA
  have hA0 : 0 < A := lt_min hh hB
  have hAB : A ≤ B := min_le_right _ _
  have hkg : IntegrableOn (fun t ↦ k t * g t) (Icc (-B) B) :=
    (integrableOn_of_holderOnWith_of_odd hh.le hgy hodd).continuousOn_mul hk isCompact_Icc
  have hkg' : IntegrableOn (fun t ↦ k t * g' t) (Icc (-B) B) :=
    (integrableOn_of_holderOnWith_of_odd hh.le hg'y hodd').continuousOn_mul hk isCompact_Icc
  rw [setIntegral_Icc_neg_eq hB.le heven hkg, setIntegral_Icc_neg_eq hB.le heven hkg']
  set H : ℝ → ℝ := fun t ↦ g t + g (-t) with hH
  set H' : ℝ → ℝ := fun t ↦ g' t + g' (-t) with hH'
  have hHi : IntervalIntegrable (fun t ↦ k t * H t) volume 0 B :=
    intervalIntegrable_fold hB.le heven hkg
  have hH'i : IntervalIntegrable (fun t ↦ k t * H' t) volume 0 B :=
    intervalIntegrable_fold hB.le heven hkg'
  -- the lower end `m` of the balanced interval `[m, A]`
  set m : ℝ := if c < A then T A else A with hm
  obtain ⟨hm0, hmA⟩ : 0 ≤ m ∧ m ≤ A := balancedEnd_mem hA0 hT0 hTc
  have hkA : ContinuousOn k (Icc 0 A) := hk.mono (Icc_subset_Icc (by linarith) hAB)
  have hΨA : ∀ t ∈ Icc 0 A, HasDerivAt Ψ (k t) t := fun t ht ↦ hΨ t ⟨ht.1, ht.2.trans hAB⟩
  have hkm : ∀ t, 0 ≤ t → t ≤ m → t ≠ c → k t ≤ 0 := fun t ht0 htm htc ↦ by
    refine hneg t ht0 (lt_of_le_of_ne ?_ htc)
    simp only [hm] at htm
    split_ifs at htm with hcA
    exacts [htm.trans (hTc A hcA).le, htm.trans (not_lt.1 hcA)]
  -- the mass of `k` on `[m, A]` vanishes
  have hbal : ∫ t in m..A, k t = 0 := by
    rw [intervalIntegral.integral_of_le hmA, ← integral_Icc_eq_integral_Ioc]
    simp only [hm]
    split_ifs with hcA
    · have hTA0 := hT0 A hcA
      rw [setIntegral_Icc_eq_sub_of_hasDerivAt ((hTc A hcA).trans hcA).le
        (hkA.mono (Icc_subset_Icc hTA0.le le_rfl))
        (fun x hx ↦ hΨA x ⟨hTA0.le.trans hx.1, hx.2⟩), hmass A hcA, sub_self]
    · simp
  -- splitting `[0, B]` at `m` and `A`
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ B → uIcc a b ⊆ uIcc 0 B := fun h0 hab hb ↦
    uIcc_subset_uIcc (mem_uIcc_of_le h0 (hab.trans hb)) (mem_uIcc_of_le (h0.trans hab) hb)
  have hsplit : ∀ F : ℝ → ℝ, IntervalIntegrable F volume 0 B →
      ∫ t in (0 : ℝ)..B, F t =
        (∫ t in (0 : ℝ)..m, F t) + (∫ t in m..A, F t) + ∫ t in A..B, F t := fun F hF ↦ by
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hF.mono_set (hsub le_rfl hm0 (hmA.trans hAB))) (hF.mono_set (hsub hm0 hmA hAB)),
      intervalIntegral.integral_add_adjacent_intervals
        (hF.mono_set (hsub le_rfl hA0.le hAB)) (hF.mono_set (hsub hA0.le hAB le_rfl))]
  rw [hsplit _ hHi, hsplit _ hH'i]
  -- the negative part: comparing `H` with `H'`
  have hlow : ENNReal.ofReal |(∫ t in (0 : ℝ)..m, k t * H t) - ∫ t in (0 : ℝ)..m, k t * H' t| ≤
      Cx * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |∫ t in Icc (-A) A, k t|) := by
    have hkm' : IntervalIntegrable k volume 0 m :=
      (hkA.mono (Icc_subset_Icc le_rfl hmA)).intervalIntegrable_of_Icc hm0
    set K : ℝ := 2 * Cx * (2 * p) ^ (1 / 2 : ℝ)
    have hpt : ∀ᵐ t, t ∈ Ioc 0 m → ‖k t * H t - k t * H' t‖ ≤ -k t * K := by
      filter_upwards [Measure.ae_ne volume c] with t htc ht
      have hkt := hkm t ht.1.le ht.2 htc
      have hd : |H t - H' t| ≤ 2 * Cx * (2 * p) ^ (1 / 2 : ℝ) := by
        have h₁ := hx t ⟨by linarith [ht.1], ht.2.trans hmA⟩
        have h₂ := hx (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
        calc |H t - H' t| = |(g t - g' t) + (g (-t) - g' (-t))| := by simp only [H, H']; ring_nf
          _ ≤ |g t - g' t| + |g (-t) - g' (-t)| := abs_add_le _ _
          _ ≤ _ := by linarith
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonpos hkt]
      exact mul_le_mul_of_nonneg_left hd (by linarith)
    have hbd := intervalIntegral.norm_integral_le_of_norm_le hm0 hpt (hkm'.neg.mul_const K)
    rw [← intervalIntegral.integral_sub (hHi.mono_set (hsub le_rfl hm0 (hmA.trans hAB)))
      (hH'i.mono_set (hsub le_rfl hm0 (hmA.trans hAB))), ← Real.norm_eq_abs]
    have hm_eq : ∫ t in (0 : ℝ)..m, k t = ∫ t in (0 : ℝ)..A, k t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hkm'
        ((hkA.mono (Icc_subset_Icc hm0 le_rfl)).intervalIntegrable_of_Icc hmA), hbal, add_zero]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hm_eq] at hbd
    have hnp : ∫ t in (0 : ℝ)..A, k t ≤ 0 := by
      rw [← hm_eq, ← neg_nonneg, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_nonneg_of_ae_restrict hm0 ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (Measure.ae_ne volume c)] with t ht htc
      exact neg_nonneg.2 (hkm t ht.1 ht.2 htc)
    calc ENNReal.ofReal ‖∫ t in (0 : ℝ)..m, k t * H t - k t * H' t‖
        ≤ ENNReal.ofReal (-(∫ t in (0 : ℝ)..A, k t) * K) := ENNReal.ofReal_le_ofReal hbd
      _ = Cx * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |∫ t in Icc (-A) A, k t|) := by
        rw [integral_Icc_neg_eq_two_mul hA0.le heven (hk.mono (Icc_subset_Icc (by linarith) hAB)),
          abs_mul, abs_two, abs_of_nonpos hnp, ← ENNReal.ofReal_coe_nnreal,
          ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
        congr 1
        simp only [K]
        ring
  -- the balanced part and the part above `h`
  set cost : ℝ≥0∞ := ∫⁻ t in Ioc c A, ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ))
  set L : ℝ≥0∞ := ∫⁻ t in Ioc h B, ‖k t‖ₑ
  have hb := abs_integral_balanced_le hkA hΨA hneg hpos hTm hT0 hTc hTanti hmass
    (holderOnWith_fold hAB hgy)
  have hb' := abs_integral_balanced_le hkA hΨA hneg hpos hTm hT0 hTc hTanti hmass
    (holderOnWith_fold hAB hg'y)
  have he := abs_integral_odd_le (k := k) hh hgy hodd
  have he' := abs_integral_odd_le (k := k) hh hg'y hodd'
  calc ENNReal.ofReal |((∫ t in (0 : ℝ)..m, k t * H t) + (∫ t in m..A, k t * H t) +
          ∫ t in A..B, k t * H t) - ((∫ t in (0 : ℝ)..m, k t * H' t) +
          (∫ t in m..A, k t * H' t) + ∫ t in A..B, k t * H' t)|
      = ENNReal.ofReal |((∫ t in (0 : ℝ)..m, k t * H t) - ∫ t in (0 : ℝ)..m, k t * H' t) +
          ((∫ t in m..A, k t * H t) - ∫ t in m..A, k t * H' t) +
          ((∫ t in A..B, k t * H t) - ∫ t in A..B, k t * H' t)| := by ring_nf
    _ ≤ ENNReal.ofReal |(∫ t in (0 : ℝ)..m, k t * H t) - ∫ t in (0 : ℝ)..m, k t * H' t| +
          (ENNReal.ofReal |∫ t in m..A, k t * H t| + ENNReal.ofReal |∫ t in m..A, k t * H' t|) +
          (ENNReal.ofReal |∫ t in A..B, k t * H t| + ENNReal.ofReal |∫ t in A..B, k t * H' t|) :=
        (ofReal_abs_add_le _ _).trans (add_le_add ((ofReal_abs_add_le _ _).trans
          (add_le_add le_rfl (ofReal_abs_sub_le _ _))) (ofReal_abs_sub_le _ _))
    _ ≤ Cx * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |∫ t in Icc (-A) A, k t|) +
          (2 * Cy * cost + 2 * Cy * cost) +
          (Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * L +
            Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * L) := by
        gcongr
    _ = _ := by ring

/-- **The inner column estimate** of Chen and Hou, Part I, Appendix B.1 (the estimate of `v_x` on
the columns near the two points). With the hypotheses of
`abs_integral_sub_integral_le_of_hasDerivAt` on `k` and `T`, `A = min(h, B)`, and `g` `1/2`-Hölder
with constant `C_y` on `[-B, A]` and odd about `h` on `(h, B]`:

`|∫_{-B}^{B} k g - (∫_{-A}^{A} k) g(0)| ≤ 2 C_y ∫_c^A |k(t)| |t - T t|^{1/2} dt
  + 2 C_y ∫_0^{m} |k(t)| t^{1/2} dt + C_y (2h)^{1/2} ∫_h^B |k|`,

`m = T(A)` for `c < A` and `m = A` otherwise: the column mass is moved to the height `0` of the
two points, vertically (by `T` above `m`, directly below). -/
theorem abs_integral_sub_mul_le_of_hasDerivAt {B h : ℝ} (hB : 0 < B) (hh : 0 < h)
    (hk : ContinuousOn k (Icc (-B) B)) (heven : ∀ t, k (-t) = k t)
    (hΨ : ∀ t ∈ Icc 0 B, HasDerivAt Ψ (k t) t) (hneg : ∀ t, 0 ≤ t → t < c → k t ≤ 0)
    (hpos : ∀ t, c < t → 0 ≤ k t) (hTm : Measurable T) (hT0 : ∀ t, c < t → 0 < T t)
    (hTc : ∀ t, c < t → T t < c) (hTanti : AntitoneOn T (Ioi c))
    (hmass : ∀ t, c < t → Ψ (T t) = Ψ t) {g : ℝ → ℝ} {Cy : ℝ≥0}
    (hgy : HolderOnWith Cy (1 / 2) g (Icc (-B) (min h B)))
    (hodd : ∀ t ∈ Ioc h B, g t = -g (2 * h - t)) :
    ENNReal.ofReal |(∫ t in Icc (-B) B, k t * g t) -
        (∫ t in Icc (-min h B) (min h B), k t) * g 0| ≤
      2 * Cy * (∫⁻ t in Ioc c (min h B), ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ))) +
      2 * Cy * (∫⁻ t in Ioc 0 (if c < min h B then T (min h B) else min h B),
        ‖k t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))) +
      Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * ∫⁻ t in Ioc h B, ‖k t‖ₑ := by
  set A := min h B with hA
  have hA0 : 0 < A := lt_min hh hB
  have hAB : A ≤ B := min_le_right _ _
  have hkA : ContinuousOn k (Icc 0 A) := hk.mono (Icc_subset_Icc (by linarith) hAB)
  have hΨA : ∀ t ∈ Icc 0 A, HasDerivAt Ψ (k t) t := fun t ht ↦ hΨ t ⟨ht.1, ht.2.trans hAB⟩
  have hkg : IntegrableOn (fun t ↦ k t * g t) (Icc (-B) B) :=
    (integrableOn_of_holderOnWith_of_odd hh.le hgy hodd).continuousOn_mul hk isCompact_Icc
  set H : ℝ → ℝ := fun t ↦ g t + g (-t) with hH
  have hHi : IntervalIntegrable (fun t ↦ k t * H t) volume 0 B :=
    intervalIntegrable_fold hB.le heven hkg
  have hHy : HolderOnWith (2 * Cy) (1 / 2) H (Icc 0 A) := holderOnWith_fold hAB hgy
  set G : ℝ → ℝ := fun t ↦ H t - 2 * g 0 with hG
  have hGy : HolderOnWith (2 * Cy) (1 / 2) G (Icc 0 A) := fun t ht t' ht' ↦ by
    simpa only [hG, edist_sub_right] using hHy t ht t' ht'
  have hG0 : ∀ t ∈ Icc 0 A, |G t| ≤ 2 * Cy * t ^ (1 / 2 : ℝ) := fun t ht ↦ by
    have h := hHy.dist_le ht ⟨le_rfl, hA0.le⟩
    rw [Real.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg ht.1,
      show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num] at h
    have e : H 0 = 2 * g 0 := by simp only [hH, neg_zero]; ring
    simpa only [hG, e, NNReal.coe_mul, NNReal.coe_ofNat] using h
  -- the folded identity
  have hfold : (∫ t in Icc (-B) B, k t * g t) - (∫ t in Icc (-A) A, k t) * g 0 =
      (∫ t in (0 : ℝ)..A, k t * G t) + ∫ t in A..B, k t * H t := by
    have h1 := hHi.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le hA0.le hAB))
    rw [setIntegral_Icc_neg_eq hB.le heven hkg, integral_Icc_neg_eq_two_mul hA0.le heven
        (hk.mono (Icc_subset_Icc (by linarith) hAB)),
      ← intervalIntegral.integral_add_adjacent_intervals h1
        (hHi.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le hA0.le hAB)))]
    have e : ∫ t in (0 : ℝ)..A, k t * G t =
        (∫ t in (0 : ℝ)..A, k t * H t) - (∫ t in (0 : ℝ)..A, k t) * (2 * g 0) := by
      simp only [hG, mul_sub]
      rw [intervalIntegral.integral_sub h1 ((hkA.intervalIntegrable_of_Icc hA0.le).mul_const _),
        intervalIntegral.integral_mul_const]
    rw [e]
    ring
  rw [hfold]
  -- the lower end `m`
  set m : ℝ := if c < A then T A else A with hm
  obtain ⟨hm0, hmA⟩ : 0 ≤ m ∧ m ≤ A := balancedEnd_mem hA0 hT0 hTc
  have hkG : IntervalIntegrable (fun t ↦ k t * G t) volume 0 A :=
    (hkA.mul (hGy.continuousOn (by norm_num))).intervalIntegrable_of_Icc hA0.le
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hkG.mono_set (uIcc_subset_uIcc_left (mem_uIcc_of_le hm0 hmA)))
    (hkG.mono_set (uIcc_subset_uIcc_right (mem_uIcc_of_le hm0 hmA)))]
  -- the three bounds
  have hlow : ENNReal.ofReal |∫ t in (0 : ℝ)..m, k t * G t| ≤
      2 * Cy * ∫⁻ t in Ioc 0 m, ‖k t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_of_le hm0, ← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    refine setLIntegral_mono' measurableSet_Ioc fun t ht ↦ ?_
    rw [enorm_mul, mul_left_comm, Real.enorm_eq_ofReal_abs (G t)]
    gcongr
    rw [← ENNReal.ofReal_coe_nnreal, show (2 : ℝ≥0∞) * ENNReal.ofReal (Cy : ℝ) *
        ENNReal.ofReal (t ^ (1 / 2 : ℝ)) = ENNReal.ofReal (2 * Cy * t ^ (1 / 2 : ℝ)) by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_ofNat]]
    exact ENNReal.ofReal_le_ofReal (hG0 t ⟨ht.1.le, ht.2.trans hmA⟩)
  have hmid := abs_integral_balanced_le hkA hΨA hneg hpos hTm hT0 hTc hTanti hmass hGy
  have hup := abs_integral_odd_le (k := k) hh hgy hodd
  calc ENNReal.ofReal |(∫ t in (0 : ℝ)..m, k t * G t) + (∫ t in m..A, k t * G t) +
        ∫ t in A..B, k t * H t|
      ≤ ENNReal.ofReal |∫ t in (0 : ℝ)..m, k t * G t| + ENNReal.ofReal |∫ t in m..A, k t * G t| +
          ENNReal.ofReal |∫ t in A..B, k t * H t| :=
        (ofReal_abs_add_le _ _).trans (add_le_add (ofReal_abs_add_le _ _) le_rfl)
    _ ≤ 2 * Cy * (∫⁻ t in Ioc 0 m, ‖k t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))) +
          2 * Cy * (∫⁻ t in Ioc c A, ‖k t‖ₑ * ENNReal.ofReal (|t - T t| ^ (1 / 2 : ℝ))) +
          Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) * ∫⁻ t in Ioc h B, ‖k t‖ₑ := by
        gcongr
    _ = _ := by ring

end Column

/-! ### The kernel `K₂` on vertical lines -/

/-- `∂_t (t / (2 (a² + t²))) = K₂(a, t)` for `a ≠ 0`. -/
theorem hasDerivAt_shearPrimitive {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    HasDerivAt (fun t ↦ t / (2 * (a ^ 2 + t ^ 2))) (shearDensity a t) t := by
  have hne : 2 * (a ^ 2 + t ^ 2) ≠ 0 := by positivity
  have hg : HasDerivAt (fun t ↦ 2 * (a ^ 2 + t ^ 2)) (2 * (2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_add (a ^ 2)).const_mul 2
  refine ((hasDerivAt_id t).div hg hne).congr_deriv ?_
  rw [shearDensity_eq, id]
  field_simp
  ring

/-- `K₂(a, ·)` is continuous for `a ≠ 0`. -/
theorem continuous_shearDensity_right {a : ℝ} (ha : a ≠ 0) : Continuous (shearDensity a) :=
  continuous_iff_continuousAt.2 fun t ↦ by
    have hne : 2 * (a ^ 2 + t ^ 2) ^ 2 ≠ 0 := by positivity
    rw [show shearDensity a = fun b ↦ (a ^ 2 - b ^ 2) / (2 * (a ^ 2 + b ^ 2) ^ 2) from
      funext (shearDensity_eq a)]
    exact (continuous_const.sub (continuous_pow 2)).continuousAt.div (by fun_prop) hne

/-- `∫_{-A}^{A} K₂(a, t) dt = A / (a² + A²)` for `a ≠ 0`. -/
theorem integral_Icc_shearDensity {a : ℝ} (ha : a ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    ∫ t in Icc (-A) A, shearDensity a t = A / (a ^ 2 + A ^ 2) := by
  rw [setIntegral_Icc_eq_sub_of_hasDerivAt (by linarith)
    (continuous_shearDensity_right ha).continuousOn fun t _ ↦ hasDerivAt_shearPrimitive ha t]
  have hne : a ^ 2 + A ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The localized kernel of the horizontal estimate of `u_y` -/

/-- The localized kernel difference
`Δ_B(p, t) = 1{|p + 1| ≤ B} K₂(p + 1, t) - 1{|p - 1| ≤ B} K₂(p - 1, t)` of Chen and Hou, Part I,
(B.2), (B.6) and (B.7), at unit half-distance: the points are `(∓1, 0)` and the boxes have
half-width `B`. -/
def localShearDifference (B p t : ℝ) : ℝ :=
  (if |p + 1| ≤ B then shearDensity (p + 1) t else 0) -
    (if |p - 1| ≤ B then shearDensity (p - 1) t else 0)

/-- The localized sign threshold of Chen and Hou, Part I, (B.9): `s_c(p)` for `|p| + 1 ≤ B`
and `|p| - 1` otherwise. -/
def localShearThreshold (B p : ℝ) : ℝ :=
  if |p| + 1 ≤ B then shearThreshold p else |p| - 1

/-- The localized vertical transport map of Chen and Hou, Part I, (B.17) and (B.19): the map (B.66)
for `|p| + 1 ≤ B`, and `(|p| - 1)² / t`, the map of the single kernel `-K₂(|p| - 1, ·)`,
otherwise. -/
def localShearMap (B p t : ℝ) : ℝ :=
  if |p| + 1 ≤ B then shearMap p t else (|p| - 1) ^ 2 / t

/-- The vertical transport cost `∫_{s_c}^{A} |Δ_B(p, t)| |t - T(p, t)|^{1/2} dt` of the column
`p`, with the localized threshold and map. -/
def shearCost (B A p : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc (localShearThreshold B p) A, ‖localShearDifference B p t‖ₑ *
    ENNReal.ofReal (|t - localShearMap B p t| ^ (1 / 2 : ℝ))

/-- The column mass `Δ_{1D}(p) = ∫_{-A}^{A} Δ_B(p, t) dt` of Chen and Hou, Part I, (B.4), in the
closed form (B.14): `g_A(p + 1) 1{|p + 1| ≤ B} - g_A(p - 1) 1{|p - 1| ≤ B}`,
`g_A(y) = A/(y² + A²)`. -/
def shearMass (B A p : ℝ) : ℝ :=
  (if |p + 1| ≤ B then A / ((p + 1) ^ 2 + A ^ 2) else 0) -
    (if |p - 1| ≤ B then A / ((p - 1) ^ 2 + A ^ 2) else 0)

variable {B : ℝ}

/-- `Δ_B` is odd in `p`. -/
theorem localShearDifference_neg_left (p t : ℝ) :
    localShearDifference B (-p) t = -localShearDifference B p t := by
  simp only [localShearDifference]
  rw [show -p + 1 = -(p - 1) by ring, show -p - 1 = -(p + 1) by ring, abs_neg, abs_neg,
    shearDensity_neg_left, shearDensity_neg_left]
  ring

/-- `Δ_B` is even in `t`. -/
theorem localShearDifference_neg_right (p t : ℝ) :
    localShearDifference B p (-t) = localShearDifference B p t := by
  simp only [localShearDifference, shearDensity_neg_right]

/-- Inside, `Δ_B = Δ`. -/
theorem localShearDifference_of_le {p : ℝ} (hp : |p| + 1 ≤ B) (t : ℝ) :
    localShearDifference B p t = shearDifference p t := by
  have h₁ : |p + 1| ≤ B := (abs_add_le p 1).trans (by rwa [abs_one])
  have h₂ : |p - 1| ≤ B := (abs_sub _ _).trans (by rwa [abs_one])
  simp only [localShearDifference, h₁, h₂, ite_true, shearDifference]

/-- Near the edge, `Δ_B(p, t) = -K₂(p - 1, t)` for `B - 1 < p ≤ B + 1`. -/
theorem localShearDifference_of_lt (hB : 1 ≤ B) {p : ℝ} (hp₁ : B < p + 1) (hp₂ : p ≤ B + 1)
    (t : ℝ) : localShearDifference B p t = -shearDensity (p - 1) t := by
  have h₁ : ¬|p + 1| ≤ B := fun h ↦ by linarith [le_abs_self (p + 1)]
  have h₂ : |p - 1| ≤ B := abs_le.2 ⟨by linarith, by linarith⟩
  simp only [localShearDifference, h₁, h₂, ite_true, ite_false, zero_sub]

/-- Outside, `Δ_B(p, t) = 0` for `p > B + 1`. -/
theorem localShearDifference_of_gt {p : ℝ} (hp : B + 1 < p) (t : ℝ) :
    localShearDifference B p t = 0 := by
  have h₁ : ¬|p + 1| ≤ B := fun h ↦ by linarith [le_abs_self (p + 1)]
  have h₂ : ¬|p - 1| ≤ B := fun h ↦ by linarith [le_abs_self (p - 1)]
  simp only [localShearDifference, h₁, h₂, ite_false, sub_zero]

/-- The column mass is the integral of `Δ_B` over `[-A, A]` (`p ≠ ±1`). -/
theorem integral_Icc_localShearDifference {p : ℝ} (hp₁ : p + 1 ≠ 0) (hp₂ : p - 1 ≠ 0) {A : ℝ}
    (hA : 0 ≤ A) : ∫ t in Icc (-A) A, localShearDifference B p t = shearMass B A p := by
  have hi : ∀ q : ℝ, q ≠ 0 → IntegrableOn (shearDensity q) (Icc (-A) A) := fun q hq ↦
    (continuous_shearDensity_right hq).continuousOn.integrableOn_Icc
  have hite : ∀ q : ℝ, q ≠ 0 → ∀ P : Prop, [Decidable P] →
      ∫ t in Icc (-A) A, (if P then shearDensity q t else 0) =
        if P then A / (q ^ 2 + A ^ 2) else 0 := fun q hq P _ ↦ by
    split_ifs
    · exact integral_Icc_shearDensity hq hA
    · simp
  have hi' : ∀ q : ℝ, q ≠ 0 → ∀ P : Prop, [Decidable P] →
      IntegrableOn (fun t ↦ if P then shearDensity q t else 0) (Icc (-A) A) := fun q hq P _ ↦ by
    split_ifs
    · exact hi q hq
    · exact integrableOn_zero
  simp only [localShearDifference]
  rw [integral_sub (hi' _ hp₁ _) (hi' _ hp₂ _), hite _ hp₁, hite _ hp₂, shearMass]

/-- For `B ≥ 2`, `0 < p ≤ B + 1` and `p ≠ 1`, the kernel `Δ_B(p, ·)` with the localized threshold
and map satisfies the hypotheses of the column estimates
`abs_integral_sub_integral_le_of_hasDerivAt` and `abs_integral_sub_mul_le_of_hasDerivAt`: inside
with the map (B.66), near the edge with the single kernel `-K₂(p - 1, ·)` and the map
`(p - 1)² / t`. -/
private theorem localShearDifference_transport (hB : 2 ≤ B) {p : ℝ} (hp : 0 < p) (hp1 : p ≠ 1)
    (hpB : p ≤ B + 1) :
    ContinuousOn (localShearDifference B p) (Icc (-B) B) ∧
      (∀ t, localShearDifference B p (-t) = localShearDifference B p t) ∧
      ∃ Ψ : ℝ → ℝ, (∀ t ∈ Icc 0 B, HasDerivAt Ψ (localShearDifference B p t) t) ∧
      (∀ t, 0 ≤ t → t < localShearThreshold B p → localShearDifference B p t ≤ 0) ∧
      (∀ t, localShearThreshold B p < t → 0 ≤ localShearDifference B p t) ∧
      Measurable (localShearMap B p) ∧
      (∀ t, localShearThreshold B p < t → 0 < localShearMap B p t) ∧
      (∀ t, localShearThreshold B p < t → localShearMap B p t < localShearThreshold B p) ∧
      AntitoneOn (localShearMap B p) (Ioi (localShearThreshold B p)) ∧
      ∀ t, localShearThreshold B p < t → Ψ (localShearMap B p t) = Ψ t := by
  have hpa : |p| = p := abs_of_pos hp
  rcases le_or_gt (p + 1) B with h₁ | h₁
  · -- inside: the map (B.66)
    have h₁' : |p| + 1 ≤ B := by rwa [hpa]
    have hp2 : p ^ 2 ≠ 1 := fun h ↦ hp1 (by nlinarith)
    have hpole : ∀ t : ℝ, (p - 1) ^ 2 + t ^ 2 ≠ 0 := fun t ↦ by positivity
    have hs := shearThreshold_pos hp2
    rw [show localShearDifference B p = shearDifference p from
        funext (localShearDifference_of_le h₁'),
      show localShearThreshold B p = shearThreshold p by
        simp only [localShearThreshold, h₁', ite_true],
      show localShearMap B p = shearMap p from
        funext fun t ↦ by simp only [localShearMap, h₁', ite_true]]
    have hneg (t : ℝ) (ht : 0 ≤ t) (htc : t < shearThreshold p) : shearDifference p t ≤ 0 :=
      ((shearDifference_neg_iff hp (hpole t)).2 (by rwa [abs_of_nonneg ht])).le
    have hpos (t : ℝ) (htc : shearThreshold p < t) : 0 ≤ shearDifference p t :=
      ((shearDifference_pos_iff hp (hpole t)).2 (by rwa [abs_of_pos (hs.trans htc)])).le
    have hmass (t : ℝ) (ht : shearThreshold p < t) :
        shearPotential p (shearMap p t) = shearPotential p t :=
      shearPotential_shearMap (hs.trans ht) hp2
    exact ⟨((continuous_shearDensity_right (by linarith)).sub
        (continuous_shearDensity_right (sub_ne_zero.2 hp1))).continuousOn,
      shearDifference_neg_right p, shearPotential p,
      fun t _ ↦ hasDerivAt_shearPotential (by positivity) (hpole t), hneg, hpos,
      (measurable_shearMap.comp measurable_prodMk_left :),
      fun t ht ↦ shearMap_pos (hs.trans ht) hp2, fun t ht ↦ shearMap_lt_shearThreshold hp hp2 ht,
      (strictAntiOn_shearMap_right hp2).antitoneOn.mono (Ioi_subset_Ioi hs.le), hmass⟩
  -- near the edge: the single kernel `-K₂(p - 1, ·)` and the map `(p - 1)² / t`
  have h₁' : ¬p + 1 ≤ B := not_le.2 h₁
  have he : 0 < p - 1 := by linarith
  rw [show localShearDifference B p = fun t ↦ -shearDensity (p - 1) t from
      funext (localShearDifference_of_lt (by linarith) h₁ hpB),
    show localShearThreshold B p = p - 1 by simp only [localShearThreshold, hpa, h₁', ite_false],
    show localShearMap B p = fun t ↦ (p - 1) ^ 2 / t from
      funext fun t ↦ by simp only [localShearMap, hpa, h₁', ite_false]]
  set e := p - 1 with he_def
  refine ⟨(continuous_shearDensity_right he.ne').neg.continuousOn,
    fun t ↦ by simp only [shearDensity_neg_right], fun t ↦ -(t / (2 * (e ^ 2 + t ^ 2))),
    fun t _ ↦ (hasDerivAt_shearPrimitive he.ne' t).neg, fun t ht htc ↦ ?_, fun t htc ↦ ?_,
    measurable_const.div measurable_id, fun t ht ↦ div_pos (by positivity) (he.trans ht),
    fun t ht ↦ ?_, fun a ha b hb hab ↦ div_le_div_of_nonneg_left (by positivity) (he.trans ha) hab,
    fun t ht ↦ ?_⟩
  · have : 0 ≤ shearDensity e t := by
      simp only [shearDensity_eq]
      exact div_nonneg (by nlinarith) (by positivity)
    linarith
  · have : shearDensity e t ≤ 0 := by
      simp only [shearDensity_eq]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  · rw [div_lt_iff₀ (he.trans ht)]
    nlinarith
  · have ht0 : 0 < t := he.trans ht
    field_simp
    ring

/-- **The column estimate for `u_y`** (Chen and Hou, Part I, Appendix B.1.2, (B.21)-(B.26)). Let
`B ≥ 2`, `h > 0`, `A = min(h, B)`, `p > 0`, `p ≠ 1`, and
let `g`, `g'` (the values on the columns `p` and `-p`) be `1/2`-Hölder with constant `C_y` on
`[-B, A]`, odd about `h` on `(h, B]`, and at distance at most `C_x (2p)^{1/2}` on `[-A, A]`. Then

`|∫_{-B}^{B} Δ_B(p, t) g(t) dt + ∫_{-B}^{B} Δ_B(-p, t) g'(t) dt| ≤ 4 C_y cost_B(A, p)
  + C_x (2p)^{1/2} |Δ_{1D}(p)| + 2 C_y (2h)^{1/2} ∫_h^B |Δ_B(p, t)| dt`. -/
theorem abs_integral_localShearDifference_add_le (hB : 2 ≤ B) {h p : ℝ} (hh : 0 < h)
    (hp : 0 < p) (hp1 : p ≠ 1) {g g' : ℝ → ℝ} {Cx Cy : ℝ≥0}
    (hgy : HolderOnWith Cy (1 / 2) g (Icc (-B) (min h B)))
    (hg'y : HolderOnWith Cy (1 / 2) g' (Icc (-B) (min h B)))
    (hodd : ∀ t ∈ Ioc h B, g t = -g (2 * h - t)) (hodd' : ∀ t ∈ Ioc h B, g' t = -g' (2 * h - t))
    (hx : ∀ t ∈ Icc (-min h B) (min h B), |g t - g' t| ≤ Cx * (2 * p) ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal |(∫ t in Icc (-B) B, localShearDifference B p t * g t) +
        ∫ t in Icc (-B) B, localShearDifference B (-p) t * g' t| ≤
      4 * Cy * shearCost B (min h B) p +
      Cx * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B (min h B) p|) +
      2 * Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
        ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ := by
  have hB0 : 0 < B := by linarith
  simp only [localShearDifference_neg_left, neg_mul, integral_neg, ← sub_eq_add_neg]
  rw [← integral_Icc_localShearDifference (by linarith) (sub_ne_zero.2 hp1)
    (le_min hh.le hB0.le)]
  rcases le_or_gt p (B + 1) with hpB | hpB
  · obtain ⟨hk, heven, Ψ, hΨ, hneg, hpos, hTm, hT0, hTc, hTanti, hmass⟩ :=
      localShearDifference_transport hB hp hp1 hpB
    exact abs_integral_sub_integral_le_of_hasDerivAt hB0 hh hk heven hΨ hneg hpos hTm hT0 hTc
      hTanti hmass hgy hg'y hodd hodd' hx
  · simp only [localShearDifference_of_gt hpB, zero_mul, integral_zero, sub_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le

/-- The cost `∫_0^{min(T(p, A), A)} |Δ_B(p, t)| t^{1/2} dt` of moving the nonpositive part of the
column `p` to the height of the two points (Chen and Hou, Part I, (B.22), the second term). -/
def shearLowCost (B A p : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (if localShearThreshold B p < A then localShearMap B p A else A),
    ‖localShearDifference B p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))

/-- **The inner column estimate for `v_x`** (Chen and Hou, Part I, Appendix B.1.2, (B.21)-(B.23)):
for `B ≥ 2`, `h > 0`, `A = min(h, B)`, `p > 0`, `p ≠ 1` and `g` `1/2`-Hölder with constant `C_y` on
`[-B, A]` and odd about `h` on `(h, B]`,
`|∫_{-B}^{B} Δ_B(p, t) g(t) dt - Δ_{1D}(p) g(0)| ≤ 2 C_y cost_B(A, p) + 2 C_y low_B(A, p)
  + C_y (2h)^{1/2} ∫_h^B |Δ_B(p, t)| dt`. -/
theorem abs_integral_localShearDifference_sub_mul_le (hB : 2 ≤ B) {h p : ℝ} (hh : 0 < h)
    (hp : 0 < p) (hp1 : p ≠ 1) {g : ℝ → ℝ} {Cy : ℝ≥0}
    (hgy : HolderOnWith Cy (1 / 2) g (Icc (-B) (min h B)))
    (hodd : ∀ t ∈ Ioc h B, g t = -g (2 * h - t)) :
    ENNReal.ofReal |(∫ t in Icc (-B) B, localShearDifference B p t * g t) -
        shearMass B (min h B) p * g 0| ≤
      2 * Cy * shearCost B (min h B) p + 2 * Cy * shearLowCost B (min h B) p +
      Cy * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
        ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ := by
  have hB0 : 0 < B := by linarith
  rw [← integral_Icc_localShearDifference (by linarith) (sub_ne_zero.2 hp1)
    (le_min hh.le hB0.le)]
  rcases le_or_gt p (B + 1) with hpB | hpB
  · obtain ⟨hk, heven, Ψ, hΨ, hneg, hpos, hTm, hT0, hTc, hTanti, hmass⟩ :=
      localShearDifference_transport hB hp hp1 hpB
    exact abs_integral_sub_mul_le_of_hasDerivAt hB0 hh hk heven hΨ hneg hpos hTm hT0 hTc hTanti
      hmass hgy hodd
  · simp only [localShearDifference_of_gt hpB, zero_mul, integral_zero, sub_zero, abs_zero,
      ENNReal.ofReal_zero]
    exact zero_le

/-! ### The constants of the horizontal estimate of `u_y` -/

/-- `S̃_{1D}(B, A) = ∫_0^∞ (2p)^{1/2} |Δ_{1D}(p)| dp` of Chen and Hou, Part I, (B.40). -/
def shearMassCost (B A : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi 0, ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)

/-- `S_up(B, A) = 4 ∫_0^∞ ∫_0^A 1{t ≥ s_c(p)} |Δ_B(p, t)| |t - T(p, t)|^{1/2} dt dp` of Chen and
Hou, Part I, (B.40). -/
def shearUpperCost (B A : ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ p in Ioi 0, shearCost B A p

/-- `S_out(B, h) = 1{h < B} (2h)^{1/2} ∫_ℝ ∫_h^B |Δ_B(p, t)| dt dp` of Chen and Hou, Part I,
(B.39), written over `p > 0` with the factor `2` (`Δ_B` is odd in `p`); it vanishes for `h ≥ B`. -/
def shearOuterCost (B h : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal ((2 * h) ^ (1 / 2 : ℝ)) *
    ∫⁻ p in Ioi 0, ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ

/-- `Δ_B` is jointly measurable. -/
theorem measurable_localShearDifference (B : ℝ) :
    Measurable fun q : ℝ × ℝ ↦ localShearDifference B q.1 q.2 := by
  have hd : ∀ c : ℝ, Measurable fun q : ℝ × ℝ ↦ shearDensity (q.1 + c) q.2 := fun c ↦ by
    simp only [shearDensity_eq]
    fun_prop
  have hs : ∀ c : ℝ, MeasurableSet {q : ℝ × ℝ | |q.1 + c| ≤ B} := fun c ↦
    measurableSet_le (by fun_prop) measurable_const
  unfold localShearDifference
  refine Measurable.sub (Measurable.ite (hs 1) (hd 1) measurable_const) ?_
  have e : ∀ q : ℝ × ℝ, q.1 - 1 = q.1 + -1 := fun q ↦ by ring
  simp only [e]
  exact Measurable.ite (hs (-1)) (hd (-1)) measurable_const

/-- The column mass is measurable. -/
theorem measurable_shearMass (B A : ℝ) : Measurable (shearMass B A) := by
  have hs : ∀ c : ℝ, MeasurableSet {p : ℝ | |p + c| ≤ B} := fun c ↦
    measurableSet_le (by fun_prop) measurable_const
  unfold shearMass
  refine Measurable.sub (Measurable.ite (hs 1) (by fun_prop) measurable_const) ?_
  have e : ∀ p : ℝ, p - 1 = p + -1 := fun p ↦ by ring
  simp only [e]
  exact Measurable.ite (hs (-1)) (by fun_prop) measurable_const

/-- The outer column integral `p ↦ ∫_h^B |Δ_B(p, t)| dt` is measurable. -/
theorem measurable_lintegral_localShearDifference (B h : ℝ) :
    Measurable fun p ↦ ∫⁻ t in Ioc h B, ‖localShearDifference B p t‖ₑ :=
  (measurable_localShearDifference B).enorm.lintegral_prod_right'

/-- The column mass vanishes for `|p| > B + 1`. -/
theorem shearMass_of_lt {A p : ℝ} (hp : B + 1 < |p|) : shearMass B A p = 0 := by
  have h₁ : ¬|p + 1| ≤ B := fun h ↦ by
    have := abs_sub_abs_le_abs_sub p (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add] at this
    linarith
  have h₂ : ¬|p - 1| ≤ B := fun h ↦ by
    have := abs_sub_abs_le_abs_sub p 1
    rw [abs_one] at this
    linarith
  simp only [shearMass, h₁, h₂, ite_false, sub_zero]

/-- The column mass is bounded by `2/A` for `A > 0`. -/
theorem abs_shearMass_le {A : ℝ} (hA : 0 < A) (p : ℝ) : |shearMass B A p| ≤ 2 / A := by
  have hq : ∀ q : ℝ, 0 ≤ A / (q ^ 2 + A ^ 2) ∧ A / (q ^ 2 + A ^ 2) ≤ 1 / A := fun q ↦ by
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ (by positivity) hA]
    nlinarith [sq_nonneg q]
  have hite : ∀ q : ℝ, ∀ P : Prop, [Decidable P] →
      0 ≤ (if P then A / (q ^ 2 + A ^ 2) else 0) ∧
        (if P then A / (q ^ 2 + A ^ 2) else 0) ≤ 1 / A := fun q P _ ↦ by
    split_ifs
    · exact hq q
    · exact ⟨le_rfl, by positivity⟩
  obtain ⟨a₁, a₂⟩ := hite (p + 1) (|p + 1| ≤ B)
  obtain ⟨b₁, b₂⟩ := hite (p - 1) (|p - 1| ≤ B)
  have e : 2 / A = 1 / A + 1 / A := by ring
  rw [shearMass, abs_le, e]
  constructor <;> linarith

/-- A function continuous on `[-(B + 1), B + 1]` times the column mass is integrable on bounded
measurable sets: the mass vanishes outside. -/
theorem integrableOn_shearMass_mul {A : ℝ} (hA : 0 < A) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Icc (-(B + 1)) (B + 1))) {S : Set ℝ} (hSb : volume S ≠ ⊤) :
    IntegrableOn (fun p ↦ shearMass B A p * φ p) S := by
  set I := Icc (-(B + 1)) (B + 1) with hI
  have heq : (fun p ↦ shearMass B A p * φ p) = fun p ↦ shearMass B A p * I.indicator φ p := by
    ext p
    by_cases hp : p ∈ I
    · rw [indicator_of_mem hp]
    · rw [indicator_of_notMem hp, shearMass_of_lt, zero_mul, zero_mul]
      by_contra h
      exact hp (abs_le.1 (not_lt.1 h))
  rw [heq]
  by_cases hI0 : I.Nonempty
  · obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
    refine Measure.integrableOn_of_bounded (M := 2 / A * K) hSb
      ((measurable_shearMass B A).aestronglyMeasurable.mul
        ((aestronglyMeasurable_indicator_iff measurableSet_Icc).2
          (hφ.aestronglyMeasurable measurableSet_Icc))) (ae_of_all _ fun p ↦ ?_)
    rw [norm_mul]
    refine mul_le_mul (abs_shearMass_le hA p) ?_ (norm_nonneg _) (by positivity)
    by_cases hp : p ∈ I
    · rw [indicator_of_mem hp]
      exact hK p hp
    · rw [indicator_of_notMem hp, norm_zero]
      exact (norm_nonneg _).trans (hK _ hI0.some_mem)
  · have : I.indicator φ = 0 := by
      ext p
      exact indicator_of_notMem (fun hp ↦ hI0 ⟨p, hp⟩) _
    rw [this]
    simp

/-- The residual line cost `S_{1D}(B, A)` of Chen and Hou, Part I, (B.39):
`2 ∫_{1/9}^{9} |Δ_{1D}| |p - 1|^{1/2} + ∫_0^{1/9} |Δ_{1D}| (2p)^{1/2} + √2 |π + P(1/9)|`, with
`P(1/9) = ∫_{1/9}^9 Δ_{1D}`. The absolute value in the last term makes the bound independent of
the sign of `π + P(1/9)`. -/
def shearLineCost (B A : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (|shearMass B A p| * |p - 1| ^ (1 / 2 : ℝ))) +
    (∫⁻ p in Ioc 0 (1 / 9), ENNReal.ofReal (|shearMass B A p| * (2 * p) ^ (1 / 2 : ℝ))) +
    ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, shearMass B A p|)

/-- **The horizontal transport of the residual column masses** (Chen and Hou, Part I,
(B.27)-(B.29)): for `B ≥ 4`, `A > 0` and `u` `1/2`-Hölder with constant `C` on `[-(B + 1), B + 1]`,
`|∫_0^9 Δ_{1D}(p) (u(p) - u(-p)) dp + π (u(1) - u(-1))| ≤ C S_{1D}(B, A)`: the masses on
`[1/9, 9]` are moved to `±1`, those on `[0, 1/9]` across to `-p`. -/
theorem abs_integral_shearMass_mul_add_le (hB : 4 ≤ B) {A : ℝ} (hA : 0 < A) {u : ℝ → ℝ}
    {C : ℝ≥0} (hu : ∀ p ∈ Icc (-(B + 1)) (B + 1), ∀ q ∈ Icc (-(B + 1)) (B + 1),
      |u p - u q| ≤ C * |p - q| ^ (1 / 2 : ℝ)) :
    ENNReal.ofReal |(∫ p in Ioc 0 9, shearMass B A p * (u p - u (-p))) +
        Real.pi * (u 1 - u (-1))| ≤ C * shearLineCost B A := by
  set M := shearMass B A with hM
  set I := Icc (-(B + 1)) (B + 1) with hI
  have huc : ContinuousOn u I := by
    refine HolderOnWith.continuousOn (C := C) (r := 1 / 2) (fun p hp q hq ↦ ?_) (by norm_num)
    rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
      ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.dist_eq] using hu p hp q hq)
  have hnegI : ∀ p ∈ I, -p ∈ I := fun p hp ↦ ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have h1I : (1 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hm1I : (-1 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  -- the three integrands
  set G : ℝ → ℝ := fun p ↦ u p - u (-p) with hG
  set D : ℝ → ℝ := fun p ↦ (u p - u 1) - (u (-p) - u (-1)) with hD
  have hGc : ContinuousOn G I :=
    huc.sub (huc.comp continuous_neg.continuousOn fun p hp ↦ hnegI p hp)
  have hDc : ContinuousOn D I :=
    ((huc.sub continuousOn_const).sub ((huc.comp continuous_neg.continuousOn
      fun p hp ↦ hnegI p hp).sub continuousOn_const))
  have hi₁ : IntegrableOn (fun p ↦ M p * G p) (Ioc 0 9) :=
    integrableOn_shearMass_mul hA hGc (by simp)
  have hi₂ : IntegrableOn (fun p ↦ M p * D p) (Ioc (1 / 9) 9) :=
    integrableOn_shearMass_mul hA hDc (by simp)
  have hi₃ : IntegrableOn M (Ioc (1 / 9) 9) := by
    simpa using integrableOn_shearMass_mul (B := B) hA (φ := fun _ ↦ 1) continuousOn_const
      (show volume (Ioc (1 / 9 : ℝ) 9) ≠ ⊤ by simp)
  -- the decomposition
  have hsplit : ∫ p in Ioc 0 9, M p * G p =
      (∫ p in Ioc 0 (1 / 9), M p * G p) + (∫ p in Ioc (1 / 9) 9, M p * D p) +
        (∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1)) := by
    rw [← Ioc_union_Ioc_eq_Ioc (by norm_num : (0 : ℝ) ≤ 1 / 9) (by norm_num : (1 / 9 : ℝ) ≤ 9),
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (hi₁.mono_set (Ioc_subset_Ioc le_rfl (by norm_num)))
        (hi₁.mono_set (Ioc_subset_Ioc (by norm_num) le_rfl))]
    have e : ∫ p in Ioc (1 / 9) 9, M p * G p =
        (∫ p in Ioc (1 / 9) 9, M p * D p) + (∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1)) := by
      rw [← integral_mul_const, ← integral_add hi₂ (hi₃.mul_const _)]
      congr 1
      ext p
      simp only [hG, hD]
      ring
    rw [e, add_assoc]
  rw [hsplit]
  -- the bounds
  have b₁ : ENNReal.ofReal |∫ p in Ioc 0 (1 / 9), M p * G p| ≤
      C * ∫⁻ p in Ioc 0 (1 / 9), ENNReal.ofReal (|M p| * (2 * p) ^ (1 / 2 : ℝ)) := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
    have hpI : p ∈ I := ⟨by linarith [hp.1], by linarith [hp.2]⟩
    have h := hu p hpI (-p) (hnegI p hpI)
    rw [show p - -p = 2 * p by ring, abs_of_pos (by linarith [hp.1] : (0 : ℝ) < 2 * p)] at h
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul
      (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (by ring)
  have b₂ : ENNReal.ofReal |∫ p in Ioc (1 / 9) 9, M p * D p| ≤
      C * (2 * ∫⁻ p in Ioc (1 / 9) 9, ENNReal.ofReal (|M p| * |p - 1| ^ (1 / 2 : ℝ))) := by
    rw [← Real.enorm_eq_ofReal_abs]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← mul_assoc, ← lintegral_const_mul' _ _ (by finiteness)]
    refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
    rw [Real.enorm_eq_ofReal_abs, show (C : ℝ≥0∞) * 2 = ENNReal.ofReal (2 * C) by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal,
        mul_comm], ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul]
    by_cases hpB : p ≤ B + 1
    · have hpI : p ∈ I := ⟨by linarith [hp.1], hpB⟩
      have h₁ := hu p hpI 1 h1I
      have h₂ := hu (-p) (hnegI p hpI) (-1) hm1I
      rw [show -p - -1 = -(p - 1) by ring, abs_neg] at h₂
      have hDb : |D p| ≤ 2 * C * |p - 1| ^ (1 / 2 : ℝ) := (abs_sub _ _).trans (by linarith)
      exact (mul_le_mul_of_nonneg_left hDb (abs_nonneg _)).trans_eq (by ring)
    · rw [hM, shearMass_of_lt (by rw [abs_of_pos (by linarith [hp.1])]; linarith), abs_zero,
        zero_mul]
      positivity
  have b₃ : ENNReal.ofReal |(Real.pi + ∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1))| ≤
      C * ENNReal.ofReal (Real.sqrt 2 * |Real.pi + ∫ p in Ioc (1 / 9) 9, M p|) := by
    have h := hu 1 h1I (-1) hm1I
    rw [show (1 : ℝ) - -1 = 2 by ring, abs_two, ← Real.sqrt_eq_rpow] at h
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (by ring)
  have e : (∫ p in Ioc 0 (1 / 9), M p * G p) + (∫ p in Ioc (1 / 9) 9, M p * D p) +
      (∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1)) + Real.pi * (u 1 - u (-1)) =
      (∫ p in Ioc 0 (1 / 9), M p * G p) + (∫ p in Ioc (1 / 9) 9, M p * D p) +
        (Real.pi + ∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1)) := by ring
  rw [e]
  calc _ ≤ ENNReal.ofReal |∫ p in Ioc 0 (1 / 9), M p * G p| +
        ENNReal.ofReal |∫ p in Ioc (1 / 9) 9, M p * D p| +
        ENNReal.ofReal |(Real.pi + ∫ p in Ioc (1 / 9) 9, M p) * (u 1 - u (-1))| :=
      (ofReal_abs_add_le _ _).trans (add_le_add (ofReal_abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add b₁ b₂) b₃
    _ = C * shearLineCost B A := by
      simp only [shearLineCost, hM]
      ring

/-- `S_low(B, A) = 4 ∫_0^9 ∫_0^{min(T(p, A), A)} |Δ_B(p, t)| t^{1/2} dt dp` of Chen and Hou,
Part I, (B.39) (the second part of `S_{in,y}`). -/
def shearLowerCost (B A : ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ p in Ioc 0 9, shearLowCost B A p

/-- `S_{in,x}(B, A) = ∫_9^∞ (2p)^{1/2} |Δ_{1D}(p)| dp` of Chen and Hou, Part I, (B.39). -/
def shearInnerMassCost (B A : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ioi 9, ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ) * |shearMass B A p|)

/-- The localized threshold is measurable. -/
theorem measurable_localShearThreshold (B : ℝ) : Measurable (localShearThreshold B) := by
  unfold localShearThreshold shearThreshold
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop)
    (by fun_prop)

/-- The localized map at a fixed height is measurable in the column. -/
theorem measurable_localShearMap_left (B A : ℝ) : Measurable fun p ↦ localShearMap B p A := by
  have h₁ : Measurable fun p : ℝ ↦ shearMap p A := by
    have := measurable_shearMap.comp (measurable_id.prodMk (measurable_const (a := A)))
    simpa only [Function.comp_def, id] using this
  have h₂ : Measurable fun p : ℝ ↦ (|p| - 1) ^ 2 / A := by fun_prop
  unfold localShearMap
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) h₁ h₂

/-- The low cost is measurable in the column. -/
theorem measurable_shearLowCost (B A : ℝ) : Measurable (shearLowCost B A) := by
  set e : ℝ → ℝ := fun p ↦ if localShearThreshold B p < A then localShearMap B p A else A
  have he : Measurable e := Measurable.ite
    (measurableSet_lt (measurable_localShearThreshold B) measurable_const)
    (measurable_localShearMap_left B A) measurable_const
  set S : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ e q.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (he.comp measurable_fst))
  have hF : Measurable fun q : ℝ × ℝ ↦
      ‖localShearDifference B q.1 q.2‖ₑ * ENNReal.ofReal (q.2 ^ (1 / 2 : ℝ)) :=
    (measurable_localShearDifference B).enorm.mul (measurable_snd.pow_const _).ennreal_ofReal
  have heq : shearLowCost B A = fun p ↦ ∫⁻ t, S.indicator (fun q : ℝ × ℝ ↦
      ‖localShearDifference B q.1 q.2‖ₑ * ENNReal.ofReal (q.2 ^ (1 / 2 : ℝ))) (p, t) := by
    ext p
    rw [shearLowCost, ← lintegral_indicator measurableSet_Ioc]
    refine lintegral_congr fun t ↦ ?_
    by_cases ht : t ∈ Ioc 0 (e p)
    · rw [indicator_of_mem ht, indicator_of_mem (show (p, t) ∈ S from ht)]
    · rw [indicator_of_notMem ht, indicator_of_notMem (show (p, t) ∉ S from ht)]
  rw [heq]
  exact (hF.indicator hS).lintegral_prod_right'

end IncompressibleFlow.SharpHolder
