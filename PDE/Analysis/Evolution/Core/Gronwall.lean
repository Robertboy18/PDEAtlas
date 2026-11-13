/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.DerivativeTest
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Grönwall estimates and uniqueness for evolution equations

Integral and differential Grönwall inequalities for a real energy `e(t)` on
`[a, b]`. The integral forms follow from Mathlib's differential Grönwall theorem
(`le_gronwallBound_of_liminf_deriv_right_le`) applied to the primitive
`F(t) = ∫_a^t e`. An absolutely continuous energy with `e' ≤ K e + g` almost
everywhere, `K ≥ 0` and `g ≥ 0`, satisfies `e(t) ≤ (e(a) + ∫ₐᵇ g) e^{K(t-a)}`.
A term `D (t - a) e(t)` on the right of an integral inequality is absorbed when
`D (b - a) < 1`.

For `e' + α e ≤ β` with `α > 0`, the energy obeys
`e(t) ≤ e(a) e^{-α(t-a)} + (β/α)(1 - e^{-α(t-a)})`, so every sublevel `{e ≤ R}`
with `β ≤ α R` is invariant. A continuous `e` with `e(a) < R` and `e' < 0`
wherever `e = R` stays below `R`.

## Main results

* `eq_zero_on_of_nonneg_le_mul_intervalIntegral`: `e ≤ K ∫_a^t e` with
  `e ≥ 0` forces `e = 0` (the uniqueness form).
* `eq_zero_on_of_eq_intervalIntegral_of_norm_le` and
  `eq_on_of_eq_const_add_intervalIntegral_of_norm_sub_le`: uniqueness for
  Banach-space integral evolutions, with continuity supplied by their integral identities.
* `le_mul_exp_of_le_const_add_mul_intervalIntegral`: `e ≤ δ + K ∫_a^t e`
  gives `e(t) ≤ δ e^{K(t-a)}` (the continuous-dependence form).
* `le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le`: absolute continuity and
  an almost-everywhere bound `e' ≤ K e + g`, with `K, g ≥ 0`, give
  `e(t) ≤ (e(a) + ∫ₐᵇ g) exp (K (t-a))`.
* `eq_zero_on_of_le_integral_add_length_mul_self`: small-time absorption of
  a `D (t - a) e(t)` term.
* `le_gronwallBound_of_hasDerivWithinAt_le`, `dissipative_energy_bound`,
  `dissipative_energy_sublevel_invariant`: differential forms and the
  dissipative sublevel principle.
* `strict_sublevel_invariant_of_deriv_neg_on_boundary`: a continuous `e`
  with `e(a) < R` and `e' < 0` wherever `e = R` stays below `R`.
* `backward_energy_estimate_to_gronwall`: the real-number rearrangement used
  by the backward wave-energy uniqueness argument.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix B.2(j) and (k) (Grönwall's inequality in
  differential and integral form), and §7.2.2, Theorem 4 (uniqueness of weak solutions of
  second-order hyperbolic equations). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Filter

/-- Integral Grönwall lemma in the zero-data form.

Let `e` be a continuous nonnegative function on `[a,b]`. If

`e(t) ≤ K ∫ₐᵗ e(s) ds`

for every `t ∈ [a,b]`, then `e` vanishes identically. The proof applies
Mathlib's differential Grönwall theorem to the primitive
`F(t) = ∫ₐᵗ e(s) ds`.
-/
theorem eq_zero_on_of_nonneg_le_mul_intervalIntegral
    {e : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b)
    (heContinuous : ContinuousOn e (Set.Icc a b))
    (heNonneg : ∀ t ∈ Set.Icc a b, 0 ≤ e t)
    (heIntegral : ∀ t ∈ Set.Icc a b,
      e t ≤ K * ∫ s in a..t, e s) :
    ∀ t ∈ Set.Icc a b, e t = 0 := by
  let F : ℝ → ℝ := fun t ↦ ∫ s in a..t, e s
  have heIntervalIntegrable : IntervalIntegrable e volume a b :=
    heContinuous.intervalIntegrable_of_Icc hab
  have hFContinuous : ContinuousOn F (Set.Icc a b) := by
    simpa [F, Set.uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval'
        heIntervalIntegrable Set.left_mem_uIcc)
  have hFDeriv (t : ℝ) (ht : t ∈ Set.Ico a b) :
      HasDerivWithinAt F (e t) (Set.Ici t) t := by
    have htIcc : t ∈ Set.Icc a b := Set.Ico_subset_Icc_self ht
    let : Fact (t ∈ Set.Icc a b) := ⟨htIcc⟩
    have heIntegrableToT : IntervalIntegrable e volume a t :=
      (heContinuous.mono (Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1
    have hWithin :
        HasDerivWithinAt F (e t) (Set.Icc a b) t := by
      simpa [F] using
        (intervalIntegral.integral_hasDerivWithinAt_right
          heIntegrableToT
          (heContinuous.stronglyMeasurableAtFilter_nhdsWithin
            measurableSet_Icc t)
          (heContinuous t htIcc))
    exact hWithin.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  have hFUpper : ∀ t ∈ Set.Icc a b, F t ≤ 0 := by
    have hgronwall :=
      le_gronwallBound_of_liminf_deriv_right_le
        (f := F) (f' := e) (δ := 0) (K := K) (ε := 0)
        (a := a) (b := b)
        hFContinuous
        (fun t ht _r hr ↦ (hFDeriv t ht).liminf_right_slope_le hr)
        (show F a ≤ 0 by simp [F])
        (fun t ht ↦ by
          simpa [F] using heIntegral t (Set.Ico_subset_Icc_self ht))
    intro t ht
    simpa [gronwallBound_ε0_δ0] using hgronwall t ht
  have hFNonneg : ∀ t ∈ Set.Icc a b, 0 ≤ F t := by
    intro t ht
    exact intervalIntegral.integral_nonneg ht.1 fun s hs ↦
      heNonneg s ⟨hs.1, hs.2.trans ht.2⟩
  intro t ht
  have hFZero : F t = 0 := le_antisymm (hFUpper t ht) (hFNonneg t ht)
  apply le_antisymm
  · simpa [F, hFZero] using heIntegral t ht
  · exact heNonneg t ht

/-- An integrable homogeneous evolution with zero initial value vanishes if its
rate is bounded by a constant times its norm. Continuity of the trajectory
follows from the integral identity; it need not be assumed separately. -/
theorem eq_zero_on_of_eq_intervalIntegral_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u h : ℝ → E} {a b K : ℝ} (hab : a ≤ b)
    (hh : IntervalIntegrable h volume a b)
    (hu : ∀ t ∈ Icc a b, u t = ∫ s in a..t, h s)
    (hbound : ∀ t ∈ Icc a b, ‖h t‖ ≤ K * ‖u t‖) :
    ∀ t ∈ Icc a b, u t = 0 := by
  have hprimitive : ContinuousOn (fun t ↦ ∫ s in a..t, h s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hh left_mem_uIcc
  have hcont : ContinuousOn u (Icc a b) :=
    hprimitive.congr fun t ht ↦ hu t ht
  have hinequality (t : ℝ) (ht : t ∈ Icc a b) :
      ‖u t‖ ≤ K * ∫ s in a..t, ‖u s‖ := by
    have hht : IntervalIntegrable h volume a t :=
      hh.mono_set (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
    rw [hu t ht]
    calc
      _ ≤ ∫ s in a..t, ‖h s‖ :=
        intervalIntegral.norm_integral_le_integral_norm ht.1
      _ ≤ ∫ s in a..t, K * ‖u s‖ :=
        intervalIntegral.integral_mono_on ht.1 hht.norm
          ((hcont.norm.const_mul K).mono (Icc_subset_Icc_right ht.2)
            |>.intervalIntegrable_of_Icc ht.1)
          (fun s hs ↦ hbound s ⟨hs.1, hs.2.trans ht.2⟩)
      _ = _ := intervalIntegral.integral_const_mul K (fun s ↦ ‖u s‖)
  have hzero := eq_zero_on_of_nonneg_le_mul_intervalIntegral hab hcont.norm
    (fun _ _ ↦ norm_nonneg _) hinequality
  exact fun t ht ↦ norm_eq_zero.mp (hzero t ht)

/-- Two integral evolutions with the same initial value agree when the difference
of their rates is bounded by a constant times the difference of their states. -/
theorem eq_on_of_eq_const_add_intervalIntegral_of_norm_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v f g : ℝ → E} {a b K : ℝ} {u₀ : E} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hu : ∀ t ∈ Icc a b, u t = u₀ + ∫ s in a..t, f s)
    (hv : ∀ t ∈ Icc a b, v t = u₀ + ∫ s in a..t, g s)
    (hbound : ∀ t ∈ Icc a b, ‖f t - g t‖ ≤ K * ‖u t - v t‖) :
    ∀ t ∈ Icc a b, u t = v t := by
  have hzero := eq_zero_on_of_eq_intervalIntegral_of_norm_le hab (hf.sub hg)
    (u := fun t ↦ u t - v t) (K := K) (fun t ht ↦ by
      have hft : IntervalIntegrable f volume a t :=
        hf.mono_set (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
      have hgt : IntervalIntegrable g volume a t :=
        hg.mono_set (uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht))
      rw [hu t ht, hv t ht, intervalIntegral.integral_sub hft hgt]
      abel) hbound
  exact fun t ht ↦ sub_eq_zero.mp (hzero t ht)

/--
Small-time absorption followed by integral Grönwall.

Suppose a continuous nonnegative energy satisfies

`e(t) ≤ C ∫ₐᵗ e(r) dr + D (t-a) e(t)`.

If `D ≥ 0` and `D (b-a) < 1`, the final term can be absorbed uniformly on
`[a,b]`, reducing the estimate to the zero-data Grönwall lemma.
-/
theorem eq_zero_on_of_le_integral_add_length_mul_self
    {e : ℝ → ℝ} {a b C D : ℝ}
    (hab : a ≤ b)
    (heContinuous : ContinuousOn e (Set.Icc a b))
    (heNonneg : ∀ t ∈ Set.Icc a b, 0 ≤ e t)
    (hD : 0 ≤ D)
    (hshort : D * (b - a) < 1)
    (heIntegral : ∀ t ∈ Set.Icc a b,
      e t ≤ C * (∫ r in a..t, e r) + D * (t - a) * e t) :
    ∀ t ∈ Set.Icc a b, e t = 0 := by
  have hdenominator : 0 < 1 - D * (b - a) := sub_pos.mpr hshort
  apply eq_zero_on_of_nonneg_le_mul_intervalIntegral
    (K := C / (1 - D * (b - a)))
    hab heContinuous heNonneg
  intro t ht
  have htime : t - a ≤ b - a := sub_le_sub_right ht.2 a
  have habsorb :
      D * (t - a) * e t ≤ D * (b - a) * e t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htime hD) (heNonneg t ht)
  have hbase := heIntegral t ht
  have hrearranged :
      (1 - D * (b - a)) * e t ≤
        C * (∫ r in a..t, e r) := by
    linarith
  calc
    e t ≤
        (C * (∫ r in a..t, e r)) /
          (1 - D * (b - a)) :=
      (le_div_iff₀ hdenominator).2 (by
        simpa only [mul_comm] using hrearranged)
    _ =
        (C / (1 - D * (b - a))) *
          ∫ r in a..t, e r := by ring

/--
Real-number rearrangement of the backward energy estimate in the uniqueness
proof for second-order hyperbolic equations (Evans, §7.2.2, Theorem 4) into the form
of `eq_zero_on_of_le_integral_add_length_mul_self`.

`U` is the squared endpoint kinetic norm, `W` the squared forward-primitive
norm, and `V` the integrated squared backward primitive. `Iu`, `Iw` and `Ie`
are time integrals, `length` is the elapsed time, and `e = U + c W`,
`Ie = Iu + c Iw`. The wave equation enters only through `hestimate` and
`hbackward`.
-/
theorem backward_energy_estimate_to_gronwall
    {U W V Iu Iw Ie e length c LA LR : ℝ}
    (hc : 0 < c) (hLA : 0 ≤ LA) (hLR : 0 ≤ LR)
    (hU : 0 ≤ U)
    (hIu : 0 ≤ Iu) (hIw : 0 ≤ Iw) (hlength : 0 ≤ length)
    (hestimate :
      (1 / 2 : ℝ) * U + (1 / 2 : ℝ) * c * W ≤
        (1 / 2 : ℝ) * LA * V +
          (1 / 2 : ℝ) * LR * (Iu + V))
    (hbackward : V ≤ 2 * length * W + 2 * Iw)
    (hendpoint : e = U + c * W)
    (hintegral : Ie = Iu + c * Iw) :
    e ≤
      (2 * (LA + LR) / c + LR) * Ie +
        (2 * (LA + LR) / c) * length * e := by
  have hsum : 0 ≤ LA + LR := add_nonneg hLA hLR
  have hendpointPrimitive : W ≤ e / c := by
    apply (le_div_iff₀ hc).2
    rw [hendpoint]
    nlinarith
  have hintegratedPrimitive : Iw ≤ Ie / c := by
    apply (le_div_iff₀ hc).2
    rw [hintegral]
    nlinarith
  have hintegratedKinetic : Iu ≤ Ie := by
    rw [hintegral]
    exact le_add_of_nonneg_right (mul_nonneg hc.le hIw)
  have hbase :
      e ≤
        2 * (LA + LR) * length * W +
          2 * (LA + LR) * Iw + LR * Iu := by
    rw [hendpoint]
    nlinarith
  have hendpointTerm :
      2 * (LA + LR) * length * W ≤
        (2 * (LA + LR) / c) * length * e := by
    calc
      2 * (LA + LR) * length * W ≤
          2 * (LA + LR) * length * (e / c) :=
        mul_le_mul_of_nonneg_left hendpointPrimitive
          (mul_nonneg (mul_nonneg (by positivity) hsum) hlength)
      _ = (2 * (LA + LR) / c) * length * e := by ring
  have hintegratedPrimitiveTerm :
      2 * (LA + LR) * Iw ≤
        (2 * (LA + LR) / c) * Ie := by
    calc
      2 * (LA + LR) * Iw ≤
          2 * (LA + LR) * (Ie / c) :=
        mul_le_mul_of_nonneg_left hintegratedPrimitive
          (mul_nonneg (by positivity) hsum)
      _ = (2 * (LA + LR) / c) * Ie := by ring
  have hintegratedKineticTerm : LR * Iu ≤ LR * Ie :=
    mul_le_mul_of_nonneg_left hintegratedKinetic hLR
  linarith

/-- Integral Grönwall inequality in the inhomogeneous form used for
continuous dependence.

If a continuous scalar function satisfies

`e(t) ≤ δ + K ∫ₐᵗ e(s) ds`

on `[a,b]`, with `K ≥ 0`, then

`e(t) ≤ δ exp (K (t-a))`.

The proof applies differential Grönwall to the primitive majorant
`F(t) = δ + K ∫ₐᵗ e(s) ds`.
-/
theorem le_mul_exp_of_le_const_add_mul_intervalIntegral
    {e : ℝ → ℝ} {a b δ K : ℝ}
    (heContinuous : ContinuousOn e (Set.Icc a b))
    (hK : 0 ≤ K)
    (heIntegral : ∀ t ∈ Set.Icc a b,
      e t ≤ δ + K * ∫ s in a..t, e s) :
    ∀ t ∈ Set.Icc a b, e t ≤ δ * Real.exp (K * (t - a)) := by
  by_cases hab : a ≤ b
  swap
  · exact fun t ht ↦ absurd (ht.1.trans ht.2) hab
  let F : ℝ → ℝ := fun t ↦ δ + K * ∫ s in a..t, e s
  have heIntervalIntegrable : IntervalIntegrable e volume a b :=
    heContinuous.intervalIntegrable_of_Icc hab
  have hPrimitiveContinuous :
      ContinuousOn (fun t ↦ ∫ s in a..t, e s) (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using
      (intervalIntegral.continuousOn_primitive_interval'
        heIntervalIntegrable Set.left_mem_uIcc)
  have hFContinuous : ContinuousOn F (Set.Icc a b) := by
    have hfun :
        F = (fun _ : ℝ ↦ δ) +
          fun t ↦ K * ∫ s in a..t, e s := by
      funext t
      rfl
    rw [hfun]
    exact continuousOn_const.add (hPrimitiveContinuous.const_mul K)
  have hFDeriv (t : ℝ) (ht : t ∈ Set.Ico a b) :
      HasDerivWithinAt F (K * e t) (Set.Ici t) t := by
    have htIcc : t ∈ Set.Icc a b := Set.Ico_subset_Icc_self ht
    let : Fact (t ∈ Set.Icc a b) := ⟨htIcc⟩
    have heIntegrableToT : IntervalIntegrable e volume a t :=
      (heContinuous.mono
        (Set.Icc_subset_Icc_right ht.2.le)).intervalIntegrable_of_Icc ht.1
    have hWithin :
        HasDerivWithinAt (fun x ↦ ∫ s in a..x, e s) (e t)
          (Set.Icc a b) t :=
      intervalIntegral.integral_hasDerivWithinAt_right
        heIntegrableToT
        (heContinuous.stronglyMeasurableAtFilter_nhdsWithin
          measurableSet_Icc t)
        (heContinuous t htIcc)
    have hRight := hWithin.mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
    simpa [F] using (hRight.const_mul K).const_add δ
  have hFBound : ∀ t ∈ Set.Icc a b,
      F t ≤ gronwallBound δ K 0 (t - a) := by
    apply le_gronwallBound_of_liminf_deriv_right_le
      (f := F) (f' := fun t ↦ K * e t)
      hFContinuous
    · intro t ht r hr
      exact (hFDeriv t ht).liminf_right_slope_le hr
    · simp [F]
    · intro t ht
      have hscaled :=
        mul_le_mul_of_nonneg_left
          (heIntegral t (Set.Ico_subset_Icc_self ht)) hK
      simpa [F] using hscaled
  intro t ht
  calc
    e t ≤ F t := by simpa [F] using heIntegral t ht
    _ ≤ gronwallBound δ K 0 (t - a) := hFBound t ht
    _ = δ * Real.exp (K * (t - a)) := gronwallBound_ε0 δ K (t - a)

/-- An absolutely continuous scalar energy with an almost-everywhere differential
inequality has an exponential bound controlled by the full integrable source.
Nonnegativity of the source allows every prefix integral to use the same budget. -/
theorem le_mul_exp_of_absolutelyContinuousOnInterval_deriv_le
    {e g : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b)
    (he : AbsolutelyContinuousOnInterval e a b)
    (hg : IntervalIntegrable g volume a b)
    (hg_nonneg : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ g t)
    (hK : 0 ≤ K)
    (hderiv : ∀ᵐ t ∂volume.restrict (Ioc a b),
      deriv e t ≤ K * e t + g t) :
    ∀ t ∈ Icc a b,
      e t ≤ (e a + ∫ s in a..b, g s) * Real.exp (K * (t - a)) := by
  have hecont : ContinuousOn e (Icc a b) := by
    simpa only [uIcc_of_le hab] using he.continuousOn
  have hderivIcc : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv e t ≤ K * e t + g t := by
    simpa only [restrict_Ioc_eq_restrict_Icc] using hderiv
  have hintegral : ∀ t ∈ Icc a b,
      e t ≤ (e a + ∫ s in a..b, g s) + K * ∫ s in a..t, e s := by
    intro t ht
    have hsubset : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
    have hinterval : uIcc a t ⊆ uIcc a b :=
      uIcc_subset_uIcc_left (by simpa only [uIcc_of_le hab] using ht)
    have heAt : AbsolutelyContinuousOnInterval e a t := he.mono hinterval
    have heInt : IntervalIntegrable e volume a t :=
      (hecont.mono hsubset).intervalIntegrable_of_Icc ht.1
    have hgAt : IntervalIntegrable g volume a t := hg.mono_set hinterval
    have hderivAt : ∀ᵐ s ∂volume.restrict (Icc a t),
        deriv e s ≤ K * e s + g s :=
      hderivIcc.filter_mono (ae_mono ((volume : Measure ℝ).restrict_mono_set hsubset))
    -- Absolute continuity supplies integrability of the derivative itself.
    have hbound := intervalIntegral.integral_mono_ae_restrict ht.1
      heAt.intervalIntegrable_deriv ((heInt.const_mul K).add hgAt) hderivAt
    rw [heAt.integral_deriv_eq_sub,
      intervalIntegral.integral_add (heInt.const_mul K) hgAt,
      intervalIntegral.integral_const_mul] at hbound
    have hprefix := intervalIntegral.integral_mono_interval
      (le_refl a) ht.1 ht.2 hg_nonneg hg
    linarith
  exact le_mul_exp_of_le_const_add_mul_intervalIntegral hecont hK hintegral

/--
Differential Grönwall bound for a scalar function on a closed interval.

If `e` has derivative `de` on `[a,b]`, starts below `δ`, and satisfies
`de(t) ≤ K e(t) + ε`, then it is bounded by Mathlib's explicit
`gronwallBound`.  The coefficient `K` may have either sign.
-/
theorem le_gronwallBound_of_hasDerivWithinAt_le
    {e de : ℝ → ℝ} {a b δ K ε : ℝ}
    (he : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt e (de t) (Set.Icc a b) t)
    (ha : e a ≤ δ)
    (hbound : ∀ t ∈ Set.Icc a b, de t ≤ K * e t + ε) :
    ∀ t ∈ Set.Icc a b,
      e t ≤ gronwallBound δ K ε (t - a) := by
  have heContinuous : ContinuousOn e (Set.Icc a b) := by
    intro t ht
    exact (he t ht).continuousWithinAt
  have heRight (t : ℝ) (ht : t ∈ Set.Ico a b) :
      HasDerivWithinAt e (de t) (Set.Ici t) t := by
    exact (he t (Set.Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)
  apply le_gronwallBound_of_liminf_deriv_right_le
    (f' := de) heContinuous
  · intro t ht r hr
    exact (heRight t ht).liminf_right_slope_le hr
  · exact ha
  · intro t ht
    exact hbound t (Set.Ico_subset_Icc_self ht)

/--
Explicit bound for a dissipative scalar energy inequality.

The assumption `de(t) + α e(t) ≤ β`, with `α > 0`, yields the convex
combination of the initial energy and the equilibrium level `β / α`.
-/
theorem dissipative_energy_bound
    {e de : ℝ → ℝ} {a b α β : ℝ}
    (hα : 0 < α)
    (he : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt e (de t) (Set.Icc a b) t)
    (hbound : ∀ t ∈ Set.Icc a b, de t + α * e t ≤ β) :
    ∀ t ∈ Set.Icc a b,
      e t ≤
        e a * Real.exp (-α * (t - a)) +
          (β / α) * (1 - Real.exp (-α * (t - a))) := by
  intro t ht
  have hgronwall :=
    le_gronwallBound_of_hasDerivWithinAt_le
      (δ := e a) (K := -α) (ε := β) he le_rfl (by
        intro s hs
        have hsbound := hbound s hs
        linarith) t ht
  calc
    e t ≤ gronwallBound (e a) (-α) β (t - a) := hgronwall
    _ =
        e a * Real.exp (-α * (t - a)) +
          (β / α) * (1 - Real.exp (-α * (t - a))) := by
      rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr hα.ne')]
      cas

/--
A dissipative differential inequality preserves every sublevel above its
equilibrium level.

If `e(a) ≤ R` and `β ≤ α R`, then any trajectory satisfying
`de + α e ≤ β` remains below `R` throughout `[a,b]`.
-/
theorem dissipative_energy_sublevel_invariant
    {e de : ℝ → ℝ} {a b α β R : ℝ}
    (hα : 0 < α)
    (he : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt e (de t) (Set.Icc a b) t)
    (ha : e a ≤ R)
    (hequilibrium : β ≤ α * R)
    (hbound : ∀ t ∈ Set.Icc a b, de t + α * e t ≤ β) :
    ∀ t ∈ Set.Icc a b, e t ≤ R := by
  intro t ht
  have henergy := dissipative_energy_bound hα he hbound t ht
  let q : ℝ := Real.exp (-α * (t - a))
  have hq_nonneg : 0 ≤ q := (Real.exp_pos _).le
  have hq_le_one : q ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simpa only [neg_mul] using
      neg_nonpos.mpr (mul_nonneg hα.le (sub_nonneg.mpr ht.1))
  have hequilibrium' : β / α ≤ R := by
    apply (div_le_iff₀ hα).2
    simpa only [mul_comm] using hequilibrium
  have hinitial : e a * q ≤ R * q :=
    mul_le_mul_of_nonneg_right ha hq_nonneg
  have hsteady : (β / α) * (1 - q) ≤ R * (1 - q) :=
    mul_le_mul_of_nonneg_right hequilibrium' (sub_nonneg.mpr hq_le_one)
  calc
    e t ≤ e a * q + (β / α) * (1 - q) := by
      simpa only [q] using henergy
    _ ≤ R * q + R * (1 - q) := add_le_add hinitial hsteady
    _ = R := by ring

/--
A continuous scalar trajectory cannot cross a strict upper barrier if its
derivative is strictly negative whenever it meets that barrier.

This is the first-contact principle of bootstrap arguments. The condition
`deriv e t < 0` is required only at times where `e t = R`.
-/
theorem strict_sublevel_invariant_of_deriv_neg_on_boundary
    {e : ℝ → ℝ} {a b R : ℝ}
    (he : ContinuousOn e (Set.Icc a b))
    (ha : e a < R)
    (hderiv : ∀ t ∈ Set.Icc a b, e t = R → deriv e t < 0) :
    ∀ t ∈ Set.Icc a b, e t < R := by
  intro t ht
  by_contra hnot
  have hRet : R ≤ e t := le_of_not_gt hnot
  have hcont : ContinuousOn e (Set.Icc a t) :=
    he.mono (Set.Icc_subset_Icc_right ht.2)
  have hhitNonempty :
      (Set.Icc a t ∩ e ⁻¹' {R}).Nonempty := by
    have hRmem : R ∈ Set.Icc (e a) (e t) := ⟨ha.le, hRet⟩
    rcases intermediate_value_Icc ht.1 hcont hRmem with ⟨s, hs, hsE⟩
    exact ⟨s, hs, by simp [hsE]⟩
  have hhitClosed : IsClosed (Set.Icc a t ∩ e ⁻¹' {R}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hhitCompact : IsCompact (Set.Icc a t ∩ e ⁻¹' {R}) :=
    isCompact_Icc.of_isClosed_subset hhitClosed Set.inter_subset_left
  obtain ⟨tau, htauMem, htauLeast⟩ :=
    hhitCompact.exists_isLeast hhitNonempty
  have htauIcc : tau ∈ Set.Icc a b :=
    ⟨htauMem.1.1, htauMem.1.2.trans ht.2⟩
  have htauEq : e tau = R := by simpa using htauMem.2
  have hat : a < tau :=
    lt_of_le_of_ne htauMem.1.1
      (fun h ↦ ha.ne (by simpa [h] using htauEq))
  have hsign : ∀ᶠ x in nhds tau,
      SignType.sign (e x - R) = SignType.sign (tau - x) := by
    simpa using eventually_nhdsWithin_sign_eq_of_deriv_neg
      (f := fun x ↦ e x - R) (x₀ := tau)
      (by simpa only [deriv_sub_const] using hderiv tau htauIcc htauEq)
      (by simp [htauEq])
  obtain ⟨x, hxlt, hxsign, hax⟩ :=
    (hsign.and (Ioi_mem_nhds hat)).exists_lt
  have hRex : R < e x := by
    have hsignOne : SignType.sign (e x - R) = 1 := by
      rw [hxsign, sign_pos (sub_pos.mpr hxlt)]
    exact sub_pos.mp (sign_eq_one_iff.mp hsignOne)
  have hxt : x ≤ t := hxlt.le.trans htauMem.1.2
  have hcontAx : ContinuousOn e (Set.Icc a x) :=
    hcont.mono (Set.Icc_subset_Icc_right hxt)
  have hRmem : R ∈ Set.Icc (e a) (e x) := ⟨ha.le, hRex.le⟩
  rcases intermediate_value_Icc hax.le hcontAx hRmem with ⟨y, hy, hyE⟩
  have hyHit : y ∈ Set.Icc a t ∩ e ⁻¹' {R} :=
    ⟨⟨hy.1, hy.2.trans hxt⟩, by simp [hyE]⟩
  exact (not_lt_of_ge (htauLeast hyHit)) (hy.2.trans_lt hxlt)

end PDE.Analysis.Evolution
