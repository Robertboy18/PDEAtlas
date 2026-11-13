/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Osgood lemma for the modulus `r (1 + log (A / r))`

The modulus `φ_A(r) = r (1 + log (A / r))` is continuous, increasing on `[0, A]`, and satisfies
`∫₀ dr / φ_A(r) = ∞`. A bounded monotone function `w ≥ 0` with
`w(t) ≤ C ∫₀ᵗ φ_A(w(s)) ds` therefore vanishes: its primitive stays below the solutions
`A exp(1 - K e^{-(C + 1) t})` of `y' = (C + 1) φ_A(y)` for every large `K`, and these tend to
zero. Monotonicity makes every integrand interval integrable.

The same estimate for a doubly indexed family, `D(n + 1, m + 1)(t) ≤ C ∫₀ᵗ φ_A(D(n, m)(s)) ds`,
shows that `D(n, m) → 0` uniformly as `n, m → ∞`: the tail suprema
`w_n = sup_{m, m' ≥ n} D(m, m')` decrease to a limit that satisfies the Osgood inequality. This is
how the Picard iterates of an equation whose nonlinearity is only log-Lipschitz form a Cauchy
sequence, without any contraction.

The homogeneous form `B (1 + log (2 + M / B)) ≤ φ_{2A' + M}(B)` for `0 ≤ B ≤ A'` converts
Kato-type bounds into this modulus.

## Main definitions

* `osgoodModulus`: the modulus `φ_A(r) = r (1 + log (A / r))`.

## Main results

* `monotoneOn_osgoodModulus`: `φ_A` is increasing on `[0, A]`.
* `mul_one_add_log_le_osgoodModulus`: `B (1 + log (2 + M / B)) ≤ φ_{2A' + M}(B)` for
  `0 ≤ B ≤ A'` and `M ≥ 0`.
* `eq_zero_of_le_integral_osgoodModulus`: a monotone function `0 ≤ w ≤ A` on `[0, T]` with
  `w(t) ≤ C ∫₀ᵗ φ_A(w(s)) ds` vanishes on `[0, T]`.
* `forall_le_of_le_integral_osgoodModulus`: monotone functions `0 ≤ D n m ≤ A` with
  `D(n + 1, m + 1)(t) ≤ C ∫₀ᵗ φ_A(D(n, m)(s)) ds` tend to `0` uniformly on `[0, T]` as
  `n, m → ∞`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace PDE.Analysis

/-- The Osgood modulus `r (1 + log (A / r))`. -/
def osgoodModulus (A r : ℝ) : ℝ :=
  r * (1 + Real.log (A / r))

variable {A r : ℝ}

/-- The modulus vanishes at `0` (the logarithm is totalized by `log 0 = 0`). -/
@[simp]
theorem osgoodModulus_zero (A : ℝ) : osgoodModulus A 0 = 0 := by
  simp [osgoodModulus]

/-- For `A > 0`, `φ_A(r) = r (1 + log A) - r log r` for every real `r`. -/
theorem osgoodModulus_eq (hA : 0 < A) (r : ℝ) :
    osgoodModulus A r = r * (1 + Real.log A) - r * Real.log r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [osgoodModulus, Real.log_div hA.ne' hr]
    ring

/-- At `r = A` the modulus equals `A`. -/
@[simp]
theorem osgoodModulus_self (A : ℝ) : osgoodModulus A A = A := by
  rcases eq_or_ne A 0 with rfl | hA
  · simp
  · simp [osgoodModulus, div_self hA]

/-- For `A > 0` the modulus is continuous on `ℝ`. -/
theorem continuous_osgoodModulus (hA : 0 < A) : Continuous (osgoodModulus A) := by
  rw [show osgoodModulus A = fun r ↦ r * (1 + Real.log A) - r * Real.log r from
    funext (osgoodModulus_eq hA)]
  exact (continuous_id.mul continuous_const).sub Real.continuous_mul_log

/-- Away from `0` the derivative of `φ_A` is `log A - log r`. -/
theorem hasDerivAt_osgoodModulus (hA : 0 < A) (hr : r ≠ 0) :
    HasDerivAt (osgoodModulus A) (Real.log A - Real.log r) r := by
  have h := ((hasDerivAt_id' r).mul_const (1 + Real.log A)).sub (Real.hasDerivAt_mul_log hr)
  rw [show ((fun y : ℝ ↦ y * (1 + Real.log A)) - fun x ↦ x * Real.log x) = osgoodModulus A from
    funext fun x ↦ (osgoodModulus_eq hA x).symm] at h
  convert h using 1
  ring

/-- On `[0, A]` the modulus dominates the identity. -/
theorem le_osgoodModulus (hr : 0 ≤ r) (hrA : r ≤ A) : r ≤ osgoodModulus A r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hlog : 0 ≤ Real.log (A / r) := Real.log_nonneg ((one_le_div hr).mpr hrA)
  unfold osgoodModulus
  nlinarith

/-- The modulus is nonnegative on `[0, A]`. -/
theorem osgoodModulus_nonneg (hr : 0 ≤ r) (hrA : r ≤ A) : 0 ≤ osgoodModulus A r :=
  hr.trans (le_osgoodModulus hr hrA)

/-- The modulus is positive on `(0, A]`. -/
theorem osgoodModulus_pos (hr : 0 < r) (hrA : r ≤ A) : 0 < osgoodModulus A r :=
  hr.trans_le (le_osgoodModulus hr.le hrA)

/-- The modulus is increasing on `[0, A]`. -/
theorem monotoneOn_osgoodModulus (hA : 0 < A) : MonotoneOn (osgoodModulus A) (Icc 0 A) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 A) (continuous_osgoodModulus hA).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_osgoodModulus hA hx.1.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_osgoodModulus hA hx.1.ne').deriv, sub_nonneg]
    exact Real.log_le_log hx.1 hx.2.le

/-- The modulus is increasing in `A`. -/
theorem osgoodModulus_le_osgoodModulus {A' : ℝ} (hA : 0 < A) (hAA' : A ≤ A') (hr : 0 ≤ r) :
    osgoodModulus A r ≤ osgoodModulus A' r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  unfold osgoodModulus
  gcongr

/-- Scaling by `c ≥ 1` costs at most the factor `c`. -/
theorem osgoodModulus_mul_le {c : ℝ} (hA : 0 < A) (hc : 1 ≤ c) (hr : 0 ≤ r) :
    osgoodModulus A (c * r) ≤ c * osgoodModulus A r := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hsplit : Real.log (A / (c * r)) = Real.log (A / r) - Real.log c := by
    rw [show A / (c * r) = A / r / c by field_simp, Real.log_div (div_pos hA hr).ne' hc0.ne']
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc
  unfold osgoodModulus
  rw [hsplit]
  nlinarith [mul_pos hc0 hr]

/-- The homogeneous Kato form: for `0 ≤ B ≤ A'` and `M ≥ 0`,
`B (1 + log (2 + M / B)) ≤ φ_{2A' + M}(B)`. -/
theorem mul_one_add_log_le_osgoodModulus {B A' M : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A')
    (hM : 0 ≤ M) : B * (1 + Real.log (2 + M / B)) ≤ osgoodModulus (2 * A' + M) B := by
  rcases hB.eq_or_lt with rfl | hB
  · simp
  unfold osgoodModulus
  gcongr
  rw [le_div_iff₀ hB, add_mul, div_mul_cancel₀ M hB.ne']
  linarith

/-- `s ↦ φ_A(f(s))` is monotone on `[0, T]` for a monotone `f` with values in `[0, A]`. -/
private theorem monotoneOn_osgoodModulus_comp {f : ℝ → ℝ} {T : ℝ} (hA : 0 < A)
    (hf : MonotoneOn f (Icc 0 T)) (h0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hle : ∀ t ∈ Icc 0 T, f t ≤ A) :
    MonotoneOn (fun s ↦ osgoodModulus A (f s)) (Icc 0 T) := fun x hx y hy hxy ↦
  monotoneOn_osgoodModulus hA ⟨h0 x hx, hle x hx⟩ ⟨h0 y hy, hle y hy⟩ (hf hx hy hxy)

private theorem intervalIntegrable_osgoodModulus_comp {f : ℝ → ℝ} {T a b : ℝ} (hA : 0 < A)
    (hf : MonotoneOn f (Icc 0 T)) (h0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hle : ∀ t ∈ Icc 0 T, f t ≤ A)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IntervalIntegrable (fun s ↦ osgoodModulus A (f s)) volume a b :=
  ((monotoneOn_osgoodModulus_comp hA hf h0 hle).mono
    (by rw [uIcc_of_le hab]; exact Icc_subset_Icc ha hb)).intervalIntegrable

/-- **Osgood's lemma.** A monotone function `0 ≤ w ≤ A` on `[0, T]` with
`w(t) ≤ C ∫₀ᵗ φ_A(w(s)) ds` vanishes on `[0, T]`. -/
theorem eq_zero_of_le_integral_osgoodModulus {w : ℝ → ℝ} {T C : ℝ} (hA : 0 < A) (hC : 0 ≤ C)
    (hw : MonotoneOn w (Icc 0 T)) (h0 : ∀ t ∈ Icc 0 T, 0 ≤ w t)
    (hle : ∀ t ∈ Icc 0 T, w t ≤ A)
    (h : ∀ t ∈ Icc 0 T, w t ≤ C * ∫ s in (0)..t, osgoodModulus A (w s)) :
    ∀ t ∈ Icc 0 T, w t = 0 := by
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have hφw := monotoneOn_osgoodModulus_comp hA hw h0 hle
  have hint {a b : ℝ} := @intervalIntegrable_osgoodModulus_comp A w T a b hA hw h0 hle
  set F : ℝ → ℝ := fun t ↦ C * ∫ s in (0)..t, osgoodModulus A (w s) with hF
  set ψ : ℝ → ℝ := fun r ↦ osgoodModulus A (min r A) with hψ
  have hψc : Continuous ψ :=
    (continuous_osgoodModulus hA).comp (continuous_id.min continuous_const)
  have hFcont : ContinuousOn F (Icc 0 T) := by
    have hprim := intervalIntegral.continuousOn_primitive_interval
      (μ := volume) (a := 0) (b := T) (f := fun s ↦ osgoodModulus A (w s))
      (by rw [uIcc_of_le hT]; exact hφw.integrableOn_isCompact isCompact_Icc)
    rw [uIcc_of_le hT] at hprim
    exact continuousOn_const.mul hprim
  -- the slope of `F` from the right is at most `C ψ(F)`
  have hslope (x : ℝ) (hx : x ∈ Ico 0 T) (z : ℝ) (hz : z ∈ Ioc x T) :
      slope F x z ≤ C * ψ (F z) := by
    have hz0 : z ∈ Icc 0 T := ⟨hx.1.trans hz.1.le, hz.2⟩
    have hdiff : F z - F x = C * ∫ s in x..z, osgoodModulus A (w s) := by
      simp only [hF, ← mul_sub]
      rw [intervalIntegral.integral_interval_sub_left (hint le_rfl hz0.1 hz0.2)
        (hint le_rfl hx.1 hx.2.le)]
    have hbound : (∫ s in x..z, osgoodModulus A (w s)) ≤ (z - x) * osgoodModulus A (w z) := by
      have := intervalIntegral.integral_mono_on hz.1.le (hint hx.1 hz.1.le hz.2)
        (intervalIntegrable_const (c := osgoodModulus A (w z)))
        (fun s hs ↦ hφw ⟨hx.1.trans hs.1, hs.2.trans hz.2⟩ hz0 hs.2)
      simpa [intervalIntegral.integral_const, smul_eq_mul] using this
    have hmin : w z ≤ min (F z) A := le_min (h z hz0) (hle z hz0)
    have hwz : osgoodModulus A (w z) ≤ ψ (F z) := monotoneOn_osgoodModulus hA
      ⟨h0 z hz0, hle z hz0⟩ ⟨(h0 z hz0).trans hmin, min_le_right _ _⟩ hmin
    have hzx : 0 < z - x := sub_pos.mpr hz.1
    rw [slope_def_field, hdiff, div_le_iff₀ hzx]
    linarith [mul_le_mul_of_nonneg_left (hbound.trans (mul_le_mul_of_nonneg_left hwz hzx.le)) hC]
  -- comparison with `y(t) = A exp(1 - K e^{-(C + 1) t})`
  have hcompare (K : ℝ) (hK : Real.exp ((C + 1) * T) ≤ K) :
      ∀ t ∈ Icc 0 T, F t ≤ A * Real.exp (1 - K * Real.exp (-((C + 1) * t))) := by
    set y : ℝ → ℝ := fun t ↦ A * Real.exp (1 - K * Real.exp (-((C + 1) * t))) with hy
    have hyA (x : ℝ) (hx : x ≤ T) : y x ≤ A := by
      have hge : 1 ≤ K * Real.exp (-((C + 1) * x)) := by
        rw [Real.exp_neg, ← div_eq_mul_inv, one_le_div (Real.exp_pos _)]
        exact (Real.exp_le_exp.mpr (by nlinarith)).trans hK
      exact mul_le_of_le_one_right hA.le (Real.exp_le_one_iff.mpr (by linarith))
    have hypos (x : ℝ) : 0 < y x := mul_pos hA (Real.exp_pos _)
    have hφy (x : ℝ) :
        osgoodModulus A (y x) = y x * (K * Real.exp (-((C + 1) * x))) := by
      have hlog : Real.log (A / y x) = K * Real.exp (-((C + 1) * x)) - 1 := by
        rw [hy, show A / (A * Real.exp (1 - K * Real.exp (-((C + 1) * x)))) =
            (Real.exp (1 - K * Real.exp (-((C + 1) * x))))⁻¹ by field_simp, Real.log_inv,
          Real.log_exp]
        ring
      rw [osgoodModulus, hlog]
      ring
    have hyd (x : ℝ) : HasDerivAt y ((C + 1) * osgoodModulus A (y x)) x := by
      have h1 : HasDerivAt (fun t ↦ -((C + 1) * t)) (-((C + 1) * 1)) x :=
        ((hasDerivAt_id' x).const_mul (C + 1)).neg
      convert ((h1.exp.const_mul K).const_sub 1).exp.const_mul A using 1
      rw [hφy x, hy]
      ring
    intro t ht
    refine image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := fun x ↦ C * ψ (F x))
      (B := y) (B' := fun x ↦ (C + 1) * osgoodModulus A (y x)) hFcont ?_ ?_
      (fun x _ ↦ (hyd x).continuousAt.continuousWithinAt) (fun x _ ↦ (hyd x).hasDerivWithinAt)
      ?_ ht
    · intro x hx r hr
      have hcont : ContinuousWithinAt F (Ioi x) x :=
        (hFcont x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)
      refine Eventually.frequently ?_
      filter_upwards [(((hψc.tendsto _).comp hcont).const_mul C).eventually_lt_const hr,
        Ioc_mem_nhdsGT hx.2] with z hz hzI using (hslope x hx z hzI).trans_lt hz
    · simpa only [hF, intervalIntegral.integral_same, mul_zero] using (hypos 0).le
    · intro x hx hFy
      have hψF : ψ (F x) = osgoodModulus A (y x) := by
        simp only [hψ, hFy, min_eq_left (hyA x hx.2.le)]
      rw [hψF]
      linarith [osgoodModulus_pos (hypos x) (hyA x hx.2.le)]
  -- the comparison functions tend to `0` as `K → ∞`
  have hlim : Tendsto (fun K ↦ A * Real.exp (1 - K * Real.exp (-((C + 1) * t₀)))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_atBot_add_const_left _ 1
      (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const (Real.exp_pos
        (-((C + 1) * t₀))))))).const_mul A
    simpa only [mul_zero, Function.comp_def, id, sub_eq_add_neg] using this
  refine le_antisymm (ge_of_tendsto hlim ?_) (h0 t₀ ht₀)
  filter_upwards [eventually_ge_atTop (Real.exp ((C + 1) * T))] with K hK
  exact (h t₀ ht₀).trans (hcompare K hK t₀ ht₀)

/-- **Cauchy form for iterates.** If the nonnegative functions `D n m ≤ A`, monotone on `[0, T]`,
satisfy `D (n + 1) (m + 1) t ≤ C ∫₀ᵗ φ_A(D n m s) ds`, then `D n m → 0` uniformly on `[0, T]` as
`n, m → ∞`. -/
theorem forall_le_of_le_integral_osgoodModulus (D : ℕ → ℕ → ℝ → ℝ) {T C : ℝ} (hA : 0 < A)
    (hC : 0 ≤ C) (hmono : ∀ n m, MonotoneOn (D n m) (Icc 0 T))
    (h0 : ∀ n m, ∀ t ∈ Icc 0 T, 0 ≤ D n m t) (hle : ∀ n m, ∀ t ∈ Icc 0 T, D n m t ≤ A)
    (hstep : ∀ n m, ∀ t ∈ Icc 0 T,
      D (n + 1) (m + 1) t ≤ C * ∫ s in (0)..t, osgoodModulus A (D n m s)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ t ∈ Icc 0 T, D n m t ≤ ε := by
  intro ε hε
  by_cases hT : 0 ≤ T
  swap
  · exact ⟨0, fun n _ m _ t ht ↦ absurd (ht.1.trans ht.2) hT⟩
  -- tail suprema
  let ι (n : ℕ) := {p : ℕ × ℕ // n ≤ p.1 ∧ n ≤ p.2}
  have hne (n : ℕ) : Nonempty (ι n) := ⟨⟨(n, n), le_rfl, le_rfl⟩⟩
  let w (n : ℕ) (t : ℝ) : ℝ := ⨆ p : ι n, D p.1.1 p.1.2 t
  have hbdd (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
      BddAbove (range fun p : ι n ↦ D p.1.1 p.1.2 t) :=
    ⟨A, by rintro _ ⟨p, rfl⟩; exact hle _ _ t ht⟩
  have hle_w {n m m' : ℕ} (hm : n ≤ m) (hm' : n ≤ m') {t : ℝ} (ht : t ∈ Icc 0 T) :
      D m m' t ≤ w n t :=
    le_ciSup (f := fun p : ι n ↦ D p.1.1 p.1.2 t) (hbdd n ht) ⟨(m, m'), hm, hm'⟩
  have hw_le (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) : w n t ≤ A :=
    have := hne n; ciSup_le fun p ↦ hle _ _ t ht
  have hw_nonneg (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) : 0 ≤ w n t :=
    (h0 n n t ht).trans (hle_w le_rfl le_rfl ht)
  have hw_mono (n : ℕ) : MonotoneOn (w n) (Icc 0 T) := fun s hs t ht hst ↦
    have := hne n; ciSup_le fun p ↦ (hmono _ _ hs ht hst).trans (hle_w p.2.1 p.2.2 ht)
  have hw_anti {t : ℝ} (ht : t ∈ Icc 0 T) : Antitone fun n ↦ w n t :=
    antitone_nat_of_succ_le fun n ↦ have := hne (n + 1)
      ciSup_le fun p ↦ hle_w (n.le_succ.trans p.2.1) (n.le_succ.trans p.2.2) ht
  have hφmono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ A) :
      osgoodModulus A a ≤ osgoodModulus A b :=
    monotoneOn_osgoodModulus hA ⟨ha, hab.trans hb⟩ ⟨ha.trans hab, hb⟩ hab
  have hwint (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :=
    intervalIntegrable_osgoodModulus_comp hA (hw_mono n) (fun s hs ↦ hw_nonneg n hs)
      (fun s hs ↦ hw_le n hs) le_rfl ht.1 ht.2
  have hw_step (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
      w (n + 1) t ≤ C * ∫ s in (0)..t, osgoodModulus A (w n s) := by
    have := hne (n + 1)
    refine ciSup_le ?_
    rintro ⟨⟨a, b⟩, ha, hb⟩
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' ha
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hb
    refine (hstep (a + n) (b + n) t ht).trans (mul_le_mul_of_nonneg_left ?_ hC)
    refine intervalIntegral.integral_mono_on ht.1 (intervalIntegrable_osgoodModulus_comp hA
      (hmono _ _) (h0 _ _) (hle _ _) le_rfl ht.1 ht.2) (hwint n ht) fun s hs ↦ ?_
    have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    exact hφmono (h0 _ _ s hs') (hle_w (n.le_add_left a) (n.le_add_left b) hs') (hw_le n hs')
  -- the decreasing limit
  let W (t : ℝ) : ℝ := ⨅ n, w n t
  have hbddW {t : ℝ} (ht : t ∈ Icc 0 T) : BddBelow (range fun n ↦ w n t) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hw_nonneg n ht⟩
  have hW_le {t : ℝ} (ht : t ∈ Icc 0 T) (n : ℕ) : W t ≤ w n t := ciInf_le (hbddW ht) n
  have hW_mono : MonotoneOn W (Icc 0 T) := fun s hs t ht hst ↦
    le_ciInf fun n ↦ (hW_le hs n).trans (hw_mono n hs ht hst)
  have hW_step (t : ℝ) (ht : t ∈ Icc 0 T) :
      W t ≤ C * ∫ s in (0)..t, osgoodModulus A (W s) := by
    have hlim : Tendsto (fun n ↦ C * ∫ s in (0)..t, osgoodModulus A (w n s)) atTop
        (𝓝 (C * ∫ s in (0)..t, osgoodModulus A (W s))) := by
      refine Tendsto.const_mul C <|
        intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ A)
        (.of_forall fun n ↦ (hwint n ht).def'.aestronglyMeasurable)
        (.of_forall fun n ↦ .of_forall fun s hs ↦ ?_) intervalIntegrable_const
        (.of_forall fun s hs ↦ ?_)
      all_goals
        rw [uIoc_of_le ht.1] at hs
        have hs' : s ∈ Icc 0 T := ⟨hs.1.le, hs.2.trans ht.2⟩
      · exact (Real.norm_of_nonneg (osgoodModulus_nonneg (hw_nonneg n hs') (hw_le n hs'))).trans_le
          ((hφmono (hw_nonneg n hs') (hw_le n hs') le_rfl).trans_eq (osgoodModulus_self A))
      · exact ((continuous_osgoodModulus hA).tendsto _).comp
          (tendsto_atTop_ciInf (hw_anti hs') (hbddW hs'))
    exact ge_of_tendsto' hlim fun n ↦ (hW_le ht (n + 1)).trans (hw_step n ht)
  have hTmem : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  have hW_zero := eq_zero_of_le_integral_osgoodModulus hA hC hW_mono
    (fun t ht ↦ le_ciInf fun n ↦ hw_nonneg n ht) (fun t ht ↦ (hW_le ht 0).trans (hw_le 0 ht))
    hW_step T hTmem
  obtain ⟨N, hN⟩ : ∃ N, w N T < ε := exists_lt_of_ciInf_lt (hW_zero.trans_lt hε)
  exact ⟨N, fun n hn m hm t ht ↦
    ((hle_w hn hm ht).trans (hw_mono N ht hTmem ht.2)).trans hN.le⟩

end PDE.Analysis
