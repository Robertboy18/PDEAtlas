/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Growth of solutions of differential inequalities with a sublinear forcing

Let `γ` satisfy `‖γ'‖ ≤ c(t) ‖γ‖ + A (1 + ‖γ‖)^(1 - δ)` on `[0, T]`, with `c ≥ 0` continuous,
`A ≥ 0` and `δ > 0`. The linear part makes `γ` grow like `exp (∫₀ᵗ c)`, and once this growth is
divided out the sublinear part only adds a bounded amount:

```text
1 + ‖γ t‖ ≤ exp (∫₀ᵗ c) ((1 + ‖γ 0‖)^δ + δ A ∫₀ᵗ exp (-δ ∫₀ˢ c) ds)^(1/δ)
```

(`one_add_norm_le_sublinearBound`). If moreover `c ≥ c₀ > 0`, the bracket is at most
`(1 + ‖γ 0‖)^δ + A / c₀` (`one_add_norm_le_of_le_rate`). This is the estimate behind the control
of supports under dynamic rescaling: a particle moved by `c(t) x + u` with `|u| ≲ |x|^(1-δ)` stays,
in units of the scale `exp (∫₀ᵗ c)`, in a bounded set.

The bound solves `y' = c (1 + y) + A (1 + y)^(1 - δ)`, for which `(1 + y)^δ exp (-δ ∫ c)` has the
derivative `δ A exp (-δ ∫ c)`. The proof compares `‖γ‖` with the solutions for the coefficient
`A + ε` and the initial value `‖γ 0‖ + ε`, which dominate strictly, and lets `ε → 0`.

## Main definitions

* `sublinearBound c A δ y₀ t`: the right-hand side above with `y₀ = ‖γ 0‖`.

## Main results

* `one_add_norm_le_sublinearBound`: the growth bound.
* `sublinearBound_le_of_le_rate`, `one_add_norm_le_of_le_rate`: the bound for a rate `c ≥ c₀ > 0`.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis.ODE

/-- The growth bound `exp (∫₀ᵗ c) ((1 + y₀)^δ + δ A ∫₀ᵗ exp (-δ ∫₀ˢ c) ds)^(1/δ)` for the inequality
`‖γ'‖ ≤ c ‖γ‖ + A (1 + ‖γ‖)^(1 - δ)` with `‖γ 0‖ = y₀`. -/
def sublinearBound (c : ℝ → ℝ) (A δ y₀ t : ℝ) : ℝ :=
  Real.exp (∫ s in (0)..t, c s) *
    ((1 + y₀) ^ δ + δ * A * ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r)) ^ (1 / δ)

/-- For `Q ≥ 0` and `δ > 0`, `exp I · Q^(1/δ - 1) · exp (-δ I) = (exp I · Q^(1/δ))^(1 - δ)`. -/
private theorem rpow_one_sub_eq {I Q δ : ℝ} (hQ : 0 ≤ Q) (hδ : 0 < δ) :
    Real.exp I * Q ^ (1 / δ - 1) * Real.exp (-δ * I) = (Real.exp I * Q ^ (1 / δ)) ^ (1 - δ) := by
  have h1 : 1 / δ * (1 - δ) = 1 / δ - 1 := by field_simp
  rw [Real.mul_rpow (Real.exp_pos I).le (Real.rpow_nonneg hQ _), ← Real.rpow_mul hQ,
    ← Real.exp_mul, h1, mul_comm (Real.exp I), mul_assoc, ← Real.exp_add,
    show I * (1 - δ) = I + -δ * I by ring]
  ring

/-- **Growth under a sublinear forcing.** If `‖γ'(t)‖ ≤ c(t) ‖γ(t)‖ + A (1 + ‖γ(t)‖)^(1 - δ)` on
`[0, T)` with right derivatives, `c ≥ 0` continuous on `[0, T]`, `A ≥ 0` and `δ > 0`, then
`1 + ‖γ t‖ ≤ sublinearBound c A δ ‖γ 0‖ t` on `[0, T]`. -/
theorem one_add_norm_le_sublinearBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ γ' : ℝ → E} {c : ℝ → ℝ} {A δ T : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hc : ContinuousOn c (Icc 0 T)) (hc0 : ∀ t ∈ Icc 0 T, 0 ≤ c t)
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (γ' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, ‖γ' t‖ ≤ c t * ‖γ t‖ + A * (1 + ‖γ t‖) ^ (1 - δ))
    {t : ℝ} (ht : t ∈ Icc 0 T) : 1 + ‖γ t‖ ≤ sublinearBound c A δ ‖γ 0‖ t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  -- extend the rate continuously to the line
  set c' : ℝ → ℝ := fun s ↦ c (projIcc 0 T hT s) with hc'def
  have hc'cont : Continuous c' :=
    hc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s ↦ (projIcc 0 T hT s).2)
  have hc'eq : ∀ s ∈ Icc 0 T, c' s = c s := fun s hs ↦ by
    simp only [c', projIcc_of_mem hT hs]
  set I : ℝ → ℝ := fun s ↦ ∫ r in (0)..s, c' r with hIdef
  have hI : ∀ s, HasDerivAt I (c' s) s := fun s ↦
    (hc'cont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hIcont : Continuous I := continuous_iff_continuousAt.2 fun s ↦ (hI s).continuousAt
  set g : ℝ → ℝ := fun s ↦ Real.exp (-δ * I s) with hgdef
  have hgcont : Continuous g := Real.continuous_exp.comp (continuous_const.mul hIcont)
  set J : ℝ → ℝ := fun s ↦ ∫ r in (0)..s, g r with hJdef
  have hJ : ∀ s, HasDerivAt J (g s) s := fun s ↦
    (hgcont.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hJcont : Continuous J := continuous_iff_continuousAt.2 fun s ↦ (hJ s).continuousAt
  have hJ0 : ∀ s, 0 ≤ s → 0 ≤ J s := fun s hs ↦
    intervalIntegral.integral_nonneg hs (fun r _ ↦ (Real.exp_pos _).le)
  set y₀ := ‖γ 0‖ with hy₀
  have hy₀0 : 0 ≤ y₀ := norm_nonneg _
  -- the comparison functions
  set Q : ℝ → ℝ → ℝ := fun ε s ↦ (1 + y₀ + ε) ^ δ + δ * (A + ε) * J s with hQdef
  set P : ℝ → ℝ → ℝ := fun ε s ↦ Real.exp (I s) * Q ε s ^ (1 / δ) with hPdef
  have hQpos : ∀ ε, 0 ≤ ε → ∀ s, 0 ≤ s → 0 < Q ε s := fun ε hε s hs ↦ by
    have := hJ0 s hs
    simp only [Q]
    positivity
  have hPpos : ∀ ε, 0 ≤ ε → ∀ s, 0 ≤ s → 0 < P ε s := fun ε hε s hs ↦
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (hQpos ε hε s hs) _)
  have hP0 : ∀ ε, 0 ≤ ε → P ε 0 = 1 + y₀ + ε := fun ε hε ↦ by
    simp only [P, Q, I, J, intervalIntegral.integral_same, mul_zero, add_zero, Real.exp_zero,
      one_mul]
    rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hδ.ne', Real.rpow_one]
  have hPderiv : ∀ ε, 0 ≤ ε → ∀ s, 0 ≤ s →
      HasDerivAt (P ε) (c' s * P ε s + (A + ε) * P ε s ^ (1 - δ)) s := by
    intro ε hε s hs
    have hQd : HasDerivAt (Q ε) (δ * (A + ε) * g s) s :=
      ((hJ s).const_mul (δ * (A + ε))).const_add _
    have hQp : HasDerivAt (fun q ↦ Q ε q ^ (1 / δ))
        (1 / δ * Q ε s ^ (1 / δ - 1) * (δ * (A + ε) * g s)) s := by
      simpa [Function.comp_def] using (Real.hasDerivAt_rpow_const (p := 1 / δ)
        (Or.inl (hQpos ε hε s hs).ne')).comp s hQd
    convert (hI s).exp.mul hQp using 1
    have hid := rpow_one_sub_eq (I := I s) (hQpos ε hε s hs).le hδ
    simp only [P, g] at hid ⊢
    rw [← hid]
    field_simp
  -- the strict comparison for `ε > 0`
  have hcomp : ∀ ε, 0 < ε → ‖γ t‖ ≤ P ε t - 1 := by
    intro ε hε
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary' hγ hγ'
      (B := fun s ↦ P ε s - 1) (B' := fun s ↦ c' s * P ε s + (A + ε) * P ε s ^ (1 - δ))
      ?_ ?_ ?_ ?_ ht
    · rw [hP0 ε hε.le]
      linarith
    · exact fun s hs ↦
        ((hPderiv ε hε.le s hs.1).continuousAt.sub continuousAt_const).continuousWithinAt
    · exact fun s hs ↦ ((hPderiv ε hε.le s hs.1).sub_const 1).hasDerivWithinAt
    · intro s hs heq
      have hsI : s ∈ Icc 0 T := Ico_subset_Icc_self hs
      have hPs := hPpos ε hε.le s hs.1
      have h1 : 1 + ‖γ s‖ = P ε s := by linarith
      have hcs : 0 ≤ c' s := by rw [hc'eq s hsI]; exact hc0 s hsI
      have hpow : 0 < P ε s ^ (1 - δ) := Real.rpow_pos_of_pos hPs _
      calc ‖γ' s‖ ≤ c s * ‖γ s‖ + A * (1 + ‖γ s‖) ^ (1 - δ) := hbound s hs
        _ = c' s * (P ε s - 1) + A * P ε s ^ (1 - δ) := by
            rw [hc'eq s hsI, h1, show ‖γ s‖ = P ε s - 1 by linarith]
        _ < c' s * P ε s + (A + ε) * P ε s ^ (1 - δ) := by nlinarith
  -- the limit `ε → 0`
  have hlim : Tendsto (fun ε ↦ P ε t - 1) (𝓝[>] 0) (𝓝 (P 0 t - 1)) := by
    have hQc : ContinuousAt (fun ε ↦ Q ε t) 0 :=
      ((continuousAt_const.add continuousAt_id).rpow_const (Or.inr hδ.le)).add
        ((continuousAt_const.mul (continuousAt_const.add continuousAt_id)).mul continuousAt_const)
    have hPc : ContinuousAt (fun ε ↦ P ε t) 0 :=
      continuousAt_const.mul (hQc.rpow_const (Or.inr (by positivity)))
    exact ((hPc.sub continuousAt_const).tendsto).mono_left nhdsWithin_le_nhds
  have hle : ‖γ t‖ ≤ P 0 t - 1 :=
    ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε ↦ hcomp ε hε)
  -- identify `P 0 t` with the bound
  have hIt : ∀ s ∈ Icc 0 T, I s = ∫ r in (0)..s, c r := fun s hs ↦
    intervalIntegral.integral_congr fun r hr ↦ hc'eq r
      ((uIcc_of_le hs.1 ▸ hr : r ∈ Icc 0 s) |> fun h ↦ ⟨h.1, h.2.trans hs.2⟩)
  have hJt : J t = ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r) :=
    intervalIntegral.integral_congr fun s hs ↦ by
      rw [uIcc_of_le ht.1] at hs
      simp only [g, hIt s ⟨hs.1, hs.2.trans ht.2⟩]
  have hPt : P 0 t = sublinearBound c A δ y₀ t := by
    simp only [P, Q, sublinearBound, add_zero, hIt t ht, hJt]
  linarith [hPt ▸ hle]

/-- `s ↦ exp (-δ ∫₀ˢ c)` is continuous on `[0, t]` for `c` continuous there. -/
private theorem continuousOn_exp_neg_mul_primitive {c : ℝ → ℝ} {t : ℝ} (δ : ℝ) (ht : 0 ≤ t)
    (hc : ContinuousOn c (Icc 0 t)) :
    ContinuousOn (fun s ↦ Real.exp (-δ * ∫ r in (0)..s, c r)) (Icc 0 t) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) ht) left_mem_uIcc
  rw [uIcc_of_le ht] at h
  exact (continuousOn_const.mul h).rexp

/-- With a rate `c ≥ c₀ > 0` the sublinear forcing contributes at most `A / c₀` to the
bracket of `sublinearBound`. -/
theorem sublinearBound_le_of_le_rate {c : ℝ → ℝ} {A δ c₀ y₀ T t : ℝ} (hδ : 0 < δ)
    (hA : 0 ≤ A) (hc₀ : 0 < c₀) (hc : ContinuousOn c (Icc 0 T))
    (hcc₀ : ∀ s ∈ Icc 0 T, c₀ ≤ c s) (hy₀ : 0 ≤ y₀) (ht : t ∈ Icc 0 T) :
    sublinearBound c A δ y₀ t ≤
      Real.exp (∫ s in (0)..t, c s) * ((1 + y₀) ^ δ + A / c₀) ^ (1 / δ) := by
  have hsub : ∀ s ∈ Icc 0 t, s ∈ Icc 0 T := fun s hs ↦ ⟨hs.1, hs.2.trans ht.2⟩
  -- `∫₀ˢ c ≥ c₀ s`
  have hint : ∀ s ∈ Icc 0 t, c₀ * s ≤ ∫ r in (0)..s, c r := by
    intro s hs
    have hcs : IntervalIntegrable c MeasureTheory.volume 0 s :=
      (hc.mono fun r hr ↦ hsub r ⟨hr.1, hr.2.trans hs.2⟩).intervalIntegrable_of_Icc hs.1
    calc c₀ * s = ∫ _ in (0)..s, c₀ := by simp [mul_comm]
      _ ≤ ∫ r in (0)..s, c r :=
        intervalIntegral.integral_mono_on hs.1 intervalIntegrable_const hcs fun r hr ↦
          hcc₀ r (hsub r ⟨hr.1, hr.2.trans hs.2⟩)
  have hJle : ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r) ≤
      ∫ s in (0)..t, Real.exp (-(δ * c₀) * s) :=
    intervalIntegral.integral_mono_on ht.1 ((continuousOn_exp_neg_mul_primitive δ ht.1
        (hc.mono fun s hs ↦ hsub s hs)).intervalIntegrable_of_Icc ht.1)
      ((by fun_prop : Continuous fun s : ℝ ↦ Real.exp (-(δ * c₀) * s)).intervalIntegrable _ _)
      fun s hs ↦ Real.exp_le_exp.2 (by linarith [mul_le_mul_of_nonneg_left (hint s hs) hδ.le])
  have hk : 0 < δ * c₀ := mul_pos hδ hc₀
  have hJexp : ∫ s in (0)..t, Real.exp (-(δ * c₀) * s) =
      (1 - Real.exp (-(δ * c₀) * t)) / (δ * c₀) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s ↦ -Real.exp (-(δ * c₀) * s) / (δ * c₀))
      (fun s _ ↦ (((hasDerivAt_id' s).const_mul _).exp.neg.div_const _).congr_deriv
        (by field_simp))
      ((by fun_prop : Continuous fun s : ℝ ↦ Real.exp (-(δ * c₀) * s)).intervalIntegrable _ _)]
    simp only [mul_zero, Real.exp_zero]
    field_simp
    ring
  have hbr : δ * A * ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r) ≤ A / c₀ := by
    calc _ ≤ δ * A * ((1 - Real.exp (-(δ * c₀) * t)) / (δ * c₀)) :=
          hJexp ▸ mul_le_mul_of_nonneg_left hJle (mul_nonneg hδ.le hA)
      _ = A * (1 - Real.exp (-(δ * c₀) * t)) / c₀ := by field_simp
      _ ≤ A / c₀ := div_le_div_of_nonneg_right
          (mul_le_of_le_one_right hA (by linarith [Real.exp_pos (-(δ * c₀) * t)])) hc₀.le
  have hbase : 0 ≤ (1 + y₀) ^ δ + δ * A * ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r) :=
    add_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg (mul_nonneg hδ.le hA)
      (intervalIntegral.integral_nonneg ht.1 fun _ _ ↦ (Real.exp_pos _).le))
  unfold sublinearBound
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hbase (by linarith) (by positivity)) (Real.exp_pos _).le

/-- At the initial time the bound is `1 + y₀`. -/
theorem sublinearBound_zero {c : ℝ → ℝ} {A δ y₀ : ℝ} (hδ : 0 < δ) (hy₀ : -1 ≤ y₀) :
    sublinearBound c A δ y₀ 0 = 1 + y₀ := by
  simp only [sublinearBound, intervalIntegral.integral_same, Real.exp_zero, mul_zero, add_zero,
    one_mul]
  rw [← Real.rpow_mul (by linarith), mul_one_div_cancel hδ.ne', Real.rpow_one]

/-- The bound is monotone in the initial size. -/
theorem sublinearBound_mono {c : ℝ → ℝ} {A δ y₀ y₁ t : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hy₀ : -1 ≤ y₀) (hy : y₀ ≤ y₁) : sublinearBound c A δ y₀ t ≤ sublinearBound c A δ y₁ t := by
  have hI : 0 ≤ δ * A * ∫ s in (0)..t, Real.exp (-δ * ∫ r in (0)..s, c r) :=
    mul_nonneg (mul_nonneg hδ.le hA)
      (intervalIntegral.integral_nonneg ht fun _ _ ↦ (Real.exp_pos _).le)
  unfold sublinearBound
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ (by positivity)) (Real.exp_pos _).le
  · exact add_nonneg (Real.rpow_nonneg (by linarith) _) hI
  · have := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ 1 + y₀) (by linarith : 1 + y₀ ≤ 1 + y₁)
      hδ.le
    linarith

/-- **The linear case** `δ = 1`: for a rate `0 ≤ c ≤ M` on `[0, t]`,
`sublinearBound c A 1 y₀ t ≤ exp (M t) (1 + y₀ + A t)`. -/
theorem sublinearBound_one_le {c : ℝ → ℝ} {A M y₀ t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hy₀ : -1 ≤ y₀) (hc : ContinuousOn c (Icc 0 t)) (hc0 : ∀ s ∈ Icc 0 t, 0 ≤ c s)
    (hcM : ∀ s ∈ Icc 0 t, c s ≤ M) :
    sublinearBound c A 1 y₀ t ≤ Real.exp (M * t) * (1 + y₀ + A * t) := by
  have hci : IntervalIntegrable c MeasureTheory.volume 0 t := hc.intervalIntegrable_of_Icc ht
  have hcM' : ∫ s in (0)..t, c s ≤ M * t := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht hci
      intervalIntegrable_const hcM
    simpa [mul_comm] using this
  have hsub : ∀ s ∈ Icc 0 t, 0 ≤ ∫ r in (0)..s, c r := fun s hs ↦
    intervalIntegral.integral_nonneg hs.1 fun r hr ↦ hc0 r ⟨hr.1, hr.2.trans hs.2⟩
  have hJ : ∫ s in (0)..t, Real.exp (-1 * ∫ r in (0)..s, c r) ≤ t := by
    have hle : ∀ s ∈ Icc 0 t, Real.exp (-1 * ∫ r in (0)..s, c r) ≤ 1 := fun s hs ↦ by
      rw [Real.exp_le_one_iff]
      linarith [hsub s hs]
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht
      ((continuousOn_exp_neg_mul_primitive 1 ht hc).intervalIntegrable_of_Icc ht)
      intervalIntegrable_const hle
    simpa using this
  unfold sublinearBound
  rw [div_one, Real.rpow_one, Real.rpow_one, one_mul]
  refine mul_le_mul (Real.exp_le_exp.2 hcM') ?_ ?_ (Real.exp_pos _).le
  · nlinarith [mul_le_mul_of_nonneg_left hJ hA]
  · exact add_nonneg (by linarith) (mul_nonneg hA
      (intervalIntegral.integral_nonneg ht fun _ _ ↦ (Real.exp_pos _).le))

/-- **Growth under a sublinear forcing with a positive rate.** Under the hypotheses of
`one_add_norm_le_sublinearBound` and `c ≥ c₀ > 0` on `[0, T]`,
`1 + ‖γ t‖ ≤ exp (∫₀ᵗ c) ((1 + ‖γ 0‖)^δ + A / c₀)^(1/δ)`. -/
theorem one_add_norm_le_of_le_rate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ γ' : ℝ → E} {c : ℝ → ℝ} {A δ c₀ T : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hc₀ : 0 < c₀)
    (hc : ContinuousOn c (Icc 0 T)) (hcc₀ : ∀ t ∈ Icc 0 T, c₀ ≤ c t)
    (hγ : ContinuousOn γ (Icc 0 T)) (hγ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt γ (γ' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, ‖γ' t‖ ≤ c t * ‖γ t‖ + A * (1 + ‖γ t‖) ^ (1 - δ))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    1 + ‖γ t‖ ≤ Real.exp (∫ s in (0)..t, c s) * ((1 + ‖γ 0‖) ^ δ + A / c₀) ^ (1 / δ) :=
  (one_add_norm_le_sublinearBound hδ hA hc (fun s hs ↦ hc₀.le.trans (hcc₀ s hs)) hγ hγ' hbound
    ht).trans (sublinearBound_le_of_le_rate hδ hA hc₀ hc hcc₀ (norm_nonneg _) ht)

end PDE.Analysis.ODE
