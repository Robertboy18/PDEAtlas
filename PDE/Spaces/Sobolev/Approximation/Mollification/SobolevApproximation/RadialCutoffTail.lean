/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoff
public import PDE.FDeriv.PartialDeriv.WordBounds
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.RadialCutoffBounds

/-!
# Far-field tails of decaying functions

If the derivatives of `F` decay like `‖DⁱF(x)‖ ≤ C (1 + |x|)^{α - i}` on a set `s`, with `α ≤ 1`,
then so do the derivatives of the tail `(1 - χ_R) F` outside the radius `R`, with a constant
independent of `R ≥ 1`. Each derivative that falls on the cutoff costs a factor `R⁻¹`, and
`R⁻¹ ≤ 2 |x|⁻¹` wherever the cutoff is not constant.

## Main results

* `exists_norm_iteratedFDeriv_radialCutoff_le`: `‖Dⁱχ_R‖ ≤ M R^{-i}` for `i ≤ k`, with `M`
  independent of `R`.
* `exists_norm_iteratedFDeriv_tail_le`: `‖Dʲ((1 - χ_R) F)(x)‖ ≤ K |x|^{α - j}` for `j ≤ k` at the
  points of `s` with `|x| ≥ R ≥ 1`, with `K` independent of `R`.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter Set
open scoped Topology ContDiff

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- The iterated derivatives of the radial cutoff satisfy `‖Dⁱχ_R‖ ≤ M R^{-i}` for `i ≤ k`,
with `M` independent of `R`. -/
theorem exists_norm_iteratedFDeriv_radialCutoff_le (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i ≤ k, ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      ‖iteratedFDeriv ℝ i (radialCutoff R) x‖ ≤ M * R⁻¹ ^ i := by
  choose B hB0 hB using fun w : List (Fin n) ↦ exists_radialCutoff_derivative_bound (n := n) w
  set C : ℕ → ℝ := fun i ↦ (n : ℝ) ^ i * ∑ v : Fin i → Fin n, B (List.ofFn v) with hC
  have hC0 : ∀ i, 0 ≤ C i := fun i ↦
    mul_nonneg (by positivity) (Finset.sum_nonneg fun v _ ↦ hB0 _)
  refine ⟨∑ i ∈ Finset.range (k + 1), C i, Finset.sum_nonneg fun i _ ↦ hC0 i,
    fun i hi R hR x ↦ ?_⟩
  have hword : ∀ w : List (Fin n), w.length = i →
      ‖iteratedPartialDeriv w (radialCutoff R) x‖ ≤
        (∑ v : Fin i → Fin n, B (List.ofFn v)) * R⁻¹ ^ i := by
    intro w hw
    subst hw
    rw [Real.norm_eq_abs]
    refine (hB w R hR x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have := Finset.single_le_sum (f := fun v : Fin w.length → Fin n ↦ B (List.ofFn v))
      (fun v _ ↦ hB0 _) (Finset.mem_univ w.get)
    simpa [List.ofFn_get] using this
  calc ‖iteratedFDeriv ℝ i (radialCutoff R) x‖
      ≤ (n : ℝ) ^ i * ((∑ v : Fin i → Fin n, B (List.ofFn v)) * R⁻¹ ^ i) :=
        PDE.norm_iteratedFDeriv_le_of_forall_word i
          ((radialCutoff_contDiff R).contDiffAt.of_le (by simp)) hword
    _ = C i * R⁻¹ ^ i := by rw [hC]; ring
    _ ≤ (∑ i ∈ Finset.range (k + 1), C i) * R⁻¹ ^ i := by
        gcongr
        exact Finset.single_le_sum (f := C) (fun i _ ↦ hC0 i) (Finset.mem_range.2 (by omega))

/-- For `r ≥ 1` and `p ≤ 1`, `(1 + r)^p ≤ 2 r^p`. -/
private theorem one_add_rpow_le {p : ℝ} (hp : p ≤ 1) {r : ℝ} (hr : 1 ≤ r) :
    (1 + r) ^ p ≤ 2 * r ^ p := by
  have hr0 : 0 < r := by linarith
  rcases le_total p 0 with hp0 | hp0
  · calc (1 + r) ^ p ≤ r ^ p := Real.rpow_le_rpow_of_nonpos hr0 (by linarith) hp0
      _ ≤ 2 * r ^ p := by have := Real.rpow_nonneg hr0.le p; linarith
  · calc (1 + r) ^ p ≤ (2 * r) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp0
      _ = 2 ^ p * r ^ p := Real.mul_rpow (by norm_num) hr0.le
      _ ≤ 2 * r ^ p := by
          gcongr
          calc (2 : ℝ) ^ p ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp
            _ = 2 := Real.rpow_one 2

/-- The derivatives of `1 - χ_R` at a point with `|x| ≥ R`: `‖Dⁱ(1 - χ_R)(x)‖ ≤ M' |x|^{-i}`
for `i ≤ k`, where `M' = 1 + 2^k M` and `M` bounds the cutoff as in
`exists_norm_iteratedFDeriv_radialCutoff_le`. -/
private theorem norm_iteratedFDeriv_one_sub_radialCutoff_le {k : ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ i ≤ k, ∀ R : ℝ, 0 < R → ∀ x : ℝ^n,
      ‖iteratedFDeriv ℝ i (radialCutoff R) x‖ ≤ M * R⁻¹ ^ i)
    {R : ℝ} (hR0 : 0 < R) {x : ℝ^n} (hxR : R ≤ ‖x‖) {i : ℕ} (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i (fun y ↦ 1 - radialCutoff R y) x‖ ≤ (1 + M * 2 ^ k) * ‖x‖⁻¹ ^ i := by
  have hr : 0 < ‖x‖ := hR0.trans_le hxR
  have hMk : 0 ≤ M * 2 ^ k := by positivity
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    have hmem := radialCutoff_mem_Icc (n := n) R x
    have : ‖1 - radialCutoff R x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    linarith
  have hχ : ContDiffAt ℝ i (radialCutoff (n := n) R) x :=
    ((radialCutoff_contDiff R).of_le (by simp)).contDiffAt
  have heq : iteratedFDeriv ℝ i (fun y ↦ 1 - radialCutoff R y) x =
      -iteratedFDeriv ℝ i (radialCutoff R) x := by
    change iteratedFDeriv ℝ i ((fun _ ↦ (1 : ℝ)) - radialCutoff R) x = _
    rw [iteratedFDeriv_sub_apply contDiffAt_const hχ, iteratedFDeriv_const_of_ne hi0.ne',
      Pi.zero_apply, zero_sub]
  rw [heq, norm_neg]
  rcases le_or_gt ‖x‖ (2 * R) with h2 | h2
  · have hinv : R⁻¹ ≤ 2 * ‖x‖⁻¹ := by
      have h := inv_anti₀ (by positivity : 0 < ‖x‖ / 2) (by linarith : ‖x‖ / 2 ≤ R)
      rwa [inv_div, div_eq_mul_inv] at h
    have h2k : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hi
    calc ‖iteratedFDeriv ℝ i (radialCutoff R) x‖ ≤ M * R⁻¹ ^ i := hM i hi R hR0 x
      _ ≤ M * (2 * ‖x‖⁻¹) ^ i := by gcongr
      _ = M * 2 ^ i * ‖x‖⁻¹ ^ i := by ring
      _ ≤ (1 + M * 2 ^ k) * ‖x‖⁻¹ ^ i := by
          gcongr
          nlinarith
  · have hev : radialCutoff (n := n) R =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds h2] with y hy
      exact radialCutoff_eq_zero_of_le_norm hR0 hy.le
    rw [(hev.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_const_of_ne hi0.ne', Pi.zero_apply,
      norm_zero]
    positivity

/-- **The far-field tail.** If `‖DⁱF(x)‖ ≤ C (1 + |x|)^{α - i}` on `s` for `i ≤ k`, with
`α ≤ 1`, then `‖Dʲ((1 - χ_R) F)(x)‖ ≤ K |x|^{α - j}` for `j ≤ k` at the points of `s` with
`|x| ≥ R ≥ 1`, for one constant `K` independent of `R`. -/
theorem exists_norm_iteratedFDeriv_tail_le {k : ℕ} {F : ℝ^n → ℝ} (hF : ContDiff ℝ k F)
    {s : Set (ℝ^n)} {C α : ℝ} (hC : 0 ≤ C) (hα : α ≤ 1)
    (hdec : ∀ i ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ i F x‖ ≤ C * (1 + ‖x‖) ^ (α - i)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R → ∀ j ≤ k, ∀ x ∈ s, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ j (fun y ↦ (1 - radialCutoff R y) * F y) x‖ ≤ K * ‖x‖ ^ (α - j) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_iteratedFDeriv_radialCutoff_le (n := n) k
  set M' : ℝ := 1 + M * 2 ^ k with hM'_def
  have hM' : 0 ≤ M' := by positivity
  refine ⟨2 ^ k * M' * (2 * C), by positivity, fun R hR j hj x hx hxR ↦ ?_⟩
  have hR0 : 0 < R := by linarith
  have hx1 : 1 ≤ ‖x‖ := hR.trans hxR
  have hr : 0 < ‖x‖ := by linarith
  have hu : ContDiff ℝ k (fun y ↦ 1 - radialCutoff (n := n) R y) :=
    contDiff_const.sub ((radialCutoff_contDiff R).of_le (by simp))
  have hL := norm_iteratedFDeriv_mul_le hu hF x (n := j) (by exact_mod_cast hj)
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y ↦ 1 - radialCutoff R y) x‖ *
        ‖iteratedFDeriv ℝ (j - i) F x‖ ≤ (j.choose i : ℝ) * (M' * (2 * C) * ‖x‖ ^ (α - j)) := by
    intro i hi
    have hij : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := norm_iteratedFDeriv_one_sub_radialCutoff_le hM0 hM hR0 hxR (hij.trans hj)
    have h2 := hdec (j - i) ((Nat.sub_le j i).trans hj) x hx
    have h3 : (1 + ‖x‖) ^ (α - ((j - i : ℕ) : ℝ)) ≤ 2 * ‖x‖ ^ (α - ((j - i : ℕ) : ℝ)) :=
      one_add_rpow_le (by have : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
        hx1
    have hpow : ‖x‖⁻¹ ^ i * ‖x‖ ^ (α - ((j - i : ℕ) : ℝ)) = ‖x‖ ^ (α - j) := by
      rw [← Real.rpow_natCast, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr]
      congr 1
      push_cast [Nat.cast_sub hij]
      ring
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y ↦ 1 - radialCutoff R y) x‖ *
          ‖iteratedFDeriv ℝ (j - i) F x‖
        ≤ (j.choose i : ℝ) * (M' * ‖x‖⁻¹ ^ i) *
            (C * (2 * ‖x‖ ^ (α - ((j - i : ℕ) : ℝ)))) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hC)
      _ = (j.choose i : ℝ) * (M' * (2 * C) * (‖x‖⁻¹ ^ i * ‖x‖ ^ (α - ((j - i : ℕ) : ℝ)))) := by
          ring
      _ = (j.choose i : ℝ) * (M' * (2 * C) * ‖x‖ ^ (α - j)) := by rw [hpow]
  have h2k : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hj
  calc ‖iteratedFDeriv ℝ j (fun y ↦ (1 - radialCutoff R y) * F y) x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun y ↦ 1 - radialCutoff R y) x‖ *
            ‖iteratedFDeriv ℝ (j - i) F x‖ := hL
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (M' * (2 * C) * ‖x‖ ^ (α - j)) :=
        Finset.sum_le_sum hterm
    _ = 2 ^ j * (M' * (2 * C) * ‖x‖ ^ (α - j)) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ k * (M' * (2 * C) * ‖x‖ ^ (α - j)) :=
        mul_le_mul_of_nonneg_right h2k (by positivity)
    _ = 2 ^ k * M' * (2 * C) * ‖x‖ ^ (α - j) := by ring

end SobolevSpace.Approximation
