/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import PDE.Analysis.Evolution.Core.Gronwall.Variable

set_option linter.style.header false

/-!
# Differential inequalities

The lemmas bound a function that satisfies a differential or an integral inequality, in the manner
of Gronwall. The proofs compare with the solution of the linear equation and use the monotonicity
lemmas of Mathlib for derivatives.

## Main results

* `PDE.Analysis.le_integral_add_mul_integral_of_periodic`: Let `N` be `1` or `2`, let `y : ℝ → ℝ` be
  continuous with `y (σ + 1) = y σ` for all `σ`, and also `y (σ + 1 / 2) = y σ` when `N = 2`, and
  let `g : ℝ → ℝ` be nonnegative, interval integrable on `0..1`, with `g (σ + 1) = g σ`. If `0 ≤ c`,
  `y b - y a = c * ∫ σ in a..b, h σ` for all `a ≤ b`, and `h σ ≤ g σ` for almost every `σ`, then
  `y σ ≤ (∫ s in 0..1, y s) + c / N * ∫ s in 0..1, g s` for every `σ`.
* `PDE.Analysis.norm_sq_sub_eq_integral_inner_sub`: Let `M` be a continuous linear map on a real
  inner product space with `inner ℝ (M y) z = inner ℝ y (M z)` for all `y z`, let `f σ = F σ` and
  `k σ = M (c σ)` for almost every real `σ`, and let `0 < P`. If `‖c b‖ ^ 2 - ‖c a‖ ^ 2 = ∫ σ in
  a..b, P * (2 * inner ℝ (c σ) (M (F σ)) + (-(1 / 2) * ‖c σ‖ ^ 2 - 2 * ‖M (c σ)‖ ^ 2))`, then `(1 /
  (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) = ∫ σ in a..b, (inner ℝ (f σ) (k σ) - ‖k σ‖ ^ 2 - (1 / 4) * ‖c
  σ‖ ^ 2)`.
* `PDE.Analysis.le_mul_exp_of_le_add_integral`: Integral form of Gronwall's inequality on
  `Set.Icc 0 T` with `0 ≤ T`: if `φ` and `b` are continuous on `Set.Icc 0 T`, `b` is nonnegative
  there, and `φ t ≤ a + ∫ s in (0 : ℝ)..t, b s * φ s` for all `t` in `Set.Icc 0 T`, then
  `φ t ≤ a * Real.exp (∫ s in (0 : ℝ)..t, b s)` for all such `t`. It restates
  `PDE.Analysis.Evolution.le_mul_exp_integral_of_le_const_add_intervalIntegral`.
* `PDE.Analysis.sub_le_mul_intervalIntegral_of_ae_le`: Let `y h g : ℝ → ℝ` and `0 ≤ c` satisfy
  `y b - y a = c * ∫ σ in a..b, h σ` for all `a ≤ b`, with `h σ ≤ g σ` for almost every `σ`,
  `0 ≤ g σ` for all `σ`, and `g` interval integrable on every interval. Then
  `y s - y b ≤ c * ∫ σ in b..e, g σ` whenever `b ≤ s` and `s ≤ e`.

There is one further lemma of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace PDE.Analysis

/-- Integral form of Gronwall's inequality on `Set.Icc 0 T` with `0 ≤ T`: if `φ` and `b` are
continuous on `Set.Icc 0 T`, `b` is nonnegative there, and `φ t ≤ a + ∫ s in (0 : ℝ)..t, b s * φ s`
for all `t` in `Set.Icc 0 T`, then `φ t ≤ a * Real.exp (∫ s in (0 : ℝ)..t, b s)` for all such `t`.
It restates `PDE.Analysis.Evolution.le_mul_exp_integral_of_le_const_add_intervalIntegral`. -/
theorem le_mul_exp_of_le_add_integral {a T : ℝ} {φ b : ℝ → ℝ} (hT : 0 ≤ T)
    (hφ : ContinuousOn φ (Icc 0 T)) (hb : ContinuousOn b (Icc 0 T))
    (hb0 : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (h : ∀ t ∈ Icc 0 T, φ t ≤ a + ∫ s in (0 : ℝ)..t, b s * φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ a * Real.exp (∫ s in (0 : ℝ)..t, b s) :=
  PDE.Analysis.Evolution.le_mul_exp_integral_of_le_const_add_intervalIntegral hT hφ hb hb0 h

/-- Let `M` be a continuous linear map on a real inner product space with
`inner ℝ (M y) z = inner ℝ y (M z)` for all `y z`, let `f σ = F σ` and `k σ = M (c σ)` for almost
every real `σ`, and let `0 < P`. If
`‖c b‖ ^ 2 - ‖c a‖ ^ 2 = ∫ σ in a..b, P * (2 * inner ℝ (c σ) (M (F σ)) + (-(1 / 2) * ‖c σ‖ ^ 2 - 2 *
‖M (c σ)‖ ^ 2))`, then `(1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
∫ σ in a..b, (inner ℝ (f σ) (k σ) - ‖k σ‖ ^ 2 - (1 / 4) * ‖c σ‖ ^ 2)`. -/
theorem norm_sq_sub_eq_integral_inner_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ y z, inner ℝ (M y) z = inner ℝ y (M z))
    (f k c F : ℝ → E) (hf : ∀ᵐ σ : ℝ, f σ = F σ) (hk : ∀ᵐ σ : ℝ, k σ = M (c σ))
    {P : ℝ} (hP : 0 < P) (a b : ℝ)
    (hen : ‖c b‖ ^ 2 - ‖c a‖ ^ 2 = ∫ σ in a..b, P * (2 * inner ℝ (c σ) (M (F σ)) +
      (-(1 / 2 : ℝ) * ‖c σ‖ ^ 2 - 2 * ‖M (c σ)‖ ^ 2))) :
    (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
      ∫ σ in a..b, (inner ℝ (f σ) (k σ) - ‖k σ‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) := by
  rw [hen, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf, hk] with σ h1 h2 _
  rw [h1, h2, ← hM, real_inner_comm (F σ)]
  field_simp
  ring

/-- Let `y h g : ℝ → ℝ` and `0 ≤ c` satisfy `y b - y a = c * ∫ σ in a..b, h σ` for all `a ≤ b`, with
`h σ ≤ g σ` for almost every `σ`, `0 ≤ g σ` for all `σ`, and `g` interval integrable on every
interval. Then `y s - y b ≤ c * ∫ σ in b..e, g σ` whenever `b ≤ s` and `s ≤ e`. The proof bounds
`∫ σ in b..s, h σ` by `∫ σ in b..s, g σ`, also when `h` is not interval integrable, and then
enlarges the interval using `0 ≤ g`. -/
theorem sub_le_mul_intervalIntegral_of_ae_le {y h g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hid : ∀ a b, a ≤ b → y b - y a = c * ∫ σ in a..b, h σ)
    (hhg : ∀ᵐ σ, h σ ≤ g σ) (hg0 : ∀ σ, 0 ≤ g σ) (hgi : ∀ a b, IntervalIntegrable g volume a b)
    {b s e : ℝ} (hbs : b ≤ s) (hse : s ≤ e) : y s - y b ≤ c * ∫ σ in b..e, g σ := by
  rw [hid b s hbs]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 : ∫ σ in b..s, h σ ≤ ∫ σ in b..s, g σ := by
    by_cases hi : IntervalIntegrable h volume b s
    · exact intervalIntegral.integral_mono_ae hbs hi (hgi b s) hhg
    · rw [intervalIntegral.integral_undef hi]
      exact intervalIntegral.integral_nonneg hbs fun x _ ↦ hg0 x
  exact h1.trans (intervalIntegral.integral_mono_interval le_rfl hbs hse
    (ae_of_all _ fun x ↦ hg0 x) (hgi b e))

/-- Let `N` be `1` or `2`, let `y : ℝ → ℝ` be continuous with `y (σ + 1) = y σ` for all `σ`, and
also `y (σ + 1 / 2) = y σ` when `N = 2`, and let `g : ℝ → ℝ` be nonnegative, interval integrable on
`0..1`, with `g (σ + 1) = g σ`. If `0 ≤ c`, `y b - y a = c * ∫ σ in a..b, h σ` for all `a ≤ b`, and
`h σ ≤ g σ` for almost every `σ`, then `y σ ≤ (∫ s in 0..1, y s) + c / N * ∫ s in 0..1, g s` for
every `σ`. The proof takes a minimum point `a` of `y` on `Icc 0 1`, where `y a` is at most the mean
of `y`, and bounds the increase of `y` from `a` to a translate of `σ` by periods, using both half
periods when `N = 2`. -/
theorem le_integral_add_mul_integral_of_periodic {y h g : ℝ → ℝ} {c : ℝ} {N : ℕ}
    (hN : N = 1 ∨ N = 2) (hc : 0 ≤ c)
    (hy : Continuous y) (hper : ∀ σ, y (σ + 1) = y σ) (hhalf : N = 2 → ∀ σ, y (σ + 1 / 2) = y σ)
    (hid : ∀ a b, a ≤ b → y b - y a = c * ∫ σ in a..b, h σ)
    (hhg : ∀ᵐ σ, h σ ≤ g σ) (hg0 : ∀ σ, 0 ≤ g σ) (hgper : ∀ σ, g (σ + 1) = g σ)
    (hgi : IntervalIntegrable g volume 0 1) (σ : ℝ) :
    y σ ≤ (∫ s in (0 : ℝ)..1, y s) + c / N * ∫ s in (0 : ℝ)..1, g s := by
  have hgp : Function.Periodic g 1 := hgper
  have hgi' : ∀ a b, IntervalIntegrable g volume a b := fun a b ↦
    hgp.intervalIntegrable one_ne_zero (t := 0) (by simpa using hgi) a b
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ))
    hy.continuousOn
  have hmean : y a ≤ ∫ s in (0 : ℝ)..1, y s := by
    have := intervalIntegral.integral_mono_on (μ := volume)
        (zero_le_one' ℝ) intervalIntegrable_const
      (hy.intervalIntegrable 0 1) fun x hx ↦ (hmin hx : y a ≤ y x)
    simpa using this
  have hfull : ∫ s in a..a + 1, g s = ∫ s in (0 : ℝ)..1, g s := by
    simpa using hgp.intervalIntegral_add_eq a 0
  have K := fun {b s e : ℝ} (h1 : b ≤ s) (h2 : s ≤ e) ↦
    sub_le_mul_intervalIntegral_of_ae_le (y := y) hc hid hhg hg0 hgi' h1 h2
  rcases hN with rfl | rfl
  · have hyp : Function.Periodic y 1 := hper
    set s := toIcoMod one_pos a σ with hs
    have hmem := toIcoMod_mem_Ico one_pos a σ
    have hys : y s = y σ := by
      rw [hs, toIcoMod]
      exact hyp.sub_zsmul_eq _
    have := K hmem.1 hmem.2.le
    rw [hys, hfull] at this
    simp only [Nat.cast_one, div_one]
    linarith
  · have hyp : Function.Periodic y (1 / 2) := hhalf rfl
    have h2 : (0 : ℝ) < 1 / 2 := by norm_num
    set s := toIcoMod h2 a σ with hs
    have hmem := toIcoMod_mem_Ico h2 a σ
    have hys : y s = y σ := by
      rw [hs, toIcoMod]
      exact hyp.sub_zsmul_eq _
    have e1 := K hmem.1 hmem.2.le
    have e2 := K (b := a + 1 / 2) (s := s + 1 / 2) (e := a + 1) (by linarith [hmem.1])
      (by linarith [hmem.2])
    rw [hyp s, hys, hyp a] at e2
    rw [hys] at e1
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (hgi' a (a + 1 / 2))
      (hgi' (a + 1 / 2) (a + 1))
    rw [hfull] at hsplit
    have : (c * ∫ s in a..a + 1 / 2, g s) + (c * ∫ s in a + 1 / 2..a + 1, g s) =
        c * ∫ s in (0 : ℝ)..1, g s := by rw [← mul_add, hsplit]
    have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [hcast]
    have : c / 2 * ∫ s in (0 : ℝ)..1, g s = (c * ∫ s in (0 : ℝ)..1, g s) / 2 := by ring
    linarith

/-- For `T ≥ 0`, let `y` be continuous on `[0, T]` with `y 0 = 0`, with derivative `D τ` at each `τ`
in `(0, T)` and `D τ ≤ L * y τ + c` there. Then
`y t ≤ exp (|L| * T) * exp (|L| * T) * T * |c|` for every `t` in `[0, T]`. The function
`τ ↦ exp (-L * τ) * y τ - exp (|L| * T) * |c| * τ` is antitone on `[0, T]`. -/
theorem le_of_hasDerivAt_le_mul_add {T L c : ℝ} {y D : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hD : ∀ τ ∈ Ioo 0 T, HasDerivAt y (D τ) τ)
    (hb : ∀ τ ∈ Ioo 0 T, D τ ≤ L * y τ + c) (h0 : y 0 = 0) :
    ∀ t ∈ Icc 0 T, y t ≤ exp (|L| * T) * exp (|L| * T) * T * |c| := by
  intro t ht
  set C := exp (|L| * T) * |c| with hC
  have hC0 : 0 ≤ C := by positivity
  have hexp : ∀ τ ∈ Icc 0 T, exp (-L * τ) ≤ exp (|L| * T) ∧ exp (L * τ) ≤ exp (|L| * T) := by
    intro τ hτ
    have h1 : |L| * τ ≤ |L| * T := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg L)
    constructor
    · apply exp_le_exp.2
      have : -L * τ ≤ |L| * τ := mul_le_mul_of_nonneg_right (neg_le_abs L) hτ.1
      linarith
    · apply exp_le_exp.2
      have : L * τ ≤ |L| * τ := mul_le_mul_of_nonneg_right (le_abs_self L) hτ.1
      linarith
  have hanti : AntitoneOn (fun τ ↦ exp (-L * τ) * y τ - C * τ) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (f' := fun τ ↦ exp (-L * τ) * (D τ - L * y τ) - C) ?_ ?_ ?_
    · exact ((continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hy).sub
        (continuous_const.mul continuous_id).continuousOn
    · intro τ hτ
      rw [interior_Icc] at hτ
      have h1 : HasDerivAt (fun τ ↦ exp (-L * τ)) (exp (-L * τ) * (-L)) τ := by
        have := ((hasDerivAt_id τ).const_mul (-L)).exp
        simpa using this
      have h2 := (h1.mul (hD τ hτ)).sub ((hasDerivAt_id τ).const_mul C)
      refine (h2.congr_deriv ?_).hasDerivWithinAt
      ring
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ' := Ioo_subset_Icc_self hτ
      have e1 := (hexp τ hτ').1
      have hpos : 0 < exp (-L * τ) := exp_pos _
      have hb' : D τ - L * y τ ≤ |c| := by linarith [hb τ hτ, le_abs_self c]
      have h3 : exp (-L * τ) * (D τ - L * y τ) ≤ exp (-L * τ) * |c| :=
        mul_le_mul_of_nonneg_left hb' hpos.le
      have h4 : exp (-L * τ) * |c| ≤ exp (|L| * T) * |c| :=
        mul_le_mul_of_nonneg_right e1 (abs_nonneg c)
      change exp (-L * τ) * (D τ - L * y τ) - C ≤ 0
      rw [hC]
      linarith
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hg := hanti h0mem ht ht.1
  simp only [mul_zero, exp_zero, h0, sub_zero] at hg
  have hyt : y t = exp (L * t) * (exp (-L * t) * y t) := by
    rw [← mul_assoc, ← exp_add, show L * t + -L * t = 0 by ring, exp_zero, one_mul]
  rw [hyt]
  have e2 := (hexp t ht).2
  have hCt : C * t ≤ C * T := mul_le_mul_of_nonneg_left ht.2 hC0
  calc exp (L * t) * (exp (-L * t) * y t) ≤ exp (L * t) * (C * t) :=
        mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    _ ≤ exp (|L| * T) * (C * T) := mul_le_mul e2 hCt (mul_nonneg hC0 ht.1) (exp_pos _).le
    _ = exp (|L| * T) * exp (|L| * T) * T * |c| := by rw [hC]; ring

end PDE.Analysis
