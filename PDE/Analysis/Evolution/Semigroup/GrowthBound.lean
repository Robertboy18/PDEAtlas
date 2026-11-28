/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Basic
public import PDE.Analysis.Evolution.Semigroup.Basic

/-!
# The growth bound of a semigroup

Every strongly continuous semigroup on a Banach space is exponentially bounded,
`‖T(t)‖ ≤ M e^{ωt}`. The infimum of the admissible rates `ω` is the growth bound `ω₀(T)`, the
number that the spectral bound and the essential growth bound of the generator are compared
with. This module proves the exponential bound, defines `ω₀(T)` in `[-∞, ∞]` and characterizes
`ω₀(T) < ω`. The formula `ω₀(T) = lim log ‖T(t)‖ / t` is not proved here.

## Main results

* `map_natCast_mul_eq_pow`: `U(n t₀) = U(t₀)ⁿ` for a one-parameter semigroup `U` in any monoid.
* `norm_map_mul_le_of_norm_pow_mul_le`: for a one-parameter semigroup `U` in a seminormed ring
  and any element `a`, a bound `‖U(t₀)ⁿ a‖ ≤ C ρⁿ` at the multiples of `t₀ > 0` and a bound `B`
  of `U` on `[0, t₀]` give `‖U(t) a‖ ≤ B C max(1, ρ⁻¹) e^{ωt}` at all times, with
  `ω = log ρ / t₀`.
* `StronglyContinuousSemigroup.exists_norm_le_exp`: every strongly continuous semigroup on a
  real Banach space satisfies `‖T(t)‖ ≤ M e^{ωt}` for some `M` and `ω`.
* `StronglyContinuousSemigroup.growthBound`, with `growthBound_lt_iff` and
  `growthBound_lt_top`.

`StronglyContinuousSemigroup.natCast_eq_pow` and
`StronglyContinuousSemigroup.norm_mul_le_of_norm_pow_mul_le` are the case `t₀ = 1`,
`ρ = e^ω`, `ω ≥ 0` of the first two results, and they are proved from them.

## How it works

Write `t = n t₀ + s` with `0 ≤ s ≤ t₀`. The semigroup law gives `U(t) a = U(s) (U(t₀)ⁿ a)`, so
`‖U(t) a‖ ≤ B C ρⁿ`, and `ρⁿ = e^{ωt} e^{-ωs} ≤ max(1, ρ⁻¹) e^{ωt}`. Only the monoid law and the
norm enter, so one statement serves the real operators of a semigroup, its complex-linear
operators, and products `U(t) a` with a fixed projection `a`. With `a = 1`, `t₀ = 1` and the
bound on `[0, 1]` from the uniform boundedness principle
(`StronglyContinuousSemigroup.exists_norm_le_on_Icc`) it gives the exponential bound.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Graduate Texts in Mathematics 194, Springer, 2000, Chapter I, Section 5 (exponential
  boundedness and the growth bound of a strongly continuous semigroup).
  <https://doi.org/10.1007/b97696>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Evolution

/-- At a multiple of `t₀`, a one-parameter semigroup in a monoid is a power of its value at
`t₀`: `U(n t₀) = U(t₀)ⁿ`. Mathlib's `AddChar.map_nsmul_eq_pow` is the same fact for a bundled
additive character; here `U` is a plain function with the two laws as hypotheses. -/
theorem map_natCast_mul_eq_pow {M : Type*} [Monoid M] {U : NNReal → M} (hU0 : U 0 = 1)
    (hUadd : ∀ s t, U (s + t) = U s * U t) (n : ℕ) (t₀ : NNReal) : U (n * t₀) = U t₀ ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, hU0, pow_zero]
  | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hUadd, ih, pow_succ]

/-- **From discrete to continuous time.** Let `U` be a one-parameter semigroup in a seminormed
ring with `‖U(s)‖ ≤ B` for `0 ≤ s ≤ t₀`. A bound `‖U(t₀)ⁿ a‖ ≤ C ρⁿ` at the multiples of `t₀ > 0`
gives `‖U(t) a‖ ≤ B C max(1, ρ⁻¹) e^{ωt}` at all times, with `ω = log ρ / t₀`. The proof writes
`t = n t₀ + s` with `0 ≤ s ≤ t₀`; then `ρⁿ = e^{ωt} e^{-ωs}` and `e^{-ωs} ≤ max(1, ρ⁻¹)`. -/
theorem norm_map_mul_le_of_norm_pow_mul_le {𝔸 : Type*} [SeminormedRing 𝔸] {U : NNReal → 𝔸}
    (hU0 : U 0 = 1) (hUadd : ∀ s t, U (s + t) = U s * U t) {t₀ : NNReal} (ht₀ : 0 < t₀) {B : ℝ}
    (hB : ∀ s ≤ t₀, ‖U s‖ ≤ B) {a : 𝔸} {C ρ : ℝ} (hρ : 0 < ρ)
    (hC : ∀ n : ℕ, ‖U t₀ ^ n * a‖ ≤ C * ρ ^ n) (t : NNReal) :
    ‖U t * a‖ ≤ B * C * max 1 ρ⁻¹ * Real.exp (Real.log ρ / t₀ * t) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 zero_le)
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = Real.log ρ / t₀ := ⟨_, rfl⟩
  rw [← hω]
  have hωt₀ : ω * t₀ = Real.log ρ := by rw [hω, div_mul_cancel₀ _ ht₀'.ne']
  -- split `t = n t₀ + s` with `s ≤ t₀`
  obtain ⟨n, s, hs, rfl⟩ : ∃ (n : ℕ) (s : NNReal), s ≤ t₀ ∧ t = n * t₀ + s := by
    refine ⟨⌊t / t₀⌋₊, t - ⌊t / t₀⌋₊ * t₀, ?_, ?_⟩
    · rw [tsub_le_iff_left, ← add_one_mul]
      exact ((div_lt_iff₀ ht₀).mp (Nat.lt_floor_add_one _)).le
    · exact (add_tsub_cancel_of_le ((le_div_iff₀ ht₀).mp (Nat.floor_le zero_le))).symm
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ t₀ := hs
  have hsmall : Real.exp (-(ω * s)) ≤ max 1 ρ⁻¹ := by
    rcases le_or_gt 0 ω with h0 | h0
    · have := mul_nonneg h0 hs0
      exact (Real.exp_le_one_iff.mpr (by linarith)).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      rw [← Real.exp_log (inv_pos.mpr hρ), Real.log_inv, ← hωt₀]
      have := mul_le_mul_of_nonpos_left hs1 h0.le
      exact Real.exp_le_exp.mpr (by linarith)
  have hexp : ρ ^ n ≤ max 1 ρ⁻¹ * Real.exp (ω * ((n * t₀ + s : NNReal) : ℝ)) := by
    have e : ρ ^ n = Real.exp (-(ω * s)) * Real.exp (ω * ((n * t₀ + s : NNReal) : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_log hρ, ← Real.exp_nat_mul, ← hωt₀, NNReal.coe_add,
        NNReal.coe_mul, NNReal.coe_natCast]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hsmall (Real.exp_nonneg _)
  calc ‖U (n * t₀ + s) * a‖ = ‖U s * (U t₀ ^ n * a)‖ := by
        rw [add_comm, hUadd, map_natCast_mul_eq_pow hU0 hUadd, mul_assoc]
    _ ≤ B * (C * ρ ^ n) :=
        (norm_mul_le _ _).trans (mul_le_mul (hB s hs) (hC n) (norm_nonneg _) hB0)
    _ ≤ B * (C * (max 1 ρ⁻¹ * Real.exp (ω * ((n * t₀ + s : NNReal) : ℝ)))) := by
        gcongr
    _ = B * C * max 1 ρ⁻¹ * Real.exp (ω * ((n * t₀ + s : NNReal) : ℝ)) := by ring

namespace StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : StronglyContinuousSemigroup E)

/-- **Every strongly continuous semigroup on a Banach space is exponentially bounded**:
`‖T(t)‖ ≤ M e^{ωt}` for some `M` and `ω` and all `t ≥ 0`. The semigroup is bounded on `[0, 1]`
by the uniform boundedness principle, and `norm_map_mul_le_of_norm_pow_mul_le` passes from the
integers to all times. -/
theorem exists_norm_le_exp [CompleteSpace E] :
    ∃ M ω : ℝ, ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t) := by
  obtain ⟨B, -, hB⟩ := T.exists_norm_le_on_Icc 1
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = max B 1 := ⟨_, rfl⟩
  have hρ1 : 1 ≤ ρ := hρdef ▸ le_max_right _ _
  have hρ : 0 < ρ := zero_lt_one.trans_le hρ1
  have hT1 : ‖T 1‖ ≤ ρ := (hB 1 ⟨zero_le, le_rfl⟩).trans (hρdef ▸ le_max_left _ _)
  have hC : ∀ n : ℕ, ‖T 1 ^ n * (1 : E →L[ℝ] E)‖ ≤ 1 * ρ ^ n := fun n ↦ by
    rw [mul_one, one_mul]
    induction n with
    | zero =>
      rw [pow_zero, pow_zero]
      exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hT1 (norm_nonneg _) (pow_nonneg hρ.le n))
  refine ⟨B * 1 * max 1 ρ⁻¹, Real.log ρ / ((1 : NNReal) : ℝ), fun t ↦ ?_⟩
  have h := norm_map_mul_le_of_norm_pow_mul_le (U := fun t ↦ T t) T.map_zero T.map_add
    zero_lt_one
    (fun s hs ↦ hB s ⟨zero_le, hs⟩) hρ hC t
  rwa [mul_one (T t)] at h

/-- **The growth bound** `ω₀(T)` of a semigroup: the infimum, in `[-∞, ∞]`, of the `ω` such that
`‖T(t)‖ ≤ M e^{ωt}` for some `M` and all `t ≥ 0`. -/
def growthBound : EReal :=
  sInf ((fun ω : ℝ ↦ (ω : EReal)) '' {ω | ∃ M : ℝ, ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)})

variable {T}

/-- A rate of an exponential bound is at least the growth bound. -/
theorem growthBound_le_of_norm_le {M ω : ℝ} (hM : ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω * t)) :
    T.growthBound ≤ ω :=
  sInf_le ⟨ω, ⟨M, hM⟩, rfl⟩

/-- `ω₀(T) < ω` exactly when `‖T(t)‖ ≤ M e^{ω't}` for some `M` and some rate `ω' < ω`. -/
theorem growthBound_lt_iff {ω : ℝ} :
    T.growthBound < ω ↔
      ∃ M ω' : ℝ, ω' < ω ∧ ∀ t : NNReal, ‖T t‖ ≤ M * Real.exp (ω' * t) := by
  constructor
  · intro h
    obtain ⟨_, ⟨ω', ⟨M, hM⟩, rfl⟩, hlt⟩ := sInf_lt_iff.mp h
    exact ⟨M, ω', EReal.coe_lt_coe_iff.mp hlt, hM⟩
  · rintro ⟨M, ω', hω', hM⟩
    exact (growthBound_le_of_norm_le hM).trans_lt (EReal.coe_lt_coe_iff.mpr hω')

variable (T) in
/-- The growth bound of a semigroup on a Banach space is not `+∞`. -/
theorem growthBound_lt_top [CompleteSpace E] : T.growthBound < ⊤ := by
  obtain ⟨M, ω, hM⟩ := T.exists_norm_le_exp
  exact (growthBound_le_of_norm_le hM).trans_lt (EReal.coe_lt_top ω)

end StronglyContinuousSemigroup

end PDE.Analysis.Evolution
