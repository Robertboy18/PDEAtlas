/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Algebra.Order.Floor.Semiring
public import PDE.Analysis.Evolution.Semigroup.Basic
public import PDE.Analysis.Calculus.StrongOperator

/-!
# From a local semigroup to a semigroup

Perturbation arguments often build a semigroup on a short time interval `[0, α]` first, where a
smallness condition holds; the Dyson–Phillips construction of a perturbed semigroup
(`StronglyContinuousSemigroup.IsComplexLinear.perturbed`) is one. A family `S` with `S(0) = 1`
and `S(s + t) = S(s) S(t)` for `s, t ≥ 0` with `s + t ≤ α` extends to all times by
`U(t) = S(t / n)ⁿ`, for any `n ≥ 1` with `t / n ≤ α`. For operators, the extension of a bounded,
strongly continuous local semigroup is strongly continuous. The extension is the only one,
since every semigroup that agrees with `S` on `[0, α]` is `S(t / n)ⁿ` at `t`; this uniqueness is
not stated separately.

## Main results

* `extendLocal`, with `extendLocal_eq_pow`, `extendLocal_of_le`, `extendLocal_zero` and
  `extendLocal_add`: the extension of a local one-parameter semigroup in any monoid, its value
  `S(t / n)ⁿ`, its agreement with `S` on `[0, α]`, and its semigroup law.
* `map_natCast_mul_eq_pow_of_le`: `S(m a) = S(a)ᵐ` as long as `m a ≤ α`, the local form of
  `map_natCast_mul_eq_pow`.
* `continuous_extendLocal_apply`: the extension of a uniformly bounded, strongly continuous
  local semigroup of operators is strongly continuous.

## How it works

The local law gives `S(m a) = S(a)ᵐ` when `m a ≤ α`, so
`S(t / n)ⁿ = S(t / (n m))^{n m} = S(t / m)ᵐ`: the value does not depend on `n`. For two times `s`
and `t` one `n` serves `s`, `t` and `s + t`, and `S((s + t) / n) = S(s / n) S(t / n)` with
commuting factors, so `U(s + t) = U(s) U(t)`. All of this is algebra in a monoid. For operators,
strong continuity passes to powers of a bounded family (`continuous_family_pow_apply`), and
near a time `t₀` one `n` serves a whole neighbourhood. `continuous_extendLocal_apply` asks for
the bound and the strong continuity on the whole line, which is how the Dyson–Phillips family
is built, although only `[0, α]` matters.
-/

@[expose] public noncomputable section

open Filter Topology

namespace PDE.Analysis.Evolution

section Monoid

variable {M : Type*} [Monoid M] {S : ℝ → M} {α : ℝ}

/-- **The extension of a local semigroup**: `S(t / n)ⁿ` with `n = ⌈t / α⌉ + 1`, for a family
`S` that is a one-parameter semigroup on `[0, α]`. -/
def extendLocal (S : ℝ → M) (α : ℝ) (t : NNReal) : M :=
  S ((t : ℝ) / ((⌈(t : ℝ) / α⌉₊ + 1 : ℕ) : ℝ)) ^ (⌈(t : ℝ) / α⌉₊ + 1)

/-- The step `t / (⌈t / α⌉ + 1)` is at most `α`. -/
private theorem div_natCeil_add_one_le (hα : 0 < α) (t : ℝ) :
    t / ((⌈t / α⌉₊ + 1 : ℕ) : ℝ) ≤ α := by
  rw [div_le_iff₀ (by positivity)]
  have h2 := (div_le_iff₀ hα).mp (Nat.le_ceil (t / α))
  push_cast
  nlinarith

variable (hS0 : S 0 = 1)
  (hSadd : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ α → S (s + t) = S s * S t)

include hS0 hSadd

/-- A local semigroup at a multiple of `a` is a power of its value at `a`, as long as the
multiple stays in `[0, α]`. -/
theorem map_natCast_mul_eq_pow_of_le {a : ℝ} (ha : 0 ≤ a) (m : ℕ) (h : (m : ℝ) * a ≤ α) :
    S (m * a) = S a ^ m := by
  induction m with
  | zero => rw [Nat.cast_zero, zero_mul, hS0, pow_zero]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul] at h ⊢
    rw [hSadd _ _ (by positivity) ha h, ih (by linarith), pow_succ]

/-- The value `S(t / n)ⁿ` does not depend on `n`, as long as `t / n ≤ α`. -/
theorem pow_div_eq_pow_div {t : ℝ} (ht : 0 ≤ t) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnα : t / n ≤ α) (hmα : t / m ≤ α) : S (t / n) ^ n = S (t / m) ^ m := by
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hm' : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have ha : 0 ≤ t / (n * m) := by positivity
  have e1 : (m : ℝ) * (t / (n * m)) = t / n := by field_simp
  have e2 : (n : ℝ) * (t / (n * m)) = t / m := by field_simp
  have h1 := map_natCast_mul_eq_pow_of_le hS0 hSadd ha m (by rw [e1]; exact hnα)
  have h2 := map_natCast_mul_eq_pow_of_le hS0 hSadd ha n (by rw [e2]; exact hmα)
  rw [e1] at h1
  rw [e2] at h2
  rw [h1, h2, ← pow_mul, ← pow_mul, Nat.mul_comm m n]

variable (hα : 0 < α)

include hα

/-- The extension is `S(t / n)ⁿ` for every `n ≥ 1` with `t / n ≤ α`. -/
theorem extendLocal_eq_pow {t : NNReal} {n : ℕ} (hn : 0 < n) (h : (t : ℝ) / n ≤ α) :
    extendLocal S α t = S ((t : ℝ) / n) ^ n :=
  pow_div_eq_pow_div hS0 hSadd t.coe_nonneg (Nat.succ_pos _) hn
    (div_natCeil_add_one_le hα t) h

/-- On `[0, α]` the extension is the local semigroup. -/
theorem extendLocal_of_le {t : NNReal} (ht : (t : ℝ) ≤ α) : extendLocal S α t = S t := by
  rw [extendLocal_eq_pow hS0 hSadd hα one_pos (by simpa using ht)]
  simp

/-- The extension is the identity at time zero. -/
theorem extendLocal_zero : extendLocal S α 0 = 1 := by
  rw [extendLocal_of_le hS0 hSadd hα (by simpa using hα.le), NNReal.coe_zero, hS0]

/-- **The semigroup law of the extension**: `U(s + t) = U(s) U(t)` for all `s, t ≥ 0`. -/
theorem extendLocal_add (s t : NNReal) :
    extendLocal S α (s + t) = extendLocal S α s * extendLocal S α t := by
  obtain ⟨n, hn, hnα⟩ : ∃ n : ℕ, 0 < n ∧ ((s + t : NNReal) : ℝ) / n ≤ α :=
    ⟨_, Nat.succ_pos _, div_natCeil_add_one_le hα _⟩
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e : ((s + t : NNReal) : ℝ) / n = (s : ℝ) / n + (t : ℝ) / n := by
    rw [NNReal.coe_add, add_div]
  have hs0 : 0 ≤ (s : ℝ) / n := div_nonneg s.coe_nonneg hn'
  have ht0 : 0 ≤ (t : ℝ) / n := div_nonneg t.coe_nonneg hn'
  have hsum : (s : ℝ) / n + (t : ℝ) / n ≤ α := e ▸ hnα
  have hst := hSadd _ _ hs0 ht0 hsum
  have hts := hSadd _ _ ht0 hs0 (by rwa [add_comm])
  have hc : Commute (S ((s : ℝ) / n)) (S ((t : ℝ) / n)) := by
    rw [Commute, SemiconjBy, ← hst, ← hts, add_comm]
  rw [extendLocal_eq_pow hS0 hSadd hα hn hnα, extendLocal_eq_pow hS0 hSadd hα hn (by linarith),
    extendLocal_eq_pow hS0 hSadd hα hn (by linarith), e, hst, hc.mul_pow]

end Monoid

section Operator

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {S : ℝ → X →L[𝕜] X} {α N : ℝ}

/-- **The extension of a strongly continuous local semigroup is strongly continuous.** Let `S`
be a uniformly bounded, strongly continuous family of operators that is a one-parameter
semigroup on `[0, α]`. Then `t ↦ U(t) y` is continuous on `[0, ∞)` for every `y`: near a time
`t₀` the extension is `S(t / n)ⁿ` with one `n`. -/
theorem continuous_extendLocal_apply (hS0 : S 0 = 1)
    (hSadd : ∀ s t, 0 ≤ s → 0 ≤ t → s + t ≤ α → S (s + t) = S s * S t) (hα : 0 < α)
    (hb : ∀ r, ‖S r‖ ≤ N) (hc : ∀ y, Continuous fun r ↦ S r y) (y : X) :
    Continuous fun t : NNReal ↦ extendLocal S α t y := by
  refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
  obtain ⟨n, hn, hnα⟩ : ∃ n : ℕ, 0 < n ∧ ((t₀ : ℝ) + 1) / n ≤ α :=
    ⟨_, Nat.succ_pos _, div_natCeil_add_one_le hα _⟩
  have hopen : IsOpen {t : NNReal | (t : ℝ) < t₀ + 1} :=
    isOpen_lt NNReal.continuous_coe continuous_const
  have hcont : Continuous fun t : NNReal ↦ (S ((t : ℝ) / n) ^ n) y :=
    (continuous_family_pow_apply hb hc n).comp
      ((NNReal.continuous_coe.div_const _).prodMk continuous_const)
  refine hcont.continuousAt.congr ?_
  filter_upwards [hopen.mem_nhds (by simp : (t₀ : ℝ) < t₀ + 1)] with t ht
  rw [extendLocal_eq_pow hS0 hSadd hα hn
    ((div_le_div_of_nonneg_right (le_of_lt ht) (Nat.cast_nonneg n)).trans hnα)]

end Operator

end PDE.Analysis.Evolution
