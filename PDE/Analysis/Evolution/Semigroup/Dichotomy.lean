/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Basic
public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientWeighted

/-!
# Exponential dichotomy of a semigroup

Let `T` be a strongly continuous semigroup on a real normed space, `P` a projection commuting
with `T`, and `W` an operator commuting with `T` that inverts the time-one map on the range of
`P`: `T(1) W = P` and `P W = W`. Discrete bounds `‖T(1)ⁿ (1 - P)‖ ≤ M e^{ω n}` and
`‖Wⁿ P‖ ≤ M e^{-κ n}` then give an exponential dichotomy in continuous time.

* On the stable part, `‖T(t) (1 - P)‖ ≤ B M e^{ω t}` for `ω ≥ 0`, where `B` bounds the
  semigroup on `[0, 1]` (`norm_mul_le_of_norm_pow_mul_le`).
* On the range of `P` the semigroup extends to a group, `unstableGroup T W P t = T(t + n) Wⁿ P`
  for every natural `n ≥ -t`. It satisfies the group law, agrees with `T(t) P` at
  nonnegative times, decays like `e^{-κ r}` at time `-r` and is continuous in operator norm
  when `P` has finite rank.

A splitting of `S(1)` on a space `E` lifts to a space `F` with an injective lowering
`ι : F → E` intertwining `T` with `S` and a lift `G : E → F` of `S(1)`: the operators `G W₀ ι`
and `G W₀² ι` split `T(1)` with the same rates (`lift_splitting`). This transfers a spectral
splitting on `L²` to a Sobolev space through smoothing.

For a family `g` of operators from a second space into `E`, continued by `T` and with a
singular bound `C r^{-1/2} e^{ω_g r}`, the stable kernel `(1 - P) g(r) L` has the bound
`M r^{-1/2} e^{η r}` for every `η` above the stable rate, and the unstable kernel
`G(-r) Q` decays like `e^{-κ r}`. These are the kernels of the mixed ancient Duhamel operator.
An operator intertwining the time-one map with a power-bounded operator annihilates the range
of `P` (`mul_eq_zero_of_mul_eq_mul`). An eigenvector with eigenvalue `e^μ` gives the ancient
paths `τ ↦ e^{μτ} v`, represented with a weight `η ≤ μ` by `exponentialPath`.
-/

@[expose] public noncomputable section

open Set Filter Topology
open scoped NNReal BoundedContinuousFunction

/-- An idempotent `p` with `p w = w` absorbs the powers of `w` from both sides:
`p wⁿ p = wⁿ p`. -/
theorem IsIdempotentElem.mul_pow_mul_self_of_mul_eq {M : Type*} [Monoid M] {p w : M}
    (hp : IsIdempotentElem p) (hpw : p * w = w) (n : ℕ) : p * w ^ n * p = w ^ n * p := by
  cases n with
  | zero => rw [pow_zero, mul_one, one_mul, hp.eq]
  | succ n => rw [pow_succ', ← mul_assoc, hpw]

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a natural time the semigroup is the power of its time-one map. -/
theorem natCast_eq_pow (T : StronglyContinuousSemigroup E) (n : ℕ) : T n = T 1 ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero, pow_zero]; rfl
  | succ n ih => rw [Nat.cast_succ, map_add, ih, pow_succ]; rfl

/-- A discrete bound `‖T(1)ⁿ A‖ ≤ M e^{ω n}` with `ω ≥ 0` and a bound `B` of the semigroup on
`[0, 1]` give the continuous-time bound `‖T(t) A‖ ≤ B M e^{ω t}`. -/
theorem norm_mul_le_of_norm_pow_mul_le (T : StronglyContinuousSemigroup E) {A : E →L[ℝ] E}
    {B M ω : ℝ} (hω : 0 ≤ ω) (hB : ∀ s : ℝ≥0, s ≤ 1 → ‖T s‖ ≤ B)
    (hM : ∀ n : ℕ, ‖T 1 ^ n * A‖ ≤ M * Real.exp (ω * n)) (t : ℝ≥0) :
    ‖T t * A‖ ≤ B * M * Real.exp (ω * t) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 zero_le_one)
  have hM0 : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hM 0)
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  set n := ⌊t⌋₊
  have hnt : (n : ℝ≥0) ≤ t := Nat.floor_le t.2
  have hts : t - n ≤ 1 := by
    have := Nat.lt_floor_add_one t
    rw [tsub_le_iff_left]
    exact this.le
  have hsplit : T t = T (t - n) * T 1 ^ n := by
    rw [← natCast_eq_pow, ContinuousLinearMap.mul_def, ← map_add, tsub_add_cancel_of_le hnt]
  have hn : (n : ℝ) ≤ t := by exact_mod_cast hnt
  calc
    ‖T t * A‖ = ‖T (t - n) * (T 1 ^ n * A)‖ := by rw [hsplit, mul_assoc]
    _ ≤ ‖T (t - n)‖ * ‖T 1 ^ n * A‖ := norm_mul_le _ _
    _ ≤ B * (M * Real.exp (ω * n)) :=
      mul_le_mul (hB _ hts) (hM n) (norm_nonneg _) hB0
    _ ≤ B * (M * Real.exp (ω * t)) := by
      gcongr
    _ = B * M * Real.exp (ω * t) := by ring

/-! ### Extension to negative times on an invertible part -/

/-- The extension of a semigroup `T` to all real times on the range of a projection `P`, through
an operator `W` inverting `T(1)` there: `T(t + n) Wⁿ P` with `n = ⌈-t⌉₊`. -/
def unstableGroup (T : StronglyContinuousSemigroup E) (W P : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  T (t + ⌈-t⌉₊).toNNReal * W ^ ⌈-t⌉₊ * P

variable {T : StronglyContinuousSemigroup E} {W P : E →L[ℝ] E}

/-- At nonnegative times the extension is `T(t) P`. -/
theorem unstableGroup_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    unstableGroup T W P t = T t.toNNReal * P := by
  rw [unstableGroup, Nat.ceil_eq_zero.mpr (by linarith), Nat.cast_zero, add_zero, pow_zero,
    mul_one]

/-- One more power of `W` in `T(t + n) Wⁿ P` does not change it, for `n ≥ -t`. -/
theorem unstableGroup_succ (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W)
    {t : ℝ} {n : ℕ} (hn : -t ≤ n) :
    T (t + (n + 1 : ℕ)).toNNReal * W ^ (n + 1) * P = T (t + n).toNNReal * W ^ n * P := by
  have h0 : 0 ≤ t + n := by linarith
  have hsum : (t + (n + 1 : ℕ)).toNNReal = (t + n).toNNReal + 1 := by
    rw [Nat.cast_succ, ← add_assoc, Real.toNNReal_add h0 zero_le_one, Real.toNNReal_one]
  rw [hsum, map_add, ← ContinuousLinearMap.mul_def, pow_succ']
  calc
    T (t + n).toNNReal * T 1 * (W * W ^ n) * P = T (t + n).toNNReal * (T 1 * W) * W ^ n * P := by
      simp only [mul_assoc]
    _ = T (t + n).toNNReal * (P * W ^ n * P) := by rw [hTW]; simp only [mul_assoc]
    _ = T (t + n).toNNReal * W ^ n * P := by rw [hP.mul_pow_mul_self_of_mul_eq hPW, mul_assoc]

/-- The extension is `T(t + n) Wⁿ P` for every natural `n ≥ -t`. -/
theorem unstableGroup_eq (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W)
    {t : ℝ} {n : ℕ} (hn : -t ≤ n) :
    unstableGroup T W P t = T (t + n).toNNReal * W ^ n * P := by
  have hN : ⌈-t⌉₊ ≤ n := Nat.ceil_le.mpr hn
  induction n, hN using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    have hm' : -t ≤ m := (Nat.ceil_le.mp hm)
    rw [ih hm', unstableGroup_succ hP hTW hPW hm']

/-- The projection fixes the extension from the left. -/
theorem mul_unstableGroup_self (hP : IsIdempotentElem P) (hPW : P * W = W)
    (hcP : ∀ s, Commute (T s) P) (t : ℝ) :
    P * unstableGroup T W P t = unstableGroup T W P t := by
  rw [unstableGroup, ← mul_assoc, ← mul_assoc, (hcP _).eq.symm, mul_assoc, mul_assoc,
    ← mul_assoc P, hP.mul_pow_mul_self_of_mul_eq hPW, ← mul_assoc]

/-- The projection fixes the extension from the right. -/
theorem unstableGroup_mul_self (hP : IsIdempotentElem P) (t : ℝ) :
    unstableGroup T W P t * P = unstableGroup T W P t := by
  rw [unstableGroup, mul_assoc, hP.eq]

/-- The group law of the extension. -/
theorem unstableGroup_add (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W)
    (hcW : ∀ s, Commute (T s) W) (hcP : ∀ s, Commute (T s) P) (s t : ℝ) :
    unstableGroup T W P (s + t) = unstableGroup T W P s * unstableGroup T W P t := by
  set m := ⌈-s⌉₊
  set n := ⌈-t⌉₊
  have hm : -s ≤ m := Nat.le_ceil _
  have hn : -t ≤ n := Nat.le_ceil _
  have hmn : -(s + t) ≤ ((m + n : ℕ) : ℝ) := by push_cast; linarith
  have hcomm : Commute (T (t + n).toNNReal) (W ^ m * P) := ((hcW _).pow_right m).mul_right (hcP _)
  have hsum : (s + t + ((m + n : ℕ) : ℝ)).toNNReal = (s + m).toNNReal + (t + n).toNNReal := by
    rw [← Real.toNNReal_add (by linarith) (by linarith)]
    congr 1
    push_cast
    ring
  rw [unstableGroup_eq hP hTW hPW hmn, unstableGroup_eq hP hTW hPW hm,
    unstableGroup_eq hP hTW hPW hn, hsum, map_add, ← ContinuousLinearMap.mul_def, pow_add]
  calc
    T (s + m).toNNReal * T (t + n).toNNReal * (W ^ m * W ^ n) * P =
        T (s + m).toNNReal * T (t + n).toNNReal * W ^ m * (W ^ n * P) := by
      simp only [mul_assoc]
    _ = T (s + m).toNNReal * T (t + n).toNNReal * W ^ m * (P * W ^ n * P) := by
      rw [hP.mul_pow_mul_self_of_mul_eq hPW n]
    _ = T (s + m).toNNReal * (T (t + n).toNNReal * (W ^ m * P)) * (W ^ n * P) := by
      simp only [mul_assoc]
    _ = T (s + m).toNNReal * (W ^ m * P * T (t + n).toNNReal) * (W ^ n * P) := by
      rw [hcomm.eq]
    _ = T (s + m).toNNReal * W ^ m * P * (T (t + n).toNNReal * W ^ n * P) := by
      simp only [mul_assoc]

/-- The semigroup continues the extension: `T(a) G(t) = G(a + t)` for `a ≥ 0`. -/
theorem mul_unstableGroup (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W)
    (hcW : ∀ s, Commute (T s) W) (hcP : ∀ s, Commute (T s) P) (a : ℝ≥0) (t : ℝ) :
    T a * unstableGroup T W P t = unstableGroup T W P (a + t) := by
  rw [unstableGroup_add hP hTW hPW hcW hcP, unstableGroup_of_nonneg a.coe_nonneg, Real.toNNReal_coe,
    mul_assoc, mul_unstableGroup_self hP hPW hcP]

/-- A discrete bound `‖Wⁿ P‖ ≤ M e^{-κ n}` with `κ ≥ 0` and a bound `B` of the semigroup on
`[0, 1]` give `‖G(-r)‖ ≤ B M e^{-κ r}` for `r ≥ 0`. -/
theorem norm_unstableGroup_neg_le {B M κ : ℝ} (hκ : 0 ≤ κ)
    (hB : ∀ s : ℝ≥0, s ≤ 1 → ‖T s‖ ≤ B) (hM : ∀ n : ℕ, ‖W ^ n * P‖ ≤ M * Real.exp (-(κ * n)))
    {r : ℝ} (hr : 0 ≤ r) :
    ‖unstableGroup T W P (-r)‖ ≤ B * M * Real.exp (-(κ * r)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 zero_le_one)
  rw [unstableGroup, neg_neg]
  set N := ⌈r⌉₊
  have hN1 : (N : ℝ) < r + 1 := Nat.ceil_lt_add_one hr
  have hNr : r ≤ N := Nat.le_ceil r
  have hs : (-r + N).toNNReal ≤ 1 := by
    rw [Real.toNNReal_le_one]
    linarith
  calc
    ‖T (-r + N).toNNReal * W ^ N * P‖ ≤ ‖T (-r + N).toNNReal‖ * ‖W ^ N * P‖ := by
      rw [mul_assoc]; exact norm_mul_le _ _
    _ ≤ B * (M * Real.exp (-(κ * N))) := mul_le_mul (hB _ hs) (hM N) (norm_nonneg _) hB0
    _ ≤ B * (M * Real.exp (-(κ * r))) := by
      have hM0 : 0 ≤ M * Real.exp (-(κ * N)) := (norm_nonneg _).trans (hM N)
      have hM0' : 0 ≤ M := nonneg_of_mul_nonneg_left hM0 (Real.exp_pos _)
      gcongr
    _ = B * M * Real.exp (-(κ * r)) := by ring

/-- On a finite-dimensional range the extension is continuous in operator norm. -/
theorem continuous_unstableGroup [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W) :
    Continuous (unstableGroup T W P) := by
  rw [continuous_iff_continuousAt]
  intro t
  set n := ⌈-t⌉₊ + 1
  have htn : -t < n := by
    have := Nat.le_ceil (-t)
    push_cast [n]
    linarith
  set V := LinearMap.range P.toLinearMap
  have hmem : ∀ x, (W ^ n * P) x ∈ V := fun x ↦ ⟨(W ^ n * P) x, by
    exact congrArg (· x) (hP.mul_pow_mul_self_of_mul_eq hPW n)⟩
  set A : E →L[ℝ] V := (W ^ n * P).codRestrict V hmem
  have hA : W ^ n * P = V.subtypeL.comp A := by ext x; rfl
  have hcont : Continuous fun s : ℝ ↦ (T (s + n).toNNReal).comp V.subtypeL := by
    refine continuous_clm_apply.mpr fun y ↦ ?_
    exact (T.continuous_orbit (y : E)).comp
      (continuous_real_toNNReal.comp (continuous_id.add continuous_const))
  have heq : (fun s : ℝ ↦ ((T (s + n).toNNReal).comp V.subtypeL).comp A) =ᶠ[𝓝 t]
      unstableGroup T W P := by
    filter_upwards [lt_mem_nhds (show -(n : ℝ) < t by linarith)] with s hs
    rw [unstableGroup_eq hP hTW hPW (show -s ≤ n by linarith), mul_assoc, hA]
    rfl
  exact ((hcont.clm_comp_const A).continuousAt).congr heq

/-! ### Lifting a splitting by smoothing -/

section Lift

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : StronglyContinuousSemigroup E} {T : StronglyContinuousSemigroup F}
  {ι : F →L[ℝ] E} {G : E →L[ℝ] F} {P₀ W₀ : E →L[ℝ] E}

/-- Lowering the lifted projection: if `ι G = S(1)` and `S(1) W₀ = P₀`, then `ι G W₀ = P₀`. -/
theorem lower_liftProjection_apply (hιG : ∀ y, ι (G y) = S 1 y) (hTW₀ : S 1 * W₀ = P₀) (y : E) :
    ι (G (W₀ y)) = P₀ y := by
  rw [hιG]
  exact congrArg (fun A ↦ A y) hTW₀

/-- A splitting `(P₀, W₀)` of `S(1)` lifts to a splitting of `T(1)` through an injective lowering
`ι` intertwining `T` with `S` and a lift `G` of `S(1)`: `P = G W₀ ι` and `W = G W₀² ι` satisfy the
same algebraic relations, commute with `T`, have finite rank when `P₀` has, and obey discrete
bounds with the same rates. -/
theorem lift_splitting (hι : Function.Injective ι) (hιT : ∀ t x, ι (T t x) = S t (ι x))
    (hιG : ∀ y, ι (G y) = S 1 y) (hP₀ : IsIdempotentElem P₀)
    (hfin₀ : FiniteDimensional ℝ (LinearMap.range P₀.toLinearMap))
    (hcP₀ : ∀ t, Commute (S t) P₀) (hcW₀ : ∀ t, Commute (S t) W₀)
    (hTW₀ : S 1 * W₀ = P₀) (hPW₀ : P₀ * W₀ = W₀) {M ω' M' κ : ℝ} (hM : 0 ≤ M) (hω' : 0 ≤ ω')
    (hst : ∀ n : ℕ, ‖S 1 ^ n * (1 - P₀)‖ ≤ M * Real.exp (ω' * n))
    (hun : ∀ n : ℕ, ‖W₀ ^ n * P₀‖ ≤ M' * Real.exp (-(κ * n))) :
    IsIdempotentElem (G.comp (W₀.comp ι)) ∧ T 1 * G.comp ((W₀ * W₀).comp ι) = G.comp (W₀.comp ι) ∧
      G.comp (W₀.comp ι) * G.comp ((W₀ * W₀).comp ι) = G.comp ((W₀ * W₀).comp ι) ∧
      (∀ t, Commute (T t) (G.comp (W₀.comp ι))) ∧
      (∀ t, Commute (T t) (G.comp ((W₀ * W₀).comp ι))) ∧
      FiniteDimensional ℝ (LinearMap.range (G.comp (W₀.comp ι)).toLinearMap) ∧
      (∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ n : ℕ,
        ‖T 1 ^ n * (1 - G.comp (W₀.comp ι))‖ ≤ M₁ * Real.exp (ω' * n)) ∧
      ∃ M₁ : ℝ, ∀ n : ℕ,
        ‖G.comp ((W₀ * W₀).comp ι) ^ n * G.comp (W₀.comp ι)‖ ≤ M₁ * Real.exp (-(κ * n)) := by
  have hιP : ∀ y, ι (G (W₀ y)) = P₀ y := lower_liftProjection_apply hιG hTW₀
  have hιW : ∀ y, ι (G ((W₀ * W₀) y)) = W₀ y := fun y ↦
    (lower_liftProjection_apply hιG hTW₀ (W₀ y)).trans (congrArg (fun A ↦ A y) hPW₀)
  have hιpow : ∀ (n : ℕ) x, ι ((T 1 ^ n) x) = (S 1 ^ n) (ι x) := by
    intro n
    induction n with
    | zero => exact fun _ ↦ rfl
    | succ n ih => intro x; rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, hιT, ih]
  have hιWpow : ∀ (n : ℕ) x, ι ((G.comp ((W₀ * W₀).comp ι) ^ n) x) = (W₀ ^ n) (ι x) := by
    intro n
    induction n with
    | zero => exact fun _ ↦ rfl
    | succ n ih =>
      intro x
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp, ← ih]
      exact hιW _
  have hPW : ∀ y, P₀ (W₀ y) = W₀ y := fun y ↦ congrArg (· y) hPW₀
  refine ⟨?_, ?_, ?_, fun t ↦ ?_, fun t ↦ ?_, ?_, ?_, ?_⟩
  · exact ContinuousLinearMap.ext fun x ↦ hι <| by
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιP] using
        congrArg (· (ι x)) hP₀.eq
  · exact ContinuousLinearMap.ext fun x ↦ hι <| by
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιT, hιP, hPW] using
        congrArg (· (ι x)) hTW₀
  · exact ContinuousLinearMap.ext fun x ↦ hι <| by
      simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιP, hPW]
  · exact ContinuousLinearMap.ext fun x ↦ hι <| by
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιT, hιP] using
        congrArg (· (ι x)) (hcP₀ t).eq
  · exact ContinuousLinearMap.ext fun x ↦ hι <| by
      simpa only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, hιT, hιP, hPW] using
        congrArg (· (ι x)) (hcW₀ t).eq
  · have hle : LinearMap.range (G.comp (W₀.comp ι)).toLinearMap ≤
        (LinearMap.range P₀.toLinearMap).map G.toLinearMap := by
      rintro _ ⟨x, rfl⟩
      exact ⟨W₀ (ι x), ⟨W₀ (ι x), congrArg (fun A ↦ A (ι x)) hPW₀⟩, rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · refine ⟨‖1 - G.comp (W₀.comp ι)‖ + ‖G‖ * M * ‖ι‖, by positivity, fun n ↦ ?_⟩
    cases n with
    | zero =>
      rw [pow_zero, one_mul, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      exact le_add_of_nonneg_right (by positivity)
    | succ n =>
      have heq : T 1 ^ (n + 1) * (1 - G.comp (W₀.comp ι)) =
          G.comp ((S 1 ^ n * (1 - P₀)).comp ι) := by
        refine ContinuousLinearMap.ext fun x ↦ hι ?_
        change ι ((T 1 ^ (n + 1)) (x - G (W₀ (ι x)))) = ι (G ((S 1 ^ n) (ι x - P₀ (ι x))))
        rw [hιpow, map_sub, hιP, hιG, pow_succ']
        rfl
      rw [heq]
      calc ‖G.comp ((S 1 ^ n * (1 - P₀)).comp ι)‖
          ≤ ‖G‖ * (‖S 1 ^ n * (1 - P₀)‖ * ‖ι‖) :=
            (G.opNorm_comp_le _).trans (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ ‖G‖ * (M * Real.exp (ω' * ↑(n + 1)) * ‖ι‖) := by
          gcongr; exact (hst n).trans (by gcongr; exact_mod_cast n.le_succ)
        _ = ‖G‖ * M * ‖ι‖ * Real.exp (ω' * ↑(n + 1)) := by ring
        _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (norm_nonneg _)
  · refine ⟨‖G‖ * ‖W₀‖ * M' * ‖ι‖, fun n ↦ ?_⟩
    have heq : G.comp ((W₀ * W₀).comp ι) ^ n * G.comp (W₀.comp ι) =
        G.comp ((W₀ * (W₀ ^ n * P₀)).comp ι) := by
      refine ContinuousLinearMap.ext fun x ↦ hι ?_
      change ι ((G.comp ((W₀ * W₀).comp ι) ^ n) (G (W₀ (ι x)))) =
        ι (G (W₀ ((W₀ ^ n * P₀) (ι x))))
      rw [hιWpow, hιP, hιP]
      exact (congrArg (fun A ↦ A (ι x)) (hP₀.mul_pow_mul_self_of_mul_eq hPW₀ n)).symm
    rw [heq]
    calc ‖G.comp ((W₀ * (W₀ ^ n * P₀)).comp ι)‖
        ≤ ‖G‖ * (‖W₀ * (W₀ ^ n * P₀)‖ * ‖ι‖) :=
          (G.opNorm_comp_le _).trans (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖G‖ * (‖W₀‖ * (M' * Real.exp (-(κ * n))) * ‖ι‖) := by
        gcongr; exact (norm_mul_le _ _).trans (by gcongr; exact hun n)
      _ = _ := by ring

end Lift

end PDE.Analysis.Evolution.StronglyContinuousSemigroup

namespace PDE.Analysis.Evolution

open StronglyContinuousSemigroup

/-- For `δ > 0` and `r ≥ 1` the factor `√r` is absorbed by the exponential gap `δ`:
`e^{ω r} ≤ δ⁻¹ r^{-1/2} e^{(ω + δ) r}`. -/
theorem exp_mul_le_inv_mul_rpow_mul_exp {δ r : ℝ} (hδ : 0 < δ) (hr : 1 ≤ r) (ω : ℝ) :
    Real.exp (ω * r) ≤ δ⁻¹ * r ^ (-(1 / 2 : ℝ)) * Real.exp ((ω + δ) * r) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have h1 : r ^ (1 / 2 : ℝ) ≤ r := by
    calc r ^ (1 / 2 : ℝ) ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
      _ = r := Real.rpow_one r
  have h2 : δ * r ≤ Real.exp (δ * r) := by linarith [Real.add_one_le_exp (δ * r)]
  have hsq : 0 < r ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have h3 : 1 ≤ δ⁻¹ * (r ^ (1 / 2 : ℝ))⁻¹ * Real.exp (δ * r) := by
    rw [← mul_inv, inv_mul_eq_div, one_le_div (mul_pos hδ hsq)]
    calc δ * r ^ (1 / 2 : ℝ) ≤ δ * r := mul_le_mul_of_nonneg_left h1 hδ.le
      _ ≤ _ := h2
  rw [Real.rpow_neg hr0.le, add_mul, Real.exp_add]
  calc Real.exp (ω * r) = Real.exp (ω * r) * 1 := (mul_one _).symm
    _ ≤ Real.exp (ω * r) * (δ⁻¹ * (r ^ (1 / 2 : ℝ))⁻¹ * Real.exp (δ * r)) :=
      mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = _ := by ring

variable {E F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- **The unstable range is invisible to a power-bounded intertwined part.** Let `W` invert `A`
on the range of the idempotent `P`, with `‖Wⁿ P‖ ≤ M e^{-κ n}` and `κ > 0`. If `R A = F R` for
an operator `F` with `‖Fⁿ‖ ≤ 1`, then `R P = 0`. -/
theorem mul_eq_zero_of_mul_eq_mul {A F R W P : E →L[ℝ] E} (hP : IsIdempotentElem P)
    (hAW : A * W = P) (hPW : P * W = W) (hRA : R * A = F * R) (hF : ∀ n : ℕ, ‖F ^ n‖ ≤ 1)
    {M κ : ℝ} (hκ : 0 < κ) (hun : ∀ n : ℕ, ‖W ^ n * P‖ ≤ M * Real.exp (-(κ * n))) :
    R * P = 0 := by
  have hkey : ∀ n : ℕ, A ^ n * (W ^ n * P) = P := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, one_mul, one_mul]
    | succ n ih =>
      calc A ^ (n + 1) * (W ^ (n + 1) * P) = A ^ n * ((A * W) * W ^ n * P) := by
            rw [pow_succ, pow_succ']; simp only [mul_assoc]
        _ = A ^ n * (W ^ n * P) := by
            rw [hAW, hP.mul_pow_mul_self_of_mul_eq hPW n]
        _ = P := ih
  have hRA' : ∀ n : ℕ, R * A ^ n = F ^ n * R := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, mul_one, one_mul]
    | succ n ih =>
      rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, hRA, ← mul_assoc]
  have hbound : ∀ n : ℕ, ‖R * P‖ ≤ ‖R‖ * M * Real.exp (-(κ * n)) := by
    intro n
    calc ‖R * P‖ = ‖F ^ n * R * (W ^ n * P)‖ := by
          rw [← hRA', mul_assoc, hkey]
      _ ≤ ‖F ^ n‖ * ‖R‖ * ‖W ^ n * P‖ := (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ 1 * ‖R‖ * (M * Real.exp (-(κ * n))) := by gcongr; exacts [hF n, hun n]
      _ = ‖R‖ * M * Real.exp (-(κ * n)) := by ring
  have hlim : Tendsto (fun n : ℕ ↦ ‖R‖ * M * Real.exp (-(κ * n))) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ Real.exp (-(κ * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop hκ))
    simpa using h.const_mul (‖R‖ * M)
  exact norm_le_zero_iff.mp (ge_of_tendsto' hlim hbound)

/-! ### The stable kernel -/

section Stable

variable {T : StronglyContinuousSemigroup E} {P : E →L[ℝ] E} {g : ℝ → F₂ →L[ℝ] E}
  {L : F₂ →L[ℝ] F₂}

variable (P g L) in
/-- The stable kernel `(1 - P) g(r) L` of a family `g` of operators from `F₂` into `E`. -/
def stableKernel (r : ℝ) : F₂ →L[ℝ] E :=
  (1 - P).comp ((g r).comp L)

variable (P g L) in
/-- The stable kernel applied to a vector. -/
theorem stableKernel_apply (r : ℝ) (x : F₂) :
    stableKernel P g L r x = g r (L x) - P (g r (L x)) :=
  rfl

/-- An idempotent `P` annihilates the stable kernel. -/
theorem map_stableKernel (hP : IsIdempotentElem P) (r : ℝ) (x : F₂) :
    P (stableKernel P g L r x) = 0 := by
  rw [stableKernel_apply, map_sub, ← mul_apply_eq_comp P P, hP.eq, sub_self]

/-- The stable kernel acts jointly continuously at positive times when `g` does. -/
theorem continuousOn_stableKernel
    (hg : ContinuousOn (fun p : ℝ × F₂ ↦ g p.1 p.2) (Ioi 0 ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × F₂ ↦ stableKernel P g L p.1 p.2) (Ioi 0 ×ˢ univ) := by
  have hmap : Continuous (fun p : ℝ × F₂ ↦ (p.1, L p.2)) :=
    continuous_fst.prodMk (L.continuous.comp continuous_snd)
  have hcomp := hg.comp hmap.continuousOn
    (fun p (hp : p ∈ Ioi (0 : ℝ) ×ˢ (univ : Set F₂)) ↦ ⟨hp.1, mem_univ _⟩)
  exact (1 - P).continuous.comp_continuousOn hcomp

/-- If `P` commutes with `T` and `T(t) g(s) = g(t + s)`, the semigroup continues the stable
kernel. -/
theorem semigroup_stableKernel (hcP : ∀ t, Commute (T t) P)
    (hTg : ∀ (t : ℝ≥0) (s : ℝ), 0 < s → ∀ y, T t (g s y) = g (t + s) y) (t : ℝ≥0) {r : ℝ}
    (hr : 0 < r) (x : F₂) : T t (stableKernel P g L r x) = stableKernel P g L (t + r) x := by
  rw [stableKernel_apply, stableKernel_apply, ← hTg t r hr, map_sub]
  exact congrArg (_ - ·) (congrArg (fun A ↦ A (g r (L x))) (hcP t).eq)

/-- **Bound of the stable kernel.** If `‖T(t) (1 - P)‖ ≤ K e^{ω' t}` with `0 ≤ ω' < η`, and the
family `g` has the singular bound `C r^{-1/2} e^{ω_g r}` and is continued by `T`, then
`‖(1 - P) g(r) L‖ ≤ M r^{-1/2} e^{η r}` for all `r > 0`. -/
theorem exists_norm_stableKernel_le (hcP : ∀ t, Commute (T t) P)
    (hTg : ∀ (t : ℝ≥0) (s : ℝ), 0 < s → ∀ y, T t (g s y) = g (t + s) y) {K ω' η C ωg : ℝ}
    (hst : ∀ t : ℝ≥0, ‖T t * (1 - P)‖ ≤ K * Real.exp (ω' * t))
    (hgb : ∀ r, 0 < r → ‖g r‖ ≤ C * r ^ (-(1 / 2 : ℝ)) * Real.exp (ωg * r))
    (hω' : 0 ≤ ω') (hω'η : ω' < η) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r, 0 < r →
      ‖stableKernel P g L r‖ ≤ M * r ^ (-(1 / 2 : ℝ)) * Real.exp (η * r) := by
  have hK : 0 ≤ K := by
    have h := (norm_nonneg _).trans (hst 0)
    rwa [NNReal.coe_zero, mul_zero, Real.exp_zero, mul_one] at h
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hgb 1 one_pos)
    rw [Real.one_rpow, mul_one] at h
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  have hη : 0 < η := hω'.trans_lt hω'η
  have hδ : 0 < η - ω' := sub_pos.mpr hω'η
  refine ⟨‖1 - P‖ * C * Real.exp |ωg| * ‖L‖ + K * ‖g 1‖ * ‖L‖ * (η - ω')⁻¹,
    by positivity, fun r hr ↦ ?_⟩
  have hrp : 0 < r ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hr _
  rcases lt_or_ge r 1 with hr1 | hr1
  · have hexp : Real.exp (ωg * r) ≤ Real.exp |ωg| := Real.exp_le_exp.mpr <| by
      linarith [mul_le_mul_of_nonneg_right (le_abs_self ωg) hr.le,
        mul_le_mul_of_nonneg_left hr1.le (abs_nonneg ωg)]
    calc ‖stableKernel P g L r‖ ≤ ‖1 - P‖ * (‖g r‖ * ‖L‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (by gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖1 - P‖ * (C * r ^ (-(1 / 2 : ℝ)) * Real.exp |ωg| * ‖L‖) := by
          gcongr; exact (hgb r hr).trans (by gcongr)
      _ = ‖1 - P‖ * C * Real.exp |ωg| * ‖L‖ * r ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ ‖1 - P‖ * C * Real.exp |ωg| * ‖L‖ * r ^ (-(1 / 2 : ℝ)) * Real.exp (η * r) :=
          le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (by positivity)
  · set t : ℝ≥0 := (r - 1).toNNReal with ht
    have htr : (t : ℝ) = r - 1 := Real.coe_toNNReal _ (by linarith)
    have hsplit : stableKernel P g L r = (T t * (1 - P)).comp ((g 1).comp L) := by
      refine ContinuousLinearMap.ext fun x ↦ ?_
      have h := semigroup_stableKernel (L := L) hcP hTg t one_pos x
      rw [htr, sub_add_cancel] at h
      rw [← h]
      rfl
    calc ‖stableKernel P g L r‖ ≤ ‖T t * (1 - P)‖ * ‖(g 1).comp L‖ := by
          rw [hsplit]; exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * Real.exp (ω' * (r - 1)) * (‖g 1‖ * ‖L‖) := by
          rw [← htr]; gcongr; exacts [hst t, ContinuousLinearMap.opNorm_comp_le _ _]
      _ = K * ‖g 1‖ * ‖L‖ * Real.exp (ω' * (r - 1)) := by ring
      _ ≤ K * ‖g 1‖ * ‖L‖ * Real.exp (ω' * r) := by gcongr; linarith
      _ ≤ K * ‖g 1‖ * ‖L‖ * ((η - ω')⁻¹ * r ^ (-(1 / 2 : ℝ)) * Real.exp ((ω' + (η - ω')) * r)) := by
          gcongr
          exact exp_mul_le_inv_mul_rpow_mul_exp hδ hr1 ω'
      _ = K * ‖g 1‖ * ‖L‖ * (η - ω')⁻¹ * r ^ (-(1 / 2 : ℝ)) * Real.exp (η * r) := by
          rw [add_sub_cancel]; ring
      _ ≤ _ := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)

end Stable

/-! ### The unstable kernel -/

section Unstable

variable {T : StronglyContinuousSemigroup E} {W P : E →L[ℝ] E} {Q : F₂ →L[ℝ] E}

variable (T W P Q) in
/-- The unstable kernel `G(-r) Q`, with `G = unstableGroup T W P` the extension of `T` to
negative times on the range of `P`. -/
def unstableKernel (r : ℝ) : F₂ →L[ℝ] E :=
  (T.unstableGroup W P (-r)).comp Q

variable (T W P Q) in
/-- The unstable kernel applied to a vector. -/
theorem unstableKernel_apply (r : ℝ) (x : F₂) :
    unstableKernel T W P Q r x = T.unstableGroup W P (-r) (Q x) :=
  rfl

/-- On a finite-dimensional range the unstable kernel is continuous in operator norm. -/
theorem continuous_unstableKernel [FiniteDimensional ℝ (LinearMap.range P.toLinearMap)]
    (hP : IsIdempotentElem P) (hTW : T 1 * W = P) (hPW : P * W = W) :
    Continuous (unstableKernel T W P Q) :=
  ((continuous_unstableGroup hP hTW hPW).comp continuous_neg).clm_comp_const Q

/-- The unstable kernel decays at positive times with the rate of `Wⁿ P`. -/
theorem norm_unstableKernel_le {B M κ : ℝ} (hκ : 0 ≤ κ)
    (hB : ∀ s : ℝ≥0, s ≤ 1 → ‖T s‖ ≤ B) (hM : ∀ n : ℕ, ‖W ^ n * P‖ ≤ M * Real.exp (-(κ * n)))
    {r : ℝ} (hr : 0 ≤ r) :
    ‖unstableKernel T W P Q r‖ ≤ B * M * ‖Q‖ * Real.exp (-(κ * r)) := by
  calc ‖unstableKernel T W P Q r‖ ≤ ‖T.unstableGroup W P (-r)‖ * ‖Q‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * M * Real.exp (-(κ * r)) * ‖Q‖ := by
        gcongr
        exact norm_unstableGroup_neg_le hκ hB hM hr
    _ = _ := by ring

/-- The semigroup shifts the unstable kernel: `T(t) Ku(r) = Ku(r - t)`. -/
theorem semigroup_unstableKernel (hP : IsIdempotentElem P) (hTW : T 1 * W = P)
    (hPW : P * W = W) (hcW : ∀ s, Commute (T s) W) (hcP : ∀ s, Commute (T s) P) (t : ℝ≥0)
    (r : ℝ) (x : F₂) : T t (unstableKernel T W P Q r x) = unstableKernel T W P Q (r - t) x := by
  rw [unstableKernel_apply, unstableKernel_apply, ← mul_apply_eq_comp,
    mul_unstableGroup hP hTW hPW hcW hcP, show (t : ℝ) + -r = -(r - t) by ring]

/-- The projection fixes the unstable kernel. -/
theorem map_unstableKernel (hP : IsIdempotentElem P) (hPW : P * W = W)
    (hcP : ∀ s, Commute (T s) P) (r : ℝ) (x : F₂) :
    P (unstableKernel T W P Q r x) = unstableKernel T W P Q r x := by
  rw [unstableKernel_apply, ← mul_apply_eq_comp, mul_unstableGroup_self hP hPW hcP]

/-- At negative times the unstable kernel is the forward evolution of `P Q`. -/
theorem unstableKernel_neg {r : ℝ} (hr : 0 ≤ r) (x : F₂) :
    unstableKernel T W P Q (-r) x = T r.toNNReal (P (Q x)) := by
  rw [unstableKernel_apply, neg_neg, unstableGroup_of_nonneg hr]
  rfl

end Unstable

/-! ### Exponential ancient paths -/

section ExponentialPath

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {μ η : ℝ}

/-- The exponential path `τ ↦ e^{(μ - η) τ} v` on `(-∞, 0]`, bounded for `η ≤ μ`. With the
weight `η` it represents the ancient path `τ ↦ e^{μ τ} v`. -/
def exponentialPath (h : η ≤ μ) (v : F) : Iic (0 : ℝ) →ᵇ F :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun τ : Iic (0 : ℝ) ↦ Real.exp ((μ - η) * τ) • v)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_subtype_val)).smul
      continuous_const) ‖v‖ fun τ ↦ by
      rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) τ.2

/-- With the weight `η`, the exponential path decodes to `τ ↦ e^{μτ} v`. -/
theorem ancientLift_exponentialPath (h : η ≤ μ) (v : F) {τ : ℝ} (hτ : τ ≤ 0) :
    ancientLift η (exponentialPath h v) τ = Real.exp (μ * τ) • v := by
  change Real.exp (η * τ) • (Real.exp ((μ - η) * min τ 0) • v) = _
  rw [min_eq_left hτ, smul_smul, ← Real.exp_add]
  congr 2
  ring

/-- The exponential path has the terminal value `v`. -/
theorem exponentialPath_zero (h : η ≤ μ) (v : F) : exponentialPath h v ⟨0, self_mem_Iic⟩ = v := by
  change Real.exp ((μ - η) * 0) • v = v
  rw [mul_zero, Real.exp_zero, one_smul]

/-- The exponential path has norm at most `‖v‖`. -/
theorem norm_exponentialPath_le (h : η ≤ μ) (v : F) : ‖exponentialPath h v‖ ≤ ‖v‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

end ExponentialPath

end PDE.Analysis.Evolution
