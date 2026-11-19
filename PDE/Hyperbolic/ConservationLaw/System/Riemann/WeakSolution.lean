/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.WeakGluing
public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm

/-!
# Finite assembly of separated elementary waves

Ordered speed intervals make adjacent wave profiles agree with their common
state outside disjoint wedges. Inductively applying the nonlinear
gluing theorem constructs a weak solution. At every positive-time point the
assembled value is one of the elementary values, so a common norm bound is
preserved without a factor depending on the number of waves.

For elementary waves this is the last step of the proof of Evans, §11.2.4, Theorem 4: each
wave is constant outside its sector of speeds, the sectors are ordered and do not intersect,
and together the waves give the solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.4, step 4 of the proof of Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Assemble finitely many ordered waves. The zero-wave case is the constant
initial state. The outer-state conclusions are expressed for every common
lower or upper speed bound, allowing a uniform propagation cone to be chosen
before the Riemann data. The last identity records the finite gluing,
including its values outside the positive-time domain. -/
theorem exists_weakSolution_of_separated_waves {m n : ℕ} {flux : ℝ^m → ℝ^m} (state : ℕ → ℝ^m)
    (wave : Fin n → ℝ^2 → ℝ^m) (a b : Fin n → ℝ) {K : ℝ} (hstate : ‖state 0‖ ≤ K)
    (hseparated : ∀ i j : Fin n, i < j → b i ≤ a j)
    (hweak : ∀ k, IsWeakSolution flux forwardHalfSpace (wave k)) (hmeas : ∀ k, Measurable (wave k))
    (hbound : ∀ k p, 0 < p 0 → ‖wave k p‖ ≤ K)
    (hscale : ∀ k (c : ℝ), 0 < c → ∀ p, wave k (c • p) = wave k p)
    (hleft : ∀ k p, 0 < p 0 → p 1 < a k * p 0 → wave k p = state k)
    (hright : ∀ k p, 0 < p 0 → b k * p 0 ≤ p 1 → wave k p = state (k + 1)) :
    ∃ u : ℝ^2 → ℝ^m,
      IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧
      (∀ c : ℝ, (∀ k, c ≤ a k) →
        ∀ p : ℝ^2, 0 < p 0 → p 1 < c * p 0 → u p = state 0) ∧
      (∀ c : ℝ, (∀ k, b k ≤ c) →
        ∀ p : ℝ^2, 0 < p 0 → c * p 0 ≤ p 1 → u p = state n) ∧
      (∀ p, u p = state 0 + ∑ k : Fin n, (wave k p - state k)) := by
  have hprefix : ∀ j : ℕ, j ≤ n → ∃ u : ℝ^2 → ℝ^m,
        IsWeakSolution flux forwardHalfSpace u ∧ Measurable u ∧ (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
        (∀ c : ℝ, 0 < c → ∀ p, u (c • p) = u p) ∧ (∀ c : ℝ, (∀ k : Fin n, k.val < j → c ≤ a k) →
          ∀ p : ℝ^2, 0 < p 0 → p 1 < c * p 0 → u p = state 0) ∧
        (∀ c : ℝ, (∀ k : Fin n, k.val < j → b k ≤ c) →
          ∀ p : ℝ^2, 0 < p 0 → c * p 0 ≤ p 1 → u p = state j) ∧ (∀ p, u p = state 0 +
          ∑ k : Fin n, if k.val < j then wave k p - state k else 0) := by
    intro j hj
    induction j with
    | zero =>
      exact ⟨fun _ ↦ state 0, isWeakSolution_const forwardHalfSpace (state 0),
        measurable_const, fun _ _ ↦ hstate, fun _ _ _ ↦ rfl,
        fun _ _ _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ rfl, fun _ ↦ by simp⟩
    | succ j ih =>
      obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hformula⟩ := ih (Nat.le_of_succ_le hj)
      let k : Fin n := ⟨j, Nat.lt_of_succ_le hj⟩
      have hcommon : ∀ p ∈ forwardHalfSpace, u p = state j ∨ wave k p = state j :=
        fun p hp ↦ (lt_or_ge (p 1) (a k * p 0)).elim (fun hx ↦ .inr (hleft k p hp hx))
          fun hx ↦ .inl (hru (a k) (fun i hi ↦ hseparated i k hi) p hp hx)
      refine ⟨glueAtCommonState (state j) u (wave k), hu.glue_at_common_state (hweak k) hcommon,
        (hmu.add (hmeas k)).sub measurable_const, fun p hp ↦ ?_, fun c hc p ↦ ?_,
        fun c hc p hp hx ↦ ?_, fun c hc p hp hx ↦ ?_, fun p ↦ ?_⟩
      · rcases hcommon p hp with h | h
        · simpa only [glueAtCommonState, h, add_sub_cancel_left] using hbound k p hp
        · simpa only [glueAtCommonState, h, add_sub_cancel_right] using hbu p hp
      · simp only [glueAtCommonState, hsu c hc p, hscale k c hc p]
      · simp only [glueAtCommonState, hlu c (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi)) p hp hx,
          hleft k p hp (hx.trans_le (mul_le_mul_of_nonneg_right (hc k (Nat.lt_succ_self j)) hp.le)),
          k, add_sub_cancel_right]
      · simp only [glueAtCommonState, hru c (fun i hi ↦ hc i (Nat.lt_succ_of_lt hi)) p hp hx,
          hright k p hp ((mul_le_mul_of_nonneg_right (hc k (Nat.lt_succ_self j)) hp.le).trans hx),
          k, add_sub_cancel_left]
      · have hterm (i : Fin n) : (if i.val < j + 1 then wave i p - state i else 0) =
              (if i.val < j then wave i p - state i else 0) +
                (if i = k then wave k p - state j else 0) := by
          obtain rfl | hik := eq_or_ne i k
          · simp [k]
          · simp only [Nat.lt_succ_iff_lt_or_eq, show (i : ℕ) ≠ j from fun h ↦ hik (Fin.ext h),
              or_false, hik, ↓reduceIte, add_zero]
        simp_rw [hterm]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, glueAtCommonState, hformula]
        abel
  obtain ⟨u, hu, hmu, hbu, hsu, hlu, hru, hformula⟩ := hprefix n le_rfl
  exact ⟨u, hu, hmu, hbu, hsu, fun c hc ↦ hlu c (fun k _ ↦ hc k), fun c hc ↦ hru c (fun k _ ↦ hc k),
    fun p ↦ by simpa only [Fin.is_lt, ite_true] using hformula p⟩

end PDE.Hyperbolic.ConservationLaw.System
