/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.EntropyGluing
public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm

/-!
# Profiles and entropy inequalities in finite Riemann gluing

In each separated speed window the finite gluing equals that window's
elementary wave. The other contributions telescope through the preceding
constant states. Thus statements about the elementary profiles apply
pointwise to the assembled solution.

Entropy inequalities also pass through finite gluing, by the
two-wave theorem. This step assumes the inequality for each component.
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m n : ℕ}

/-- Inside a wave's half-open speed window the finite assembly is exactly
that wave. This is a pointwise identity, including its left interface. -/
theorem sum_waves_eq_of_mem_window (state : ℕ → ℝ^m) (wave : Fin n → ℝ^2 → ℝ^m) (a b : Fin n → ℝ)
    (hseparated : ∀ i j : Fin n, i < j → b i ≤ a j)
    (hleft : ∀ k p, 0 < p 0 → p 1 < a k * p 0 → wave k p = state k)
    (hright : ∀ k p, 0 < p 0 → b k * p 0 ≤ p 1 → wave k p = state (k + 1)) (k : Fin n) {p : ℝ^2}
    (ht : 0 < p 0) (ha : a k * p 0 ≤ p 1) (hb : p 1 < b k * p 0) :
    state 0 + ∑ i : Fin n, (wave i p - state i) = wave k p := by
  let values : ℕ → ℝ^m := fun i ↦ if i ≤ k.val then state i else wave k p
  have hterm (i : Fin n) : wave i p - state i = values (i + 1) - values i := by
    rcases lt_trichotomy i k with hik | hik | hik
    · have hir : wave i p = state (i + 1) :=
        hright i p ht ((mul_le_mul_of_nonneg_right (hseparated i k hik) ht.le).trans ha)
      have hi : i.val < k.val := hik
      simp only [values, ite_eq_left (Nat.le_of_lt hi), ite_eq_left (Nat.succ_le_of_lt hi), hir]
    · subst i
      simp [values]
    · have hil : wave i p = state i :=
        hleft i p ht (hb.trans_le (mul_le_mul_of_nonneg_right (hseparated k i hik) ht.le))
      have hi : k.val < i.val := hik
      simp only [values, ite_eq_right (not_le.mpr hi),
        ite_eq_right (not_le.mpr (hi.trans (Nat.lt_succ_self _))), hil, sub_self]
  have hzero : values 0 = state 0 := by simp [values]
  have hlast : values n = wave k p := by simp [values, not_le.mpr k.is_lt]
  rw [← hzero]
  simp_rw [hterm]
  rw [← Finset.sum_range (fun i ↦ values (i + 1) - values i), Finset.sum_range_sub, hlast]
  abel

/-- Finitely many separated component inequalities give the same inequality
for their finite-sum assembly. The empty family gives the constant state. -/
theorem satisfiesEntropyInequalityFor_sum_waves {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (state : ℕ → ℝ^m) (wave : Fin n → ℝ^2 → ℝ^m) (a b : Fin n → ℝ)
    (hseparated : ∀ i j : Fin n, i < j → b i ≤ a j)
    (hentropy : ∀ k, SatisfiesEntropyInequalityFor forwardHalfSpace (wave k) E)
    (hleft : ∀ k p, 0 < p 0 → p 1 < a k * p 0 → wave k p = state k)
    (hright : ∀ k p, 0 < p 0 → b k * p 0 ≤ p 1 → wave k p = state (k + 1)) :
    SatisfiesEntropyInequalityFor forwardHalfSpace
      (fun p ↦ state 0 + ∑ k : Fin n, (wave k p - state k)) E := by
  induction n with
  | zero => simpa using satisfiesEntropyInequalityFor_const E forwardHalfSpace (state 0)
  | succ n ih =>
    let v : ℝ^2 → ℝ^m := fun p ↦ state 0 + ∑ i : Fin n, (wave i.castSucc p - state i)
    have hv : SatisfiesEntropyInequalityFor forwardHalfSpace v E :=
      ih (fun i ↦ wave i.castSucc) (fun i ↦ a i.castSucc) (fun i ↦ b i.castSucc)
        (fun i j hij ↦ hseparated i.castSucc j.castSucc hij) (fun i ↦ hentropy i.castSucc)
        (fun i ↦ hleft i.castSucc) (fun i ↦ hright i.castSucc)
    have hcommon : ∀ p ∈ forwardHalfSpace, v p = state n ∨ wave (Fin.last n) p = state n := by
      intro p hp
      by_cases hx : p 1 < a (Fin.last n) * p 0
      · exact Or.inr (hleft (Fin.last n) p hp hx)
      · left
        have hright' (i : Fin n) : wave i.castSucc p = state (i + 1) :=
          hright i.castSucc p hp ((mul_le_mul_of_nonneg_right
            (hseparated i.castSucc (Fin.last n) (Fin.castSucc_lt_last i)) hp.le).trans
              (le_of_not_gt hx))
        simp only [v, hright']
        rw [← Finset.sum_range (fun i ↦ state (i + 1) - state i), Finset.sum_range_sub]
        abel
    have hglue := hv.glue_at_common_state (hentropy (Fin.last n)) hcommon
    convert hglue using 1
    funext p
    simp only [glueAtCommonState, v, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    abel

/-- A separated finite assembly satisfies every convex entropy inequality
when every component does. -/
theorem satisfiesEntropyInequality_sum_waves {flux : ℝ^m → ℝ^m} (state : ℕ → ℝ^m)
    (wave : Fin n → ℝ^2 → ℝ^m) (a b : Fin n → ℝ) (hseparated : ∀ i j : Fin n, i < j → b i ≤ a j)
    (hentropy : ∀ k, SatisfiesEntropyInequality flux forwardHalfSpace (wave k))
    (hleft : ∀ k p, 0 < p 0 → p 1 < a k * p 0 → wave k p = state k)
    (hright : ∀ k p, 0 < p 0 → b k * p 0 ≤ p 1 → wave k p = state (k + 1)) :
    SatisfiesEntropyInequality flux forwardHalfSpace
      (fun p ↦ state 0 + ∑ k : Fin n, (wave k p - state k)) :=
  fun E ↦ satisfiesEntropyInequalityFor_sum_waves E.toEntropyPair state wave a b
    hseparated (fun k ↦ hentropy k E) hleft hright

end PDE.Hyperbolic.ConservationLaw.System
