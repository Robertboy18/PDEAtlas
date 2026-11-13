/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Nonautonomous.Lipschitz

/-!
# Invertible fundamental solutions in Banach algebras

For a coefficient `B : ℝ → A` in a normed real algebra, `FundamentalSolution B t₀ times`
consists of a forward path `Φ' = B Φ` and an inverse path `Ψ' = -Ψ B` on the time
domain `times`, both equal to `1` at `t₀`, with `Φ(t) Ψ(t) = Ψ(t) Φ(t) = 1`. Its
propagator `U(t, s) = Φ(t) Ψ(s)` satisfies `U(t, t) = 1`, `U(t, s) U(s, r) = U(t, r)`
and `∂ₜ U(t, s) = B(t) U(t, s)`.

In a Banach algebra, a continuous bounded coefficient has a fundamental solution on
the whole line through any initial time. The construction solves two globally
Lipschitz equations, and differentiation and ODE uniqueness prove both inverse
identities. `A` need not be finite-dimensional. Extending a continuous coefficient
on `[a, b]` by its endpoint values supplies the bounded coefficient required by the
construction.
-/

@[expose] public noncomputable section

open Function Set
open scoped NNReal

namespace PDE.Analysis.Evolution

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- A fundamental path and its inverse for `Φ' = B Φ` on a time domain.

On a closed interval the derivatives are relative to the interval, so the two
endpoints require only one-sided derivatives. Omitting the domain gives the
usual whole-line fundamental solution. -/
structure FundamentalSolution (B : ℝ → A) (t₀ : ℝ) (times : Set ℝ := univ) where
  /-- Forward path from the identity. -/
  forward : ℝ → A
  /-- Inverse path, solving `Ψ' = -Ψ B`. -/
  backward : ℝ → A
  /-- Initial value of the forward path. -/
  forward_initial : forward t₀ = 1
  /-- Initial value of the inverse path. -/
  backward_initial : backward t₀ = 1
  /-- Forward equation within the time domain. -/
  forward_hasDerivWithinAt :
    ∀ t ∈ times, HasDerivWithinAt forward (B t * forward t) times t
  /-- Inverse equation within the time domain. -/
  backward_hasDerivWithinAt :
    ∀ t ∈ times, HasDerivWithinAt backward (-(backward t * B t)) times t
  /-- Right inverse identity. -/
  forward_mul_backward : ∀ t ∈ times, forward t * backward t = 1
  /-- Left inverse identity. -/
  backward_mul_forward : ∀ t ∈ times, backward t * forward t = 1

/-- A continuous coefficient with `‖B t‖ ≤ K` for all `t` has a fundamental solution on
the whole real line through `1` at any initial time `t₀`. -/
theorem nonempty_fundamentalSolution [CompleteSpace A] {B : ℝ → A} (hB : Continuous B)
    {K : ℝ≥0} (hbound : ∀ t, ‖B t‖ ≤ K) (t₀ : ℝ) :
    Nonempty (FundamentalSolution B t₀) := by
  have hLipL (t : ℝ) : LipschitzWith K (fun x : A ↦ B t * x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm, ← mul_sub]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg _))
  have hLipR (t : ℝ) : LipschitzWith K (fun x : A ↦ -(x * B t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_neg_neg, dist_eq_norm, dist_eq_norm, ← sub_mul]
    exact (norm_mul_le _ _).trans
      ((mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)).trans_eq (mul_comm _ _))
  obtain ⟨Φ, hΦ₀, hΦ⟩ := exists_eq_hasDerivAt_of_lipschitz
    ((hB.comp continuous_fst).mul continuous_snd) hLipL t₀ 1
  obtain ⟨Ψ, hΨ₀, hΨ⟩ := exists_eq_hasDerivAt_of_lipschitz
    (continuous_snd.mul (hB.comp continuous_fst)).neg hLipR t₀ 1
  have hback : (fun t ↦ Ψ t * Φ t) = fun _ ↦ (1 : A) := by
    apply ODE_solution_unique_univ
      (v := fun _ _ ↦ (0 : A)) (s := fun _ ↦ univ)
      (fun _ ↦ (LipschitzWith.const 0).lipschitzOnWith)
    · intro t
      refine ⟨?_, mem_univ _⟩
      convert! (hΨ t).mul (hΦ t) using 1
      simp only [neg_mul, mul_assoc, neg_add_cancel]
    · exact fun t ↦ ⟨hasDerivAt_const t 1, mem_univ _⟩
    · rw [hΨ₀, hΦ₀, one_mul]
  have hLipC (t : ℝ) :
      LipschitzWith (K + K) (fun x : A ↦ B t * x - x * B t) := by
    simpa only [sub_eq_add_neg] using (hLipL t).add (hLipR t)
  have hfront : (fun t ↦ Φ t * Ψ t) = fun _ ↦ (1 : A) := by
    apply ODE_solution_unique_univ
      (v := fun t x ↦ B t * x - x * B t) (s := fun _ ↦ univ)
      (fun t ↦ (hLipC t).lipschitzOnWith)
    · intro t
      refine ⟨?_, mem_univ _⟩
      convert! (hΦ t).mul (hΨ t) using 1
      simp only [mul_neg, mul_assoc, sub_eq_add_neg]
    · intro t
      refine ⟨?_, mem_univ _⟩
      simpa only [mul_one, one_mul, sub_self] using hasDerivAt_const t (1 : A)
    · rw [hΦ₀, hΨ₀, one_mul]
  exact ⟨⟨Φ, Ψ, hΦ₀, hΨ₀, fun t _ ↦ (hΦ t).hasDerivWithinAt,
    fun t _ ↦ (hΨ t).hasDerivWithinAt,
    fun t _ ↦ congrFun hfront t, fun t _ ↦ congrFun hback t⟩⟩

/-- Construct inverse fundamental paths for a coefficient known only on a compact interval.
Outside the interval the coefficient is clamped to its endpoint values. -/
def fundamentalSolutionOn [CompleteSpace A] {a b : ℝ} (B : C(Icc a b, A)) (t₀ : Icc a b) :
    FundamentalSolution (IccExtend (t₀.2.1.trans t₀.2.2) B) t₀ :=
  Classical.choice (nonempty_fundamentalSolution
    (B.continuous.Icc_extend' (h := t₀.2.1.trans t₀.2.2))
    (K := ‖B‖₊) (fun _ ↦ B.norm_coe_le_norm _) t₀)

namespace FundamentalSolution

variable {B : ℝ → A} {t₀ : ℝ} {times : Set ℝ}

/-- The forward path is continuous relative to its time domain. -/
theorem continuousOn_forward (S : FundamentalSolution B t₀ times) :
    ContinuousOn S.forward times :=
  fun t ht ↦ (S.forward_hasDerivWithinAt t ht).continuousWithinAt

/-- The inverse path is continuous relative to its time domain. -/
theorem continuousOn_backward (S : FundamentalSolution B t₀ times) :
    ContinuousOn S.backward times :=
  fun t ht ↦ (S.backward_hasDerivWithinAt t ht).continuousWithinAt

/-- Restrict a fundamental solution to a smaller time domain. -/
def restrict (S : FundamentalSolution B t₀ times) {s : Set ℝ} (hs : s ⊆ times) :
    FundamentalSolution B t₀ s where
  forward := S.forward
  backward := S.backward
  forward_initial := S.forward_initial
  backward_initial := S.backward_initial
  forward_hasDerivWithinAt := fun t ht ↦ (S.forward_hasDerivWithinAt t (hs ht)).mono hs
  backward_hasDerivWithinAt := fun t ht ↦ (S.backward_hasDerivWithinAt t (hs ht)).mono hs
  forward_mul_backward := fun t ht ↦ S.forward_mul_backward t (hs ht)
  backward_mul_forward := fun t ht ↦ S.backward_mul_forward t (hs ht)

/-- Changing a coefficient outside the time domain does not change its fundamental paths. -/
def congr (S : FundamentalSolution B t₀ times) {C : ℝ → A} (hBC : EqOn B C times) :
    FundamentalSolution C t₀ times where
  forward := S.forward
  backward := S.backward
  forward_initial := S.forward_initial
  backward_initial := S.backward_initial
  forward_hasDerivWithinAt := fun t ht ↦ hBC ht ▸ S.forward_hasDerivWithinAt t ht
  backward_hasDerivWithinAt := fun t ht ↦ hBC ht ▸ S.backward_hasDerivWithinAt t ht
  forward_mul_backward := S.forward_mul_backward
  backward_mul_forward := S.backward_mul_forward

/-- The two-time evolution carries data at `s` to time `t`. -/
def propagator (S : FundamentalSolution B t₀ times) (t s : ℝ) : A :=
  S.forward t * S.backward s

/-- Evolution for zero elapsed time is the identity at every time in the domain. -/
theorem propagator_self_of_mem (S : FundamentalSolution B t₀ times) {t : ℝ}
    (ht : t ∈ times) : S.propagator t t = 1 :=
  S.forward_mul_backward t ht

/-- Evolution composes through any intermediate time in the domain. -/
theorem propagator_mul_of_mem (S : FundamentalSolution B t₀ times) (t r : ℝ) {s : ℝ}
    (hs : s ∈ times) :
    S.propagator t s * S.propagator s r = S.propagator t r := by
  simp only [propagator, mul_assoc, ← mul_assoc (S.backward s),
    S.backward_mul_forward s hs, one_mul]

/-- The propagator solves the homogeneous equation with the domain's endpoint convention. -/
theorem hasDerivWithinAt_propagator (S : FundamentalSolution B t₀ times) {t : ℝ}
    (ht : t ∈ times) (s : ℝ) :
    HasDerivWithinAt (fun r ↦ S.propagator r s) (B t * S.propagator t s) times t := by
  simpa only [propagator, mul_assoc] using
    (S.forward_hasDerivWithinAt t ht).mul_const (S.backward s)

variable {B : ℝ → A} {t₀ : ℝ} (S : FundamentalSolution B t₀)

/-- On the whole real line, the forward equation uses ordinary derivatives. -/
theorem forward_derivative (t : ℝ) : HasDerivAt S.forward (B t * S.forward t) t :=
  (S.forward_hasDerivWithinAt t (mem_univ t)).hasDerivAt (by simp)

/-- On the whole real line, the inverse equation uses ordinary derivatives. -/
theorem backward_derivative (t : ℝ) :
    HasDerivAt S.backward (-(S.backward t * B t)) t :=
  (S.backward_hasDerivWithinAt t (mem_univ t)).hasDerivAt (by simp)

/-- The forward and backward paths are right inverses at every real time. -/
theorem forward_backward (t : ℝ) : S.forward t * S.backward t = 1 :=
  S.forward_mul_backward t (mem_univ t)

/-- The forward and backward paths are left inverses at every real time. -/
theorem backward_forward (t : ℝ) : S.backward t * S.forward t = 1 :=
  S.backward_mul_forward t (mem_univ t)

/-- The forward fundamental path is continuous. -/
theorem continuous_forward : Continuous S.forward :=
  continuous_iff_continuousAt.mpr fun t ↦ (S.forward_derivative t).continuousAt

/-- The inverse fundamental path is continuous. -/
theorem continuous_backward : Continuous S.backward :=
  continuous_iff_continuousAt.mpr fun t ↦ (S.backward_derivative t).continuousAt

/-- Evolution for zero elapsed time is the identity. -/
@[simp] theorem propagator_self (t : ℝ) : S.propagator t t = 1 :=
  S.forward_backward t

/-- Evolution composes at any intermediate time, in either time direction. -/
theorem propagator_mul (t s r : ℝ) :
    S.propagator t s * S.propagator s r = S.propagator t r := by
  simp only [propagator, mul_assoc, ← mul_assoc (S.backward s),
    S.backward_forward, one_mul]

/-- Joint continuity of the two-time evolution in the Banach-algebra norm. -/
theorem continuous_propagator : Continuous (fun ts : ℝ × ℝ ↦ S.propagator ts.1 ts.2) :=
  (S.continuous_forward.comp continuous_fst).mul
    (S.continuous_backward.comp continuous_snd)

/-- The propagator solves the homogeneous equation in its final time. -/
theorem hasDerivAt_propagator (t s : ℝ) :
    HasDerivAt (fun t ↦ S.propagator t s) (B t * S.propagator t s) t := by
  simpa only [propagator, mul_assoc] using
    (S.forward_derivative t).mul_const (S.backward s)

end FundamentalSolution

end PDE.Analysis.Evolution
