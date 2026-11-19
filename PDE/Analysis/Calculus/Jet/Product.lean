/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The leading difference in a product jet

When two coefficients have equal jets and two factors agree below the top
order, Leibniz's formula leaves only the coefficient times the top difference.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

namespace PDE

/-- Equal coefficient jets cancel every lower term in the product rule. -/
theorem iteratedDeriv_mul_sub_eq_of_jet_eq
    {n : ℕ} {a b f g : 𝕜 → 𝕜} {x : 𝕜}
    (ha : ContDiffAt 𝕜 n a x) (hb : ContDiffAt 𝕜 n b x)
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hab : ∀ i ≤ n, iteratedDeriv i a x = iteratedDeriv i b x)
    (hfg : ∀ i < n, iteratedDeriv i f x = iteratedDeriv i g x) :
    iteratedDeriv n (a * f) x - iteratedDeriv n (b * g) x =
      a x * (iteratedDeriv n f x - iteratedDeriv n g x) := by
  rw [iteratedDeriv_mul ha hf, iteratedDeriv_mul hb hg, ← Finset.sum_sub_distrib]
  have hzero : a x = b x := hab 0 (Nat.zero_le n)
  calc
    _ = (n.choose 0 : 𝕜) * iteratedDeriv 0 a x * iteratedDeriv (n - 0) f x -
        (n.choose 0 : 𝕜) * iteratedDeriv 0 b x * iteratedDeriv (n - 0) g x := by
      apply Finset.sum_eq_single 0
      · intro i hi hi0
        have hin : i ≤ n := by simpa using hi
        rw [hab i hin, hfg (n - i) (by omega), sub_self]
      · simp
    _ = _ := by simp [hzero, mul_sub]

end PDE
