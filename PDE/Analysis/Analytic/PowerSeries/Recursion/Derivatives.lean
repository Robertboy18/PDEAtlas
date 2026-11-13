/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Recursion

/-!
# Formal differential equations of arbitrary order

The coefficient of degree `n` of the right-hand side of an equation of order `k`
may depend on coefficients of the unknown through degree `n + k - 1`. Dividing
by the ascending factorial gives a strictly triangular coefficient recursion.
The coefficient ring may itself be a ring of formal spatial power series.
-/

@[expose] public section

namespace PowerSeries

variable {ι R : Type*} [CommRing R] [Algebra ℚ R]

/-- A time-causal formal differential system of order `k` has a unique solution
with prescribed coefficients below degree `k`. The data are coefficients,
rather than factorial-scaled derivatives. -/
theorem existsUnique_iterate_derivative_eq_of_coeff_depend_lt
    (k : ℕ) (F : (ι → PowerSeries R) → ι → PowerSeries R) (a : ι → Fin k → R)
    (hF : ∀ n u v,
      (∀ i j, j < n + k → coeff j (u i) = coeff j (v i)) →
        ∀ i, coeff n (F u i) = coeff n (F v i)) :
    ∃! u : ι → PowerSeries R,
      (∀ i (j : Fin k), coeff (j : ℕ) (u i) = a i j) ∧
        ∀ i, derivative^[k] (u i) = F u i := by
  classical
  let G (n : ℕ) (u : ι → PowerSeries R) (i : ι) : R :=
    if h : n < k then a i ⟨n, h⟩
    else ((n - k + 1).ascFactorial k : ℚ)⁻¹ • coeff (n - k) (F u i)
  have hG (n : ℕ) (u v : ι → PowerSeries R)
      (h : ∀ i j, j < n → coeff j (u i) = coeff j (v i)) : G n u = G n v := by
    funext i
    by_cases hn : n < k
    · simp only [G, dite_eq_left hn]
    · have hkn : k ≤ n := Nat.le_of_not_gt hn
      simp only [G, dite_eq_right hn]
      congr 1
      exact hF (n - k) u v
        (fun l j hj ↦ h l j (by simpa only [Nat.sub_add_cancel hkn] using hj)) i
  have hD (u : PowerSeries R) (n : ℕ) :
      coeff n (derivative^[k] u) =
        ((n + 1).ascFactorial k : ℚ) • coeff (n + k) u := by
    simpa only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using
      coeff_iterate_derivative u k n
  have hne (n : ℕ) : ((n + 1).ascFactorial k : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.ascFactorial_pos n k))
  have heq (u : ι → PowerSeries R) :
      (∀ n i, coeff n (u i) = G n u i) ↔
        (∀ i (j : Fin k), coeff (j : ℕ) (u i) = a i j) ∧
          ∀ i, derivative^[k] (u i) = F u i := by
    constructor
    · intro h
      refine ⟨fun i j ↦ ?_, fun i ↦ ?_⟩
      · simpa only [G, dite_eq_left j.isLt] using h (j : ℕ) i
      · apply ext
        intro n
        have hn : ¬ n + k < k := by omega
        have hGnk : G (n + k) u i =
            ((n + 1).ascFactorial k : ℚ)⁻¹ • coeff n (F u i) := by
          simp only [G, dite_eq_right hn, Nat.add_sub_cancel_right]
        rw [hD, h (n + k) i, hGnk, smul_smul, mul_inv_cancel₀ (hne n), one_smul]
    · rintro ⟨hdata, hderiv⟩ n i
      by_cases hn : n < k
      · simpa only [G, dite_eq_left hn] using hdata i ⟨n, hn⟩
      · have hkn : k ≤ n := Nat.le_of_not_gt hn
        have h := congrArg (coeff (n - k)) (hderiv i)
        rw [hD, Nat.sub_add_cancel hkn] at h
        have h := congrArg (((n - k + 1).ascFactorial k : ℚ)⁻¹ • ·) h
        simpa only [G, dite_eq_right hn, smul_smul, inv_mul_cancel₀ (hne (n - k)),
          one_smul] using h
  obtain ⟨u, hu, huniq⟩ := existsUnique_coeff_eq_of_depend_lt G hG
  exact ⟨u, (heq u).mp hu, fun v hv ↦ huniq v ((heq v).mpr hv)⟩

end PowerSeries
