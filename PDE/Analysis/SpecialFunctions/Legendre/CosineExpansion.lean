/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Legendre.CosineSeries
public import PDE.Analysis.SpecialFunctions.Legendre.VectorHarmonics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Legendre polynomials of `cos θ` as cosine series

A finite cosine series `S(θ) = ∑ⱼ aⱼ cos (kⱼ θ)` whose terms satisfy the weighted spherical
angular equation `(sin θ S')' + n (n + 1) sin θ S = 0` (the residuals `cosineModeResidual` sum to
zero) is `S(0) P_n (cos θ)` (`cosineSeries_eq_mul_legendre`): by the Chebyshev identity
`cos (k θ) = T_k (cos θ)` the series is a polynomial `Q` in `cos θ`, the angular equation becomes
the Legendre equation for `Q`, and its polynomial solutions are the multiples `Q (1) P_n`.

The coefficients `evenCosineCoefficient` and `oddCosineCoefficient` of `CosineSeries` satisfy
the angular equation, so `P_{2N} (cos θ)` and `P_{2N+1} (cos θ)` are their cosine series divided by
the value at `θ = 0` (`legendre_eval_cos_even`, `legendre_eval_cos_odd`, `zonalHarmonic_even_eq`,
`zonalHarmonic_odd_eq`). The coefficients are positive (`sum_evenCosineCoefficient_pos`,
`sum_oddCosineCoefficient_pos`), so products of zonal harmonics integrate against trigonometric
modes by sums of positive terms without cancellation.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

open CAS.Analysis.SpecialFunctions
open Polynomial Real
open scoped BigOperators

/-- A cosine series solving the weighted spherical angular equation with eigenvalue `n (n + 1)` is
`S(0) P_n (cos θ)`. -/
theorem cosineSeries_eq_mul_legendre {n K : ℕ} (a : ℕ → ℝ) (k : ℕ → ℕ)
    (hres : ∀ θ : ℝ, ∑ j ∈ Finset.range (K + 1),
      PDE.Analysis.cosineModeResidual ((n : ℝ) * (n + 1)) (a j) (k j) θ = 0) (θ : ℝ) :
    ∑ j ∈ Finset.range (K + 1), a j * Real.cos (k j * θ) =
      (∑ j ∈ Finset.range (K + 1), a j) * (legendre n).eval (Real.cos θ) := by
  set Q : ℝ[X] := ∑ j ∈ Finset.range (K + 1), C (a j) * Chebyshev.T ℝ (k j : ℤ) with hQdef
  set S : ℝ → ℝ := fun t ↦ ∑ j ∈ Finset.range (K + 1), a j * Real.cos (k j * t) with hSdef
  set Tf : ℝ → ℝ := fun t ↦ ∑ j ∈ Finset.range (K + 1), a j * k j * Real.sin (k j * t)
    with hTdef
  have hQ (t : ℝ) : Q.eval (Real.cos t) = S t := by
    simp only [hQdef, hSdef, eval_finsetSum, eval_mul, eval_C, Chebyshev.T_real_cos]
    push_cast
    rfl
  have hS (t : ℝ) : HasDerivAt S (-Tf t) t := by
    have h := HasDerivAt.sum (u := Finset.range (K + 1)) fun j _ ↦
      (((hasDerivAt_id t).const_mul (k j : ℝ)).cos.const_mul (a j))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · simp only [hTdef, id, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    · simp only [hSdef, id, Finset.sum_apply]
  have hQ' (t : ℝ) : Q.derivative.eval (Real.cos t) * Real.sin t = Tf t :=
    PDE.Analysis.derivative_eval_cos_mul_sin hQ (hS t)
  have hTf (t : ℝ) : HasDerivAt Tf
      (∑ j ∈ Finset.range (K + 1), a j * k j * (k j * Real.cos (k j * t))) t := by
    have h := HasDerivAt.sum (u := Finset.range (K + 1)) fun j _ ↦
      (((hasDerivAt_id t).const_mul (k j : ℝ)).sin.const_mul (a j * k j))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [id]
      ring
    · simp only [hTdef, id, Finset.sum_apply]
  have hflux (θ : ℝ) : HasDerivAt (fun t ↦ Real.sin t ^ 2 * Q.derivative.eval (Real.cos t))
      ((n : ℝ) * (n + 1) * Real.sin θ * Q.eval (Real.cos θ)) θ := by
    have hfun : (fun t ↦ Real.sin t ^ 2 * Q.derivative.eval (Real.cos t)) =
        fun t ↦ Real.sin t * Tf t := by
      funext t
      rw [← hQ' t]
      ring
    rw [hfun]
    refine ((Real.hasDerivAt_sin θ).mul (hTf θ)).congr_deriv ?_
    have h := hres θ
    rw [hQ θ]
    have e : (n : ℝ) * (n + 1) * Real.sin θ * S θ - (Real.cos θ * Tf θ + Real.sin θ *
        ∑ j ∈ Finset.range (K + 1), a j * k j * (k j * Real.cos (k j * θ))) =
        ∑ j ∈ Finset.range (K + 1),
          PDE.Analysis.cosineModeResidual ((n : ℝ) * (n + 1)) (a j) (k j) θ := by
      simp only [hSdef, hTdef, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [PDE.Analysis.cosineModeResidual]
      ring
    linarith
  have hode := legendre_equation_of_hasDerivAt hflux
  have hQeq := eq_C_mul_legendre_of_legendre_equation_eval (n := n) (Q := Q) fun c ↦ by
    have := hode c
    linarith
  have h1 : Q.eval 1 = ∑ j ∈ Finset.range (K + 1), a j := by
    rw [← Real.cos_zero, hQ 0]
    simp [hSdef]
  have h2 := congrArg (fun P : ℝ[X] ↦ P.eval (Real.cos θ)) hQeq
  simp only [eval_mul, eval_C] at h2
  rw [hQ θ, h1] at h2
  exact h2

/-- `P_{2N} (cos θ) · S(0) = S(θ)` for the even cosine series `S` of `CosineSeries`. -/
theorem legendre_eval_cos_even (N : ℕ) (θ : ℝ) :
    ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.evenCosineCoefficient N j : ℝ) *
        Real.cos ((2 * j : ℕ) * θ) =
      (∑ j ∈ Finset.range (N + 1), (PDE.Analysis.evenCosineCoefficient N j : ℝ)) *
        (legendre (2 * N)).eval (Real.cos θ) := by
  refine cosineSeries_eq_mul_legendre (n := 2 * N) _ (fun j ↦ 2 * j) (fun t ↦ ?_) θ
  have h := PDE.Analysis.sum_cosineModeResidual_evenCosineCoefficient N N le_rfl t
  push_cast at h ⊢
  rw [show (2 * (N : ℝ)) * (2 * (N : ℝ) + 1) = 2 * (N : ℝ) * (2 * (N : ℝ) + 1) by ring] at h
  exact h

/-- `P_{2N+1} (cos θ) · S(0) = S(θ)` for the odd cosine series `S` of `CosineSeries`. -/
theorem legendre_eval_cos_odd (N : ℕ) (θ : ℝ) :
    ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.oddCosineCoefficient N j : ℝ) *
        Real.cos ((2 * j + 1 : ℕ) * θ) =
      (∑ j ∈ Finset.range (N + 1), (PDE.Analysis.oddCosineCoefficient N j : ℝ)) *
        (legendre (2 * N + 1)).eval (Real.cos θ) := by
  refine cosineSeries_eq_mul_legendre (n := 2 * N + 1) _ (fun j ↦ 2 * j + 1) (fun t ↦ ?_) θ
  have h := PDE.Analysis.sum_cosineModeResidual_oddCosineCoefficient N N le_rfl t
  push_cast at h ⊢
  rw [show (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) = (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 1 + 1)
    by ring] at h
  exact h

/-- The normalized double factorials are positive. -/
theorem halfCentralBinomial_pos' (n : ℕ) : 0 < PDE.Analysis.halfCentralBinomial n := by
  unfold PDE.Analysis.halfCentralBinomial
  refine Finset.prod_pos fun k _ ↦ ?_
  have hk : (1 : ℚ) / (2 * ((k : ℚ) + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℚ) ≤ k := Nat.cast_nonneg k
    linarith
  linarith

/-- The even coefficients sum to a positive number. -/
theorem sum_evenCosineCoefficient_pos (N : ℕ) :
    0 < ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.evenCosineCoefficient N j : ℝ) := by
  have hpos (j : ℕ) (hj : j ≤ N) : (0 : ℝ) < PDE.Analysis.evenCosineCoefficient N j := by
    have h1 := halfCentralBinomial_pos' (N + j)
    have h2 := halfCentralBinomial_pos' (N - j)
    unfold PDE.Analysis.evenCosineCoefficient
    simp only [hj, ↓reduceIte]
    have h3 : (0 : ℚ) < (if j = 0 then 1 else 2) := by split_ifs <;> norm_num
    exact_mod_cast mul_pos (mul_pos h3 h1) h2
  exact Finset.sum_pos (fun j hj ↦ hpos j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩

/-- The odd coefficients sum to a positive number. -/
theorem sum_oddCosineCoefficient_pos (N : ℕ) :
    0 < ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.oddCosineCoefficient N j : ℝ) := by
  have hpos (j : ℕ) (hj : j ≤ N) : (0 : ℝ) < PDE.Analysis.oddCosineCoefficient N j := by
    have h1 := halfCentralBinomial_pos' (N + j + 1)
    have h2 := halfCentralBinomial_pos' (N - j)
    unfold PDE.Analysis.oddCosineCoefficient
    simp only [hj, ↓reduceIte]
    exact_mod_cast mul_pos (mul_pos (by norm_num) h1) h2
  exact Finset.sum_pos (fun j hj ↦ hpos j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩

/-- `S_{2N} (θ) = P_{2N} (cos θ)` as the normalized even cosine series. -/
theorem zonalHarmonic_even_eq (N : ℕ) (θ : ℝ) :
    zonalHarmonic (2 * N) θ =
      (∑ j ∈ Finset.range (N + 1), (PDE.Analysis.evenCosineCoefficient N j : ℝ) *
        Real.cos ((2 * j : ℕ) * θ)) /
      ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.evenCosineCoefficient N j : ℝ) := by
  rw [legendre_eval_cos_even, mul_div_cancel_left₀ _ (sum_evenCosineCoefficient_pos N).ne']
  rfl

/-- `S_{2N+1} (θ) = P_{2N+1} (cos θ)` as the normalized odd cosine series. -/
theorem zonalHarmonic_odd_eq (N : ℕ) (θ : ℝ) :
    zonalHarmonic (2 * N + 1) θ =
      (∑ j ∈ Finset.range (N + 1), (PDE.Analysis.oddCosineCoefficient N j : ℝ) *
        Real.cos ((2 * j + 1 : ℕ) * θ)) /
      ∑ j ∈ Finset.range (N + 1), (PDE.Analysis.oddCosineCoefficient N j : ℝ) := by
  rw [legendre_eval_cos_odd, mul_div_cancel_left₀ _ (sum_oddCosineCoefficient_pos N).ne']
  rfl

end PDE.Analysis.SpecialFunctions
