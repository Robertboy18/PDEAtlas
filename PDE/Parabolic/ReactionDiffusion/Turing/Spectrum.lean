/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.ReactionDiffusion.Turing.Coefficients
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import CAS.ExactTactic

/-!
# The unstable eigenpair of a Turing mode

A negative determinant of a real two-species mode matrix gives a positive root of its characteristic
quadratic (`exists_positive_quadratic_root`). We construct its eigenvector explicitly, with nonzero
first component when the coupling `b` is nonzero, and use Mathlib's `HasEigenvector`, rather than
assuming a positive eigenvalue (`exists_positive_mode_eigenvector`). Under `Conditions` this gives a
positive growth rate at the squared wave number `Coefficients.selectedFrequencySq`
(`exists_unstable_mode`). SymLean's `cas` tactic verifies the root and eigenvector equations.

In Evans's §4.1.2 the characteristic polynomial of the mode matrix `A_j` is (28), with constant term
`p(λ_j)`. The product of its roots is `p(λ_j)`, so `p(λ_j) < 0` gives real roots of opposite signs
and a positive growth rate; his threshold (30) is the borderline case `p(λ_j) = 0`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.2 (Application: Turing instability), (28)-(30), p. 174.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace ReactionDiffusion.Turing

/-- A quadratic with negative constant term has a positive root. The root is
constructed by the quadratic formula, with no assumption about its existence. -/
theorem exists_positive_quadratic_root (trace determinant : ℝ) (hdet : determinant < 0) :
    ∃ rate : ℝ, 0 < rate ∧ rate ^ 2 - trace * rate + determinant = 0 := by
  have hdiscr : 0 ≤ trace ^ 2 - 4 * determinant := by nlinarith [sq_nonneg trace]
  have hsqrt := Real.sq_sqrt hdiscr
  have hsqrt_nonneg := Real.sqrt_nonneg (trace ^ 2 - 4 * determinant)
  have habs : |trace| < Real.sqrt (trace ^ 2 - 4 * determinant) := by
    apply (sq_lt_sq₀ (abs_nonneg trace) hsqrt_nonneg).mp
    rw [sq_abs, hsqrt]
    linarith
  refine ⟨(trace + Real.sqrt (trace ^ 2 - 4 * determinant)) / 2, ?_, ?_⟩
  · have hneg := neg_le_abs trace
    linarith
  · cas using hsqrt

/-- A negative mode determinant and nonzero first coupling produce a
positive eigenpair. Its first species component is nonzero. -/
theorem exists_positive_mode_eigenvector (C : Coefficients) (μ : ℝ)
    (hdet : (C.modeMatrix μ).det < 0) (hb : C.b ≠ 0) :
    ∃ rate : ℝ, 0 < rate ∧ ∃ vector : Fin 2 → ℝ,
      Module.End.HasEigenvector (C.modeMatrix μ).toLin' rate vector ∧ vector 0 ≠ 0 := by
  obtain ⟨rate, hrate, hroot⟩ := exists_positive_quadratic_root
    (C.a - C.diffusion₁ * μ + (C.d - C.diffusion₂ * μ))
    ((C.a - C.diffusion₁ * μ) * (C.d - C.diffusion₂ * μ) - C.b * C.c)
    (by simpa [Coefficients.modeMatrix, Matrix.det_fin_two] using hdet)
  refine ⟨rate, hrate, ![C.b, rate - (C.a - C.diffusion₁ * μ)], ?_, hb⟩
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i
    · simp only [Matrix.toLin'_apply, Coefficients.modeMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul]
      cas
    · simp only [Matrix.toLin'_apply, Coefficients.modeMatrix, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul]
      cas using hroot
  · intro hz
    exact hb (congrFun hz 0)

/-- The raw Turing inequalities yield a positive eigenvalue at a strictly nonzero frequency. -/
theorem exists_unstable_mode {C : Coefficients} (h : Conditions C) :
    ∃ μ rate : ℝ, 0 < μ ∧ 0 < rate ∧ ∃ vector : Fin 2 → ℝ,
      Module.End.HasEigenvector (C.modeMatrix μ).toLin' rate vector ∧ vector 0 ≠ 0 := by
  obtain ⟨rate, hrate, vector, hvector, hfirst⟩ :=
    exists_positive_mode_eigenvector C C.selectedFrequencySq
      (selected_mode_det_neg h) (coupling_ne_zero h)
  exact ⟨C.selectedFrequencySq, rate, selectedFrequencySq_pos h, hrate, vector, hvector,
    hfirst⟩

end ReactionDiffusion.Turing
