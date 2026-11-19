/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.LpBound
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Cutoff.Derivative

/-!
# The cutoff term in the normal derivative

Differentiating the extension in height produces two terms. The derivative of the mollifier is
controlled by the fractional boundary seminorm. We bound the other term, `χ'(t) (ρₜ * g)(x)`, using
only the boundary `Lᵖ` norm. The constant comes from the fixed smooth cutoff and is independent of
`g`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace SobolevSpace.Trace.HalfSpace

open SobolevSpace.Approximation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cutoff-derivative contribution has a finite `Lᵖ` norm,
bounded uniformly by the boundary norm in every dimension. -/
theorem exists_pos_deriv_heightCutoff_mollifyVector_bound
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (μ : Mollifier n) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℝ^n → F) (_ : MemLp g p volume),
      MemLp (fun z : ℝ^(n + 1) ↦ deriv heightCutoff (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
        p (volume.restrict ℝ^(n + 1)₊) ∧
      eLpNorm (fun z : ℝ^(n + 1) ↦ deriv heightCutoff (splitTangentialNormal z).2 •
        mollifyVector μ (splitTangentialNormal z).2 g (splitTangentialNormal z).1)
        p (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal C * eLpNorm g p volume := by
  obtain ⟨B, hB, hbound⟩ := exists_pos_bound_deriv_heightCutoff
  let b : ℝ≥0 := ⟨B, hB.le⟩
  have hC (t : ℝ) (_ : 0 < t) : ‖deriv heightCutoff t‖ ≤ b := hbound t
  have hT (t : ℝ) (ht : (3 : ℝ≥0) ≤ t) : deriv heightCutoff t = 0 := by
    apply deriv_heightCutoff_eq_zero_of_two_lt
    have : 2 < t := by exact lt_of_lt_of_le (by norm_num) ht
    exact this.trans_le (le_abs_self t)
  refine ⟨(3 : ℝ) ^ (1 / p.toReal) * B, by positivity, ?_⟩
  intro g hg
  refine ⟨memLp_height_smul_mollifyVector μ hp hg
    continuous_deriv_heightCutoff.measurable hC hT, ?_⟩
  have hnorm := eLpNorm_height_smul_mollifyVector_le μ hp hg
    continuous_deriv_heightCutoff.measurable hC hT
  have hcoef : ENNReal.ofReal ((3 : ℝ) ^ (1 / p.toReal) * B) =
      (3 : ℝ≥0∞) ^ (1 / p.toReal) * (b : ℝ≥0∞) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← ENNReal.ofReal_rpow_of_nonneg (by norm_num)
        (one_div_nonneg.mpr ENNReal.toReal_nonneg),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_eq_coe_nnreal hB.le]
    rfl
  rw [hcoef]
  simpa only [ENNReal.coe_ofNat] using hnorm

end SobolevSpace.Trace.HalfSpace
