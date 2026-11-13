/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm.Existence

/-!
# The Lax–Milgram solution of shifted divergence-form problems

`shiftedDivergenceSolve` is the Lax–Milgram solution of `B_μ(u, ·) = F` at the canonical shift
`μ = coerciveShift alpha beta gamma`, for a load in the `H⁻¹` representation
`F(v) = ⟪f₀, v⟫ + ∑ᵢ ⟪fᵢ, ∂ᵢv⟫`. It satisfies the weak equation, vanishes for zero data, is
the only weak solution, and obeys an explicit `H¹₀` bound.

## Main results

* `shiftedDivergenceSolve`, `isWeakSolution_iff_eq_shiftedDivergenceSolve`: the solution and
  its characterization by the weak equation.
* `norm_shiftedDivergenceSolve_le`: the estimate `‖u‖ ≤ (2 / alpha) (‖f₀‖ + ∑ᵢ ‖fᵢ‖)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax–Milgram Theorem), pp. 315-317;
  §6.2.2, Theorem 3 (First Existence Theorem for weak solutions), p. 319, and the right-hand
  sides `f₀ - ∑ᵢ ∂ᵢfᵢ` of (9), p. 320.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- The Lax–Milgram solution of the canonically shifted full divergence-form problem. -/
noncomputable def shiftedDivergenceSolve
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) : H¹₀(Ω) :=
  solve
    (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
      (coerciveShift (n := n) alpha beta gamma))
    (shiftedDivergenceForm_isCoercive
      (n := n) (Ω := Ω) A b c hA hbc)
    (generalizedLoad (n := n) (Ω := Ω) f0 f)

/-- The named solution satisfies the shifted full weak equation. -/
theorem shiftedDivergenceSolve_isWeakSolution
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) :
    IsWeakSolution
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma))
      (generalizedLoad (n := n) (Ω := Ω) f0 f)
      (shiftedDivergenceSolve (n := n) (Ω := Ω) A b c hA hbc f0 f) := by
  have hB : IsCoercive
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma)) :=
    shiftedDivergenceForm_isCoercive
      (n := n) (Ω := Ω) A b c hA hbc
  unfold shiftedDivergenceSolve
  exact @solve.isWeakSolution H¹₀(Ω) inferInstance inferInstance inferInstance
    (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
      (coerciveShift (n := n) alpha beta gamma))
    hB
    (generalizedLoad (n := n) (Ω := Ω) f0 f)

/--
The shifted full divergence-form problem has zero weak solution for zero
`H^{-1}` data.

Here zero data means both pieces of Evans' `f₀ - div f` representation vanish:
`f₀ = 0` and every vector forcing component `fᵢ = 0`.
-/
theorem shiftedDivergenceSolve_zero
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma) :
    shiftedDivergenceSolve (n := n) (Ω := Ω) A b c hA hbc
      (0 : L2) (0 : Fin n → L2) = 0 := by
  unfold shiftedDivergenceSolve
  rw [generalizedLoad_zero]
  apply solve.zero

/-- Uniqueness for the shifted lower-order Evans weak problem: any weak
solution agrees with the named Gårding/Lax–Milgram solution. -/
theorem eq_shiftedDivergenceSolve_of_isWeakSolution
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) {u : H¹₀(Ω)}
    (hu : IsWeakSolution
      (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma))
      (generalizedLoad (n := n) (Ω := Ω) f0 f) u) :
    u = shiftedDivergenceSolve (n := n) (Ω := Ω) A b c hA hbc f0 f := by
  exact (existsUnique_shiftedDivergence_weakSolution
    (n := n) (Ω := Ω) A b c hA hbc f0 f).unique hu
      (shiftedDivergenceSolve_isWeakSolution
        (n := n) (Ω := Ω) A b c hA hbc f0 f)

/-- The shifted lower-order weak equation characterizes the named solver. -/
theorem isWeakSolution_iff_eq_shiftedDivergenceSolve
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) {u : H¹₀(Ω)} :
    IsWeakSolution
        (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
          (coerciveShift (n := n) alpha beta gamma))
        (generalizedLoad (n := n) (Ω := Ω) f0 f) u ↔
      u = shiftedDivergenceSolve (n := n) (Ω := Ω) A b c hA hbc f0 f := by
  constructor
  · exact eq_shiftedDivergenceSolve_of_isWeakSolution
      (n := n) (Ω := Ω) A b c hA hbc f0 f
  · rintro rfl
    exact shiftedDivergenceSolve_isWeakSolution
      (n := n) (Ω := Ω) A b c hA hbc f0 f

/-- The zero-data shifted lower-order weak equation has exactly the zero solution. -/
theorem isWeakSolution_zero_iff
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    {u : H¹₀(Ω)} :
    IsWeakSolution
        (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
          (coerciveShift (n := n) alpha beta gamma))
        (generalizedLoad (n := n) (Ω := Ω) (0 : L2) (0 : Fin n → L2)) u ↔
      u = 0 := by
  rw [isWeakSolution_iff_eq_shiftedDivergenceSolve
    (n := n) (Ω := Ω) A b c hA hbc (0 : L2) (0 : Fin n → L2)]
  rw [shiftedDivergenceSolve_zero (n := n) (Ω := Ω) A b c hA hbc]

/-- Evans-readable variational equation for the named solution. -/
theorem shiftedDivergenceSolve_equation
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) (v : H¹₀(Ω)) :
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c
        (coerciveShift (n := n) alpha beta gamma)
        (shiftedDivergenceSolve (n := n) (Ω := Ω) A b c hA hbc f0 f) v =
      inner ℝ f0 (baseCoordCLM (n := n) (Ω := Ω) v) +
        ∑ i : Fin n,
          inner ℝ (f i) (derivCoordCLM (n := n) (Ω := Ω) i v) := by
  have h := shiftedDivergenceSolve_isWeakSolution
    (n := n) (Ω := Ω) A b c hA hbc f0 f v
  calc
    _ = generalizedLoad (n := n) (Ω := Ω) f0 f v := h
    _ = _ := generalizedLoad_apply (n := n) (Ω := Ω) f0 f v

/-- Explicit `H^1_0` estimate in terms of the `H^{-1}` representation data. -/
theorem norm_shiftedDivergenceSolve_le
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) :
    ‖shiftedDivergenceSolve (n := n) (Ω := Ω)
      A b c hA hbc f0 f‖ ≤
      (2 / alpha) * (‖f0‖ + ∑ i : Fin n, ‖f i‖) := by
  let u := shiftedDivergenceSolve (n := n) (Ω := Ω)
    A b c hA hbc f0 f
  have hweak := shiftedDivergenceSolve_isWeakSolution
    (n := n) (Ω := Ω) A b c hA hbc f0 f
  change IsWeakSolution
    (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
      (coerciveShift (n := n) alpha beta gamma))
    (generalizedLoad (n := n) (Ω := Ω) f0 f) u at hweak
  have hcoercive := shiftedDivergenceForm_coercive_bound
    (n := n) (Ω := Ω) A b c hA hbc u
  have hload := norm_generalizedLoad_apply_le
    (n := n) (Ω := Ω) f0 f u
  have heq := hweak u
  have habs :
      shiftedDivergenceForm (n := n) (Ω := Ω) A b c
          (coerciveShift (n := n) alpha beta gamma) u u ≤
        ‖generalizedLoad (n := n) (Ω := Ω) f0 f u‖ := by
    calc
      _ = generalizedLoad (n := n) (Ω := Ω) f0 f u := heq
      _ ≤ ‖generalizedLoad (n := n) (Ω := Ω) f0 f u‖ :=
        Real.le_norm_self _
  have hmain : alpha / 2 * ‖u‖ * ‖u‖ ≤
      (‖f0‖ + ∑ i : Fin n, ‖f i‖) * ‖u‖ :=
    hcoercive.trans (habs.trans hload)
  by_cases hu : ‖u‖ = 0
  · rw [hu]
    have hfactor : 0 ≤ 2 / alpha := div_nonneg (by norm_num) hA.1.le
    positivity
  · have huPos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
    have hcancel : alpha / 2 * ‖u‖ ≤ ‖f0‖ + ∑ i : Fin n, ‖f i‖ := by
      exact le_of_mul_le_mul_right (by simpa [mul_assoc] using hmain) huPos
    have halphaHalf : 0 < alpha / 2 := div_pos hA.1 (by norm_num)
    calc
      ‖u‖ ≤ (‖f0‖ + ∑ i : Fin n, ‖f i‖) / (alpha / 2) :=
        (le_div_iff₀ halphaHalf).2 (by simpa [mul_comm] using hcancel)
      _ = (2 / alpha) * (‖f0‖ + ∑ i : Fin n, ‖f i‖) := by
        calc
          (‖f0‖ + ∑ i : Fin n, ‖f i‖) / (alpha / 2) =
              (‖f0‖ + ∑ i : Fin n, ‖f i‖) * (alpha / 2)⁻¹ :=
            div_eq_mul_inv _ _
          _ = (‖f0‖ + ∑ i : Fin n, ‖f i‖) * (2 / alpha) := by
            rw [inv_div]
          _ = (2 / alpha) * (‖f0‖ + ∑ i : Fin n, ‖f i‖) :=
            mul_comm _ _

end GraphSpace

end SobolevSpace
