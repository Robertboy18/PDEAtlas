/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.Construction

/-!
# The even-dimensional retarded representation

On a forward interval the source slices are the original ones. Hadamard descent
then identifies the kernel with the ball formula (38) of Evans, §2.4.1(e), including its
double-factorial normalization. The single zero-age endpoint does not affect the integral.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(e), equation (38); §2.4.2, equations (40)-(41).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The even-dimensional retarded integral uses the original source on forward time. -/
theorem evenDuhamelSolution_eq_integral (k : ℕ) (f : ℝ^(2 * k + 2 + 1) → ℝ) (x : ℝ^(2 * k + 2))
    {t : ℝ} (ht : 0 ≤ t) :
    evenDuhamelSolution k f (timeSpaceCons t x) = ∫ s in (0 : ℝ)..t, evenWaveSolution k (fun _ ↦ 0)
      (fun y ↦ f (timeSpaceCons s y)) (timeSpaceCons (t - s) x) := by
  change (∫ s in (0 : ℝ)..t, evenWaveSolution k (fun _ ↦ 0)
    (fun y ↦ f (timeSpaceCons (max 0 s) y)) (timeSpaceCons (t - s) x)) = _
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  rw [Set.uIcc_of_le ht] at hs
  simp only [max_eq_right hs.1]

/-- At positive ages the kernel is the ball formula (38) of Evans, §2.4.1(e). Its endpoint
value at age zero is irrelevant to the retarded integral. -/
theorem evenDuhamelSolution_eq_integral_evansEvenDimensionalFormula (k : ℕ)
    {f : ℝ^(2 * k + 2 + 1) → ℝ} (hf : ContDiffOn ℝ (k + 2) f {p | 0 ≤ p 0}) (x : ℝ^(2 * k + 2))
    {t : ℝ} (ht : 0 ≤ t) :
    evenDuhamelSolution k f (timeSpaceCons t x) = ∫ s in (0 : ℝ)..t, if hs : s <
      t then evansEvenDimensionalFormula k (fun _ ↦ 0) (fun y ↦ f (timeSpaceCons s y)) x
      ⟨t - s, sub_pos.mpr hs⟩ else 0 := by
  rw [evenDuhamelSolution_eq_integral k f x ht]
  refine intervalIntegral.integral_congr_Ioo_of_le ht fun s hs ↦ ?_
  simp only [dite_eq_left hs.2]
  exact evenWaveSolution_eq_evansEvenDimensionalFormula k contDiff_const
    (hf.contDiff_forward_spatialSlice hs.1.le).continuous x ⟨t - s, sub_pos.mpr hs.2⟩

end WaveEquation
