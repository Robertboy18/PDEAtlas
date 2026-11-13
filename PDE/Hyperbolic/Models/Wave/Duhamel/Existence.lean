/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.EvenDimensions.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.Duhamel.OddDimensions.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution

/-!
# Finite-order forced-wave existence in every positive dimension

The d'Alembert and spherical-mean retarded formulas cover every spatial dimension
`n ≥ 1`. They use exactly `⌊n/2⌋ + 1` source derivatives within the closed forward halfspace.
The resulting field has joint classical closure regularity and both joint
initial traces. The regularity is local. This is Evans, §2.4.2, Theorem 4, together with the
one-dimensional formula (43) of his Example (i); his theorem assumes `n ≥ 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, Theorem 4 and equation (43).
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- Finite-order forward forcing admits a classical solution with
zero Cauchy data and joint initial traces. The witnesses are the explicit
retarded formulas, including the one-dimensional characteristic integral. -/
theorem exists_contDiff_forcedWave_zeroCauchyData {n : ℕ} (hn : 1 ≤ n) {f : ℝ^(n + 1) → ℝ}
    (hf : ContDiffOn ℝ (↑(n / 2 + 1)) f {p | 0 ≤ p 0}) :
    ∃ u : ℝ^(n + 1) → ℝ, ContDiff ℝ 2 u ∧
      SatisfiesPDEProblem
        (forcedWaveResidualAssignedCauchyDataProblem (n := n) f
          (fun _ ↦ 0) (fun _ ↦ 0)) u ∧
      (∀ x, Filter.Tendsto u (nhds (timeSpaceCons 0 x)) (nhds 0)) ∧
      (∀ x, Filter.Tendsto (∂[0] u)
        (nhds (timeSpaceCons 0 x)) (nhds 0)) := by
  by_cases hdim : n = 1
  · subst n
    norm_num at hf
    exact ⟨dAlembertDuhamelSolution f, contDiff_two_dAlembertDuhamelSolution hf,
      dAlembertDuhamelSolution_satisfiesResidualAssignedCauchyData hf,
      tendsto_dAlembertDuhamelSolution_initial hf,
      tendsto_partialDeriv_dAlembertDuhamelSolution_initial hf⟩
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k + 2 ∨ n = 2 * k + 3 :=
    ⟨n / 2 - 1, by omega⟩
  · subst n
    have horder : (2 * k + 2) / 2 + 1 = k + 2 := by omega
    simp only [horder, Nat.cast_add, Nat.cast_ofNat] at hf
    exact ⟨evenDuhamelSolution k f, contDiff_two_evenDuhamelSolution k hf,
      evenDuhamelSolution_satisfiesResidualAssignedCauchyData k hf,
      tendsto_evenDuhamelSolution_initial k hf,
      tendsto_partialDeriv_evenDuhamelSolution_initial k hf⟩
  · subst n
    have horder : (2 * k + 3) / 2 + 1 = k + 2 := by omega
    simp only [horder, Nat.cast_add, Nat.cast_ofNat] at hf
    exact ⟨oddDuhamelSolution k f, contDiff_two_oddDuhamelSolution k hf,
      oddDuhamelSolution_satisfiesResidualAssignedCauchyData k hf,
      tendsto_oddDuhamelSolution_initial k hf, tendsto_partialDeriv_oddDuhamelSolution_initial k hf⟩

end WaveEquation
