/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.Potential

/-!
# Construction of the classical wave in every odd dimension

For dimension `2k+3`, `C^(k+3)` displacement and `C^(k+2)` velocity data give the
representation formula (31) of Evans, §2.4.1; this is his Theorem 2 with `m = k + 2`. The
signed-time construction is jointly
`C²`, solves the wave equation at positive times, and has both joint initial
traces. The velocity potential needs only two derivatives after transformation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(d), equation (31) and Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The signed-time extension of Evans's odd-dimensional formula, normalized
by the positive dimension constant `(2k+1)‼`. -/
def oddWaveSolution
    (k : ℕ) (g h : ℝ^(2 * k + 3) → ℝ) : ℝ^(2 * k + 3 + 1) → ℝ :=
  fun p ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ *
    ((∂[0] (oddWavePotential k g)) p + oddWavePotential k h p)

/-- The constructed field is the positive-time formula, with the
same spherical means, radial transform, and dimension normalization. -/
theorem oddWaveSolution_eq_evansOddDimensionalFormula (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 1) g) (x : ℝ^(2 * k + 3)) (t : Set.Ioi (0 : ℝ)) :
    oddWaveSolution k g h (timeSpaceCons t x) = evansOddDimensionalFormula k g h x t := by
  rw [oddWaveSolution, partialDeriv_oddWavePotential_time k hg, oddWavePotential_timeSpaceCons]
  simp only [evansOddDimensionalFormula, div_eq_mul_inv, mul_comm]

/-- Evans's odd-dimensional formula is jointly `C²` up to time zero.
The proof supplies a `C²` extension to all signed times. -/
theorem contDiff_two_oddWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ} (hg : ContDiff ℝ (k + 3) g)
    (hh : ContDiff ℝ (k + 2) h) :
    ContDiff ℝ 2 (oddWaveSolution k g h) :=
  contDiff_const.mul
    ((PDE.contDiff_partialDeriv_of_succ (m := 2) (contDiff_oddWavePotential k 3 hg)).add
      (contDiff_oddWavePotential k 2 hh))

/-- Closed-halfspace regularity of the constructed formula. -/
theorem contDiffOn_two_oddWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ} (hg : ContDiff ℝ (k + 3) g)
    (hh : ContDiff ℝ (k + 2) h) :
    ContDiffOn ℝ 2 (oddWaveSolution k g h) {p | 0 ≤ p 0} :=
  (contDiff_two_oddWaveSolution k hg hh).contDiffOn

/-- The constructed formula solves the wave equation at every positive time. -/
theorem waveOperator_oddWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ} (hg : ContDiff ℝ (k + 3) g)
    (hh : ContDiff ℝ (k + 2) h) {p : ℝ^(2 * k + 3 + 1)} (hp : 0 < p 0) :
    waveOperator (oddWaveSolution k g h) p = 0 := by
  have hgt := PDE.contDiff_partialDeriv_of_succ (m := 2) (i := 0) (contDiff_oddWavePotential k 3 hg)
  unfold oddWaveSolution
  rw [waveOperator_const_mul,
    waveOperator_add hgt.contDiffAt (contDiff_oddWavePotential k 2 hh).contDiffAt,
    waveOperator_partialDeriv_eq_zero_of_positive_time (contDiff_oddWavePotential k 3 hg)
      (fun _ hq ↦ waveOperator_oddWavePotential k (hg.of_le (by norm_cast; omega)) hq),
    waveOperator_oddWavePotential k hh hp, add_zero, mul_zero]
  exact hp

/-- The total field has the prescribed initial displacement. -/
theorem oddWaveSolution_initial_position (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 1) g) (x : ℝ^(2 * k + 3)) :
    oddWaveSolution k g h (timeSpaceCons 0 x) = g x := by
  have hγ : (Nat.doubleFactorial (2 * k + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  simp only [oddWaveSolution, partialDeriv_oddWavePotential_initial k hg,
    oddWavePotential_initial, add_zero, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]

/-- The initial velocity follows from the zero acceleration of the
displacement potential and the center derivative of the velocity potential. -/
theorem partialDeriv_oddWaveSolution_initial_velocity (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 2) g) (hh : ContDiff ℝ (k + 1) h) (x : ℝ^(2 * k + 3)) :
    (∂[0] (oddWaveSolution k g h)) (timeSpaceCons 0 x) = h x := by
  have hγ : (Nat.doubleFactorial (2 * k + 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
  have hgt := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0) (contDiff_oddWavePotential k 2 hg)
  change (∂[0] (fun p ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ •
    ((∂[0] (oddWavePotential k g)) p + oddWavePotential k h p))) (timeSpaceCons 0 x) = _
  rw [PDE.partialDeriv_const_smul, PDE.partialDeriv_add (hgt.differentiable one_ne_zero _)
      ((contDiff_oddWavePotential k 1 hh).differentiable one_ne_zero _),
    secondPartialDeriv_oddWavePotential_initial k hg, partialDeriv_oddWavePotential_initial k hh]
  simp only [zero_add, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hγ, one_mul]

/-- The formula satisfies the wave residual and both assigned data.
Its regularity is proved separately by `contDiff_two_oddWaveSolution`. -/
theorem oddWaveSolution_satisfiesResidualAssignedCauchyData (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * k + 3) g h)
      (oddWaveSolution k g h) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_oddWaveSolution k hg hh hp
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := oddWaveSolution_initial_position k
      (hg.of_le (by norm_cast; omega)) (h := h) (spatialPartCLM (2 * k + 3) p)
    rwa [he] at hi
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_oddWaveSolution_initial_velocity k
      (hg.of_le (by norm_cast; omega)) (hh.of_le (by norm_cast; omega))
      (spatialPartCLM (2 * k + 3) p)
    rwa [he] at hi

/-- The displacement trace is joint in space and time. It therefore also
holds when approaching through strictly positive times. -/
theorem tendsto_oddWaveSolution_initial_position (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (x : ℝ^(2 * k + 3)) :
    Filter.Tendsto (oddWaveSolution k g h) (nhds (timeSpaceCons 0 x)) (nhds (g x)) := by
  simpa only [ContinuousAt, oddWaveSolution_initial_position k
    (hg.of_le (by norm_cast; omega))] using
      (contDiff_two_oddWaveSolution k hg hh).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The first time derivative has the prescribed joint initial trace. -/
theorem tendsto_partialDeriv_oddWaveSolution_initial_velocity (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (x : ℝ^(2 * k + 3)) :
    Filter.Tendsto (∂[0] (oddWaveSolution k g h)) (nhds (timeSpaceCons 0 x)) (nhds (h x)) := by
  have hreg := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_oddWaveSolution k hg hh)
  simpa only [ContinuousAt, partialDeriv_oddWaveSolution_initial_velocity k
    (hg.of_le (by norm_cast; omega)) (hh.of_le (by norm_cast; omega))] using
      hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

/-- Every other globally `C²` Cauchy solution agrees with the constructed
formula at nonnegative times. -/
theorem eq_oddWaveSolution_of_satisfiesResidualAssignedCauchyData (k : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) {u : ℝ^(2 * k + 3 + 1) → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * k + 3) g h) u)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ^(2 * k + 3)) :
    u (timeSpaceCons t x) = oddWaveSolution k g h (timeSpaceCons t x) := by
  have : Fact (0 < 2 * k + 3) := ⟨by omega⟩
  exact eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData hu
    (contDiff_two_oddWaveSolution k hg hh) hsol
    (oddWaveSolution_satisfiesResidualAssignedCauchyData k hg hh) ht x

/-- Every globally `C²` Cauchy solution equals Evans's odd-dimensional formula at positive
times. Unlike `eq_evansOddDimensionalFormula_of_wave`, the spherical means need no regularity
hypothesis. -/
theorem eq_evansOddDimensionalFormula_of_satisfiesResidualAssignedCauchyData (k : ℕ)
    {g h : ℝ^(2 * k + 3) → ℝ} (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h)
    {u : ℝ^(2 * k + 3 + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * k + 3) g h) u)
    (x : ℝ^(2 * k + 3)) (t : Set.Ioi (0 : ℝ)) :
    u (timeSpaceCons t x) = evansOddDimensionalFormula k g h x t := by
  rw [eq_oddWaveSolution_of_satisfiesResidualAssignedCauchyData k hg hh hu hsol (le_of_lt t.2) x,
    oddWaveSolution_eq_evansOddDimensionalFormula k (hg.of_le (by norm_cast; omega)) x t]

end WaveEquation
