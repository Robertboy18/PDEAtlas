/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.FundamentalSolution
public import PDE.Elliptic.Classical.Harmonic.IteratedDerivativeEstimates
public import PDE.FDeriv.PartialDeriv.Norm

/-!
# Decay of higher derivatives of the Newtonian kernel

The kernel is harmonic away from its pole. On the half-radius ball around
`X`, its size is at most `1 / (π² |X|³)`. The harmonic interior estimate
`IsHarmonicPDE.norm_iteratedFDeriv_le` then bounds every derivative, spending the available
radius evenly.

This gives an explicit constant at every order, including the fifth and
sixth derivatives used on separated source annuli. No derivative formula
or decay assumption is needed.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace PotentialTheory

/-- An explicit, nonoptimal decay constant obtained from the harmonic
interior estimate. The extra unit in the radius budget also covers order zero. -/
def fiveDimensionalHigherKernelConstant (k : ℕ) : ℝ :=
  (10 * ((k : ℝ) + 1)) ^ k / Real.pi ^ 2

/-- The higher-kernel constant is positive at every finite order. -/
theorem fiveDimensionalHigherKernelConstant_pos (k : ℕ) :
    0 < fiveDimensionalHigherKernelConstant k := by
  unfold fiveDimensionalHigherKernelConstant
  positivity

/-- Every full derivative has the expected Newtonian decay. Harmonic
regularity supplies all derivatives away from the pole. -/
theorem norm_iteratedFDeriv_fundamentalSolution_five_le
    (k : ℕ) (X : ℝ^5) (hX : X ≠ 0) :
    ‖iteratedFDeriv ℝ k (fundamentalSolution 5) X‖ ≤
      fiveDimensionalHigherKernelConstant k / ‖X‖ ^ (k + 3) := by
  let : Fact (0 < (5 : ℕ)) := ⟨by norm_num⟩
  have hnorm : 0 < ‖X‖ := norm_pos_iff.mpr hX
  let r : ℝ := ‖X‖ / (2 * ((k : ℝ) + 1))
  let M : ℝ := 1 / (Real.pi ^ 2 * ‖X‖ ^ 3)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hradius : (k : ℝ) * r ≤ ‖X‖ / 2 := by
    dsimp only [r]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((k : ℝ) + 1))).2
    nlinarith
  have haway (Y : ℝ^5) (hY : Y ∈ Metric.closedBall X ((k : ℝ) * r)) :
      ‖X‖ / 2 ≤ ‖Y‖ := by
    linarith [(Metric.mem_closedBall.mp hY).trans hradius, norm_le_norm_add_norm_sub Y X,
      dist_eq_norm Y X]
  have hball : Metric.closedBall X ((k : ℝ) * r) ⊆ ({0} : Set (ℝ^5))ᶜ := fun Y hY hzero ↦ by
    linarith [haway Y hY, norm_eq_zero.mpr (Set.mem_singleton_iff.mp hzero)]
  have hbound (Y : ℝ^5) (hY : Y ∈ Metric.closedBall X ((k : ℝ) * r)) :
      |fundamentalSolution 5 Y| ≤ M := by
    have hYpos : 0 < ‖Y‖ := (half_pos hnorm).trans_le (haway Y hY)
    have hpow : (‖X‖ / 2) ^ 3 ≤ ‖Y‖ ^ 3 := by gcongr; exact haway Y hY
    have hcoeff : 0 ≤ 1 / (8 * Real.pi ^ 2) := by positivity
    calc
      _ = (1 / (8 * Real.pi ^ 2)) / ‖Y‖ ^ 3 := by
        rw [fundamentalSolution_five, Real.rpow_neg (norm_nonneg Y)]
        rw [abs_of_nonneg (mul_nonneg hcoeff (inv_nonneg.mpr (by positivity)))]
        simp only [div_eq_mul_inv, Real.rpow_ofNat]
      _ ≤ (1 / (8 * Real.pi ^ 2)) / (‖X‖ / 2) ^ 3 :=
        div_le_div_of_nonneg_left hcoeff (by positivity) hpow
      _ = M := by
        dsimp only [M]
        field_simp
        ring
  have hharmonic : LaplacianEquation.IsHarmonicPDE 5 (fundamentalSolution 5)
      ({0} : Set (ℝ^5))ᶜ :=
    ⟨fun Y hY ↦ ((contDiffAt_fundamentalSolution 5 Y (by simpa using hY)).of_le
        (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffWithinAt,
      fun Y hY ↦ laplacian_fundamentalSolution_eq_zero 5 Y (by simpa using hY)⟩
  have h := hharmonic.norm_iteratedFDeriv_le isClosed_singleton.isOpen_compl hr hball hbound
  refine h.trans_eq ?_
  dsimp only [r, M, fiveDimensionalHigherKernelConstant]
  simp only [div_pow, mul_pow, pow_add]
  field_simp
  rw [show (10 : ℝ) ^ k = 2 ^ k * 5 ^ k by rw [← mul_pow]; norm_num]
  ring

/-- The same decay bound holds for every mixed coordinate derivative.
This is the form used before reducing to physical profile coordinates. -/
theorem abs_iteratedPartialDeriv_fundamentalSolution_five_le
    (indices : List (Fin 5)) (X : ℝ^5) (hX : X ≠ 0) :
    |iteratedPartialDeriv indices (fundamentalSolution 5) X| ≤
      fiveDimensionalHigherKernelConstant indices.length / ‖X‖ ^ (indices.length + 3) := by
  have hf : ContDiffAt ℝ indices.length (fundamentalSolution 5) X :=
    (contDiffAt_fundamentalSolution 5 X hX).of_le
      (by exact_mod_cast (show (indices.length : ℕ∞) ≤ ⊤ from le_top))
  have h := PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv indices hf
  rw [Real.norm_eq_abs] at h
  exact h.trans (norm_iteratedFDeriv_fundamentalSolution_five_le indices.length X hX)

end PotentialTheory
