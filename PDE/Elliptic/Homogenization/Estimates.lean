/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Weighted
public import PDE.Elliptic.Homogenization.Dirichlet
import CAS.ExactTactic

/-!
# Quantitative one-dimensional homogenization

The error in each resistance integral is controlled by the bounded primitive of the
reciprocal oscillation. Positivity of the mean reciprocal controls the denominator
in the flux constant for small microscopic lengths. Combining these estimates gives
a uniform error of order `|ε|` for arbitrary continuous forcing.
-/

@[expose] public section

noncomputable section

open PDE.Analysis (primitive hasDerivAt_primitive)

namespace PDE.Elliptic.Homogenization

open MeasureTheory Set
open PDE.Analysis.PeriodicAveraging

namespace PeriodicMedium

variable (a : PeriodicMedium)

/-- The resistance differs from its averaged linear profile by `O(|ε|)`. -/
theorem resistance_error_le {K ε : ℝ}
    (hb : ∀ y, |fluctuation a.reciprocal y| ≤ K) (hε : ε ≠ 0) (x : ℝ) :
    |a.resistance ε x - a.meanReciprocal * x| ≤ |ε| * K :=
  abs_primitive_rescale_sub_le hb hε x

/-- Weighted resistance converges at the same rate for continuous forcing. -/
theorem weightedResistance_error_le {f : ℝ → ℝ} {K M ε x : ℝ}
    (hf : Continuous f) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hb : ∀ y, |fluctuation a.reciprocal y| ≤ K)
    (hfM : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M)
    (hε : ε ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    |a.weightedResistance f ε x - a.meanReciprocal * primitive (primitive f) x| ≤
      2 * M * (|ε| * K) :=
  abs_weighted_rescale_sub_le a.continuous_reciprocal (hasDerivAt_primitive hf) hf
    hK hM hb (fun _ hy ↦ abs_primitive_le_on_unit hM hfM hy) hfM hε hx

/-- The Dirichlet flux constants converge quantitatively. -/
theorem fluxConstant_error_le {f : ℝ → ℝ} {K M ε : ℝ}
    (hf : Continuous f) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hb : ∀ y, |fluctuation a.reciprocal y| ≤ K)
    (hfM : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M)
    (hε : ε ≠ 0) (hsmall : |ε| * K ≤ a.meanReciprocal / 2) :
    |a.fluxConstant f ε - primitive (primitive f) 1| ≤
      6 * M * (|ε| * K) / a.meanReciprocal := by
  let J := primitive (primitive f) 1
  let D := a.resistance ε 1
  let B := a.weightedResistance f ε 1
  let δ := |ε| * K
  have hδ : 0 ≤ δ := mul_nonneg (abs_nonneg _) hK
  have hm := a.meanReciprocal_pos
  have hD : 0 < D := a.resistance_one_pos ε
  have hJ : |J| ≤ M := abs_primitive_le_on_unit hM
    (fun _ hy ↦ abs_primitive_le_on_unit hM hfM hy) (by simp)
  have hr : |D - a.meanReciprocal| ≤ δ := by
    simpa only [mul_one] using a.resistance_error_le hb hε 1
  have hw : |B - a.meanReciprocal * J| ≤ 2 * M * δ :=
    a.weightedResistance_error_le hf hK hM hb hfM hε (by simp)
  have hden : a.meanReciprocal / 2 ≤ D := by
    have := (abs_le.mp hr).1
    dsimp [δ] at *
    linarith
  have hnum : |B - D * J| ≤ 3 * M * δ := by
    calc
      |B - D * J| = |(B - a.meanReciprocal * J) + (a.meanReciprocal - D) * J| := by
        congr 1
        ring
      _ ≤ |B - a.meanReciprocal * J| + |(a.meanReciprocal - D) * J| := abs_add_le _ _
      _ ≤ 2 * M * δ + δ * M := by
        apply add_le_add hw
        rw [abs_mul, abs_sub_comm]
        exact mul_le_mul hr hJ (abs_nonneg _) hδ
      _ = 3 * M * δ := by cas
  have heq : a.fluxConstant f ε - J = (B - D * J) / D := by
    dsimp [fluxConstant, B, D]
    field_simp [(a.resistance_one_pos ε).ne']
  rw [heq, abs_div, abs_of_pos hD]
  calc
    |B - D * J| / D ≤ (3 * M * δ) / D := div_le_div_of_nonneg_right hnum hD.le
    _ ≤ (3 * M * δ) / (a.meanReciprocal / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 6 * M * δ / a.meanReciprocal := by cas

/-- Uniform order-`|ε|` error on the unit interval, with explicit admissible scales. -/
theorem solution_error_le {f : ℝ → ℝ} {K M ε x : ℝ}
    (hf : Continuous f) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hb : ∀ y, |fluctuation a.reciprocal y| ≤ K)
    (hfM : ∀ y ∈ Icc (0 : ℝ) 1, |f y| ≤ M)
    (hε : ε ≠ 0) (hsmall : |ε| * K ≤ a.meanReciprocal / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |a.solution f ε x - a.homogenizedSolution f x| ≤ 15 * M * (|ε| * K) := by
  let J := primitive (primitive f) 1
  let δ := |ε| * K
  have hm := a.meanReciprocal_pos
  have hδ : 0 ≤ δ := mul_nonneg (abs_nonneg _) hK
  have hJ : |J| ≤ M := abs_primitive_le_on_unit hM
    (fun _ hy ↦ abs_primitive_le_on_unit hM hfM hy) (by simp)
  have hr := a.resistance_error_le hb hε x
  have hw := a.weightedResistance_error_le hf hK hM hb hfM hε hx
  have hc := a.fluxConstant_error_le hf hK hM hb hfM hε hsmall
  have hR : |a.resistance ε x| ≤ 2 * a.meanReciprocal := by
    calc
      |a.resistance ε x| = |(a.resistance ε x - a.meanReciprocal * x) +
          a.meanReciprocal * x| := by rw [sub_add_cancel]
      _ ≤ |a.resistance ε x - a.meanReciprocal * x| + |a.meanReciprocal * x| :=
        abs_add_le _ _
      _ ≤ δ + a.meanReciprocal := by
        apply add_le_add hr
        rw [abs_mul, abs_of_pos hm, abs_of_nonneg hx.1]
        exact mul_le_of_le_one_right hm.le hx.2
      _ ≤ 2 * a.meanReciprocal := by dsimp [δ]; linarith
  have heq : a.solution f ε x - a.homogenizedSolution f x =
      (a.fluxConstant f ε - J) * a.resistance ε x +
        J * (a.resistance ε x - a.meanReciprocal * x) -
          (a.weightedResistance f ε x - a.meanReciprocal * primitive (primitive f) x) := by
    dsimp [solution, homogenizedSolution, J]
    ring
  rw [heq]
  calc
    |(a.fluxConstant f ε - J) * a.resistance ε x +
        J * (a.resistance ε x - a.meanReciprocal * x) -
          (a.weightedResistance f ε x - a.meanReciprocal * primitive (primitive f) x)| ≤
        (|(a.fluxConstant f ε - J) * a.resistance ε x| +
          |J * (a.resistance ε x - a.meanReciprocal * x)|) +
            |a.weightedResistance f ε x - a.meanReciprocal * primitive (primitive f) x| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (6 * M * δ / a.meanReciprocal * (2 * a.meanReciprocal) + M * δ) + 2 * M * δ := by
      apply add_le_add _ hw
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul hc hR (abs_nonneg _) (by positivity)
      · rw [abs_mul]
        exact mul_le_mul hJ hr (abs_nonneg _) hM
    _ = 15 * M * δ := by cas using hm

end PeriodicMedium

end PDE.Elliptic.Homogenization
