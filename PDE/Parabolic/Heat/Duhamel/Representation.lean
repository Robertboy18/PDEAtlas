/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Parabolic.Heat.InitialValue

/-!
# Duhamel representation for the heat equation

The source contribution is the integral of the heat evolution of each source slice. We define that
formula and its sum with the initial-data evolution, write it as a source-time integral of heat
evolutions, and check the initial value and the zero-forcing case. These are Evans's Duhamel formula
(13) and the combined formula (17) in §2.3.1(c); the slices are the solutions `u(·; s)` of his
problems (12ₛ).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(c), Duhamel's principle, (12ₛ) and (13), p. 49, and
  (17), p. 51.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise Topology Interval
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- Duhamel integral formula for a non-homogeneous heat source. -/
noncomputable def nonhomogeneousSolution (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else
  ∫ s in Set.Icc 0 t, ∫ y : ℝ^n, shiftedFundamentalSolutionHeat x y t s *
      f (timeSpaceCons (n := n) s y)

/-- The heat-kernel convolution of the initial data `g` plus the Duhamel term of the
source `f`. -/
noncomputable def generalSolution
    (f : ℝ^(n + 1) → ℝ) (g : ℝ^n → ℝ)
    (x : ℝ^n) (t : ℝ) : ℝ :=
  initialValueSolution g x t + nonhomogeneousSolution f x t

/-- Away from the measure-zero endpoint `s = t`, the shifted-kernel integrand is the homogeneous
heat evolution of the spatial source slice at time `s`. This is the semigroup form of Duhamel's
formula used in the differentiation argument. -/
theorem nonhomogeneousSolution_eq_integral_initialValueSolution
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    nonhomogeneousSolution (n := n) f x t =
      ∫ s in Set.Icc 0 t,
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y))
          x (t - s) := by
  simp only [nonhomogeneousSolution, not_le_of_gt ht]
  rw [integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo]
  apply integral_congr_ae
  refine ae_restrict_of_forall_mem measurableSet_Ioo ?_
  intro s hs
  have hts : 0 < t - s := sub_pos.mpr hs.2
  simp [initialValueSolution, shiftedFundamentalSolutionHeat, not_le_of_gt hts]

/-- The Duhamel term has zero value at the initial time. -/
theorem nonhomogeneousSolution_initial_value
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) :
    nonhomogeneousSolution (n := n) f x 0 = 0 := by
  simp [nonhomogeneousSolution]

/-- The combined Duhamel formula has the prescribed initial value. -/
theorem generalSolution_initial_value
    (f : ℝ^(n + 1) → ℝ)
    (g : ℝ^n → ℝ)
    (x : ℝ^n) :
    generalSolution (n := n) f g x 0 = g x := by
  simp [generalSolution, initialValueSolution_of_t_eq_zero,
    nonhomogeneousSolution_initial_value]

/-- The Duhamel term for zero forcing is identically zero. -/
theorem nonhomogeneousSolution_zero
    (x : ℝ^n) (t : ℝ) :
    nonhomogeneousSolution (n := n)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ)) x t = 0 := by
  by_cases ht : t ≤ 0
  · simp [nonhomogeneousSolution, ht]
  · simp [nonhomogeneousSolution, ht]

/-- With zero forcing, the combined heat formula reduces to the initial-data heat-kernel formula. -/
theorem generalSolution_zero_forcing
    (g : ℝ^n → ℝ)
    (x : ℝ^n) (t : ℝ) :
    generalSolution (n := n)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ)) g x t =
        initialValueSolution (n := n) g x t := by
  simp [generalSolution, nonhomogeneousSolution_zero (n := n) x t]

/-- Clamping source times and the upper endpoint to zero gives a single interval-integral formula
for the totalized Duhamel solution. -/
theorem nonhomogeneousSolution_eq_intervalIntegral_clamp
    (f : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t : ℝ) :
    nonhomogeneousSolution f x t =
      ∫ s in 0..max 0 t, initialValueSolution
        (fun y ↦ f (timeSpaceCons (max 0 s) y)) x (max 0 t - s) := by
  by_cases ht : t ≤ 0
  · simp [nonhomogeneousSolution, ht]
  · have hpos : 0 < t := lt_of_not_ge ht
    rw [max_eq_right hpos.le,
      nonhomogeneousSolution_eq_integral_initialValueSolution f x t hpos,
      intervalIntegral.integral_of_le hpos.le, integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    simp only [max_eq_right hs.1.le]

end HeatEquation
