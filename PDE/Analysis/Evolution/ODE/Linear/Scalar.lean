/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.Gronwall.Variable
public import PDE.Analysis.Integration.Primitive.Regularity

/-!
# Scalar integrating factors

`scalarLinearSolution a b t₀ q₀` is the integrating-factor solution
`q(t) = e^{-A(t)} (q₀ + ∫_{t₀}^t e^{A(v)} b(v) dv)`, `A(t) = ∫_{t₀}^t a`, of
`q' = b - a q` with `q(t₀) = q₀`. It solves the equation at every time when `a` and
`b` are continuous, and it is smooth when they are smooth.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace PDE.Analysis.Evolution

/-- The integrating-factor solution of `q' = b - a q` with value `q₀` at `t₀`. -/
def scalarLinearSolution (a b : ℝ → ℝ) (t₀ q₀ t : ℝ) : ℝ :=
  Real.exp (-(∫ s in t₀..t, a s)) *
    (q₀ + ∫ v in t₀..t, Real.exp (∫ s in t₀..v, a s) * b v)

/-- The integrating-factor solution has the prescribed initial value. -/
@[simp]
theorem scalarLinearSolution_initial (a b : ℝ → ℝ) (t₀ q₀ : ℝ) :
    scalarLinearSolution a b t₀ q₀ t₀ = q₀ := by
  simp [scalarLinearSolution]

/-- For continuous `a` and `b`, `scalarLinearSolution` solves `q' = b - a q` at every
real time. -/
theorem hasDerivAt_scalarLinearSolution {a b : ℝ → ℝ}
    (ha : Continuous a) (hb : Continuous b) (t₀ q₀ t : ℝ) :
    HasDerivAt (scalarLinearSolution a b t₀ q₀)
      (b t - a t * scalarLinearSolution a b t₀ q₀ t) t := by
  have hA (t : ℝ) : HasDerivAt (fun v ↦ ∫ s in t₀..v, a s) (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable t₀ t)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hc : Continuous (fun v ↦ Real.exp (∫ s in t₀..v, a s) * b v) :=
    (Real.continuous_exp.comp (continuous_iff_continuousAt.mpr
      (fun v ↦ (hA v).continuousAt))).mul hb
  have hB := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable t₀ t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have h := (hA t).neg.exp.mul (hB.const_add q₀)
  convert! h using 1
  dsimp [scalarLinearSolution]
  have he : Real.exp (-(∫ s in t₀..t, a s)) * Real.exp (∫ s in t₀..t, a s) = 1 := by
    rw [← Real.exp_add]
    simp
  nlinarith [congrArg (fun v : ℝ ↦ v * b t) he]

/-- Smooth coefficients give a smooth solution of the same explicit formula. -/
theorem contDiff_scalarLinearSolution {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (t₀ q₀ : ℝ) :
    ContDiff ℝ ∞ (scalarLinearSolution a b t₀ q₀) := by
  have hA : ContDiff ℝ ∞ (fun t ↦ ∫ s in t₀..t, a s) := by
    simpa using contDiff_intervalIntegral_of_contDiff ha t₀
  have hB : ContDiff ℝ ∞
      (fun t ↦ ∫ v in t₀..t, Real.exp (∫ s in t₀..v, a s) * b v) := by
    simpa using contDiff_intervalIntegral_of_contDiff (hA.exp.mul hb) t₀
  exact hA.neg.exp.mul (contDiff_const.add hB)

end PDE.Analysis.Evolution
