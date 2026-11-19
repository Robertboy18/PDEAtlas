/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.Radon.Real
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy
public import PDE.Hyperbolic.Models.Wave.Radon.OddDimension

/-!
# A real wave solution from hyperplane data

For real Schwartz initial data, taking the real part of the Fourier derivation
gives a formula entirely in terms of real hyperplane integrals and ordinary
derivatives. In three dimensions we use that expression to define `radonSolution`.
Its equality with the Fourier solution supplies joint C² regularity, the wave
equation, and the assigned displacement and velocity at time zero.

The coefficient is `-1/(16π²)` when the sphere has full Euclidean surface measure.
At time zero the two displacement terms coincide and recover the Radon inversion
coefficient `-1/(8π²)`. All formulas use unit wave speed.
-/

@[expose] public noncomputable section

open PDE (SatisfiesPDEProblem)
open MeasureTheory
open scoped RealInnerProductSpace SchwartzMap

namespace WaveEquation.Fourier

open PDE.Common PDE.Analysis.Fourier

/-- Real Schwartz data in odd dimension give a wave formula using ordinary
derivatives of their real hyperplane integrals. -/
theorem realSolution_eq_integral_iteratedDeriv_radonTransform {n : ℕ} (g h : 𝓢(ℝ^n, ℝ)) (k : ℕ)
    (hdim : n = 2 * k + 1) (t : ℝ) (x : ℝ^n) :
    realSolution g h (timeSpaceCons t x) =
      ((-1 : ℝ) ^ k / (4 * (2 * Real.pi) ^ (2 * k))) *
        ∫ θ : Metric.sphere (0 : ℝ^n) 1,
          iteratedDeriv (2 * k) (radonTransform g (θ : ℝ^n)) (⟪(θ : ℝ^n), x⟫ + t) +
            iteratedDeriv (2 * k) (radonTransform g (θ : ℝ^n)) (⟪(θ : ℝ^n), x⟫ - t) +
            (∫ y in ⟪(θ : ℝ^n), x⟫ - t..⟪(θ : ℝ^n), x⟫ + t,
              iteratedDeriv (2 * k) (radonTransform h (θ : ℝ^n)) y)
          ∂(volume : Measure (ℝ^n)).toSphere := by
  have hn : n ≠ 0 := by omega
  let : NeZero n := ⟨hn⟩
  let gC := g.postcompCLM Complex.ofRealCLM
  let hC := h.postcompCLM Complex.ofRealCLM
  have hd (f : 𝓢(ℝ^n, ℝ)) (θ : Metric.sphere (0 : ℝ^n) 1) (s : ℝ) : iteratedDeriv (2 * k)
          (radonTransform (f.postcompCLM Complex.ofRealCLM) (θ : ℝ^n)) s =
        Complex.ofReal (iteratedDeriv (2 * k) (radonTransform f (θ : ℝ^n)) s) := by
    have he : radonTransform (f.postcompCLM Complex.ofRealCLM) (θ : ℝ^n) =
        Complex.ofRealCLM ∘ radonTransform f (θ : ℝ^n) := by
      funext y
      exact radonTransform_ofReal f _ y
    rw [he]
    exact Complex.ofRealCLM.iteratedDeriv_comp_left
      (f.contDiff_radonTransform_real (θ := (θ : ℝ^n)) (by simp) _).contDiffAt
  have hw := cauchySolution_eq_integral_iteratedDeriv_radonTransform gC hC k
    (by simpa using hdim) t x
  dsimp only [gC, hC] at hw
  simp_rw [hd] at hw
  simp only [intervalIntegral.integral_ofReal, ← Complex.ofReal_add] at hw
  rw [integral_complex_ofReal] at hw
  simp only [Complex.real_smul, ← Complex.ofReal_mul] at hw
  have hr := congrArg Complex.re hw
  simp only [Complex.ofReal_re] at hr
  simpa [realSolution, Function.comp_def, PDE.time] using hr

/-- The three-dimensional real wave formula, with the velocity integral reduced
to endpoint derivatives by the fundamental theorem of calculus. -/
theorem realSolution_eq_integral_secondDeriv_radonTransform (g h : 𝓢(ℝ^3, ℝ)) (t : ℝ) (x : ℝ^3) :
    realSolution g h (timeSpaceCons t x) = (-1 / (16 * Real.pi ^ 2) : ℝ) *
      ∫ θ : Metric.sphere (0 : ℝ^3) 1,
        deriv (deriv (radonTransform g (θ : ℝ^3))) (⟪(θ : ℝ^3), x⟫ + t) +
          deriv (deriv (radonTransform g (θ : ℝ^3))) (⟪(θ : ℝ^3), x⟫ - t) +
          (deriv (radonTransform h (θ : ℝ^3)) (⟪(θ : ℝ^3), x⟫ + t) -
            deriv (radonTransform h (θ : ℝ^3)) (⟪(θ : ℝ^3), x⟫ - t))
        ∂(volume : Measure (ℝ^3)).toSphere := by
  have hw := realSolution_eq_integral_iteratedDeriv_radonTransform g h 1 rfl t x
  norm_num only [Nat.mul_one, pow_one, iteratedDeriv_succ, iteratedDeriv_zero] at hw
  have hi (θ : Metric.sphere (0 : ℝ^3) 1) (a b : ℝ) :
      (∫ y in a..b, deriv (deriv (radonTransform h (θ : ℝ^3))) y) =
        deriv (radonTransform h (θ : ℝ^3)) b -
          deriv (radonTransform h (θ : ℝ^3)) a := by
    have hc := h.contDiff_radonTransform_real (θ := (θ : ℝ^3)) (by simp) 2
    exact intervalIntegral.integral_deriv_eq_sub (fun y _ ↦ hc.differentiable_deriv_two y)
      (hc.deriv'.continuous_deriv_one.intervalIntegrable a b)
  simp_rw [hi] at hw
  convert hw using 1
  congr 1
  ring

end WaveEquation.Fourier

namespace WaveEquation

open PDE.Common PDE.Analysis.Fourier

/-- The three-dimensional unit-speed wave reconstructed from the real Radon
transforms of its Schwartz displacement and velocity data. -/
def radonSolution (g h : 𝓢(ℝ^3, ℝ)) (p : ℝ^4) : ℝ :=
  (-1 / (16 * Real.pi ^ 2) : ℝ) *
    ∫ θ : Metric.sphere (0 : ℝ^3) 1,
      deriv (deriv (radonTransform g (θ : ℝ^3)))
          (⟪(θ : ℝ^3), spatialPartCLM 3 p⟫ + PDE.time p) +
        deriv (deriv (radonTransform g (θ : ℝ^3)))
          (⟪(θ : ℝ^3), spatialPartCLM 3 p⟫ - PDE.time p) +
        (deriv (radonTransform h (θ : ℝ^3))
            (⟪(θ : ℝ^3), spatialPartCLM 3 p⟫ + PDE.time p) -
          deriv (radonTransform h (θ : ℝ^3))
            (⟪(θ : ℝ^3), spatialPartCLM 3 p⟫ - PDE.time p))
      ∂(volume : Measure (ℝ^3)).toSphere

/-- Radon reconstruction and Fourier evolution give the same spacetime function. -/
theorem radonSolution_eq_fourier (g h : 𝓢(ℝ^3, ℝ)) :
    radonSolution g h = Fourier.realSolution g h := by
  funext p
  have he := Fourier.realSolution_eq_integral_secondDeriv_radonTransform g h
    (PDE.time p) (spatialPartCLM 3 p)
  simpa only [radonSolution, PDE.time, timeSpaceCons_spatialPartCLM] using he.symm

/-- The reconstructed wave is jointly C² in time and space. -/
theorem contDiff_two_radonSolution (g h : 𝓢(ℝ^3, ℝ)) :
    ContDiff ℝ 2 (radonSolution g h) := by
  rw [radonSolution_eq_fourier]
  exact Fourier.contDiff_two_realSolution g h

/-- Radon reconstruction solves the ordinary-derivative wave equation and
attains both assigned Cauchy data. -/
theorem radonSolution_satisfiesResidualAssignedCauchyData (g h : 𝓢(ℝ^3, ℝ)) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) (radonSolution g h) := by
  rw [radonSolution_eq_fourier]
  exact Fourier.realSolution_satisfiesResidualAssignedCauchyData g h

end WaveEquation
