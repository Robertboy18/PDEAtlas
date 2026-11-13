/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.InitialData
public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf
public import PDE.Parabolic.Heat.ExponentialTilt
public import PDE.Parabolic.Heat.ConvolutionSpace.OneDimensional
public import PDE.Parabolic.Heat.ConvolutionSpace.InitialContinuity
import PDE.Parabolic.Heat.InfinitePropagation
import CAS.ExactTactic

/-!
# Positive heat construction for arbitrary bounded continuous Burgers data

The exponential primitive need not be bounded. Its bounded amplitude is evolved
by the Gaussian heat convolution, then tilted with the two opposite growth rates.
Their sum is a positive smooth solution of `vₜ = νvₓₓ`. The analytic
Cole–Hopf theorem therefore gives a classical viscous Burgers solution.

All solution properties are derived from the datum and the positive viscosity.
The initial Burgers trace is proved in `Cauchy`.

In the notation of Evans, §4.4.1(b), with `a = ν`, `cauchyPotential` is the positive solution
`v` of the heat equation whose logarithm gives (9), and `cauchySolution = -2ν (log v)_x` is the
solution (10) of the viscous Burgers equation (5) (`cauchySolution_solvesViscousBurgers`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common HeatEquation
open scoped BoundedContinuousFunction ContDiff

namespace BurgersEquation.ColeHopf

/-- The ordinary Gaussian heat evolution of the bounded normalized amplitude. -/
def amplitudeHeat (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) : ℝ :=
  initialValueSolution (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0))
    (spatialPartCLM 1 p) (p 0)

/-- The positive heat potential, represented by two tilted Gaussian integrals. -/
def cauchyPotential (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) : ℝ :=
  exponentialTilt ν (initialGrowthRate ν u₀) (amplitudeHeat ν u₀) p +
    exponentialTilt ν (-initialGrowthRate ν u₀) (amplitudeHeat ν u₀) p

/-- The Cole–Hopf Cauchy solution at positive time. Its time-zero trace is proved separately. -/
def cauchySolution (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) : ℝ^2 → ℝ :=
  coleHopfTransform ν (cauchyPotential ν u₀)

/-- The normalized amplitude is continuous in Euclidean one-dimensional coordinates. -/
theorem continuous_initialAmplitude_euclidean (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0)) :=
  (continuous_initialAmplitude ν u₀).comp (EuclideanSpace.proj (0 : Fin 1)).continuous

/-- The Gaussian datum has a derived uniform bound of one. -/
theorem initialAmplitude_euclidean_bound {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    ∃ M, ∀ y : ℝ^1, |initialAmplitude ν u₀ (y 0)| ≤ M :=
  ⟨1, fun y ↦ by
    rw [abs_of_pos (initialAmplitude_pos ν u₀ _)]
    exact initialAmplitude_le_one hν u₀ _⟩

/-- The bounded-amplitude heat evolution is jointly smooth at positive time. -/
theorem contDiffAt_amplitudeHeat {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    ContDiffAt ℝ ∞ (amplitudeHeat ν u₀) p :=
  (contDiffOn_initialValueSolution_spacetime _ (continuous_initialAmplitude_euclidean ν u₀)
    (initialAmplitude_euclidean_bound hν u₀)).contDiffAt ((isOpen_lt continuous_const
        (EuclideanSpace.proj (0 : Fin 2)).continuous).mem_nhds hp)

/-- The bounded-amplitude heat evolution has strictly positive values at positive time. -/
theorem amplitudeHeat_pos {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ)
    (p : ℝ^2) (hp : 0 < p 0) : 0 < amplitudeHeat ν u₀ p :=
  initialValueSolution_pos_of_nonneg_of_exists_pos _
    (continuous_initialAmplitude_euclidean ν u₀) (initialAmplitude_euclidean_bound hν u₀)
    (fun y ↦ (initialAmplitude_pos ν u₀ (y 0)).le) ⟨0, initialAmplitude_pos ν u₀ _⟩ _ _ hp

/-- The bounded-amplitude heat evolution solves the unit heat equation. -/
theorem amplitudeHeat_heat_equation {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    (∂[0] (amplitudeHeat ν u₀)) p = (∂[1] (∂[1] (amplitudeHeat ν u₀))) p :=
  initialValueSolution_oneDimensional_heat_equation _
    (continuous_initialAmplitude_euclidean ν u₀) (initialAmplitude_euclidean_bound hν u₀) p hp

/-- The constructed heat potential is jointly smooth throughout positive time. -/
theorem contDiffAt_cauchyPotential {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    ContDiffAt ℝ ∞ (cauchyPotential ν u₀) p := by
  have htilt (k : ℝ) : ContDiffAt ℝ ∞ (exponentialTilt ν k (amplitudeHeat ν u₀)) p :=
    contDiffAt_exponentialTilt ν k _ p (contDiffAt_amplitudeHeat hν u₀ _
        (by simpa only [exponentialTiltChart, PiLp.toLp_apply, Matrix.cons_val_zero] using
          mul_pos hν hp))
  exact (htilt _).add (htilt _)

/-- Positivity of the Gaussian evolution makes division in Cole–Hopf legitimate. -/
theorem cauchyPotential_pos {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ)
    (p : ℝ^2) (hp : 0 < p 0) : 0 < cauchyPotential ν u₀ p := by
  have htilt (k : ℝ) : 0 < exponentialTilt ν k (amplitudeHeat ν u₀) p :=
    mul_pos (Real.exp_pos _) (amplitudeHeat_pos hν u₀ _
      (by simpa only [exponentialTiltChart, PiLp.toLp_apply, Matrix.cons_val_zero] using
        mul_pos hν hp))
  exact add_pos (htilt _) (htilt _)

/-- The two tilted Gaussian integrals solve the heat equation with viscosity `ν`. -/
theorem cauchyPotential_heat_equation {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    (∂[0] (cauchyPotential ν u₀)) p = ν * (∂[1] (∂[1] (cauchyPotential ν u₀))) p := by
  have hpos (k : ℝ) : 0 < exponentialTiltChart ν k p 0 := mul_pos hν hp
  have hreg (k : ℝ) : ContDiffAt ℝ 2 (exponentialTilt ν k (amplitudeHeat ν u₀)) p :=
    contDiffAt_exponentialTilt ν k _ p
      ((contDiffAt_amplitudeHeat hν u₀ _ (hpos k)).of_le (by norm_num))
  have heq (k : ℝ) : (∂[0] (exponentialTilt ν k (amplitudeHeat ν u₀))) p =
        ν * (∂[1] (∂[1] (exponentialTilt ν k (amplitudeHeat ν u₀)))) p :=
    exponentialTilt_heat_equation ν k _ p
      ((contDiffAt_amplitudeHeat hν u₀ _ (hpos k)).of_le (by norm_num))
      (amplitudeHeat_heat_equation hν u₀ _ (hpos k))
  unfold cauchyPotential
  rw [PDE.partialDeriv_add ((hreg _).differentiableAt (by norm_num))
    ((hreg _).differentiableAt (by norm_num)),
    PDE.secondPartialDeriv_add_at 1 1 (hreg _) (hreg _), heq, heq]
  cas

/-- For every bounded continuous datum and positive viscosity, the constructed field
is a classical `C²` solution of `uₜ + uuₓ = νuₓₓ` throughout positive time. -/
theorem cauchySolution_solvesViscousBurgers {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    SolvesViscousBurgersOn ν {p : ℝ^2 | 0 < p 0} (cauchySolution ν u₀) := by
  apply coleHopfTransform_solvesViscousBurgersOn ν _
    (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 2)).continuous)
  · exact fun p hp ↦ ((contDiffAt_cauchyPotential hν u₀ p hp).of_le (by norm_num)).contDiffWithinAt
  · exact fun p hp ↦ (cauchyPotential_pos hν u₀ p hp).ne'
  · exact ⟨fun p hp ↦ (contDiffAt_cauchyPotential hν u₀ p hp).of_le (by norm_num),
      cauchyPotential_heat_equation hν u₀⟩

end BurgersEquation.ColeHopf
