/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.ColeHopf.HeatConstruction
public import PDE.Parabolic.Heat.ExponentialTilt.Kernel
import CAS.ExactTactic

/-!
# Initial trace of the Cole–Hopf Cauchy construction

For bounded continuous initial velocity and positive viscosity, the constructed
classical Burgers solution approaches the datum jointly in space and time.
Both the positive heat potential and its spatial derivative extend continuously
to time zero. The derivative relation for the exponential primitive then gives
the Burgers trace by division by its positive initial value.
The potential is also the Gaussian convolution of that exponential primitive;
the integral is finite even when the primitive is unbounded.

`exists_viscousBurgersCauchySolution` solves the initial value problem (5) of Evans, §4.4.1(b),
with `a = ν`, for every bounded continuous datum `g = u₀` by the Cole–Hopf formulas (9)-(10),
and `cauchySolution_initial_trace` shows that the solution takes the initial value
continuously. By `cauchyPotential_eq_integral`, the potential is the Gaussian integral
`(4πνt)^{-1/2} ∫ e^{-|x-y|²/(4νt)} e^{-h(y)/(2ν)} dy` inside the logarithm of (9), with `h` a
primitive of the datum as in (7).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (5)-(10).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common HeatEquation Filter Set
open scoped BoundedContinuousFunction Topology

namespace BurgersEquation.ColeHopf

/-- Gaussian decay makes the convolution of the exponential primitive integrable
at every positive time, without requiring the primitive itself to be bounded. -/
theorem integrable_cauchyPotential_kernel {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ)
    (p : ℝ^2) (hp : 0 < p 0) :
    MeasureTheory.Integrable (fun y : ℝ^1 ↦ fundamentalSolutionHeat (spatialPartCLM 1 p - y)
      (ν * p 0) * initialPotential ν u₀ (y 0)) := by
  have hI (k : ℝ) := integrable_exponentialTilt_kernel_mul hν k
    (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0)) (continuous_initialAmplitude_euclidean ν u₀)
    (initialAmplitude_euclidean_bound hν u₀) p hp
  apply ((hI (initialGrowthRate ν u₀)).add (hI (-initialGrowthRate ν u₀))).congr
  exact MeasureTheory.ae_of_all _ fun y ↦ by
    simp only [Pi.add_apply]
    rw [← mul_add, ← initialPotential_eq_tilted_amplitude]

/-- The constructed Cole–Hopf potential is the direct Gaussian integral of the
exponential primitive of the bounded continuous initial velocity. -/
theorem cauchyPotential_eq_integral {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    cauchyPotential ν u₀ p = ∫ y : ℝ^1, fundamentalSolutionHeat (spatialPartCLM 1 p - y) (ν * p 0) *
      Real.exp (-(∫ s in 0..y 0, u₀ s) / (2 * ν)) := by
  have hI (k : ℝ) := integrable_exponentialTilt_kernel_mul hν k
    (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0)) (continuous_initialAmplitude_euclidean ν u₀)
    (initialAmplitude_euclidean_bound hν u₀) p hp
  unfold cauchyPotential amplitudeHeat
  rw [exponentialTilt_initialValueSolution_eq_integral hν _ _ p hp,
    exponentialTilt_initialValueSolution_eq_integral hν _ _ p hp,
    ← MeasureTheory.integral_add (hI _) (hI _)]
  apply MeasureTheory.integral_congr_ae
  exact MeasureTheory.ae_of_all _ fun y ↦ by
    dsimp only
    rw [← mul_add, ← initialPotential_eq_tilted_amplitude]
    rfl

/-- Heat evolution of the bounded continuous derivative of the normalized amplitude. -/
def amplitudeDerivativeHeat (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) : ℝ :=
  initialValueSolution (fun y : ℝ^1 ↦ deriv (initialAmplitude ν u₀) (y 0))
    (spatialPartCLM 1 p) (p 0)

/-- A continuous extension of the potential's spatial derivative through time zero. -/
def cauchyPotentialGradient (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) : ℝ :=
  let L := initialGrowthRate ν u₀
  exponentialTiltWeight ν L p *
      (L * amplitudeHeat ν u₀ (exponentialTiltChart ν L p) +
        amplitudeDerivativeHeat ν u₀ (exponentialTiltChart ν L p)) +
    exponentialTiltWeight ν (-L) p *
      (-L * amplitudeHeat ν u₀ (exponentialTiltChart ν (-L) p) +
        amplitudeDerivativeHeat ν u₀ (exponentialTiltChart ν (-L) p))

private theorem contDiff_initialAmplitude_euclidean (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    ContDiff ℝ 1 (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0)) :=
  (contDiff_initialAmplitude ν u₀).comp (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).contDiff

private theorem initialAmplitude_euclidean_fderiv_bound {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    ∃ M, ∀ y : ℝ^1, ‖fderiv ℝ (fun z : ℝ^1 ↦ initialAmplitude ν u₀ (z 0)) y‖ ≤ M := by
  refine ⟨2 * initialGrowthRate ν u₀, fun y ↦ ?_⟩
  have hh := ((contDiff_initialAmplitude ν u₀).differentiable
    (by norm_num) (y 0)).hasDerivAt.comp_hasFDerivAt y
      (EuclideanSpace.proj (0 : Fin 1) : ℝ^1 →L[ℝ] ℝ).hasFDerivAt
  have heq : fderiv ℝ (fun z : ℝ^1 ↦ initialAmplitude ν u₀ (z 0)) y =
      deriv (initialAmplitude ν u₀) (y 0) • EuclideanSpace.proj (0 : Fin 1) := hh.fderiv
  rw [heq]
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (initialGrowthRate_nonneg hν u₀))
  intro z
  simp only [smul_apply, EuclideanSpace.coe_proj, smul_eq_mul, norm_mul]
  exact mul_le_mul (abs_deriv_initialAmplitude_le hν u₀ _)
    (PiLp.norm_apply_le z 0) (norm_nonneg _) (by positivity [initialGrowthRate_nonneg hν u₀])

private theorem partialDeriv_initialAmplitude_euclidean (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    (∂[(0 : Fin 1)] (fun y : ℝ^1 ↦ initialAmplitude ν u₀ (y 0))) =
      fun y ↦ deriv (initialAmplitude ν u₀) (y 0) := by
  funext y
  rw [PDE.partialDeriv_comp_coord 0 0
    ((contDiff_initialAmplitude ν u₀).differentiable (by norm_num) _)]
  simp only [ite_true, one_smul]

/-- The evolved amplitude derivative is the spatial derivative at positive time. -/
theorem partialDeriv_amplitudeHeat {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    (∂[1] (amplitudeHeat ν u₀)) p = amplitudeDerivativeHeat ν u₀ p := by
  have h := partialDeriv_initialValueSolution_spacetime_of_bounded_derivative
    _ (contDiff_initialAmplitude_euclidean ν u₀) (initialAmplitude_euclidean_bound hν u₀)
    (initialAmplitude_euclidean_fderiv_bound hν u₀) p hp 0
  unfold amplitudeHeat amplitudeDerivativeHeat
  simpa only [Fin.succ_zero_eq_one, partialDeriv_initialAmplitude_euclidean] using h

/-- The heat representation extends continuously through time zero. -/
theorem continuous_amplitudeHeat {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (amplitudeHeat ν u₀) :=
  (continuous_initialValueSolution_timeSpace _
    (continuous_initialAmplitude_euclidean ν u₀) (initialAmplitude_euclidean_bound hν u₀)).comp
      ((EuclideanSpace.proj (0 : Fin 2)).continuous.prodMk (spatialPartCLM 1).continuous)

/-- The spatial derivative representation also extends continuously through time zero. -/
theorem continuous_amplitudeDerivativeHeat {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (amplitudeDerivativeHeat ν u₀) :=
  (continuous_initialValueSolution_timeSpace _
    ((contDiff_initialAmplitude ν u₀).continuous_deriv_one.comp
      (EuclideanSpace.proj (0 : Fin 1)).continuous)
    ⟨2 * initialGrowthRate ν u₀, fun y ↦ abs_deriv_initialAmplitude_le hν u₀ (y 0)⟩).comp
      ((EuclideanSpace.proj (0 : Fin 2)).continuous.prodMk (spatialPartCLM 1).continuous)

/-- The constructed heat potential is continuous, including on the initial time slice. -/
theorem continuous_cauchyPotential {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (cauchyPotential ν u₀) := by
  have h (k : ℝ) : Continuous (exponentialTilt ν k (amplitudeHeat ν u₀)) :=
    (contDiff_exponentialTiltWeight ν k (r := 0)).continuous.mul
      ((continuous_amplitudeHeat hν u₀).comp
        (contDiff_exponentialTiltChart ν k (r := 0)).continuous)
  exact (h _).add (h _)

/-- The potential's gradient representation is continuous through the initial slice. -/
theorem continuous_cauchyPotentialGradient {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (cauchyPotentialGradient ν u₀) := by
  have h (k : ℝ) : Continuous (fun p ↦ exponentialTiltWeight ν k p *
      (k * amplitudeHeat ν u₀ (exponentialTiltChart ν k p) +
        amplitudeDerivativeHeat ν u₀ (exponentialTiltChart ν k p))) :=
    (contDiff_exponentialTiltWeight ν k (r := 0)).continuous.mul
      ((continuous_const.mul ((continuous_amplitudeHeat hν u₀).comp
        (contDiff_exponentialTiltChart ν k (r := 0)).continuous)).add
          ((continuous_amplitudeDerivativeHeat hν u₀).comp
            (contDiff_exponentialTiltChart ν k (r := 0)).continuous))
  exact (h _).add (h _)

/-- The continuous gradient representation agrees with the PDE derivative. -/
theorem partialDeriv_cauchyPotential {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (p : ℝ^2) (hp : 0 < p 0) :
    (∂[1] (cauchyPotential ν u₀)) p = cauchyPotentialGradient ν u₀ p := by
  have hpos (k : ℝ) : 0 < exponentialTiltChart ν k p 0 := mul_pos hν hp
  have hreg (k : ℝ) : DifferentiableAt ℝ (exponentialTilt ν k (amplitudeHeat ν u₀)) p :=
    (contDiffAt_exponentialTilt ν k _ p
      (contDiffAt_amplitudeHeat hν u₀ _ (hpos k))).differentiableAt (by simp)
  unfold cauchyPotential cauchyPotentialGradient
  rw [PDE.partialDeriv_add (hreg _) (hreg _)]
  congr 1 <;> rw [partialDeriv_exponentialTilt_space _ _ _ _
      ((contDiffAt_amplitudeHeat hν u₀ _ (hpos _)).differentiableAt (by simp)),
      partialDeriv_amplitudeHeat hν u₀ _ (hpos _)]

/-- The constructed potential takes the exponential primitive as its initial value. -/
theorem cauchyPotential_initial_value (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    cauchyPotential ν u₀ !₂[0, x] = initialPotential ν u₀ x := by
  simpa only [cauchyPotential, exponentialTilt, exponentialTiltWeight,
    exponentialTiltChart, amplitudeHeat, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, initialValueSolution_of_t_eq_zero,
    spatialPartCLM_apply, Fin.succ_zero_eq_one] using
      (initialPotential_eq_tilted_amplitude ν u₀ x).symm

/-- The continuous gradient representation has the derivative of the exponential
primitive as its initial value. -/
theorem cauchyPotentialGradient_initial_value (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    cauchyPotentialGradient ν u₀ !₂[0, x] = -(u₀ x / (2 * ν)) * initialPotential ν u₀ x := by
  simp only [cauchyPotentialGradient, exponentialTiltWeight, exponentialTiltChart,
    amplitudeHeat, amplitudeDerivativeHeat, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, initialValueSolution_of_t_eq_zero,
    spatialPartCLM_apply, Fin.succ_zero_eq_one]
  rw [(hasDerivAt_initialAmplitude ν u₀ x).deriv]
  have hden := (exponentialEnvelope_pos (initialGrowthRate ν u₀) x).ne'
  unfold initialAmplitude
  unfold exponentialEnvelope at *
  cas using hden

/-- The constructed classical Burgers solution approaches every bounded continuous
initial datum jointly as `(t, x)` approaches `(0, x₀)` from positive time. -/
theorem cauchySolution_initial_trace {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    Tendsto (cauchySolution ν u₀) (𝓝[{p : ℝ^2 | 0 < p 0}] !₂[0, x]) (𝓝 (u₀ x)) := by
  have hcont : ContinuousAt (fun p : ℝ^2 ↦
      (-2 * ν) * cauchyPotentialGradient ν u₀ p / cauchyPotential ν u₀ p) !₂[0, x] :=
    (continuous_const.mul (continuous_cauchyPotentialGradient hν u₀)).continuousAt.div
      (continuous_cauchyPotential hν u₀).continuousAt
      (by rw [cauchyPotential_initial_value]; exact (initialPotential_pos ν u₀ x).ne')
  have hvalue : (-2 * ν) * cauchyPotentialGradient ν u₀ !₂[0, x] /
      cauchyPotential ν u₀ !₂[0, x] = u₀ x := by
    rw [cauchyPotentialGradient_initial_value, cauchyPotential_initial_value]
    have hw := (initialPotential_pos ν u₀ x).ne'
    cas using hν.ne'
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {p : ℝ^2 | 0 < p 0}))
  rw [hvalue] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  simp only [cauchySolution, coleHopfTransform, Fin.succ_zero_eq_one]
  rw [partialDeriv_cauchyPotential hν u₀ p hp]

/-- Existence of a classical viscous Burgers Cauchy solution for every bounded
continuous initial velocity and every positive viscosity. The initial condition holds as a joint
limit from positive times. -/
theorem exists_viscousBurgersCauchySolution {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    ∃ u : ℝ^2 → ℝ, SolvesViscousBurgersOn ν {p : ℝ^2 | 0 < p 0} u ∧
      ∀ x : ℝ, Tendsto u (𝓝[{p : ℝ^2 | 0 < p 0}] !₂[0, x]) (𝓝 (u₀ x)) :=
  ⟨cauchySolution ν u₀, cauchySolution_solvesViscousBurgers hν u₀,
    cauchySolution_initial_trace hν u₀⟩

end BurgersEquation.ColeHopf
