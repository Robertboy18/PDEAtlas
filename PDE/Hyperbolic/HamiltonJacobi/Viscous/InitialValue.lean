/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscous.ColeHopf
public import PDE.Parabolic.Heat.InitialValue
import PDE.Parabolic.Heat.ConvolutionSpace.SpatialRegularity
import PDE.Parabolic.Heat.InfinitePropagation
import PDE.Parabolic.Heat.PointwiseIVP
import CAS.ExactTactic

/-!
# The quadratic viscous Hamilton–Jacobi Cauchy solution

Evolve `exp (-g / (2ν))` by the heat equation for time `νt`, then apply `-2ν log`.
For positive viscosity and bounded continuous data this constructs a jointly smooth
solution of `u_t + ‖∇u‖² / 2 = ν Δu` on positive time.
Positivity of the heat field justifies the logarithm and all its derivatives.

The initial-value equality and the joint right trace are separate conclusions. The
vanishing-viscosity limit is in `Viscous.VanishingViscosity`.

The solution is the explicit formula (4) of Evans, §4.4.1(a), with `a = ν` and `b = 1/2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(a), equations (1)-(4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)
open scoped ContDiff

namespace HamiltonJacobi.ColeHopf

variable {n : ℕ}

/-- The Hopf–Cole Cauchy solution: heat evolution of the exponential datum at time `νt`,
followed by the logarithmic substitution. Its PDE interpretation requires `ν > 0`. -/
noncomputable def initialValueSolution (ν : ℝ) (g : ℝ^n → ℝ) : ℝ^n → ℝ → ℝ :=
  logarithmicTransform ν (fun x t ↦ HeatEquation.initialValueSolution
    (fun y ↦ Real.exp (-g y / (2 * ν))) x (ν * t))

/-- The time-zero branch recovers the datum for every nonzero transform parameter.
Analytic convergence from positive time is proved separately below. -/
@[simp]
theorem initialValueSolution_zero {ν : ℝ} (hν : ν ≠ 0) (g : ℝ^n → ℝ) (x : ℝ^n) :
    initialValueSolution ν g x 0 = g x := by
  simp only [initialValueSolution, logarithmicTransform, mul_zero,
    HeatEquation.initialValueSolution_of_t_eq_zero, Real.log_exp]
  cas using hν

/-- A bounded potential gives a bounded exponential datum, even on infinite-volume space. -/
private theorem exponential_datum_bounded {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ}
    (hgb : ∃ M, ∀ y, |g y| ≤ M) :
    ∃ B, ∀ y, |Real.exp (-g y / (2 * ν))| ≤ B := by
  obtain ⟨M, hM⟩ := hgb
  refine ⟨Real.exp (M / (2 * ν)), fun y ↦ ?_⟩
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hgy := (abs_le.mp (hM y)).1
  exact div_le_div_of_nonneg_right (by linarith only [hgy]) (by positivity)

/-- The evolved exponential datum stays strictly positive. This uses the positive
heat convolution at positive time and the exponential datum on the totalized other branch. -/
private theorem scaled_heat_pos {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ}
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) (t : ℝ) :
    0 < HeatEquation.initialValueSolution (fun y ↦ Real.exp (-g y / (2 * ν))) x (ν * t) := by
  by_cases ht : ν * t ≤ 0
  · rw [HeatEquation.initialValueSolution_of_t_le_zero _ _ ht]
    exact Real.exp_pos _
  · exact HeatEquation.initialValueSolution_pos_of_nonneg_of_exists_pos _
      (Real.continuous_exp.comp (hg.neg.div_const (2 * ν))) (exponential_datum_bounded hν hgb)
      (fun y ↦ (Real.exp_pos _).le) ⟨0, Real.exp_pos _⟩ x (ν * t) (lt_of_not_ge ht)

/-- The Cole–Hopf solution is jointly smooth at positive time. Heat evolution
smooths the exponential datum, and strict positivity lets us take the logarithm. -/
theorem contDiffAt_initialValueSolution_timeSpace {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ}
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun z : ℝ × ℝ^n ↦ initialValueSolution ν g z.2 z.1) (t, x) := by
  have hheat := HeatEquation.contDiffAt_initialValueSolution_timeSpace
    (fun y ↦ Real.exp (-g y / (2 * ν))) x (ν * t) (mul_pos hν ht)
    (Real.continuous_exp.comp (hg.neg.div_const (2 * ν))) (exponential_datum_bounded hν hgb)
  have hscale : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ^n ↦ (ν * z.1, z.2)) (t, x) :=
    (contDiffAt_const.mul contDiffAt_fst).prodMk contDiffAt_snd
  have hscaled : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ^n ↦ HeatEquation.initialValueSolution
        (fun y ↦ Real.exp (-g y / (2 * ν))) z.2 (ν * z.1)) (t, x) := by
    apply ContDiffAt.comp (g := fun z : ℝ × ℝ^n ↦ HeatEquation.initialValueSolution
        (fun y ↦ Real.exp (-g y / (2 * ν))) z.2 z.1) (t, x) hheat hscale
  exact (hscaled.log (scaled_heat_pos hν hg hgb x t).ne').const_smul (-2 * ν)

/-- Scaling heat time by ν gives the diffusivity ν in its classical equation. -/
private theorem hasDerivAt_scaled_heat {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ} (hg : Continuous g)
    (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ HeatEquation.initialValueSolution (fun y ↦ Real.exp (-g y / (2 * ν))) x
      (ν * s)) (ν * laplacian (fun z ↦ HeatEquation.initialValueSolution
      (fun y ↦ Real.exp (-g y / (2 * ν))) z (ν * t)) x) t := by
  let h : ℝ^n → ℝ := fun y ↦ Real.exp (-g y / (2 * ν))
  have hh := HeatEquation.initialValueSolution_isPointwiseHomogeneousInitialValueSolution
    (n := n) h (Real.continuous_exp.comp (hg.neg.div_const (2 * ν)))
      (exponential_datum_bounded hν hgb)
  have heq : deriv (HeatEquation.initialValueSolution h x) (ν * t) =
      laplacian (fun z ↦ HeatEquation.initialValueSolution h z (ν * t)) x :=
    sub_eq_zero.mp (hh.residual_eq x (ν * t) (mul_pos hν ht))
  have hd := (hh.differentiableAt_time x (ν * t) (mul_pos hν ht)).hasDerivAt.comp t
    ((hasDerivAt_id t).const_mul ν)
  rw [heq] at hd
  simpa only [h, Function.comp_def, mul_one, mul_comm] using hd

/-- For positive viscosity and bounded continuous data, each positive-time spatial slice
of the Hopf–Cole Cauchy solution is `C²`. -/
theorem contDiffAt_initialValueSolution_space {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ} (hg : Continuous g)
    (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (fun y ↦ initialValueSolution ν g y t) x :=
  ((contDiffAt_initialValueSolution_timeSpace hν hg hgb x ht).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp)

/-- Each positive-time trace of the Hopf–Cole Cauchy solution is differentiable. -/
theorem differentiableAt_initialValueSolution_time {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ}
    (hg : Continuous g) (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (initialValueSolution ν g x) t :=
  ((contDiffAt_initialValueSolution_timeSpace hν hg hgb x ht).comp t
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)

/-- The constructed field solves `u_t + ‖∇u‖²/2 = ν Δu` pointwise on positive time.
Both derivatives are supplied by the preceding regularity theorems. -/
theorem initialValueSolution_residual_zero {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ} (hg : Continuous g)
    (hgb : ∃ M, ∀ y, |g y| ≤ M) (x : ℝ^n) {t : ℝ} (ht : 0 < t) :
    viscousHamiltonJacobiResidual ν (initialValueSolution ν g) x t = 0 := by
  have hd := hasDerivAt_scaled_heat hν hg hgb x ht
  unfold initialValueSolution
  apply (logarithmicTransform_solves_iff (n := n) (v := fun y s ↦ HeatEquation.initialValueSolution
      (fun z ↦ Real.exp (-g z / (2 * ν))) y (ν * s)) (x := x) (t := t) hν.ne' hd.differentiableAt
    (HeatEquation.contDiff_initialValueSolution_space (n := n) _ (ν * t) (mul_pos hν ht)
      (Real.continuous_exp.comp (hg.neg.div_const (2 * ν)))
      (exponential_datum_bounded hν hgb)).contDiffAt (scaled_heat_pos hν hg hgb x t)).2
  exact hd.deriv

/-- The Hopf–Cole solution extends continuously to each point of the initial boundary.
This is a joint right trace in space and time, not only the assigned value at time zero. -/
theorem initialValueSolution_initial_trace {ν : ℝ} (hν : 0 < ν) {g : ℝ^n → ℝ} (hg : Continuous g)
    (hgb : ∃ M, ∀ y, |g y| ≤ M) (x₀ : ℝ^n) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x t, ‖x - x₀‖ < δ → 0 < t → t < δ → |initialValueSolution ν g x t - g x₀| < ε := by
  let h : ℝ^n → ℝ := fun y ↦ Real.exp (-g y / (2 * ν))
  have hh := HeatEquation.initialValueSolution_isPointwiseHomogeneousInitialValueSolution
    (n := n) h (Real.continuous_exp.comp (hg.neg.div_const (2 * ν)))
      (exponential_datum_bounded hν hgb)
  have hlog : ContinuousAt (fun r : ℝ ↦ -2 * ν * Real.log r) (h x₀) :=
    (Real.continuousAt_log (Real.exp_pos _).ne').const_mul (-2 * ν)
  obtain ⟨η, hη, hlogη⟩ := Metric.continuousAt_iff.mp hlog ε hε
  obtain ⟨ρ, hρ, htrace⟩ := hh.continuousAt_initialBoundary x₀ η hη
  refine ⟨min ρ (ρ / ν), lt_min hρ (div_pos hρ hν), fun x t hx ht htδ ↦ ?_⟩
  have hxt : ‖x - x₀‖ < ρ := hx.trans_le (min_le_left _ _)
  have htime : ν * t < ρ := by
    have h := (lt_div_iff₀ hν).mp (htδ.trans_le (min_le_right _ _))
    simpa only [mul_comm] using h
  have hhclose : dist (HeatEquation.initialValueSolution h x (ν * t)) (h x₀) < η := by
    simpa only [Real.dist_eq] using htrace x (ν * t) hxt (mul_pos hν ht) htime
  have hclose := hlogη hhclose
  have hinverse : -2 * ν * Real.log (h x₀) = g x₀ := by
    simp only [h, Real.log_exp]
    have hne : ν ≠ 0 := hν.ne'
    cas using hne
  change |-2 * ν * Real.log (HeatEquation.initialValueSolution h x (ν * t)) - g x₀| < ε
  simpa only [Real.dist_eq, hinverse] using hclose

end HamiltonJacobi.ColeHopf
