/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import PDE.Parabolic.Heat.InitialValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import PDE.Parabolic.Heat.ConvolutionSpace.GaussianDomination
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Joint differentiability of heat-kernel convolutions

For bounded continuous data `g`, the heat evolution `u(t, x) = ∫ Γ(x - y, t) g(y) dy` is
jointly Fréchet differentiable in `(t, x)` at every point with `t > 0`. The proof
differentiates under the integral sign in the product variable `(t, x)`, using the locally
uniform Gaussian majorant `exists_integrable_bound_heatKernel_timeSpace` from
`GaussianDomination`. Separate differentiability in `t` and in `x` is proved in
`ConvolutionTime` and `ConvolutionSpace.SpatialDerivatives`. Joint differentiability lets the
heat equation be read at `(t, x)` with `∂ₜ` and `Δ` the partial derivatives of a differentiable
function of two variables.

## Main results

* `differentiableAt_initialValueSolution_timeSpace`: joint differentiability of
  `(t, x) ↦ initialValueSolution g x t` at every `(t, x)` with `t > 0`.

## Implementation notes

High-priority local instances for the additive group and module structures on `ℝ` and
`ℝ × ℝ^n`, all definitionally equal to the canonical ones, steer instance search inside
this proof. They are local to this file.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1, Theorem 1(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common
open ConvolutionSpace

variable {n : ℕ}

@[reducible] private noncomputable def jointHeatRealAddCommGroup : AddCommGroup ℝ :=
  Real.normedCommRing.toCommRing.toAddCommGroup

@[reducible] private noncomputable def jointHeatRealModule : Module ℝ ℝ :=
  (NormedAlgebra.toNormedSpace ℝ).toModule

@[reducible] private noncomputable def jointHeatTimeSpaceAddCommGroup :
    AddCommGroup (ℝ × ℝ^n) :=
  Prod.normedAddCommGroup.toAddCommGroup

@[reducible] private noncomputable def jointHeatTimeSpaceModule :
    Module ℝ (ℝ × ℝ^n) :=
  Prod.normedSpace.toModule

attribute [local instance 2000] jointHeatRealAddCommGroup jointHeatRealModule
  jointHeatTimeSpaceAddCommGroup jointHeatTimeSpaceModule

/-- Bounded continuous initial data has a jointly differentiable heat evolution at every
positive time-space point. -/
theorem differentiableAt_initialValueSolution_timeSpace
    (g : ℝ^n → ℝ) (x : ℝ^n)
    (t : ℝ) (ht : 0 < t)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ y, |g y| ≤ M) :
    DifferentiableAt ℝ
      (fun p : ℝ × ℝ^n ↦
        initialValueSolution (n := n) g p.2 p.1)
      (t, x) := by
  classical
  let μ : MeasureTheory.Measure (ℝ^n) := MeasureTheory.volume
  let ε : ℝ := min (t / 2) 1
  have hε : 0 < ε := lt_min (half_pos ht) one_pos
  have hεt : ε ≤ t / 2 := min_le_left _ _
  let F : ℝ × ℝ^n → (ℝ^n) → ℝ := fun q y ↦
    fundamentalSolutionHeat (n := n) (q.2 - y) q.1 * g y
  let F' : ℝ × ℝ^n → (ℝ^n) → (ℝ × ℝ^n) →L[ℝ] ℝ := fun q y ↦
    (g y) •
      ContinuousLinearMap.coprod
        (((‖q.2 - y‖ ^ 2 / (4 * q.1 ^ 2) - (n : ℝ) / (2 * q.1)) *
              fundamentalSolutionHeat (n := n) (q.2 - y) q.1) •
          (1 : ℝ →L[ℝ] ℝ))
        ((-(1 / (2 * q.1)) * fundamentalSolutionHeat (n := n) (q.2 - y) q.1) •
          innerSL ℝ (q.2 - y))
  have htime_pos (q : ℝ × ℝ^n) (hq : q ∈ Metric.ball (t, x) ε) : 0 < q.1 := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hq
    linarith [hq.1.1]
  have hkernel (s : ℝ) (hs : 0 < s) :
      Continuous fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z s :=
    continuous_iff_continuousAt.mpr fun z ↦
      (hasFDerivAt_fundamentalSolutionHeat_space s hs z).continuousAt
  obtain ⟨bound, hbound_int, hbound⟩ :=
    exists_integrable_bound_heatKernel_timeSpace (n := n) g x t ht hg_bdd
  have hF_meas :
      ∀ᶠ q in nhds (t, x), MeasureTheory.AEStronglyMeasurable (F q) μ := by
    filter_upwards [Metric.ball_mem_nhds (t, x) hε] with q hq
    have := hkernel q.1 (htime_pos q hq)
    exact (by fun_prop : Continuous fun y ↦
      fundamentalSolutionHeat (n := n) (q.2 - y) q.1 * g y).aestronglyMeasurable
  obtain ⟨M, hM⟩ := hg_bdd
  have hF_int : MeasureTheory.Integrable (F (t, x)) μ :=
    ((μ.measurePreserving_sub_left x).integrable_comp_of_integrable
      (fundamentalSolutionHeat_integrable t ht)).mul_bdd hg_cont.aestronglyMeasurable
      (.of_forall hM)
  have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' (t, x)) μ := by
    have := hkernel t ht
    have hgradient : Continuous fun z : (ℝ^n) ↦
        (-(1 / (2 * t)) * fundamentalSolutionHeat (n := n) z t) • innerSL ℝ z :=
      continuous_iff_continuousAt.mpr fun z ↦
        (hasFDerivAt_fundamentalSolutionHeat_gradient (n := n) t ht z).continuousAt
    exact (hg_cont.smul (((by fun_prop : Continuous fun y : ℝ^n ↦
      (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) *
        fundamentalSolutionHeat (n := n) (x - y) t).smul continuous_const).continuousLinearMapCoprod
      (hgradient.comp (continuous_const.sub continuous_id)))).aestronglyMeasurable
  have h_diff : ∀ᵐ y ∂μ, ∀ q ∈ Metric.ball (t, x) ε, HasFDerivAt (F · y) (F' q y) q :=
    .of_forall fun y q hq ↦ by
      have hcomp := (hasFDerivAt_fundamentalSolutionHeat_timeSpace (n := n) (q.2 - y) q.1
        (htime_pos q hq)).comp q ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).prodMk
          ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).sub_const y))
      simpa only [F, F', Function.comp_apply, ContinuousLinearMap.fst_prod_snd,
        ContinuousLinearMap.comp_id] using hcomp.mul_const (g y)
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F' := F')
    (Metric.ball_mem_nhds (t, x) hε) hF_meas hF_int hF'_meas
    (.of_forall fun y q hq ↦ hbound y q hq) hbound_int h_diff
  refine (hmain.congr_of_eventuallyEq ?_).differentiableAt
  filter_upwards [Metric.ball_mem_nhds (t, x) hε] with q hq
  simp [F, μ, initialValueSolution, not_le_of_gt (htime_pos q hq)]

end HeatEquation
