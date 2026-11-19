/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionSpace.Scaling
import PDE.Parabolic.Heat.Kernel.Integrability
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Joint continuity of heat evolution

Write the heat evolution using the time-one Gaussian and move its dependence on time
into the datum, as `g(x + √t y)`. The Gaussian is then a single integrable majorant,
even at time zero. Dominated convergence gives joint continuity in space, time, and
any first-countable parameter indexing a bounded continuous family of data.

For Duhamel's formula the parameter is the source time. This result also applies to
continuous spatial derivatives of the source, with no extra derivatives needed to
control the corner where the heat age vanishes.
-/

@[expose] public section

namespace HeatEquation

open MeasureTheory

variable {n : ℕ}

/-- A bounded continuous family of initial data has a heat evolution continuous
jointly in the family parameter, the spatial point, and time, including time zero.

No differentiability or compact support of the data is needed. At negative times,
continuity refers to the convention that the evolution equals the initial datum. -/
theorem continuous_initialValueSolution_family
    {T : Type*} [TopologicalSpace T] [FirstCountableTopology T]
    {g : T × ℝ^n → ℝ} (hg : Continuous g)
    {M : ℝ} (hbound : ∀ p, ‖g p‖ ≤ M) :
    Continuous (fun p : T × ℝ^n × ℝ ↦
      initialValueSolution (fun y ↦ g (p.1, y)) p.2.1 p.2.2) := by
  simp_rw [initialValueSolution_eq_fixed_gaussian]
  have hkernel : Integrable (fun y : ℝ^n ↦ fundamentalSolutionHeat (0 - y) 1) :=
    (fundamentalSolutionHeat_integrable 1 zero_lt_one).comp_sub_left 0
  apply continuous_of_dominated (bound := fun y ↦
    ‖fundamentalSolutionHeat (0 - y) 1‖ * M)
  · intro p
    have hspace : Continuous (fun y : ℝ^n ↦ p.2.1 + Real.sqrt p.2.2 • y) := by
      fun_prop
    have hdatum : Continuous (fun y : ℝ^n ↦ g (p.1, p.2.1 + Real.sqrt p.2.2 • y)) :=
      hg.comp (continuous_const.prodMk hspace)
    exact hkernel.aestronglyMeasurable.mul hdatum.aestronglyMeasurable
  · intro p
    apply Filter.Eventually.of_forall
    intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound _) (norm_nonneg _)
  · exact hkernel.norm.mul_const M
  · apply Filter.Eventually.of_forall
    intro y
    have hspace : Continuous (fun p : T × ℝ^n × ℝ ↦ p.2.1 + Real.sqrt p.2.2 • y) :=
      continuous_snd.fst.add (continuous_snd.snd.sqrt.smul continuous_const)
    exact continuous_const.mul (hg.comp (continuous_fst.prodMk hspace))

end HeatEquation
