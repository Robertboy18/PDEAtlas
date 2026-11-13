/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Poisson.Variational.FiniteEnergy
import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A finite-energy candidate for a boundary-singular forcing

On the unit ball `(-1,1)` of one-dimensional Euclidean space, the forcing
`f(x) = 1 / (1 - x₀)` is not integrable, while `u(x) = 1 - x₀` gives the load
`f u = 1`. Thus `u` lies in the finite-energy class with its own boundary values,
and the variational converse applies to it with no integrability hypothesis on `f`.
Since `Δu = 0` and `f(0) = 1`, the converse shows that `u` is not a minimizer.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Poisson.SingularForcing

open MeasureTheory Set SobolevSpace PoissonEquation
open PDE (laplacian)

local notation "Ω" => Metric.ball (0 : ℝ^1) 1

/-- An affine candidate, zero at one endpoint and equal to two at the other. -/
def candidate (x : ℝ^1) : ℝ := 1 - x 0

/-- The reciprocal of the affine candidate. -/
def forcing (x : ℝ^1) : ℝ := (1 - x 0)⁻¹

/-- The affine denominator is strictly positive throughout the domain. -/
theorem candidate_pos {x : ℝ^1} (hx : x ∈ Ω) : 0 < candidate x := by
  have hxnorm : ‖x‖ < 1 := by simpa using hx
  have hxcoord : x 0 ≤ ‖x‖ :=
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
  exact sub_pos.mpr (lt_of_le_of_lt hxcoord hxnorm)

/-- The forcing is continuous on the open interval. -/
theorem forcing_continuousOn : ContinuousOn forcing Ω := by
  exact (continuousOn_const.sub (EuclideanSpace.proj 0).continuous.continuousOn).inv₀
    (fun _ hx ↦ (candidate_pos hx).ne')

/-- The load `f u` equals one on the domain. -/
theorem forcing_mul_candidate {x : ℝ^1} (hx : x ∈ Ω) :
    forcing x * candidate x = 1 := by
  exact inv_mul_cancel₀ (candidate_pos hx).ne'

/-- The candidate lies in the finite-energy class with its own boundary values. -/
theorem candidate_mem : candidate ∈ finiteClassicalDirichletClass Ω forcing candidate := by
  have hc : ContDiff ℝ 2 candidate := by cas
  have hb : ContDiffUpToBoundary 2 candidate Ω :=
    contDiffUpToBoundary_of_contDiffOn isOpen_univ hc.contDiffOn
    Metric.isBounded_ball.isCompact_closure (subset_univ _)
  have hload : IntegrableOn (fun x ↦ forcing x * candidate x) Ω := by
    apply (integrableOn_const (C := (1 : ℝ)) (hs := Metric.isBounded_ball.measure_lt_top.ne)).congr
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    exact (forcing_mul_candidate hx).symm
  exact ⟨⟨hb, hc.continuous.continuousOn, fun _ _ ↦ rfl⟩,
    integrable_classicalEnergy Metric.isOpen_ball Metric.isBounded_ball
      (hb.of_le (by omega)) hload⟩

/-- The forcing is not integrable on the domain, since `∫₀¹ (1 - y)⁻¹ dy` diverges. -/
theorem forcing_not_integrableOn : ¬IntegrableOn forcing Ω := by
  intro hf
  let e : ℝ ≃L[ℝ] ℝ^1 := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have he : MeasurePreserving e volume volume :=
    (PiLp.volume_preserving_toLp (Fin 1)).comp
      ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _)
  have hi : IntegrableOn (fun y : ℝ ↦ (1 - y)⁻¹) (Ioo 0 1) := by
    have hpre := (he.integrableOn_comp_preimage e.toHomeomorph.measurableEmbedding).mpr hf
    have hsub : Ioo (0 : ℝ) 1 ⊆ e ⁻¹' Ω := by
      intro y hy
      have hn : ‖e y‖ ^ 2 = y ^ 2 := by
        simp [EuclideanSpace.real_norm_sq_eq, e]
      have hnorm : ‖e y‖ < 1 := by nlinarith [hy.1, hy.2, norm_nonneg (e y)]
      simpa using hnorm
    exact (hpre.mono_set hsub).congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hi' : IntegrableOn (fun y : ℝ ↦ y⁻¹) (Ioo 0 1) := by
    have hp := ((volume.measurePreserving_sub_left (1 : ℝ)).integrableOn_comp_preimage
      (Homeomorph.subLeft 1).measurableEmbedding).mpr hi
    have hs : (fun y : ℝ ↦ 1 - y) ⁻¹' Ioo 0 1 = Ioo 0 1 := by
      ext y
      simp only [mem_preimage, mem_Ioo]
      constructor <;> intro h <;> constructor <;> linarith
    rw [hs] at hp
    apply hp.congr
    filter_upwards [] with y
    change (1 - (1 - y))⁻¹ = y⁻¹
    congr 1
    cas
  have hbad : IntervalIntegrable (fun y : ℝ ↦ y⁻¹) volume 0 1 := by
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  simp [intervalIntegrable_inv_iff] at hbad

/-- The singular forcing cannot be continuous on the closure. -/
theorem forcing_not_continuousOn_closure : ¬ContinuousOn forcing (closure Ω) := by
  intro hf
  exact forcing_not_integrableOn
    (hf.integrableOn_of_subset_isCompact Metric.isBounded_ball.isCompact_closure
      Metric.isOpen_ball.measurableSet subset_closure Metric.isBounded_ball.measure_lt_top.ne)

/-- The candidate does not minimize the energy over the finite-energy class. -/
theorem candidate_not_isMinOn :
    ¬IsMinOn (classicalEnergy Ω forcing)
      (finiteClassicalDirichletClass Ω forcing candidate) candidate := by
  intro hmin
  have hpde := poisson_of_isMinOn_finiteClassicalEnergy Metric.isOpen_ball
    Metric.isBounded_ball
    ((Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 1).hasC1GraphBoundary le_rfl)
    candidate_mem forcing_continuousOn hmin
  have heq := hpde 0 (by simp)
  have hlap : laplacian candidate (0 : ℝ^1) = 0 := by
    simp only [laplacian, Fin.sum_univ_one]
    cas
  norm_num [hlap, forcing] at heq

end PDE.Examples.Poisson.SingularForcing
