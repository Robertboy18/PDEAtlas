/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators
public import PDE.Analysis.Integration.PuncturedDivergence
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Removing derivative exceptions from incompressibility

A continuous vector field which is classically divergence free off a countable
set is distributionally divergence free. The countable-exception divergence
theorem is applied to its product with each compact scalar test. No classical
derivative is required at an exceptional point.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

open MeasureTheory
open scoped BigOperators

/-- Continuous classical incompressibility off a countable set implies global
incompressibility in distributions, without differentiability at the exceptions. -/
theorem distributionallyDivergenceFree_of_continuous_off_countable {n : ℕ}
    {v : ℝ^(n + 1) → ℝ^(n + 1)} {s : Set (ℝ^(n + 1))}
    (hv : Continuous v) (hs : s.Countable)
    (hdiff : ∀ x ∉ s, DifferentiableAt ℝ v x)
    (hdiv : ∀ x ∉ s, PDE.divergence v x = 0) :
    DistributionallyDivergenceFree v := by
  intro ψ hψ hcompact
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hi (i : Fin (n + 1)) : Integrable (fun x ↦ v x i * PDE.partialDeriv i ψ x) := by
    exact ((EuclideanSpace.proj i).continuous.comp hv |>.mul
      (hψ1.continuous_partialDeriv i)).integrable_of_hasCompactSupport
        (hcompact.partialDeriv i).mul_left
  have hdensity : Integrable (weakDivergencePairingDensity v ψ) := by
    exact (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).congr
      (Filter.Eventually.of_forall fun x ↦ (weakDivergencePairingDensity_eq_sum v ψ x).symm)
  have hproduct (x : ℝ^(n + 1)) (hx : x ∉ s) :
      PDE.divergence (fun y ↦ ψ y • v y) x = weakDivergencePairingDensity v ψ x := by
    have hcoord (i : Fin (n + 1)) :
        PDE.partialDeriv i (fun y ↦ (ψ y • v y) i) x =
          PDE.partialDeriv i ψ x * v x i + ψ x * PDE.partialDeriv i (fun y ↦ v y i) x := by
      exact PDE.partialDeriv_mul hψ1.differentiable_one.differentiableAt
        ((EuclideanSpace.proj i : ℝ^(n + 1) →L[ℝ] ℝ).differentiableAt.comp x (hdiff x hx))
    simp only [PDE.divergence, hcoord, Finset.sum_add_distrib, ← Finset.mul_sum]
    change (∑ i, PDE.partialDeriv i ψ x * v x i) + ψ x * PDE.divergence v x = _
    rw [hdiv x hx, mul_zero, add_zero, weakDivergencePairingDensity_eq_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hae : PDE.divergence (fun y ↦ ψ y • v y) =ᵐ[volume]
      weakDivergencePairingDensity v ψ := by
    filter_upwards [hs.ae_notMem volume] with x hx
    exact hproduct x hx
  have hint : Integrable (PDE.divergence (fun y ↦ ψ y • v y)) := hdensity.congr hae.symm
  have hzero := PDE.Analysis.integral_divergence_eq_zero_of_continuous_off_countable
    (hψ.continuous.smul hv) hcompact.smul_right hs
    (fun x hx ↦ hψ1.differentiable_one.differentiableAt.smul (hdiff x hx)) hint
  refine ⟨hdensity, ?_⟩
  rw [weakDivergencePairing, ← integral_congr_ae hae]
  exact hzero

end IncompressibleFlow
