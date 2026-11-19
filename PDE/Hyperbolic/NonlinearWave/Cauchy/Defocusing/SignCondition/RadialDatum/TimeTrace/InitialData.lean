/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.RadialDatum.TimeTrace.Integrated
import CAS.ExactTactic

/-!
# One finite-energy datum excludes the local initial-time reaction class

The witness is fixed before the lifespan and trajectories are quantified. Restriction of this same
global H¹ datum supplies the local initial value. Only the integrated displacement identity, an L∞
velocity and the signed reaction remain as candidate hypotheses. The reaction's smoothness and sign,
initial potential and superlevels are proved; no joint representative or quantitative trace
hypothesis is requested.

The example concerns the reaction requirement `f(u) ∈ L²(0,T; L²_loc(ℝⁿ))` of the weak solutions
of Evans, §12.2, together with the bounded velocity of §12.3.1, Theorem 1. It does not exclude a
weak solution class requiring only local L¹ reaction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2, definition of a weak solution; §12.3.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- A fixed admissible global datum excludes even the necessary local displacement
fields of the initial-time L² reaction class with essentially bounded velocity. -/
theorem exists_energyDatum_no_local_integrated_seventh_power_reaction :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ z ^ 7) ∧
    (∀ z : ℝ, 0 ≤ z * z ^ 7) ∧
    ∃ X : H¹(ℝ^3) × DerivLp 3 2 univ,
      X.2 = 0 ∧
      ((energyTriple 3).inclusion X.1 : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum ∧
      Integrable (fun x ↦ primitive (fun z ↦ z ^ 7) ((energyTriple 3).inclusion X.1 x))
        (domainMeasure 3 univ) ∧
      ∀ T : ℝ,
      ∀ q : Lp (W^{1,2}(Metric.ball (0 : ℝ^3) 1)) 2 (volume.restrict (Ioc 0 T)),
      ∀ v : Lp (DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)) 2
        (volume.restrict (Ioc 0 T)),
      ∀ R : ℝ → DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1),
        IsGelfandIntegratedWeakSolution (hOneLTwoGelfandTriple Metric.isOpen_ball)
          (fun _ ↦ 0)
          (fun t ↦ (hOneLTwoGelfandTriple Metric.isOpen_ball).pivotToDual (v t)) q
          (wkpBaseCoordinateCLM
            (restrictCLM measurableSet_ball (subset_univ (Metric.ball 0 1)) X.1)) →
        MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc 0 T)) →
        (∀ᵐ t ∂volume.restrict (Ioc 0 T),
          (fun x ↦ -(wkpBaseCoordinateCLM (q t) x) ^ 7)
            =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) 1)] (R t : ℝ^3 → ℝ)) →
        ¬ MemLp R 2 (volume.restrict (Ioc 0 T)) := by
  obtain ⟨G, hG, hpot⟩ := exists_energyDatum_singularRadialDatum
  have hs (z : ℝ) : 0 ≤ z * z ^ 7 := by
    have h : z * z ^ 7 = (z ^ 4) ^ 2 := by cas
    rw [h]
    exact sq_nonneg _
  refine ⟨by fun_prop, hs, (G, 0), rfl, hG, hpot, fun T q v R hq hv hreact ↦ ?_⟩
  apply not_memLp_signed_reaction_of_local_integrated_displacement hq hv ?_ hreact
  exact (restrictCLM_apply_ae measurableSet_ball (subset_univ (Metric.ball 0 1))
    G (baseIndex 3 1)).trans hG.restrict

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
