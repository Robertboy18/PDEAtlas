/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Displacement.WeakTrace
public import PDE.Analysis.Evolution.Time.WeakDerivative.LipschitzRepresentative
public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.RadialDatum.TimeTrace.InitialData

/-!
# The radial datum and its derived weak time trace

For any candidate with an ordinary weak displacement derivative and L∞ velocity,
construct its unique continuous representative before asking for the initial value.
If this Sobolev trace equals the prescribed datum, the signed reaction fails
L² on every initial time cylinder.

The endpoint equality means the Sobolev trace of the derived continuous
representative, not a value assigned to an L² class at a null time slice.
The source-class comparison is the one recorded in `TimeTrace.InitialData`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped ENNReal NNReal Sobolev
open PDE.Analysis (primitive)

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition

/-- One admissible datum obstructs the initial-time reaction class of every
bounded-velocity candidate whose derived Sobolev trace is the prescribed datum. -/
theorem exists_energyDatum_obstructing_weak_time_trace :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ ↦ z ^ 7) ∧
    (∀ z : ℝ, 0 ≤ z * z ^ 7) ∧
    ∃ X : H¹(ℝ^3) × DerivLp 3 2 univ,
      X.2 = 0 ∧
      ((energyTriple 3).inclusion X.1 : ℝ^3 → ℝ) =ᵐ[volume] singularRadialDatum ∧
      Integrable (fun x ↦ primitive (fun z ↦ z ^ 7) ((energyTriple 3).inclusion X.1 x))
        (domainMeasure 3 univ) ∧
      ∀ T : ℝ, 0 < T →
      ∀ q : Lp (W^{1,2}(Metric.ball (0 : ℝ^3) 1)) 2 (volume.restrict (Ioc 0 T)),
      ∀ v : Lp (DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)) 2
        (volume.restrict (Ioc 0 T)),
        HasWeakTimeDerivativeOn (Ioo 0 T)
          (fun t ↦ wkpBaseCoordinateCLM (q t)) (fun t ↦ v t) →
        MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc 0 T)) →
        ∃ (Q : ℝ → DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1)) (K : ℝ≥0),
          Continuous Q ∧ LipschitzOnWith K Q (Icc 0 T) ∧
          (fun t ↦ wkpBaseCoordinateCLM (q t)) =ᵐ[volume.restrict (Ioc 0 T)] Q ∧
          (∀ w : ℝ → DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1),
            ContinuousOn w (Icc 0 T) →
            w =ᵐ[volume.restrict (Ioc 0 T)] (fun t ↦ wkpBaseCoordinateCLM (q t)) →
            EqOn w Q (Icc 0 T)) ∧
          (Q 0 = wkpBaseCoordinateCLM
            (restrictCLM measurableSet_ball (subset_univ (Metric.ball 0 1)) X.1) →
            ∀ R : ℝ → DerivLp 3 2 (Metric.ball (0 : ℝ^3) 1),
              (∀ᵐ t ∂volume.restrict (Ioc 0 T),
                (fun x ↦ -(wkpBaseCoordinateCLM (q t) x) ^ 7)
                  =ᵐ[volume.restrict (Metric.ball (0 : ℝ^3) 1)] (R t : ℝ^3 → ℝ)) →
              ¬ MemLp R 2 (volume.restrict (Ioc 0 T))) := by
  obtain ⟨hf, hs, X, hzero, hX, hpot, hno⟩ :=
    exists_energyDatum_no_local_integrated_seventh_power_reaction
  refine ⟨hf, hs, X, hzero, hX, hpot, fun T hT q v hweak hv ↦ ?_⟩
  obtain ⟨Q, K, hQ, hLip, hqQ, _, _, huniq⟩ :=
    hweak.exists_unique_lipschitz_representative_of_memLp_top hT hv
  refine ⟨Q, K, hQ, hLip, hqQ, huniq, fun hinit R hreact ↦ ?_⟩
  have hi := hweak.integrated_displacement_of_weak_trace
    (T := hOneLTwoGelfandTriple Metric.isOpen_ball) hT
    (fun ell ↦ (ell.continuous.comp hQ).continuousOn) hqQ.symm hv
  rw [hinit] at hi
  exact hno T q v R hi hv hreact

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition
