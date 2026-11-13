/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Bounds

/-!
# Global waves with nonnegative spatial potentials

The derived finite-horizon bound rules out finite maximal lifespan. The
maximal Picard evolution therefore constructs a global trajectory for every
energy state. Its finite restrictions give conservation and the integrated
massless PDE, in every dimension for which a `General.Nonlinearity` is given.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Interval Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity

variable {n : ℕ} (N : Nonlinearity n)

open PDE.Analysis.Evolution

/-- The maximal energy evolution has infinite forward lifespan for every datum. -/
theorem mildLifespan_eq_top (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    (productSemigroup n).mildLifespan N.vectorField x = ∞ := by
  apply (productSemigroup n).mildLifespan_eq_top_of_finite_time_bounds
    N.vectorField_lipschitzOn_closedBall
  intro H _
  refine ⟨‖(energyTriple n).inclusion x.1‖ + (H + 1) * Real.sqrt (2 * N.energy x), ?_⟩
  intro τ hτ u hu
  apply (N.norm_of_mildSolutionOn hu ⟨τ, τ.coe_nonneg, le_rfl⟩).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (add_le_add hτ le_rfl) (Real.sqrt_nonneg _))

/-- The constructed global energy trajectory, extended constantly to negative time. -/
def globalSolution (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) :=
  ⟨fun t ↦ (productSemigroup n).maximalMildSolution N.locallyLipschitz_vectorField x (max t 0),
    ((productSemigroup n).maximalMildSolution_global_of_lifespan_eq_top
      N.locallyLipschitz_vectorField x (N.mildLifespan_eq_top x)).1.comp_continuous
        (continuous_id.max continuous_const) (fun t ↦ le_max_right t 0)⟩

/-- On forward time the global solution is the maximal Picard trajectory. -/
theorem globalSolution_apply (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    N.globalSolution x t =
      (productSemigroup n).maximalMildSolution N.locallyLipschitz_vectorField x t := by
  change (productSemigroup n).maximalMildSolution N.locallyLipschitz_vectorField x (max t 0) = _
  rw [max_eq_left ht]

/-- Both initial components are exactly the supplied energy data. -/
theorem globalSolution_zero (x : H¹(ℝ^n) × DerivLp n 2 univ) : N.globalSolution x 0 = x := by
  rw [N.globalSolution_apply x le_rfl]
  exact (productSemigroup n).maximalMildSolution_zero N.locallyLipschitz_vectorField x

/-- The global constructed trajectory satisfies variation of constants at all forward times. -/
theorem globalSolution_equation (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    N.globalSolution x t = (productSemigroup n).realOrbit x t +
      (productSemigroup n).duhamel (fun s ↦ N.vectorField (N.globalSolution x s)) t := by
  rw [N.globalSolution_apply x ht,
    (productSemigroup n).maximalMildSolution_equation N.locallyLipschitz_vectorField x ht
      (by rw [N.mildLifespan_eq_top]; exact ENNReal.ofReal_lt_top)]
  congr 1
  exact (productSemigroup n).duhamel_congr ht fun s hs ↦
    congrArg N.vectorField (N.globalSolution_apply x hs.1).symm

/-- Restriction of the global solution to a finite initial interval. -/
def globalTrace (x : H¹(ℝ^n) × DerivLp n 2 univ) (τ : NNReal) :
    C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ) :=
  ⟨fun t ↦ N.globalSolution x t, (N.globalSolution x).continuous.comp continuous_subtype_val⟩

/-- Every finite restriction is a mild solution, so all derived finite energy estimates apply. -/
theorem globalTrace_isMildSolutionOn (x : H¹(ℝ^n) × DerivLp n 2 univ) (τ : NNReal) :
    (productSemigroup n).IsMildSolutionOn N.vectorField x τ (N.globalTrace x τ) := by
  intro t
  change N.globalSolution x t = _
  rw [N.globalSolution_equation x t.property.1]
  congr 1
  refine (productSemigroup n).duhamel_congr t.property.1 fun s hs ↦ ?_
  change N.vectorField (N.globalSolution x s) =
    N.vectorField (IccExtend τ.coe_nonneg (N.globalTrace x τ) s)
  rw [IccExtend_of_mem τ.coe_nonneg (N.globalTrace x τ) ⟨hs.1, hs.2.trans t.property.2⟩]
  rfl

/-- Conservation of the massless physical energy for the constructed global solution. -/
theorem energy_globalSolution (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    N.energy (N.globalSolution x t) = N.energy x :=
  N.energy_of_mildSolutionOn (N.globalTrace_isMildSolutionOn x ⟨t, ht⟩) ⟨t, ht, le_rfl⟩

/-- The derived full norm bound holds at every forward time. -/
theorem norm_globalSolution_le (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    ‖N.globalSolution x t‖ ≤
      ‖(energyTriple n).inclusion x.1‖ + (t + 1) * Real.sqrt (2 * N.energy x) :=
  N.norm_of_mildSolutionOn (N.globalTrace_isMildSolutionOn x ⟨t, ht⟩) ⟨t, ht, le_rfl⟩

/-- The global constructor solves the weak PDE with both initial traces. -/
theorem globalSolution_isEnergySolution (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    N.IsEnergySolution x (N.globalSolution x) := by
  refine ⟨(N.globalSolution x).continuous.continuousOn, N.globalSolution_zero x, ?_, ?_⟩
  · intro t ht
    have ht : (0 : ℝ) ≤ t := ht
    have h := (N.mild_integrated_equations (N.globalTrace_isMildSolutionOn x ⟨t, ht⟩)
      ⟨t, ht, le_rfl⟩).1
    refine Eq.trans ?_ h
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht] at hs
    change (N.globalSolution x s).2 = (IccExtend ht (N.globalTrace x ⟨t, ht⟩) s).2
    rw [IccExtend_of_mem (show 0 ≤ t from ht) (N.globalTrace x ⟨t, ht⟩) hs]
    rfl
  · intro t ht
    have ht : (0 : ℝ) ≤ t := ht
    have h := (N.mild_integrated_equations (N.globalTrace_isMildSolutionOn x ⟨t, ht⟩)
      ⟨t, ht, le_rfl⟩).2
    refine Eq.trans ?_ h
    refine intervalIntegral.integral_congr fun s hs ↦ ?_
    rw [uIcc_of_le ht] at hs
    change N.acceleration (N.globalSolution x s).1 =
      N.acceleration (IccExtend ht (N.globalTrace x ⟨t, ht⟩) s).1
    rw [IccExtend_of_mem (show 0 ≤ t from ht) (N.globalTrace x ⟨t, ht⟩) hs]
    rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity
