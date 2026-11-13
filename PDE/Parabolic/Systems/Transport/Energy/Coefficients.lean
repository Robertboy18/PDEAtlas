/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Energy

/-!
# Uniform bounds for transport coefficient curves

A continuous W¹,∞ matrix curve on a compact time interval has finite
transport and derivative bounds. These constants are selected from the
coefficient curve alone, before the forcing, initial data, or diffusivity.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Systems

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

variable {n m : ℕ} {a b : ℝ}

/-- Continuous matrix coefficient curves supply both bounds needed by the
integrated H¹ and velocity estimates. -/
theorem exists_transport_energy_coefficient_bounds
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ContinuousOn A (Icc a b)) :
    ∃ K M : ℝ, 0 ≤ K ∧ 0 ≤ M ∧
      (∀ t ∈ Icc a b, transportDerivativeSum (A t) ≤ K) ∧
      (∀ t ∈ Icc a b,
        ‖vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))‖ ≤ M) := by
  have hentry (j : Fin n) (p q : Fin m) :
      ContinuousOn (fun t ↦ A t j p q) (Icc a b) :=
    (continuous_apply q).comp_continuousOn
      ((continuous_apply p).comp_continuousOn ((continuous_apply j).comp_continuousOn hA))
  have hd (l j : Fin n) (p q : Fin m) :
      ContinuousOn (fun t ↦ ‖wkpCoordinateCLM (singleDerivIndex n l) (A t j p q)‖)
        (Icc a b) :=
    (wkpCoordinateCLM (singleDerivIndex n l)).continuous.comp_continuousOn
      (hentry j p q) |>.norm
  have hK : ContinuousOn (fun t ↦ transportDerivativeSum (A t)) (Icc a b) :=
    (continuousOn_finsetSum _ fun j _ ↦ continuousOn_finsetSum _ fun p _ ↦
      continuousOn_finsetSum _ fun q _ ↦ hd j j p q).add
        ((continuousOn_finsetSum _ fun l _ ↦ continuousOn_finsetSum _ fun p _ ↦
          continuousOn_finsetSum _ fun j _ ↦ continuousOn_finsetSum _ fun q _ ↦
            hd l j p q).const_mul 2)
  have hM : ContinuousOn
      (fun t ↦ vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q)))
      (Icc a b) := by
    apply continuous_vectorTransportCLM.comp_continuousOn
    exact continuousOn_pi.mpr fun j ↦ continuousOn_pi.mpr fun p ↦
      continuousOn_pi.mpr fun q ↦
        wkpBaseCoordinateCLM.continuous.comp_continuousOn (hentry j p q)
  obtain ⟨K, hKbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hK
  have hMnorm : ContinuousOn
      (fun t ↦ ‖vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))‖)
      (Icc a b) :=
    (continuous_norm (E := (Fin m → W^{1,2}(ℝ^n)) →L[ℝ]
      (Fin m → DerivLp n 2 univ))).comp_continuousOn hM
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hMnorm
  exact ⟨max K 0, max M 0, le_max_right _ _, le_max_right _ _,
    fun t ht ↦ (le_abs_self _).trans ((hKbound t ht).trans (le_max_left _ _)),
    fun t ht ↦ (le_abs_self _).trans ((hMbound t ht).trans (le_max_left _ _))⟩

end PDE.Parabolic.Systems
