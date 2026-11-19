/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Uniqueness
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Potential

/-!
# The real-power wave equation

The constructed L² source pairs as the spatial integral of `|u|^(p-1)u`.
Consequently the integrated dual equation is the massless defocusing PDE
against every H¹ spatial test. The same energy solution has the L²
velocity as its displacement derivative, including the right derivative at zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

variable {p : ℝ} (hp : 1 < p) (hp3 : p ≤ 3)

/-- The L² source pairs as the signed-power spatial density. -/
theorem inner_source (q w : H¹(ℝ^3)) :
    ⟪source hp hp3 q, (energyTriple 3).inclusion w⟫_ℝ = ∫ x : ℝ^3, (|(energyTriple 3).inclusion q
      x| ^ (p - 1) * (energyTriple 3).inclusion q x) * (energyTriple 3).inclusion w x := by
  rw [L2.inner_def]
  simp only [domainMeasure, Measure.restrict_univ]
  apply integral_congr_ae
  filter_upwards [show source hp hp3 q =ᵐ[volume]
      fun x ↦ Real.signedPower p ((energyTriple 3).inclusion q x) from
    by simpa only [domainMeasure, Measure.restrict_univ] using source_ae hp hp3 q] with x hx
  simp only [hx, RCLike.inner_apply, conj_trivial, Real.signedPower]
  exact mul_comm _ _

/-- The acceleration is the weak Laplacian minus the defocusing source. -/
theorem acceleration_apply (q w : H¹(ℝ^3)) :
    (nonlinearity hp hp3).acceleration q w =
      -(∫ x : ℝ^3, (|(energyTriple 3).inclusion q x| ^ (p - 1) *
        (energyTriple 3).inclusion q x) * (energyTriple 3).inclusion w x) -
      ∑ i : Fin 3, ⟪q.val (singleDerivIndex 3 i), w.val (singleDerivIndex 3 i)⟫_ℝ := by
  simp only [General.Nonlinearity.acceleration, sub_apply, neg_apply,
    PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply, gradientForm_apply,
    nonlinearity, ContinuousMap.coe_mk, inner_source]

/-- The integrated velocity equation has the source and weak spatial gradients. -/
theorem integrated_velocity_pairing {x : H¹(ℝ^3) × DerivLp 3 2 univ}
    {u : C(ℝ, H¹(ℝ^3) × DerivLp 3 2 univ)} (hu : (nonlinearity hp hp3).IsEnergySolution x u) {t : ℝ}
    (ht : 0 ≤ t) (w : H¹(ℝ^3)) :
    (∫ s in (0 : ℝ)..t,
      -(∫ y : ℝ^3, (|(energyTriple 3).inclusion (u s).1 y| ^ (p - 1) *
        (energyTriple 3).inclusion (u s).1 y) * (energyTriple 3).inclusion w y) -
      ∑ i : Fin 3, ⟪(u s).1.val (singleDerivIndex 3 i),
        w.val (singleDerivIndex 3 i)⟫_ℝ) =
      ⟪(u t).2, (energyTriple 3).inclusion w⟫_ℝ -
        ⟪x.2, (energyTriple 3).inclusion w⟫_ℝ := by
  have hc : Continuous (fun s : ℝ ↦ (nonlinearity hp hp3).acceleration (u s).1) :=
    (nonlinearity hp hp3).continuous_acceleration.comp u.continuous.fst
  have he := congrArg (fun F : StrongDual ℝ H¹(ℝ^3) ↦ F w) (hu.velocity t ht)
  rw [ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable (μ := volume) 0 t) w] at he
  simpa only [acceleration_apply, sub_apply,
    PDE.Analysis.Evolution.GelfandTriple.pivotToDual_apply] using he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power
