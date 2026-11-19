/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Source
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Composition

/-!
# The physical potential of every energy-subcritical real power

For `1 < p ≤ 3`, the constructed H¹ → L² source is the derivative of the
integrable potential `|u|^(p+1)/(p+1)`. The convex integral chain rule derives
this derivative from source continuity; it requires no second derivative of
the scalar source at zero. All spatial hypotheses of the general global wave
construction are thus proved for arbitrary H¹ data.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

variable {p : ℝ} (hp : 1 < p) (hp3 : p ≤ 3)

/-- The physical power potential as a spatial integral on the whole space. -/
def potential (p : ℝ) (q : H¹(ℝ^3)) : ℝ :=
  ∫ x, Real.signedPowerPotential p ((energyTriple 3).inclusion q x) ∂domainMeasure 3 univ

include hp hp3 in
/-- The potential density is integrable for every H¹ datum. -/
theorem integrable_potential (q : H¹(ℝ^3)) :
    Integrable (fun x ↦ Real.signedPowerPotential p ((energyTriple 3).inclusion q x))
      (domainMeasure 3 univ) :=
  PDE.Analysis.Calculus.integrable_signedPowerPotential_of_L2_source hp.le
    ((energyTriple 3).inclusion q) (source hp hp3 q) (source_ae hp hp3 q)

include hp hp3 in
/-- The unnormalized physical power density is also integrable. -/
theorem integrable_abs_rpow (q : H¹(ℝ^3)) :
    Integrable (fun x ↦ |(energyTriple 3).inclusion q x| ^ (p + 1)) (volume : Measure (ℝ^3)) := by
  simpa only [domainMeasure, Measure.restrict_univ] using
    PDE.Analysis.Calculus.integrable_abs_rpow_of_L2_signedPower hp.le
      ((energyTriple 3).inclusion q) (source hp hp3 q) (source_ae hp hp3 q)

/-- The source is the Fréchet derivative of the integral potential. -/
theorem hasFDerivAt_potential (q : H¹(ℝ^3)) :
    HasFDerivAt (potential p) ((innerSL ℝ (source hp hp3 q)).comp (energyTriple 3).inclusion) q :=
  PDE.Analysis.Calculus.hasFDerivAt_integral_signedPowerPotential
    (energyTriple 3).inclusion hp.le (source hp hp3) (source_ae hp hp3) q
    (locallyLipschitz_source hp hp3).continuous.continuousAt

include hp in
/-- The potential has the defocusing sign for arbitrary spatial amplitude. -/
theorem potential_nonneg (q : H¹(ℝ^3)) : 0 ≤ potential p q :=
  integral_nonneg fun _ ↦ Real.signedPowerPotential_nonneg hp.le _

/-- Every spatial hypothesis of the general wave construction is derived here. -/
def nonlinearity : General.Nonlinearity 3 where
  source := ⟨source hp hp3, (locallyLipschitz_source hp hp3).continuous⟩
  source_lipschitzOn := fun R hR ↦ source_lipschitzOn_closedBall hp hp3 R hR.le
  potential := potential p
  potential_nonneg := potential_nonneg hp
  hasFDerivAt_potential := hasFDerivAt_potential hp hp3

/-- The potential has exactly the physical normalization `1/(p+1)`. -/
theorem potential_eq_integral (q : H¹(ℝ^3)) :
    potential p q = (1 / (p + 1)) * ∫ x : ℝ^3, |(energyTriple 3).inclusion q x| ^ (p + 1) := by
  simp only [potential, Real.signedPowerPotential, domainMeasure, Measure.restrict_univ]
  rw [integral_div]
  ring

/-- The physical energy, with weak spatial derivatives and the real-power integral. -/
def physicalEnergy (p : ℝ) (z : H¹(ℝ^3) × DerivLp 3 2 univ) : ℝ :=
  (1 / 2 : ℝ) * ‖z.2‖ ^ 2 +
  (1 / 2 : ℝ) * (∑ i : Fin 3, ‖z.1.val (singleDerivIndex 3 i)‖ ^ 2) +
  (1 / (p + 1)) * ∫ x : ℝ^3, |(energyTriple 3).inclusion z.1 x| ^ (p + 1)

/-- The general conserved energy is exactly the physical energy of the real power. -/
theorem energy_eq_physicalEnergy (z : H¹(ℝ^3) × DerivLp 3 2 univ) :
    (nonlinearity hp hp3).energy z = physicalEnergy p z := by
  simp only [General.Nonlinearity.energy, nonlinearity, gradientForm_apply,
    real_inner_self_eq_norm_sq, potential_eq_integral, physicalEnergy]
  ring

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power
