/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Source
public import PDE.Hyperbolic.NonlinearWave.Cauchy.EnergySolution

/-!
# Integrated equations for energy-space nonlinearities

The constructed linear observation identities turn each finite mild trajectory
into the weak wave equation. The competing-solution predicate `N.IsEnergySolution x u` is the
general `Cauchy.IsEnergySolutionOn` on `[0, ∞)` for the acceleration `Δu − N(u)`: it contains
only forward H¹ × L² continuity, both initial values, and the two integrated
PDE identities.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity

open PDE.Analysis.Evolution

variable {n : ℕ} (N : Nonlinearity n)

/-- The weak acceleration `Δu − N(u)`, on every H¹(ℝⁿ) displacement. -/
def acceleration (u : H¹(ℝ^n)) : StrongDual ℝ H¹(ℝ^n) :=
  -(energyTriple n).pivotToDual (N.source u) - gradientForm n u

/-- The acceleration is continuous from H¹ into its dual. -/
theorem continuous_acceleration : Continuous N.acceleration :=
  ((energyTriple n).pivotToDual.continuous.comp N.source.continuous).neg.sub
    (gradientForm n).continuous

/-- The auxiliary mass cancels exactly in the weak equation. -/
theorem force_sub_massForm (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (energyTriple n).pivotToDual (N.force z) - massForm n z.1 = N.acceleration z.1 := by
  change (energyTriple n).pivotToDual ((energyTriple n).inclusion z.1 - N.source z.1) -
    massForm n z.1 = _
  simp only [acceleration, gradientForm, map_sub, sub_apply]
  change _ - _ - _ = -_ - (_ - (energyTriple n).pivotToDual ((energyTriple n).inclusion z.1))
  abel

/-- A finite mild trajectory satisfies both integrated PDE equations, with
the continuous interval extension used only inside the integrals. -/
theorem mild_integrated_equations {x : H¹(ℝ^n) × DerivLp n 2 univ} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), H¹(ℝ^n) × DerivLp n 2 univ)}
    (hu : (productSemigroup n).IsMildSolutionOn N.vectorField x τ u) (t : Icc (0 : ℝ) (τ : ℝ)) :
    (∫ s in (0 : ℝ)..(t : ℝ), (IccExtend τ.coe_nonneg u s).2) =
        (energyTriple n).inclusion (u t).1 - (energyTriple n).inclusion x.1 ∧
      (∫ s in (0 : ℝ)..(t : ℝ), N.acceleration (IccExtend τ.coe_nonneg u s).1) =
        (energyTriple n).pivotToDual (u t).2 - (energyTriple n).pivotToDual x.2 := by
  let f := fun s ↦ N.force (IccExtend τ.coe_nonneg u s)
  have hf : Continuous f := N.force.continuous.comp u.continuous.Icc_extend'
  let z := fun s ↦ (productSemigroup n).realOrbit x s +
    (productSemigroup n).duhamel (fun r ↦ (0, f r)) s
  have he (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (τ : ℝ)) : z s = IccExtend τ.coe_nonneg u s :=
    (hu ⟨s, hs⟩).symm.trans (IccExtend_of_mem τ.coe_nonneg u hs).symm
  have ht : z t = u t := (hu t).symm
  have h := productSemigroup_forced_integral hf x t.property.1
  change (∫ s in (0 : ℝ)..(t : ℝ), (z s).2) =
      (energyTriple n).inclusion (z t).1 - (energyTriple n).inclusion x.1 ∧
    (∫ s in (0 : ℝ)..(t : ℝ), (energyTriple n).pivotToDual (f s) - massForm n (z s).1) =
      (energyTriple n).pivotToDual (z t).2 - (energyTriple n).pivotToDual x.2 at h
  rw [ht] at h
  constructor
  · refine Eq.trans ?_ h.1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    exact congrArg Prod.snd (he s ⟨hs.1, hs.2.trans t.property.2⟩).symm
  · refine Eq.trans ?_ h.2
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.property.1] at hs
    change N.acceleration (IccExtend τ.coe_nonneg u s).1 =
      (energyTriple n).pivotToDual (f s) - massForm n (z s).1
    rw [he s ⟨hs.1, hs.2.trans t.property.2⟩]
    exact (N.force_sub_massForm _).symm

/-- An energy solution is specified by the weak PDE and initial data: the general
`Cauchy.IsEnergySolutionOn` on `[0, ∞)` for the acceleration `Δu − N(u)`.
No mild identity or energy bound is part of this predicate. -/
abbrev IsEnergySolution (x : H¹(ℝ^n) × DerivLp n 2 univ)
    (u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ) : Prop :=
  IsEnergySolutionOn (fun z ↦ N.acceleration z.1) x (Ici 0) u

variable {N} in
/-- The integrated PDE gives the H¹-dual acceleration, including at zero. This is
`IsEnergySolutionOn.hasDerivWithinAt_velocity` for the continuous acceleration `Δu − N(u)`. -/
theorem IsEnergySolution.hasDerivWithinAt_velocity {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ} (h : N.IsEnergySolution x u) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s ↦ (energyTriple n).pivotToDual (u s).2)
      (N.acceleration (u t).1) (Ici 0) t :=
  IsEnergySolutionOn.hasDerivWithinAt_velocity h
    (N.continuous_acceleration.comp continuous_fst) ht

variable {N} in
/-- At every positive time the velocity is differentiable in the H¹ dual. This is
`IsEnergySolutionOn.hasDerivAt_velocity` for the continuous acceleration `Δu − N(u)`. -/
theorem IsEnergySolution.hasDerivAt_velocity {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ} (h : N.IsEnergySolution x u) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ (energyTriple n).pivotToDual (u s).2) (N.acceleration (u t).1) t :=
  IsEnergySolutionOn.hasDerivAt_velocity h (N.continuous_acceleration.comp continuous_fst) ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.General.Nonlinearity
