/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Linear
import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability

/-!
# Identifying continuous weak waves with the constructed evolution

The integrated equations produce Bochner weak waves. The autonomous coercive-form
uniqueness theorem identifies their displacement and velocity classes. Continuity
then gives equality at every time, including the initial and terminal endpoints.
This supplies the converse needed to prove uniqueness for the semilinear PDE,
rather than uniqueness only among curves already assumed to be mild.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- An energy-continuous whole-space weak wave agrees with the constructed
Duhamel curve whenever its two integrated equations have the same data and force. -/
theorem linear_integral_identification {f : ℝ → DerivLp n 2 univ} (hf : Continuous f)
    {u : ℝ → H¹(ℝ^n) × DerivLp n 2 univ} (hu : Continuous u) (x : EnergyState n) {b : ℝ}
    (hb : 0 < b)
    (hq : ∀ t ∈ Icc 0 b, (∫ s in (0 : ℝ)..t, (u s).2) =
      (energyTriple n).inclusion (u t).1 - (energyTriple n).inclusion (C x).1)
    (hp : ∀ t ∈ Icc 0 b, (∫ s in (0 : ℝ)..t, (energyTriple n).pivotToDual (f s) - massForm n
      (u s).1) = (energyTriple n).pivotToDual (u t).2 - (energyTriple n).pivotToDual (C x).2) :
    EqOn u (fun t ↦ C ((linearSemigroup n).realOrbit x t +
      (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, f s)) t)) (Icc 0 b) := by
  let z := fun t ↦ C ((linearSemigroup n).realOrbit x t +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, f s)) t)
  have hz : Continuous z := (C).continuous.comp (((linearSemigroup n).continuous_realOrbit x).add
      ((linearSemigroup n).continuous_duhamel
        ((C).symm.continuous.comp (continuous_const.prodMk hf))))
  have hell := (energyTriple n).pivotToDual.continuous.comp hf
  obtain ⟨ell₁, q₁, p₁, acc₁, he₁, hq₁, hp₁, _, hw₁⟩ :=
    exists_weakWave_of_continuous_integral_equations
      (energyTriple n) (massForm n) hell hu (C x) hb hq hp
  obtain ⟨ell₂, q₂, p₂, acc₂, he₂, hq₂, hp₂, _, hw₂⟩ :=
    exists_weakWave_of_continuous_integral_equations (energyTriple n) (massForm n) hell hz (C x) hb
      (fun t ht ↦ (linear_forced_integral hf x ht.1).1)
      (fun t ht ↦ (linear_forced_integral hf x ht.1).2)
  have he : ell₁ = ell₂ := Lp.ext (he₁.trans he₂.symm)
  rw [he] at hw₁
  have hcoercive (v : H¹(ℝ^n)) : 1 * ‖v‖ ^ 2 ≤ massForm n v v := by
    change 1 * ‖v‖ ^ 2 ≤ inner ℝ v v
    rw [one_mul, real_inner_self_eq_norm_sq]
  obtain ⟨hqeq, hpeq, _⟩ := hw₁.eq_of_autonomous_symmetric_coercive
    hw₂ massForm_symmetric zero_lt_one hcoercive
  have hae : u =ᵐ[volume.restrict (Ioc 0 b)] z := by
    rw [hqeq] at hq₁
    rw [hpeq] at hp₁
    filter_upwards [hq₁, hp₁, hq₂, hp₂] with t h₁ h₂ h₃ h₄
    exact Prod.ext (h₁.symm.trans h₃) (h₂.symm.trans h₄)
  exact Measure.eqOn_Icc_of_ae_eq volume hb.ne
    ((ae_restrict_congr_set Ioc_ae_eq_Icc).mp hae) hu.continuousOn hz.continuousOn

end PDE.Hyperbolic.NonlinearWave.Cauchy
