/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Linear
import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability

/-!
# Identifying energy weak waves with integrable forcing

Square-integrable spatial L² forcing gives a continuous energy Duhamel curve.
Autonomous weak-wave uniqueness identifies arbitrary Bochner weak representatives
with that curve, without presupposing their time continuity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Arbitrary energy data and locally integrable L² forcing satisfy both integrated
whole-space equations. In particular, velocity is the time derivative of
displacement in L², and acceleration is `f - (1 - Δ)u` in the H¹ dual. -/
theorem linear_forced_integral_of_locallyIntegrable {f : ℝ → DerivLp n 2 univ}
    (hf : LocallyIntegrable f volume) (x : EnergyState n) {t : ℝ} (ht : 0 ≤ t) :
    let z := fun s ↦ (linearSemigroup n).realOrbit x s +
      (linearSemigroup n).duhamel (fun r ↦ (C).symm (0, f r)) s
    (∫ s in (0 : ℝ)..t, (C (z s)).2) =
        (energyTriple n).inclusion (C (z t)).1 - (energyTriple n).inclusion (C x).1 ∧
      (∫ s in (0 : ℝ)..t,
        (energyTriple n).pivotToDual (f s) - massForm n (C (z s)).1) =
        (energyTriple n).pivotToDual (C (z t)).2 -
          (energyTriple n).pivotToDual (C x).2 := by
  let P : EnergyState n →L[ℝ] H¹(ℝ^n) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (C).toContinuousLinearMap
  let V : EnergyState n →L[ℝ] DerivLp n 2 univ :=
    (ContinuousLinearMap.snd ℝ _ _).comp (C).toContinuousLinearMap
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := (C).symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hforce : LocallyIntegrable (fun r ↦ (C).symm (0, f r)) volume :=
    fun r ↦ J.integrableAtFilter_comp (hf r)
  have hS : ∀ r, ‖linearSemigroup n r‖ ≤ 1 :=
    waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
      (massForm_coercive n) massForm_symmetric
  have hq := observed_forced_integral_of_locallyIntegrable (linearSemigroup n) hS
    ((energyTriple n).inclusion.comp P) V (linearSemigroup_dense_domain n)
    (fun a b h ↦ (linearSemigroup_generator h).1) hforce x ht
  have hp := observed_forced_integral_of_locallyIntegrable (linearSemigroup n) hS
    ((energyTriple n).pivotToDual.comp V) (-(massForm n).comp P) (linearSemigroup_dense_domain n)
    (fun a b h ↦ by
      have h' := (linearSemigroup_generator h).2
      change (energyTriple n).pivotToDual (C b).2 = -(massForm n (C a).1)
      exact neg_eq_iff_eq_neg.mp h'.symm) hforce x ht
  constructor
  · simpa only [P, V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero] using hq
  · simpa only [P, V, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, neg_apply, neg_add_eq_sub] using hp


/-- An arbitrary Bochner weak massive wave with square-integrable spatial L²
forcing agrees almost everywhere with the constructed Duhamel curve. -/
theorem weakWave_eq_duhamel_of_memLp {f : ℝ → DerivLp n 2 univ} (hf : LocallyIntegrable f volume)
    {b : ℝ} (hf₂ : MemLp f 2 (volume.restrict (Ioc 0 b)))
    {ell : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b))}
    {q : Lp H¹(ℝ^n) 2 (volume.restrict (Ioc 0 b))}
    {p : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc 0 b))}
    {acc : Lp (StrongDual ℝ H¹(ℝ^n)) 2 (volume.restrict (Ioc 0 b))}
    (hell : (ell : ℝ → StrongDual ℝ H¹(ℝ^n)) =ᵐ[volume.restrict (Ioc 0 b)] fun t ↦
      (energyTriple n).pivotToDual (f t))
    (x : EnergyState n)
    (hw :
      IsGelfandWeakWaveSolution (energyTriple n) (fun _ ↦ massForm n) ell q p acc (C x).1 (C x).2) :
    (fun t ↦ (q t, p t)) =ᵐ[volume.restrict (Ioc 0 b)] fun t ↦ C ((linearSemigroup n).realOrbit x
      t + (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, f s)) t) := by
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := (C).symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hforce : LocallyIntegrable (fun r ↦ (C).symm (0, f r)) volume :=
    fun r ↦ J.integrableAtFilter_comp (hf r)
  have hS : ∀ r, ‖linearSemigroup n r‖ ≤ 1 :=
    waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
      (massForm_coercive n) massForm_symmetric
  let z := fun t ↦ C ((linearSemigroup n).realOrbit x t +
    (linearSemigroup n).duhamel (fun s ↦ (C).symm (0, f s)) t)
  have hz : Continuous z := (C).continuous.comp (((linearSemigroup n).continuous_realOrbit x).add
      (continuous_duhamel_of_locallyIntegrable (linearSemigroup n) hS hforce))
  obtain ⟨ell₂, q₂, p₂, acc₂, he₂, hq₂, hp₂, _, hw₂⟩ :=
    exists_weakWave_of_integrable_integral_equations
      (energyTriple n) (massForm n) ((energyTriple n).pivotToDual.comp_memLp' hf₂)
      hz (C x) hw.interval_nonempty
      (fun t ht ↦ (linear_forced_integral_of_locallyIntegrable hf x ht.1).1)
      (fun t ht ↦ (linear_forced_integral_of_locallyIntegrable hf x ht.1).2)
  have he : ell = ell₂ := Lp.ext (hell.trans he₂.symm)
  rw [← he] at hw₂
  have hcoercive (v : H¹(ℝ^n)) : 1 * ‖v‖ ^ 2 ≤ massForm n v v := by
    change 1 * ‖v‖ ^ 2 ≤ inner ℝ v v
    rw [one_mul, real_inner_self_eq_norm_sq]
  obtain ⟨hqeq, hpeq, _⟩ := hw.eq_of_autonomous_symmetric_coercive
    hw₂ massForm_symmetric zero_lt_one hcoercive
  rw [hqeq, hpeq]
  filter_upwards [hq₂, hp₂] with t hq hp using Prod.ext hq hp

end PDE.Hyperbolic.NonlinearWave.Cauchy
