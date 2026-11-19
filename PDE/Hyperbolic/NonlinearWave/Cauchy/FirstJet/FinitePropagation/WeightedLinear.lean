/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedStability

/-!
# Weighted bounds for the linear wave semigroup

The massive wave semigroup is the first-jet equation whose reaction is the
value coordinate. Its localized energy bound follows from natural-energy
stability, including for data outside the generator domain.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

private theorem valueReaction_lipschitz :
    LipschitzWith 1 (fun p : ℝ^n × ℝ × ℝ ↦ p.2.2) :=
  (LipschitzWith.prod_snd.comp LipschitzWith.prod_snd).weaken (by norm_num)

private theorem reaction_value (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    reaction valueReaction_lipschitz rfl z = (energyTriple n).inclusion z.1 := by
  apply Lp.ext
  exact reaction_apply_ae valueReaction_lipschitz rfl z

/-- The linear orbit in displacement and velocity coordinates. -/
def linearCoordinateOrbit (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) :=
  ⟨fun t ↦ C ((linearSemigroup n).realOrbit ((C).symm x) t),
    (C).continuous.comp ((linearSemigroup n).continuous_realOrbit _)⟩

private theorem isEnergySolution_linearCoordinateOrbit (x : H¹(ℝ^n) × DerivLp n 2 univ) :
    IsEnergySolution valueReaction_lipschitz rfl x (linearCoordinateOrbit x) := by
  have hacc (z : H¹(ℝ^n) × DerivLp n 2 univ) :
      acceleration valueReaction_lipschitz rfl z = -massForm n z.1 := by
    rw [← source_sub_massForm]
    simp only [source, reaction_value, sub_self, map_zero, zero_sub]
  refine ⟨(linearCoordinateOrbit x).continuous.continuousOn, ?_, ?_, ?_⟩
  · simp [linearCoordinateOrbit]
  · intro t ht
    have h := (linear_forced_integral (n := n) (f := fun _ ↦ 0) continuous_const ((C).symm x) ht).1
    simpa only [StronglyContinuousSemigroup.duhamel, ← Prod.zero_eq_mk, map_zero,
      intervalIntegral.integral_zero, add_zero, ContinuousLinearEquiv.apply_symm_apply,
      linearCoordinateOrbit, ContinuousMap.coe_mk] using h
  · intro t ht
    have h := (linear_forced_integral (n := n) (f := fun _ ↦ 0) continuous_const ((C).symm x) ht).2
    simpa only [StronglyContinuousSemigroup.duhamel, ← Prod.zero_eq_mk, map_zero,
      intervalIntegral.integral_zero, add_zero, ContinuousLinearEquiv.apply_symm_apply,
      linearCoordinateOrbit, ContinuousMap.coe_mk, hacc, zero_sub] using h

/-- A nonnegative spatial weight with relative gradient bound controls every
linear energy orbit, without imposing higher regularity on its initial data. -/
theorem weightedEnergyForm_linearCoordinateOrbit_le (χ : W^{1,∞}(ℝ^n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ, |(χ : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n i) y| ≤ ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (x : H¹(ℝ^n) × DerivLp n 2 univ) {t : ℝ} (ht : 0 ≤ t) :
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    weightedEnergyForm a (linearCoordinateOrbit x t) (linearCoordinateOrbit x t) ≤
      weightedEnergyForm a x x * Real.exp ((3 + (n : ℝ) * ρ) * t) := by
  have h := (isEnergySolution_linearCoordinateOrbit x).weighted_sub_le_exp
    (isEnergySolution_linearCoordinateOrbit 0) χ hρ ha hd ht
  simpa only [linearCoordinateOrbit, ContinuousMap.coe_mk,
    StronglyContinuousSemigroup.realOrbit, map_zero, sub_zero, NNReal.coe_one,
    one_pow, show (2 : ℝ) + 1 = 3 by norm_num] using h

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
