/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Regularity.TimeQuotients
import PDE.Analysis.WeakCompactness
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Weak limits of first-jet wave time quotients

Bounded energy time quotients have a weakly convergent ultrafilter. The known
strong derivatives in L² and H¹ dual identify its two coordinates. This
recovers H¹ velocity and L² acceleration at every forward time without
assuming differentiability of the globally Lipschitz reaction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Observe displacement in L² and velocity in the H¹ dual. Both observations
commute with weak limits in the Hilbert energy space. -/
def weakStateCLM (m : ℕ) : EnergyState m →L[ℝ]
    DerivLp m 2 univ × StrongDual ℝ H¹(ℝ^m) :=
  let e := WaveEnergySpace.coordinates
    (H := DerivLp m 2 univ) (massForm m) (massForm_coercive m) massForm_symmetric
  ((energyTriple m).inclusion.comp
    ((ContinuousLinearMap.fst ℝ H¹(ℝ^m) (DerivLp m 2 univ)).comp e.toContinuousLinearMap)).prod
    ((energyTriple m).pivotToDual.comp
      ((ContinuousLinearMap.snd ℝ H¹(ℝ^m) (DerivLp m 2 univ)).comp e.toContinuousLinearMap))

/-- A pointwise energy bound on forward quotients gives a bounded energy lift
of the L²-displacement and dual-velocity derivatives. -/
theorem IsEnergySolution.exists_energy_derivative_lift {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(ℝ^n) × DerivLp n 2 univ} {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (h : IsEnergySolution hf hf0 x u) {t R : ℝ} (ht : 0 ≤ t)
    (hbound : ∀ a ∈ Ioc (0 : ℝ) 1, ‖(C).symm (u (t + a) - u t)‖ ≤ R * a) :
    ∃ d : EnergyState n, ‖d‖ ≤ R ∧ (energyTriple n).inclusion (C d).1 = (u t).2 ∧
      (energyTriple n).pivotToDual (C d).2 = acceleration hf hf0 (u t) := by
  let δ : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1)
  have hδ (j : ℕ) : δ j ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · exact one_div_pos.mpr (by positivity)
    · exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg j))
  let q : ℕ → EnergyState n := fun j ↦ (δ j)⁻¹ • (C).symm (u (t + δ j) - u t)
  have hq (j : ℕ) : ‖q j‖ ≤ R := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hδ j).1.le)]
    exact (inv_mul_le_iff₀ (hδ j).1).mpr
      (by simpa only [mul_comm (δ j) R] using hbound (δ j) (hδ j))
  have hb : Bornology.IsBounded (range q) :=
    isBounded_iff_forall_norm_le.mpr ⟨R, by rintro _ ⟨j, rfl⟩; exact hq j⟩
  obtain ⟨d, U, hU, hd⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter atTop q hb
  have hdR : ‖d‖ ≤ R := WeakCompactness.norm_le_of_tendsto_of_norm_le hd (Eventually.of_forall hq)
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have htδ : Tendsto (fun j ↦ t + δ j) atTop (𝓝[Ici 0 \ {t}] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa only [add_zero] using hδ0.const_add t, Eventually.of_forall fun j ↦ ?_⟩
    exact ⟨add_nonneg ht (hδ j).1.le, by simp only [mem_singleton_iff]; linarith [(hδ j).1]⟩
  have hderiv : HasDerivWithinAt
      (fun s ↦ ((energyTriple n).inclusion (u s).1, (energyTriple n).pivotToDual (u s).2))
      ((u t).2, acceleration hf hf0 (u t)) (Ici 0) t :=
    HasDerivWithinAt.prodMk (h.hasDerivWithinAt_displacement ht) (h.hasDerivWithinAt_velocity ht)
  have hobs : Tendsto (fun j ↦ weakStateCLM n (q j)) atTop
      (𝓝 ((u t).2, acceleration hf hf0 (u t))) := by
    have hs := (hasDerivWithinAt_iff_tendsto_slope.mp hderiv).comp htδ
    simpa only [Function.comp_def, slope_def_module, add_sub_cancel_left,
      weakStateCLM, q, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearEquiv.coe_coe, map_smul, map_sub,
      ContinuousLinearEquiv.apply_symm_apply] using hs
  have hweak := (WeakSpace.map (weakStateCLM n)).continuous.continuousAt.tendsto.comp hd
  have hstrong := (toWeakSpaceCLM ℝ
    (DerivLp n 2 univ × StrongDual ℝ H¹(ℝ^n))).continuous.continuousAt.tendsto.comp
      (hobs.mono_left hU)
  have heq : weakStateCLM n d = ((u t).2, acceleration hf hf0 (u t)) :=
    (toWeakSpace ℝ _).injective (tendsto_nhds_unique hweak hstrong)
  exact ⟨d, hdR, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
