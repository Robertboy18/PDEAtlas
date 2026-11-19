/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Stability

/-!
# Approximation by regular first-jet trajectories

The dense generator domain and energy stability approximate every energy
solution at each forward time by solutions with H² displacement and H¹
velocity data. This transfers weighted estimates without adding regularity
to the Cauchy data.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Convergence of energy data gives convergence of the solution at every
fixed forward time. -/
theorem IsEnergySolution.tendsto_of_initial {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u)
    {xj : ℕ → H¹(ℝ^n) × DerivLp n 2 univ} {uj : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}
    (hj : ∀ j, IsEnergySolution hf hf0 (xj j) (uj j)) (hx : Tendsto xj atTop (𝓝 x)) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun j ↦ uj j t) atTop (𝓝 (u t)) := by
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz hf hf0
  have hx' : Tendsto (fun j ↦ ‖(C).symm (xj j - x)‖ * Real.exp ((K : ℝ) * t))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, map_zero, norm_zero, zero_mul] using
      (((C).symm.continuous.tendsto (x - x)).comp (hx.sub tendsto_const_nhds)).norm.mul_const
        (Real.exp ((K : ℝ) * t))
  have hz : Tendsto (fun j ↦ ‖(C).symm (uj j t - u t)‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ norm_nonneg _) (fun j ↦ (hj j).norm_sub_le_exp hu hK ht) hx'
  have hdiff : Tendsto (fun j ↦ uj j t - u t) atTop (𝓝 0) := by
    have hz' := (tendsto_zero_iff_norm_tendsto_zero).mpr hz
    simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply, map_zero] using
      (C).continuous.tendsto 0 |>.comp hz'
  simpa only [sub_add_cancel, zero_add] using hdiff.add_const (u t)

/-- Every energy solution is the pointwise forward limit of solutions whose
data belong to the generator domain. -/
theorem IsEnergySolution.exists_generator_approximation {x : H¹(ℝ^n) × DerivLp n 2 univ}
    {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u) :
    ∃ (xj : ℕ → H¹(ℝ^n) × DerivLp n 2 univ) (Aj : ℕ → EnergyState n)
      (uj : ℕ → C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)),
      (∀ j, (linearSemigroup n).HasGeneratorAt ((C).symm (xj j)) (Aj j)) ∧
      (∀ j, IsEnergySolution hf hf0 (xj j) (uj j)) ∧
      Tendsto xj atTop (𝓝 x) ∧
      ∀ t : ℝ, 0 ≤ t → Tendsto (fun j ↦ uj j t) atTop (𝓝 (u t)) := by
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp (linearSemigroup_dense_domain n ((C).symm x))
  let xj := fun j ↦ C (z j)
  choose uj huj using fun j ↦ exists_energySolution hf hf0 (xj j)
  have hx : Tendsto xj atTop (𝓝 x) := by
    simpa only [Function.comp_def, xj, ContinuousLinearEquiv.apply_symm_apply] using
      ((C).continuous.tendsto ((C).symm x)).comp hlim
  refine ⟨xj, fun j ↦ (linearSemigroup n).generatorPMap ⟨z j, hz j⟩,
    uj, ?_, huj, hx, fun _ ht ↦ hu.tendsto_of_initial huj hx ht⟩
  intro j
  simpa only [xj, ContinuousLinearEquiv.symm_apply_apply] using
    (linearSemigroup n).hasGeneratorAt_generatorPMap ⟨z j, hz j⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
