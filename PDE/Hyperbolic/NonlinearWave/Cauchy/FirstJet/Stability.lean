/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.WeakFormulation

/-!
# Stability and time translation for first-jet energy solutions

The integral PDE determines the mild trajectory. Translation in forward time
preserves the PDE, and Grönwall controls differences by their initial energy.
These estimates use only the global Lipschitz bound of the first-jet reaction.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The whole-space massive propagator contracts the wave energy norm. -/
theorem linearSemigroup_isContraction (n : ℕ) :
    (linearSemigroup n).IsContraction :=
  waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
    (massForm_coercive n) massForm_symmetric

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x y : H¹(ℝ^n) × DerivLp n 2 univ}
variable {u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- Every energy solution satisfies the constructed mild equation at forward times. This is
`Cauchy.IsEnergySolutionOn.mild_eq` on `[0, t + 1]` for the force `source hf hf0`, with the
integrand written through `nonlinearMap hf hf0`. -/
theorem IsEnergySolution.mild_eq (h : IsEnergySolution hf hf0 x u) {t : ℝ} (ht : 0 ≤ t) :
    (C).symm (u t) = (linearSemigroup n).realOrbit ((C).symm x) t +
      (linearSemigroup n).duhamel (fun s ↦ nonlinearMap hf hf0 ((C).symm (u s))) t := by
  have heq := Cauchy.IsEnergySolutionOn.mild_eq (b := t + 1) (h.mono Icc_subset_Ici_self)
    (source_lipschitz hf hf0).continuous (source_sub_massForm hf hf0)
    (add_pos_of_nonneg_of_pos ht zero_lt_one) ⟨ht, le_add_of_nonneg_right zero_le_one⟩
  simpa only [nonlinearMap, ContinuousMap.coe_mk, ContinuousLinearEquiv.apply_symm_apply]
    using heq

/-- Restarting at any nonnegative time preserves both integrated PDE equations. -/
theorem IsEnergySolution.shift (h : IsEnergySolution hf hf0 x u) {a : ℝ} (ha : 0 ≤ a) :
    IsEnergySolution hf hf0 (u a) (fun t ↦ u (a + t)) := by
  refine ⟨(u.continuous.comp (continuous_const.add continuous_id)).continuousOn,
    by simp, ?_, ?_⟩
  · intro t ht
    rw [intervalIntegral.integral_comp_add_left (fun s ↦ (u s).2) a, add_zero]
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (u.continuous.snd.intervalIntegrable (μ := volume) 0 a)
      (u.continuous.snd.intervalIntegrable (μ := volume) a (a + t))
    rw [h.displacement a ha, h.displacement (a + t) (add_nonneg ha ht)] at hsum
    exact (eq_sub_of_add_eq' hsum).trans (by abel)
  · intro t ht
    rw [intervalIntegral.integral_comp_add_left (fun s ↦ acceleration hf hf0 (u s)) a, add_zero]
    have hc : Continuous (fun s ↦ acceleration hf hf0 (u s)) :=
      (continuous_acceleration hf hf0).comp u.continuous
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 a) (hc.intervalIntegrable (μ := volume) a (a + t))
    rw [h.velocity a ha, h.velocity (a + t) (add_nonneg ha ht)] at hsum
    exact (eq_sub_of_add_eq' hsum).trans (by abel)

/-- The first-jet wave flow is Lipschitz in its initial energy on every finite interval. -/
theorem IsEnergySolution.norm_sub_le_exp (hu : IsEnergySolution hf hf0 x u)
    (hv : IsEnergySolution hf hf0 y v) {K : NNReal} (hK : LipschitzWith K (nonlinearMap hf hf0))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖(C).symm (u t - v t)‖ ≤ ‖(C).symm (x - y)‖ * Real.exp ((K : ℝ) * t) := by
  let e := fun s ↦ ‖(C).symm (u s - v s)‖
  have he : Continuous e := ((C).symm.continuous.comp (u.continuous.sub v.continuous)).norm
  have hbound (r : NNReal) : ‖linearSemigroup n r‖ ≤ (1 : NNReal) :=
    linearSemigroup_isContraction n r
  have hi (s : ℝ) (hs : s ∈ Icc 0 t) :
      e s ≤ ‖(C).symm (x - y)‖ + (K : ℝ) * ∫ r in (0 : ℝ)..s, e r := by
    have hd := (linearSemigroup n).norm_duhamel_sub_le_integral
      (f := fun r ↦ nonlinearMap hf hf0 ((C).symm (u r)))
      (g := fun r ↦ nonlinearMap hf hf0 ((C).symm (v r))) (D := fun r ↦ (K : ℝ) * e r)
      ((nonlinearMap hf hf0).continuous.comp ((C).symm.continuous.comp u.continuous))
      ((nonlinearMap hf hf0).continuous.comp ((C).symm.continuous.comp v.continuous))
      (τ := ⟨t, ht⟩) (M := 1) (fun r _ ↦ hbound r) hs
      (continuous_const.mul he) (fun r _ ↦ by
        simpa only [← map_sub, e] using hK.norm_sub_le ((C).symm (u r)) ((C).symm (v r)))
    have ho := (linearSemigroup n s.toNNReal).le_of_opNorm_le (hbound s.toNNReal) ((C).symm (x - y))
    have heq : (C).symm (u s - v s) = linearSemigroup n s.toNNReal ((C).symm (x - y)) +
          ((linearSemigroup n).duhamel (fun r ↦ nonlinearMap hf hf0 ((C).symm (u r))) s -
          (linearSemigroup n).duhamel
            (fun r ↦ nonlinearMap hf hf0 ((C).symm (v r))) s) := by
      rw [map_sub, hu.mild_eq hs.1, hv.mild_eq hs.1]
      simp only [StronglyContinuousSemigroup.realOrbit, map_sub]
      abel
    change ‖(C).symm (u s - v s)‖ ≤ _
    rw [heq]
    apply (norm_add_le _ _).trans
    simpa only [NNReal.coe_one, one_mul, intervalIntegral.integral_const_mul] using add_le_add ho hd
  simpa only [sub_zero] using le_mul_exp_of_le_const_add_mul_intervalIntegral
    he.continuousOn K.coe_nonneg hi t ⟨ht, le_rfl⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
