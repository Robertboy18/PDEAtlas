/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.Stability
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.InitialDomain

/-!
# Energy bounds for forward time quotients

For generator-domain initial data, the linear orbit has an energy increment
bounded by time times the generator norm. Continuity bounds the nonlinear
forcing near zero. Stability of the restarted flow then bounds all forward
time quotients on a finite interval. This is the time-regularity input for our proof of
Theorem 1(ii) of Evans, §12.2.1; Evans uses spatial difference quotients instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1(ii) and step 3 of its proof.
  <https://doi.org/10.1090/gsm/019>
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

/-- The massive wave orbit of domain data has a linear energy increment bound. -/
theorem norm_linearSemigroup_sub_le {z Az : EnergyState n}
    (hz : (linearSemigroup n).HasGeneratorAt z Az) {t : ℝ} (ht : 0 ≤ t) :
    ‖(linearSemigroup n).realOrbit z t - z‖ ≤ ‖Az‖ * t := by
  have heq := ((linearSemigroup n).hasGeneratorAt_iff_integratedOperator z Az).mp hz ⟨t, ht⟩
  change (∫ s in (0 : ℝ)..t, (linearSemigroup n).realOrbit Az s) =
    linearSemigroup n ⟨t, ht⟩ z - z at heq
  have hb : ∀ s ∈ Ι (0 : ℝ) t, ‖(linearSemigroup n).realOrbit Az s‖ ≤ ‖Az‖ := by
    intro s _
    simpa only [StronglyContinuousSemigroup.realOrbit, one_mul] using
      (linearSemigroup n s.toNNReal).le_of_opNorm_le (linearSemigroup_isContraction n s.toNNReal) Az
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [heq] at hi
  have hcoe : t.toNNReal = ⟨t, ht⟩ := by
    ext
    exact Real.coe_toNNReal t ht
  simpa only [StronglyContinuousSemigroup.realOrbit, hcoe, sub_zero, abs_of_nonneg ht] using hi

variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}
variable {x : H¹(ℝ^n) × DerivLp n 2 univ}
variable {u : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)}

/-- Domain initial data give a uniform linear bound for the initial energy increment. -/
theorem IsEnergySolution.exists_initial_increment_bound (h : IsEnergySolution hf hf0 x u)
    {Ax : EnergyState n} (hx : (linearSemigroup n).HasGeneratorAt ((C).symm x) Ax) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a ∈ Icc (0 : ℝ) 1, ‖(C).symm (u a - x)‖ ≤ D * a := by
  let F : ℝ → EnergyState n := fun s ↦ nonlinearMap hf hf0 ((C).symm (u s))
  have hF : Continuous F := (nonlinearMap hf hf0).continuous.comp
    ((C).symm.continuous.comp u.continuous)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1) hF.continuousOn
  refine ⟨‖Ax‖ + max B 0, add_nonneg (norm_nonneg _) (le_max_right _ _), fun a ha ↦ ?_⟩
  have hd := (linearSemigroup n).norm_duhamel_sub_le (f := F) (g := fun _ ↦ 0) hF continuous_const
    (τ := 1) (M := 1) (fun r _ ↦ linearSemigroup_isContraction n r) ha
    (D := max B 0) (fun s hs ↦ by
      simpa only [sub_zero] using (hB s ⟨hs.1, hs.2.trans ha.2⟩).trans (le_max_left B 0))
  have hzero (t : ℝ) : (linearSemigroup n).duhamel (fun _ ↦ 0) t = 0 := by
    simp [StronglyContinuousSemigroup.duhamel]
  rw [hzero, sub_zero, NNReal.coe_one, one_mul] at hd
  have heq : (C).symm (u a - x) = ((linearSemigroup n).realOrbit ((C).symm x) a - (C).symm x) +
        (linearSemigroup n).duhamel F a := by
    rw [map_sub, h.mild_eq ha.1]
    abel
  rw [heq, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (norm_linearSemigroup_sub_le hx ha.1) hd)

/-- Forward time increments are uniformly linear in their length on finite intervals. -/
theorem IsEnergySolution.exists_time_increment_bound (h : IsEnergySolution hf hf0 x u)
    {Ax : EnergyState n} (hx : (linearSemigroup n).HasGeneratorAt ((C).symm x) Ax) (T : ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ Icc (0 : ℝ) 1,
      ‖(C).symm (u (t + a) - u t)‖ ≤ R * a := by
  obtain ⟨D, hD, hinc⟩ := h.exists_initial_increment_bound hx
  obtain ⟨K, hK⟩ := nonlinearMap_lipschitz hf hf0
  refine ⟨D * Real.exp ((K : ℝ) * T), mul_nonneg hD (Real.exp_pos _).le, ?_⟩
  intro t ht a ha
  let v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ) :=
    ⟨fun s ↦ u (a + s), u.continuous.comp (continuous_const.add continuous_id)⟩
  have hv : IsEnergySolution hf hf0 (u a) v := h.shift ha.1
  have he := hv.norm_sub_le_exp h hK ht.1
  change ‖(C).symm (u (a + t) - u t)‖ ≤ _ at he
  rw [add_comm a t] at he
  calc
    ‖(C).symm (u (t + a) - u t)‖ ≤ ‖(C).symm (u a - x)‖ * Real.exp ((K : ℝ) * t) := he
    _ ≤ (D * a) * Real.exp ((K : ℝ) * T) := mul_le_mul (hinc a ha)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg))
      (Real.exp_pos _).le (mul_nonneg hD ha.1)
    _ = (D * Real.exp ((K : ℝ) * T)) * a := mul_right_comm _ _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
