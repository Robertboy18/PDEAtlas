/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import PDE.Analysis.Integration.Cone.Surface
import PDE.FDeriv.SpaceTime

/-!
# Continuous integrals on shrinking balls

A fixed unit ball parametrization supplies continuity through the vertex.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common WaveEquation

namespace PDE.Analysis

variable {n : ℕ}

/-- Rescaling to a fixed compact ball exhibits the vanishing volume at the
cone vertex, including in one spatial dimension. -/
theorem ballIntegral_shrinking_eq_scaled_integral [Fact (0 < n)]
    (P : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T : ℝ)
    {t : ℝ} (ht : t ≤ T) :
    ballIntegral n (fun x ↦ P (timeSpaceCons t x)) c (T - t) =
      (T - t) ^ n * ∫ x in Metric.closedBall (0 : ℝ^n) 1,
        P (timeSpaceCons t (c + (T - t) • x)) := by
  rcases ht.eq_or_lt with rfl | ht
  · have hn : n ≠ 0 := Nat.ne_of_gt (Fact.out : 0 < n)
    simp [ballIntegral, hn]
  · have hr : 0 < T - t := sub_pos.mpr ht
    rw [← ballIntegral_comp_add_left]
    unfold ballIntegral
    have hscale := Measure.setIntegral_comp_smul_of_pos volume
      (fun x : ℝ^n ↦ P (timeSpaceCons t (c + x)))
      (Metric.ball (0 : ℝ^n) 1) hr
    rw [finrank_euclideanSpace_fin, smul_unitBall_of_pos hr, smul_eq_mul] at hscale
    let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
    have hball : Metric.closedBall (0 : ℝ^n) 1 =ᵐ[volume] Metric.ball (0 : ℝ^n) 1 :=
      (closedBall_ae_eq_coneGraph_domain (0 : ℝ^n) 1).trans
        (sdiff_null_ae_eq_self (measure_singleton (0 : ℝ^n)))
    rw [setIntegral_congr_set hball, hscale, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- A continuous density has a continuous integral on shrinking balls, including at the vertex. -/
theorem continuousOn_ballIntegral_shrinking [Fact (0 < n)]
    {P : ℝ^(n + 1) → ℝ} (hP : Continuous P) (c : ℝ^n) (T : ℝ) :
    ContinuousOn (fun t ↦ ballIntegral n (fun x ↦ P (timeSpaceCons t x)) c (T - t)) (Iic T) := by
  have hmap : Continuous (fun p : ℝ × ℝ^n ↦
      timeSpaceCons p.1 (c + (T - p.1) • p.2)) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_fst.prodMk
        (continuous_const.add ((continuous_const.sub continuous_fst).smul continuous_snd)))
  have hf : Continuous (Function.uncurry (fun (t : ℝ) (x : ℝ^n) ↦
      P (timeSpaceCons t (c + (T - t) • x)))) :=
    hP.comp hmap
  have hi := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_closedBall (0 : ℝ^n) 1)
  have hp : Continuous (fun t : ℝ ↦ (T - t) ^ n) :=
    (continuous_const.sub continuous_id).pow n
  apply (hp.mul hi).continuousOn.congr
  intro t ht
  exact (ballIntegral_shrinking_eq_scaled_integral P c T ht)

end PDE.Analysis
