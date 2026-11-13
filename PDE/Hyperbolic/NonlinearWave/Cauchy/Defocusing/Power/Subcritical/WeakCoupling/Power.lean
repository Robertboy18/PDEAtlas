/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower.Deriv
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.WeakCoupling.Trajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.SignCondition.Truncation
import CAS.ExactTactic

/-!
# Weak signed-power coupling on a fixed time interval

A fixed amplitude cutoff constructs the parameter family. A bound for its
retarded remainder removes the cutoff on any prescribed finite time interval
when the coupling is sufficiently small. The first-derivative limit is inherited
from the jointly C¹ cone construction and includes zeros of the solution.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Every finite time interval admits a weakly coupled signed-power family.
The parameter-dependent free field is only required to be uniformly bounded
on that interval. The cutoff is absent from the equation and from the C¹ limit. -/
theorem exists_weakCoupling_signedPower_trajectory {r : ℝ} (hr : 1 ≤ r) {S B : ℝ} (hS : 0 ≤ S)
    (hB : 0 ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ H : ℝ × (ℝ × ℝ^3) → ℝ, ContDiff ℝ 1 H → (∀ κ : ℝ, |κ| ≤ 1 → ∀ p : ℝ × ℝ^3, p.1 ∈ Icc 0 S →
        |H (κ, p)| ≤ B) → ∃ v a : ℝ → (ℝ × ℝ^3) → ℝ,
        ContDiffOn ℝ 1 (Function.uncurry v) {z | |z.1| < δ ∧ |z.2.1| < S + 1} ∧
      ContDiffOn ℝ 1 (Function.uncurry a) {z | |z.1| < δ ∧ |z.2.1| < S + 1} ∧
      (∀ κ p, |κ| < δ → |p.1| < S + 1 → v κ p = H (κ, p) + (κ * p.1) ^ 2 * a κ p) ∧
      (∀ κ p, |κ| < δ → p.1 ∈ Icc 0 S → |v κ p| < B + 1) ∧
      (∀ κ p, |κ| < δ → p.1 ∈ Icc 0 S → a κ p = ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
        -Real.signedPower r (v κ (p.1 * (s : ℝ), p.2 + p.1 • ((1 - (s : ℝ)) • (ω : ℝ^3))))
        ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3)) ∧
      TendstoLocallyUniformly v (fun p ↦ H (0, p)) (𝓝 0) ∧
      TendstoLocallyUniformly (fun κ p ↦ fderiv ℝ (v κ) p) (fderiv ℝ (fun p ↦ H (0, p))) (𝓝 0) := by
  have hs (z : ℝ) : 0 ≤ z * Real.signedPower r z := by
    unfold Real.signedPower
    nlinarith [mul_nonneg (Real.rpow_nonneg (abs_nonneg z) (r - 1)) (sq_nonneg z)]
  obtain ⟨f, C, hf, hfc, hLip, hmatch, _⟩ := SignCondition.exists_sign_preserving_lipschitz_reaction
      (m := 1) (Real.contDiff_one_signedPower hr) one_ne_zero hs
      (show 0 < B + 2 by linarith)
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hfc
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hKM : 0 ≤ ‖duhamelOperator‖ * M := mul_nonneg (norm_nonneg duhamelOperator) hM0
  obtain ⟨T, hT, htrajectory⟩ := exists_weakCoupling_cone_trajectory_of_lipschitz hf.neg hLip.neg
  have hL : 0 < S + 1 := by linarith
  have htime : ∀ᶠ κ : ℝ in 𝓝 0, |κ * (S + 1)| < T :=
    ((continuous_id.mul continuous_const).abs.continuousAt).eventually
      (gt_mem_nhds (by simpa using hT))
  have hrem : ∀ᶠ κ : ℝ in 𝓝 0, (κ * (S + 1)) ^ 2 * (‖duhamelOperator‖ * M) < 1 :=
    (((continuous_id.mul continuous_const).pow 2).mul continuous_const).continuousAt.eventually
      (gt_mem_nhds (by simp))
  obtain ⟨η, hη, hsmall⟩ := Metric.mem_nhds_iff.mp (htime.and hrem)
  let δ := min η 1
  have hδ : 0 < δ := lt_min hη zero_lt_one
  have hδη : δ ≤ η := min_le_left _ _
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hκsmall {κ : ℝ} (hκ : |κ| < δ) :
      |κ * (S + 1)| < T ∧ (κ * (S + 1)) ^ 2 * (‖duhamelOperator‖ * M) < 1 :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      using hκ.trans_le hδη)
  have htimes {κ t : ℝ} (ht : |t| < S + 1) : |κ * t| ≤ |κ * (S + 1)| := by
    rw [abs_mul, abs_mul, abs_of_pos hL]
    exact mul_le_mul_of_nonneg_left ht.le (abs_nonneg _)
  have hdom {κ t : ℝ} (hκ : |κ| < δ) (ht : |t| < S + 1) : |κ * t| < T :=
    (htimes ht).trans_lt (hκsmall hκ).1
  have htL {t : ℝ} (ht : t ∈ Icc 0 S) : |t| < S + 1 := by
    rw [abs_of_nonneg ht.1]
    linarith [ht.2]
  refine ⟨δ, hδ, hδ1, fun H hH hbound ↦ ?_⟩
  obtain ⟨v, a, hv, ha, heq, hrem, habound, hvlim, hdlim⟩ := htrajectory H hH
  have hva (κ : ℝ) (p : ℝ × ℝ^3) (hκ : |κ| < δ) (hp : p.1 ∈ Icc 0 S) :
      |v κ p| < B + 1 := by
    have hn : |a κ p| ≤ ‖duhamelOperator‖ * M := habound M hM0
      (fun z ↦ by simpa only [abs_neg, Real.norm_eq_abs] using hM z) κ p (hdom hκ (htL hp))
    have hpows : (κ * p.1) ^ 2 ≤ (κ * (S + 1)) ^ 2 := sq_le_sq.mpr (htimes (htL hp))
    rw [heq κ p (hdom hκ (htL hp))]
    refine (abs_add_le _ _).trans_lt ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg (κ * p.1))]
    linarith [(hκsmall hκ).2, hbound κ (hκ.le.trans hδ1) p hp,
      mul_le_mul_of_nonneg_left hn (sq_nonneg (κ * p.1)), mul_le_mul_of_nonneg_right hpows hKM]
  refine ⟨v, a, hv.mono (fun _ hz ↦ hdom hz.1 hz.2),
    ha.mono (fun _ hz ↦ hdom hz.1 hz.2), fun κ p hκ hp ↦ heq κ p (hdom hκ hp),
    hva, ?_, hvlim, hdlim⟩
  intro κ p hκ hp
  rw [hrem κ p (hdom hκ (htL hp))]
  congr 1 with s
  congr 3 with ω
  have hq : (physicalPoint p (rim s ω)).1 ∈ Icc 0 S := ⟨mul_nonneg hp.1 s.2.1,
      (mul_le_mul_of_nonneg_left s.2.2 hp.1).trans (by simpa using hp.2)⟩
  have hbq := hva κ (physicalPoint p (rim s ω)) hκ hq
  have hm := hmatch (show v κ (physicalPoint p (rim s ω)) ∈ Metric.closedBall 0 (B + 2) by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    linarith)
  exact congrArg Neg.neg hm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
