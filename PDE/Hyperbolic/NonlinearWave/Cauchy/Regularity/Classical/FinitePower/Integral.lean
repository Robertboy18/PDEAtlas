/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalIntegral
import PDE.Analysis.Calculus.Implicit.Regularity
import CAS.ExactTactic

/-!
# Second regularity of the uniform cone fixed point

The C¹ contraction constructs the fixed point. The finite-order
implicit function theorem upgrades that same point to C² when the reaction
operator is C².
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The uniform cone fixed point is C² for a C² Lipschitz reaction operator. -/
theorem exists_c2_integral_solution_arbitrary_input (K : E →L[ℝ] E) {N : E → E}
    (hN : ContDiff ℝ 2 N) {C : NNReal} (hLip : LipschitzWith C N) :
    ∃ T : ℝ, 0 < T ∧ ∃ ψ : ℝ × E → E, ContDiffOn ℝ 2 ψ {p | |p.1| < T} ∧
      (∀ p : ℝ × E, |p.1| < T → ψ p = p.2 + p.1 ^ 2 • K (N (ψ p))) ∧
      (∀ p : ℝ × E, |p.1| < T → ∀ w, w = p.2 + p.1 ^ 2 • K (N w) → ψ p = w) := by
  obtain ⟨T₀, hT₀, ψ, hψ, heq, huniq⟩ :=
    exists_integral_solution_arbitrary_input K (hN.of_le (by norm_num)) hLip
  have hc : Continuous (fun t : ℝ ↦ t ^ 2 * ‖K‖ * (C : ℝ)) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * ‖K‖ * (C : ℝ) < 1 / 2 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  let T := min T₀ δ
  have hT : 0 < T := lt_min hT₀ hδ
  have hTT : T ≤ T₀ := min_le_left _ _
  have hb {t : ℝ} (ht : |t| < T) : t ^ 2 * ‖K‖ * (C : ℝ) < 1 / 2 :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      using ht.trans_le (min_le_right T₀ δ))
  let F : (ℝ × E) → E → E := fun p w ↦ p.2 + p.1 ^ 2 • K (N w)
  have hFLip (p : ℝ × E) (hp : |p.1| < T) : LipschitzWith (1 / 2) (F p) := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    change dist (p.2 + p.1 ^ 2 • K (N x)) (p.2 + p.1 ^ 2 • K (N y)) ≤ _
    rw [dist_add_left, dist_eq_norm, ← smul_sub, ← map_sub, norm_smul,
      Real.norm_of_nonneg (sq_nonneg _)]
    calc
      p.1 ^ 2 * ‖K (N x - N y)‖ ≤
          p.1 ^ 2 * (‖K‖ * ((C : ℝ) * dist x y)) := by
        gcongr
        exact K.le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left
          (by simpa only [dist_eq_norm] using hLip.dist_le_mul x y) (norm_nonneg _))
      _ = (p.1 ^ 2 * ‖K‖ * (C : ℝ)) * dist x y := by cas
      _ ≤ (↑(1 / 2 : NNReal)) * dist x y := by
        norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        exact mul_le_mul_of_nonneg_right (hb hp).le dist_nonneg
  refine ⟨T, hT, ψ, ?_, fun p hp ↦ heq p (hp.trans_le hTT), fun p hp ↦ huniq p (hp.trans_le hTT)⟩
  intro p hp
  let G : (ℝ × E) × E → E := fun z ↦ z.2 - F z.1 z.2
  have hG : ContDiff ℝ 2 G := contDiff_snd.sub (contDiff_fst.snd.add
    ((contDiff_fst.fst.pow 2).smul (K.contDiff.comp (hN.comp contDiff_snd))))
  have hzero : G (p, ψ p) = 0 := sub_eq_zero.mpr (heq p (hp.trans_le hTT))
  have hF : ContDiff ℝ 2 (F p) := contDiff_const.add (contDiff_const.smul (K.contDiff.comp hN))
  have hpartial : (fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ (ℝ × E) E) =
      ContinuousLinearMap.id ℝ E - fderiv ℝ (F p) (ψ p) := by
    have hd := (hG.differentiable (by norm_num) (p, ψ p)).hasFDerivAt.comp (ψ p)
      ((hasFDerivAt_const p (ψ p)).prodMk (hasFDerivAt_id (ψ p)))
    exact hd.unique ((hasFDerivAt_id (ψ p)).sub
      (hF.differentiable (by norm_num) (ψ p)).hasFDerivAt)
  have hinv : ((fderiv ℝ G (p, ψ p)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) E)).IsInvertible := by
    rw [hpartial]
    have hn : ‖fderiv ℝ (F p) (ψ p)‖ < 1 :=
      (norm_fderiv_le_of_lipschitz ℝ (hFLip p hp)).trans_lt (by norm_num)
    obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hn
    exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩
  have hstrip : ∀ᶠ q : ℝ × E in 𝓝 p, |q.1| < T :=
    (continuous_fst.abs.isOpen_preimage _ isOpen_Iio).mem_nhds hp
  apply (hG.contDiffAt.of_implicit_eq (by norm_num) hinv (hψ.continuousOn.continuousAt
      ((isOpen_lt continuous_fst.abs continuous_const).mem_nhds (hp.trans_le hTT)))
    ?_).contDiffWithinAt
  filter_upwards [hstrip] with q hq
  exact (sub_eq_zero.mpr (heq q (hq.trans_le hTT))).trans hzero.symm

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
