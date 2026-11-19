/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Topology.MetricSpace.Contracting
import CAS.ExactTactic

/-!
# Cone integral equations with arbitrary free input

A globally Lipschitz reaction gives a contraction for uniformly small time,
independently of the size of the free input. The implicit function theorem
identifies this fixed point with a locally C¹ parameter map. In particular, the initial displacement
need not be small.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The normalized integral equation has a unique C¹ solution for every free
input, on one time strip determined only by the operator and Lipschitz constant. -/
theorem exists_integral_solution_arbitrary_input (K : E →L[ℝ] E) {N : E → E}
    (hN : ContDiff ℝ 1 N) {C : NNReal} (hLip : LipschitzWith C N) :
    ∃ T : ℝ, 0 < T ∧ ∃ ψ : ℝ × E → E, ContDiffOn ℝ 1 ψ {p | |p.1| < T} ∧
      (∀ p : ℝ × E, |p.1| < T → ψ p = p.2 + p.1 ^ 2 • K (N (ψ p))) ∧
      (∀ p : ℝ × E, |p.1| < T → ∀ w, w = p.2 + p.1 ^ 2 • K (N w) → ψ p = w) := by
  have hc : Continuous (fun t : ℝ ↦ t ^ 2 * ‖K‖ * (C : ℝ)) := by fun_prop
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, t ^ 2 * ‖K‖ * (C : ℝ) < 1 / 2 :=
    hc.continuousAt.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨T, hT, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  have hb {t : ℝ} (ht : |t| < T) : t ^ 2 * ‖K‖ * (C : ℝ) < 1 / 2 :=
    hsmall (by simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)
  let F : (ℝ × E) → E → E := fun p w ↦ p.2 + p.1 ^ 2 • K (N w)
  have hcontr (p : ℝ × E) (hp : |p.1| < T) : ContractingWith (1 / 2) (F p) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
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
  let ψ : ℝ × E → E := fun p ↦ if hp : |p.1| < T then
    (hcontr p hp).fixedPoint (F p) else 0
  have heq (p : ℝ × E) (hp : |p.1| < T) : ψ p = F p (ψ p) := by
    dsimp only [ψ]
    rw [dite_eq_left hp]
    exact (hcontr p hp).fixedPoint_isFixedPt.eq.symm
  have huniq (p : ℝ × E) (hp : |p.1| < T) (w : E) (hw : w = F p w) : ψ p = w :=
    (hcontr p hp).fixedPoint_unique' (heq p hp).symm hw.symm
  refine ⟨T, hT, ψ, ?_, heq, huniq⟩
  intro p hp
  let G : (ℝ × E) × E → E := fun z ↦ z.2 - F z.1 z.2
  have hG : ContDiff ℝ 1 G := contDiff_snd.sub (contDiff_fst.snd.add
    ((contDiff_fst.fst.pow 2).smul (K.contDiff.comp (hN.comp contDiff_snd))))
  have hzero : G (p, ψ p) = 0 := sub_eq_zero.mpr (heq p hp)
  have hF : ContDiff ℝ 1 (F p) := contDiff_const.add (contDiff_const.smul (K.contDiff.comp hN))
  have hpartial : (fderiv ℝ G (p, ψ p)).comp (ContinuousLinearMap.inr ℝ (ℝ × E) E) =
      ContinuousLinearMap.id ℝ E - fderiv ℝ (F p) (ψ p) := by
    have hd := (hG.differentiable one_ne_zero (p, ψ p)).hasFDerivAt.comp (ψ p)
      ((hasFDerivAt_const p (ψ p)).prodMk (hasFDerivAt_id (ψ p)))
    exact hd.unique ((hasFDerivAt_id (ψ p)).sub (hF.differentiable one_ne_zero (ψ p)).hasFDerivAt)
  have hinv : ((fderiv ℝ G (p, ψ p)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) E)).IsInvertible := by
    rw [hpartial]
    have hn : ‖fderiv ℝ (F p) (ψ p)‖ < 1 :=
      (norm_fderiv_le_of_lipschitz ℝ (hcontr p hp).toLipschitzWith).trans_lt (by norm_num)
    obtain ⟨v, hv⟩ := isUnit_one_sub_of_norm_lt_one hn
    exact ⟨ContinuousLinearEquiv.ofUnit v, hv⟩
  let φ := hG.contDiffAt.implicitFunction (by norm_num : (1 : ℕ∞ω) ≠ 0) hinv
  have hφ : ContDiffAt ℝ 1 φ p :=
    hG.contDiffAt.contDiffAt_implicitFunction (by norm_num) hinv
  have hφeq : ∀ᶠ q in 𝓝 p, G (q, φ q) = 0 := by
    simpa only [hzero] using hG.contDiffAt.eventually_apply_implicitFunction
      (by norm_num) hinv
  have hstrip : ∀ᶠ q : ℝ × E in 𝓝 p, |q.1| < T :=
    (continuous_fst.abs.isOpen_preimage _ isOpen_Iio).mem_nhds hp
  have hevent : ψ =ᶠ[𝓝 p] φ := by
    filter_upwards [hφeq, hstrip] with q hq hqt using huniq q hqt _ (sub_eq_zero.mp hq)
  exact (hφ.congr_of_eventuallyEq hevent).contDiffWithinAt

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
