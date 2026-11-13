/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.Strong.LocalTransport
public import PDE.Analysis.Geometry.BallChain
import CAS.ExactTactic

/-!
# Positivity on connected spatial domains

The shared interior-ball graph gives a finite path between any two spatial
points. Each edge consumes a positive portion of the available time and uses
the moving-bump comparison. A stationary bump handles the empty path.
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open PDE.Analysis Set Metric
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Positivity propagates to every later positive time in a connected open
domain, including the terminal time. Only the trace, drift, and potential
need be continuous; no global coefficient bound is assumed. -/
theorem positive_of_positive_before
    {U : Set (ℝ^n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    {T θ : ℝ} (hθ : 0 < θ)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (htrace : ContinuousOn (fun p : ℝ^n × ℝ ↦ (a p.1 p.2).trace) (U ×ˢ Ioc 0 T))
    (hb : ContinuousOn (fun p : ℝ^n × ℝ ↦ b p.1 p.2) (U ×ˢ Ioc 0 T))
    (hccont : ContinuousOn (fun p : ℝ^n × ℝ ↦ c p.1 p.2) (U ×ˢ Ioc 0 T))
    (ha : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, (a x q).PosSemidef)
    (hell : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, ∀ d : ℝ^n,
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫)
    (hc : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, 0 ≤ c x q)
    (w : ℝ^n → ℝ → ℝ)
    (hwcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ w p.1 p.2) (U ×ˢ Ioc 0 T))
    (hwspace : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun z ↦ w z q) x)
    (hwtime : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, DifferentiableAt ℝ (w x) q)
    (hwsuper : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, 0 ≤ matrixParabolicOperator a b c w x q)
    (hwnonneg : ∀ x ∈ U, ∀ q ∈ Ioc 0 T, 0 ≤ w x q)
    {y z : ℝ^n} (hy : y ∈ U) (hz : z ∈ U) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (ht : t ≤ T) (hpos : 0 < w y s) :
    0 < w z t := by
  have hlocal {p : ℝ^n} {r s t : ℝ} (hr : 0 < r)
      (hball : closedBall p (2 * r) ⊆ U) (hs : 0 < s) (hst : s < t) (ht : t ≤ T)
      (v : ℝ^n) (htravel : (t - s) * ‖v‖ ≤ r) (hpos : 0 < w p s) :
      0 < w (p + (t - s) • v) t := by
    have hB : ball p (2 * r) ⊆ U := ball_subset_closedBall.trans hball
    have htimes : Icc s t ⊆ Ioc 0 T := fun _ hq ↦ ⟨hs.trans_le hq.1, hq.2.trans ht⟩
    have hO : Ioo s t ⊆ Ioo 0 T := fun _ hq ↦ ⟨hs.trans hq.1, hq.2.trans_le ht⟩
    have hsub := Set.prod_mono hball htimes
    exact positive_at_moving_center hr hst hθ v htravel a b c
      (htrace.mono hsub) (hb.mono hsub) (hccont.mono hsub)
      (fun x hx q hq ↦ ha x (hB hx) q (hO hq)) (fun x hx q hq ↦ hell x (hB hx) q (hO hq))
      (fun x hx q hq ↦ hc x (hB hx) q (hO hq)) w (hwcont.mono hsub)
      (fun x hx q hq ↦ hwspace x (hB hx) q (hO hq)) (fun x hx q hq ↦ hwtime x (hB hx) q (hO hq))
      (fun x hx q hq ↦ hwsuper x (hB hx) q (hO hq))
      (fun x hx q hq ↦ hwnonneg x (hball hx) q (htimes hq)) hpos
  have hstay (p : U) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ T)
      (hpos : 0 < w p.1 s) : 0 < w p.1 t := by
    obtain ⟨r, hr, _, hball⟩ := exists_ballChain_radius hU
      (by cas : (0 : ℝ) ≤ 1) (by cas : (0 : ℝ) < 1) p
    have hball' : closedBall p.1 (2 * r) ⊆ U := by
      simpa only [show (1 : ℝ) + 1 = 2 by cas] using hball
    simpa using hlocal hr hball' hs hst ht 0 (by simpa using hr.le) hpos
  have hedge (p q : U) (hpq : BallChainLinked U 2 1 p q)
      {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t ≤ T) (hpos : 0 < w p.1 s) :
      0 < w q.1 t := by
    obtain ⟨r, hr, _, hdist, hball, _⟩ := hpq
    let v := (t - s)⁻¹ • (q.1 - p.1)
    have htime : 0 < t - s := sub_pos.mpr hst
    have htravel : (t - s) * ‖v‖ ≤ r := by
      dsimp only [v]
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htime),
        ← mul_assoc, mul_inv_cancel₀ htime.ne', one_mul, ← dist_eq_norm, dist_comm]
    have hend : p.1 + (t - s) • v = q.1 := by
      dsimp only [v]
      rw [smul_smul, mul_inv_cancel₀ htime.ne', one_smul, add_sub_cancel]
    simpa only [hend] using hlocal hr hball hs hst ht v htravel hpos
  let G := ballChainGraph U 2 1
  obtain ⟨path⟩ := ballChainGraph_reachable hU hconn (by cas : (0 : ℝ) ≤ 2)
    (by cas : (0 : ℝ) < 1) (⟨y, hy⟩ : U) (⟨z, hz⟩ : U)
  have hwalk {p q : U} (path : G.Walk p q) :
      ∀ {s t : ℝ}, 0 < s → s < t → t ≤ T → 0 < w p.1 s → 0 < w q.1 t := by
    induction path with
    | nil => exact fun hs hst ht hpos ↦ hstay _ hs hst ht hpos
    | @cons p q z hadj tail ih =>
        intro s t hs hst ht hpos
        have hlink : BallChainLinked U 2 1 p q :=
          ((SimpleGraph.fromRel_adj _ p q).mp hadj).2.elim id ballChainLinked_symm
        obtain ⟨r, hsr, hrt⟩ := exists_between hst
        exact ih (hs.trans hsr) hrt ht (hedge p q hlink hs hsr (hrt.le.trans ht) hpos)
  exact hwalk path hs hst ht hpos

/-- An interior zero at positive time forces a nonnegative supersolution to
vanish on the whole closed backward cylinder. The closed-cylinder conclusion
is obtained by continuity after positivity excludes every earlier positive value. -/
theorem eqOn_zero_before_of_nonneg_of_eq_zero
    {U : Set (ℝ^n)} (hU : IsOpen U) (hconn : IsPreconnected U)
    {T θ : ℝ} (hθ : 0 < θ)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (htrace : ContinuousOn (fun p : ℝ^n × ℝ ↦ (a p.1 p.2).trace) (U ×ˢ Ioc 0 T))
    (hb : ContinuousOn (fun p : ℝ^n × ℝ ↦ b p.1 p.2) (U ×ˢ Ioc 0 T))
    (hccont : ContinuousOn (fun p : ℝ^n × ℝ ↦ c p.1 p.2) (U ×ˢ Ioc 0 T))
    (ha : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, (a x q).PosSemidef)
    (hell : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, ∀ d : ℝ^n,
      θ * ‖d‖ ^ 2 ≤ ⟪d, (a x q).toEuclideanLin d⟫)
    (hc : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, 0 ≤ c x q)
    (w : ℝ^n → ℝ → ℝ)
    (hwcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ w p.1 p.2) (closedCylinder U T))
    (hwspace : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun z ↦ w z q) x)
    (hwtime : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, DifferentiableAt ℝ (w x) q)
    (hwsuper : ∀ x ∈ U, ∀ q ∈ Ioo 0 T, 0 ≤ matrixParabolicOperator a b c w x q)
    (hwnonneg : ∀ x ∈ U, ∀ q ∈ Ioc 0 T, 0 ≤ w x q)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc 0 T)
    (hzero : w x₀ t₀ = 0) :
    EqOn (fun p : ℝ^n × ℝ ↦ w p.1 p.2) (fun _ ↦ 0) (closedCylinder U t₀) := by
  have hpositiveCylinder : U ×ˢ Ioc 0 T ⊆ closedCylinder U T :=
    fun _ hp ↦ ⟨subset_closure hp.1, hp.2.1.le, hp.2.2⟩
  have hearly : EqOn (fun p : ℝ^n × ℝ ↦ w p.1 p.2) (fun _ ↦ 0) (U ×ˢ Ioo 0 t₀) := by
    intro p hp
    apply le_antisymm _ (hwnonneg p.1 hp.1 p.2 ⟨hp.2.1, hp.2.2.le.trans ht₀.2⟩)
    by_contra h
    have hpos := positive_of_positive_before hU hconn hθ a b c htrace hb hccont ha hell hc
      w (hwcont.mono hpositiveCylinder) hwspace hwtime hwsuper hwnonneg hp.1 hx₀
      hp.2.1 hp.2.2 ht₀.2 (lt_of_not_ge h)
    simp only [hzero, lt_self_iff_false] at hpos
  apply hearly.of_subset_closure
    (hwcont.mono (Set.prod_mono Subset.rfl (Icc_subset_Icc le_rfl ht₀.2)))
    continuousOn_const
  · exact fun _ hp ↦ ⟨subset_closure hp.1, hp.2.1.le, hp.2.2.le⟩
  · rw [closure_prod_eq, closure_Ioo ht₀.1.ne]

end ParabolicMaximum
