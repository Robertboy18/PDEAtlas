/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.QuadraticBarrier
import PDE.Analysis.Metric.QuadraticPenalty
import CAS.ExactTactic

/-!
# Interior maxima for localized quadratic doubling

Quadratic localization makes spatial escape too expensive. Reciprocal time
barriers exclude a later terminal face, while a small boundary penalty
excludes initial contact. Starting from one positive diagonal value, these
estimates give a maximum with both points interior.

This construction uses continuity, compact balls, and explicit scalar bounds.
It does not use a differential equation. The autonomous and position-dependent
comparison proofs choose their scales differently and share this construction.
The viscosity contact calculation remains in `QuadraticBarrier`.

For bounded uniformly continuous functions ordered initially, a positive gap
also determines the time barrier and an upper bound on the doubling scale.
`exists_localized_maximum_of_initial_le` then permits any positive localization
tolerance. Its compact set works for every sufficiently small doubling scale,
so the two comparison arguments can choose these scales in either order.

The construction follows steps 1-4 of the proof of Theorem 1 in Evans, §10.2: the localization
plays the role of the term `ε(|x|²+|y|²)` in (5), and uniform continuity excludes initial contact
as in step 4. The reciprocal time barriers are those in the proof of his Lemma (Extrema at a
terminal time).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, Lemma (Extrema at a terminal time) and its proof,
  proof of Theorem 1, steps 1-4, equations (4)-(11).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi

open Set
open scoped Topology

section Localization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bound on the localized quadratic makes its spatial gradient small when
the localization scale is small. No inner product or dimension hypothesis is
needed for this norm estimate. -/
theorem norm_localization_gradient_lt {α M r : ℝ} {z : E × ℝ} (hα : 0 < α) (hM : 0 < M) (hr : 0 < r)
    (hsmall : α < r ^ 2 / (16 * (M + 1))) (hbound : α * quadraticSize z < M) :
    ‖(2 * α) • z.1‖ < r / 2 := by
  have hb : α * ‖z.1‖ ^ 2 < M :=
    (mul_le_mul_of_nonneg_left (norm_fst_sq_le_quadraticSize z) hα.le).trans_lt hbound
  have hs := (lt_div_iff₀ (show 0 < 16 * (M + 1) by positivity)).mp hsmall
  have hm := mul_lt_mul_of_pos_left hb (show 0 < 4 * α by positivity)
  have habs := sq_abs (2 * α * ‖z.1‖)
  have h : |2 * α * ‖z.1‖| < r / 2 := by
    apply (sq_lt_sq₀ (abs_nonneg _) (show 0 ≤ r / 2 by positivity)).mp
    nlinarith only [hs, hm, habs, hα]
  simpa only [norm_smul, Real.norm_eq_abs, abs_mul, abs_norm, mul_assoc] using h

end Localization

section Maximum

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]

/-- A positive diagonal value forces an attained doubled maximum away from
the initial, terminal, and spatial boundaries.

The boundary estimate `hinitial` is supplied by uniform continuity in the
comparison applications. The remaining assumptions bound the candidate
difference and make the terminal and spatial penalties exceed that bound.
The output retains global maximality for comparison with diagonal pairs,
as well as local maximality for the viscosity tests. -/
theorem exists_isMaxOn_quadratic_barrier {u v : E × ℝ → ℝ} {ε α a T S R M η : ℝ} (hε : 0 < ε)
    (hα : 0 < α) (ha : 0 < a) (hST : S < T) (hR : 0 ≤ R) (hη : 0 ≤ η) (hterminal : M ≤ a / (T - S))
    (hRlarge : M < α * R ^ 2) (hu : ContinuousOn u (closedTimeSlab T))
    (hv : ContinuousOn v (closedTimeSlab T))
    (hbound : ∀ z ∈ closedTimeSlab T, ∀ w ∈ closedTimeSlab T, u z - v w < M)
    (hinitial : ∀ z ∈ closedTimeSlab T, ∀ w ∈ closedTimeSlab T, z.2 = 0 ∨ w.2 = 0 →
      u z - v w - dist z w ^ 2 / (2 * ε) ≤ η)
    (hwitness : ∃ z ∈ closedTimeSlab S ∩ Metric.closedBall 0 R, η <
      u z - v z - (α * (quadraticSize z + quadraticSize z) + a / (T - z.2) + a / (T - z.2))) :
    let K := closedTimeSlab S ∩ Metric.closedBall (0 : E × ℝ) R
    let F := fun q : (E × ℝ) × (E × ℝ) ↦
      u q.1 - v q.2 -
        (quadraticSize (q.1 - q.2) / (2 * ε) +
          α * (quadraticSize q.1 + quadraticSize q.2) +
          a / (T - q.1.2) + a / (T - q.2.2))
    ∃ z ∈ K, ∃ w ∈ K,
      (0 < z.2 ∧ 0 < w.2) ∧
      (quadraticSize (z - w) / (2 * ε) < M ∧
        α * quadraticSize z < M ∧ α * quadraticSize w < M) ∧
      IsMaxOn F (K ×ˢ K) (z, w) ∧ IsLocalMax F (z, w) := by
  intro K F
  have hK : IsCompact K := (isCompact_closedBall (0 : E × ℝ) R).of_isClosed_subset
    (((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)).inter Metric.isClosed_closedBall)
    inter_subset_right
  have hKslab {z : E × ℝ} (hz : z ∈ K) : z ∈ closedTimeSlab T := ⟨hz.1.1, hz.1.2.trans hST.le⟩
  have hden {z : E × ℝ} (hz : z ∈ K) : 0 < T - z.2 := sub_pos.mpr (hz.1.2.trans_lt hST)
  obtain ⟨z₀, hz₀K, hwitness⟩ := hwitness
  have hFcont : ContinuousOn F (K ×ˢ K) := by
    have := continuous_quadraticSize (E := E)
    refine ((hu.comp continuous_fst.continuousOn fun _ hq ↦ hKslab hq.1).sub
      (hv.comp continuous_snd.continuousOn fun _ hq ↦ hKslab hq.2)).sub ?_
    fun_prop (disch := intro q hq; first | exact (hden hq.1).ne' | exact (hden hq.2).ne')
  obtain ⟨⟨z, w⟩, ⟨hzK, hwK⟩, hmax⟩ := (hK.prod hK).exists_isMaxOn ⟨(z₀, z₀), hz₀K, hz₀K⟩ hFcont
  have hgap : η < F (z, w) :=
    (show η < F (z₀, z₀) by simpa [F, quadraticSize] using hwitness).trans_le (hmax ⟨hz₀K, hz₀K⟩)
  simp only [F] at hgap
  have hquad : 0 ≤ quadraticSize (z - w) / (2 * ε) :=
    div_nonneg (quadraticSize_nonneg _) (by positivity)
  have hzloc : 0 ≤ α * quadraticSize z := mul_nonneg hα.le (quadraticSize_nonneg _)
  have hwloc : 0 ≤ α * quadraticSize w := mul_nonneg hα.le (quadraticSize_nonneg _)
  have hzbar : 0 < a / (T - z.2) := div_pos ha (hden hzK)
  have hwbar : 0 < a / (T - w.2) := div_pos ha (hden hwK)
  have huv := hbound z (hKslab hzK) w (hKslab hwK)
  -- The initial-boundary estimate excludes contact at time zero.
  obtain ⟨hz0, hw0⟩ := not_or.mp fun h0 ↦ by
    have := hinitial z (hKslab hzK) w (hKslab hwK) h0
    have := div_le_div_of_nonneg_right (dist_sq_le_quadraticSize_sub z w)
      (show 0 ≤ 2 * ε by positivity)
    linarith
  -- The terminal and spatial penalties exceed `M`, so both points are interior.
  have hnhds {x : E × ℝ} (hx : x ∈ K) (hx0 : x.2 ≠ 0) (hxS : a / (T - x.2) < M)
      (hxR : α * quadraticSize x < M) : K ∈ 𝓝 x := by
    refine Filter.inter_mem (continuous_snd.continuousAt.preimage_mem_nhds (Icc_mem_nhds
      (hx.1.1.lt_of_ne' hx0) (hx.1.2.lt_of_ne fun h ↦ hterminal.not_gt (h ▸ hxS))))
        (Metric.closedBall_mem_nhds_of_mem (mem_ball_zero_iff.2 ?_))
    by_contra! h
    linarith [mul_le_mul_of_nonneg_left (norm_sq_le_quadraticSize x) hα.le,
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR h 2) hα.le]
  exact ⟨z, hzK, w, hwK, ⟨hzK.1.1.lt_of_ne' hz0, hwK.1.1.lt_of_ne' hw0⟩,
    ⟨by linarith, by linarith, by linarith⟩, hmax, hmax.isLocalMax (prod_mem_nhds
      (hnhds hzK hz0 (by linarith) (by linarith)) (hnhds hwK hw0 (by linarith) (by linarith)))⟩

-- Choose the spatial cutoff after the localization scale.
omit [ProperSpace E] in
private theorem exists_localization_radius {α M : ℝ} (hα : 0 < α) (z₀ : E × ℝ) :
    ∃ R : ℝ, ‖z₀‖ < R ∧ 1 ≤ R ∧ M < α * R ^ 2 := by
  obtain ⟨R, h₁, h₂⟩ : ∃ R, ‖z₀‖ + 1 ≤ R ∧ (M + 1) / α + 1 ≤ R :=
    ⟨_, le_max_left _ _, le_max_right _ _⟩
  have h₃ := (div_le_iff₀ hα).mp (le_sub_iff_add_le.mpr h₂)
  have h₁' : 1 ≤ R := by linarith [norm_nonneg z₀]
  refine ⟨R, by linarith, h₁', ?_⟩
  linarith [mul_le_mul_of_nonneg_left (le_self_pow₀ h₁' two_ne_zero) hα.le]

/-- A positive gap between bounded uniformly continuous candidates ordered at
initial time yields interior doubled maxima with arbitrarily small localization.

The time barrier and initial-boundary scale are fixed first. For each positive
localization tolerance `r`, one localization coefficient and one compact set
work for every smaller doubling scale. This order permits choosing the doubling
scale either before or after localization. The maxima retain the separation and
localization bounds, global maximality for diagonal comparisons, and a positive
lower bound for the time-barrier derivative. No differential equation is used. -/
theorem exists_localized_maximum_of_initial_le {u v : E × ℝ → ℝ} {T : ℝ}
    (hub : Bornology.IsBounded (u '' closedTimeSlab T))
    (hvb : Bornology.IsBounded (v '' closedTimeSlab T))
    (hu : UniformContinuousOn u (closedTimeSlab T)) (hv : UniformContinuousOn v (closedTimeSlab T))
    (hinit : ∀ x : E, u (x, 0) ≤ v (x, 0)) {z₀ : E × ℝ} (hz₀ : 0 ≤ z₀.2) (hz₀T : z₀.2 < T)
    (hgap : 0 < u z₀ - v z₀) :
    ∃ M > 0, ∃ a > 0, ∃ S < T, ∃ ε₀ > 0,
      ∀ r > 0, ∃ α > 0, α < r ^ 2 / (16 * (M + 1)) ∧ ∃ R : ℝ,
        let K := closedTimeSlab S ∩ Metric.closedBall (0 : E × ℝ) R
        ∀ ε ∈ Ioo 0 ε₀,
          let F := fun q : (E × ℝ) × (E × ℝ) ↦
            u q.1 - v q.2 -
              (quadraticSize (q.1 - q.2) / (2 * ε) +
                α * (quadraticSize q.1 + quadraticSize q.2) +
                a / (T - q.1.2) + a / (T - q.2.2))
          ∃ z ∈ K, ∃ w ∈ K,
            (0 < z.2 ∧ 0 < w.2) ∧
            (quadraticSize (z - w) / (2 * ε) < M ∧
              α * quadraticSize z < M ∧ α * quadraticSize w < M) ∧
            IsMaxOn F (K ×ˢ K) (z, w) ∧ IsLocalMax F (z, w) ∧
            a / T ^ 2 ≤ a / (T - z.2) ^ 2 := by
  set d := u z₀ - v z₀
  have hT : 0 < T := lt_of_le_of_lt hz₀ hz₀T
  have hgapTime : 0 < T - z₀.2 := sub_pos.mpr hz₀T
  have hz₀slab : z₀ ∈ closedTimeSlab T := ⟨hz₀, hz₀T.le⟩
  obtain ⟨Cu, hCu, hbu⟩ := hub.exists_pos_norm_le
  obtain ⟨Cv, hCv, hbv⟩ := hvb.exists_pos_norm_le
  set M := Cu + Cv + 1
  have hM : 0 < M := by positivity
  have huv_bound (z) (hz : z ∈ closedTimeSlab T) (w) (hw : w ∈ closedTimeSlab T) :
      u z - v w < M := by
    have h₁ := abs_le.mp (hbu _ (mem_image_of_mem u hz))
    have h₂ := abs_le.mp (hbv _ (mem_image_of_mem v hw))
    linarith
  have hdM : d < M := huv_bound z₀ hz₀slab z₀ hz₀slab
  set a := d * (T - z₀.2) / 16
  have ha : 0 < a := by positivity
  set S := T - a / (M + 1)
  have hb : 0 < a / (M + 1) := by positivity
  have hST : S < T := by linarith
  have hz₀S : z₀.2 < S := by
    have : a / (M + 1) < T - z₀.2 := by
      rw [div_lt_iff₀ (by positivity), show a = d * (T - z₀.2) / 16 from rfl]
      linarith [mul_pos (show 0 < M + 1 - d / 16 by linarith) hgapTime]
    linarith
  have hterminal : a / (T - S) = M + 1 := by
    have hMne : M + 1 ≠ 0 := by positivity
    simp only [S]
    cas using ha.ne'
  obtain ⟨ε₀, hε₀, hinitial⟩ := Metric.exists_sq_dist_penalty_le_of_mem
    (A := {z : (E × ℝ) | z.2 = 0}) hu hv hub hvb
    (fun z _ hz ↦ by simpa only [← show z.2 = 0 from hz] using hinit z.1)
    (show 0 < d / 4 by positivity)
  refine ⟨M, hM, a, ha, S, hST, ε₀, hε₀, fun r hr ↦ ?_⟩
  have hQ₀ := quadraticSize_nonneg z₀
  obtain ⟨α, hα, hαsmall⟩ := exists_between (show (0 : ℝ) < min (r ^ 2 / (16 * (M + 1)))
    (d / (16 * (quadraticSize z₀ + 1))) by positivity)
  have hαz := (lt_div_iff₀ (by positivity)).mp (hαsmall.trans_le (min_le_right _ _))
  obtain ⟨R, hR₀, hR_one, hRlarge⟩ := exists_localization_radius (M := M) hα z₀
  refine ⟨α, hα, hαsmall.trans_le (min_le_left _ _), R, fun ε hε ↦ ?_⟩
  have hz₀K : z₀ ∈ closedTimeSlab S ∩ Metric.closedBall 0 R :=
    ⟨⟨hz₀, hz₀S.le⟩, mem_closedBall_zero_iff.2 hR₀.le⟩
  have hatime : a / (T - z₀.2) = d / 16 := by
    simp only [a]
    cas using hgapTime.ne'
  obtain ⟨z, hzK, w, hwK, hpos, hbds, hmax, hlocal⟩ :=
    exists_isMaxOn_quadratic_barrier hε.1 hα ha hST (by linarith) (by positivity)
      (by rw [hterminal]; linarith) hRlarge hu.continuousOn hv.continuousOn huv_bound
      (hinitial ε hε) ⟨z₀, hz₀K, by rw [hatime]; linarith⟩
  have hden : 0 < T - z.2 := sub_pos.mpr (hzK.1.2.trans_lt hST)
  exact ⟨z, hzK, w, hwK, hpos, hbds, hmax, hlocal, div_le_div_of_nonneg_left ha.le
    (sq_pos_of_pos hden) ((sq_le_sq₀ hden.le hT.le).mpr (sub_le_self T hpos.1.le))⟩

end Maximum

end HamiltonJacobi
