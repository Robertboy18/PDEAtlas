/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Positivity.Finset

/-!
# Boundary estimates for quadratic doubling penalties

Suppose bounded, uniformly continuous functions `u` and `v` satisfy `u ≤ v`
on a subset `A` of their domain. If either of two points lies in `A`, then
`u(z) - v(w) - dist(z,w)² / (2ε)` is uniformly small for small positive `ε`.

There are two cases. For nearby points, uniform continuity transfers the
boundary inequality from one point to the other. For separated points,
the quadratic penalty exceeds the bounded difference of the functions.
For an initial-value problem, take `A` to be the time-zero face of a slab.
-/

@[expose] public section

namespace Metric

open Set

/-- A quadratic doubling penalty transfers an ordering on `A` to pairs
with at least one point in `A`, up to any prescribed positive error.

The estimate is uniform over the whole domain, which need not be compact.
Boundedness controls distant pairs and uniform continuity controls nearby
pairs. -/
theorem exists_sq_dist_penalty_le_of_mem
    {X : Type*} [PseudoMetricSpace X] {K A : Set X} {u v : X → ℝ}
    (hu : UniformContinuousOn u K) (hv : UniformContinuousOn v K)
    (hub : Bornology.IsBounded (u '' K)) (hvb : Bornology.IsBounded (v '' K))
    (horder : ∀ z ∈ K, z ∈ A → u z ≤ v z) {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ z ∈ K, ∀ w ∈ K,
      z ∈ A ∨ w ∈ A → u z - v w - dist z w ^ 2 / (2 * ε) ≤ η := by
  obtain ⟨Cu, hCu, hbu⟩ :=
    Bornology.IsBounded.exists_pos_norm_le (E := ℝ) (s := u '' K) hub
  obtain ⟨Cv, hCv, hbv⟩ :=
    Bornology.IsBounded.exists_pos_norm_le (E := ℝ) (s := v '' K) hvb
  obtain ⟨du, hdu, huclose⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨dv, hdv, hvclose⟩ := Metric.uniformContinuousOn_iff.mp hv η hη
  let d := min du dv
  have hd : 0 < d := lt_min hdu hdv
  refine ⟨d ^ 2 / (2 * (Cu + Cv + 1)), by positivity, ?_⟩
  intro ε hε z hz w hw hboundary
  have hεpos : 0 < ε := hε.1
  have hu_bound : |u z| ≤ Cu := by
    simpa only [Real.norm_eq_abs] using hbu (u z) (mem_image_of_mem u hz)
  have hv_bound : |v w| ≤ Cv := by
    simpa only [Real.norm_eq_abs] using hbv (v w) (mem_image_of_mem v hw)
  have hpenalty : 0 ≤ dist z w ^ 2 / (2 * ε) := by positivity
  by_cases hclose : dist z w < d
  · rcases hboundary with hzA | hwA
    · have hvsmall := hvclose z hz w hw (hclose.trans_le (min_le_right du dv))
      rw [Real.dist_eq] at hvsmall
      have hvdiff := (abs_lt.mp hvsmall).2
      have hzorder := horder z hz hzA
      linarith
    · have husmall := huclose z hz w hw (hclose.trans_le (min_le_left du dv))
      rw [Real.dist_eq] at husmall
      have hudiff := (abs_lt.mp husmall).2
      have hworder := horder w hw hwA
      linarith
  · have hfar : d ≤ dist z w := le_of_not_gt hclose
    have hsq : d ^ 2 ≤ dist z w ^ 2 :=
      (sq_le_sq₀ hd.le dist_nonneg).mpr hfar
    have hsmall := (lt_div_iff₀ (show 0 < 2 * (Cu + Cv + 1) by positivity)).mp hε.2
    have hlarge : Cu + Cv ≤ dist z w ^ 2 / (2 * ε) := by
      apply (le_div_iff₀ (show 0 < 2 * ε by positivity)).mpr
      nlinarith [hε.1]
    have huz := (abs_le.mp hu_bound).2
    have hvw := (abs_le.mp hv_bound).1
    linarith

/-- At a doubled maximum, a bounded separation penalty tends uniformly to zero
as its scale tends to zero. No regularity of the localization `L`, compactness
of `K`, or differential equation is needed.

Comparing with `(z,z)` and `(w,w)` cancels the localization exactly and bounds
twice the penalty by `u z - u w + v z - v w`. The domination of squared distance
and the fixed bound `M` make both differences small by uniform continuity. -/
theorem exists_penalty_lt_of_isMaxOn_sub
    {X : Type*} [PseudoMetricSpace X] {K : Set X} {u v : X → ℝ}
    (hu : UniformContinuousOn u K) (hv : UniformContinuousOn v K)
    {M η : ℝ} (hM : 0 < M) (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioo 0 ε₀, ∀ (Q : X → X → ℝ) (L : X → ℝ),
      (∀ x ∈ K, Q x x = 0) →
      ∀ z ∈ K, ∀ w ∈ K, dist z w ^ 2 ≤ Q z w →
        Q z w / (2 * ε) ≤ M →
        IsMaxOn (fun q : X × X ↦
          u q.1 - v q.2 - (Q q.1 q.2 / (2 * ε) + L q.1 + L q.2))
          (K ×ˢ K) (z, w) →
        Q z w / (2 * ε) < η := by
  obtain ⟨du, hdu, huclose⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨dv, hdv, hvclose⟩ := Metric.uniformContinuousOn_iff.mp hv η hη
  let δ := min du dv
  have hδ : 0 < δ := lt_min hdu hdv
  refine ⟨δ ^ 2 / (2 * M), by positivity, ?_⟩
  intro ε hε Q L hdiag z hz w hw hdist hbound hmax
  have hεpos : 0 < ε := hε.1
  have hden : 0 < 2 * ε := by positivity
  have hcost := (div_le_iff₀ hden).mp hbound
  have hscale := (lt_div_iff₀ (show 0 < 2 * M by positivity)).mp hε.2
  have hnear : dist z w < δ := by
    apply (sq_lt_sq₀ dist_nonneg hδ.le).mp
    nlinarith only [hdist, hcost, hscale]
  have hudiff := huclose z hz w hw (hnear.trans_le (min_le_left du dv))
  have hvdiff := hvclose z hz w hw (hnear.trans_le (min_le_right du dv))
  rw [Real.dist_eq] at hudiff hvdiff
  have hzdiag := hmax (show (z, z) ∈ K ×ˢ K from ⟨hz, hz⟩)
  have hwdiag := hmax (show (w, w) ∈ K ×ˢ K from ⟨hw, hw⟩)
  change u z - v z - (Q z z / (2 * ε) + L z + L z) ≤ _ at hzdiag
  change u w - v w - (Q w w / (2 * ε) + L w + L w) ≤ _ at hwdiag
  rw [hdiag z hz, zero_div] at hzdiag
  rw [hdiag w hw, zero_div] at hwdiag
  linarith only [hzdiag, hwdiag, (abs_lt.mp hudiff).2, (abs_lt.mp hvdiff).2]


end Metric
