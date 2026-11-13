/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearPrincipalValue
public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarQuadrantPrincipalValue

/-!
# Mixed truncations of the whole-plane principal value of `K₂`

For the unlocalized `u_y` and `v_x` (Chen and Hou, Part I, Lemma 3.5 and Appendix B.2) the two
points `x` and `z` lie on a vertical line, and the singular integrals of `K₂(x - y) W(y)` over the
plane are truncated near each point in a mixed way: on the side of the segment `[x, z]` the
vertical strip `|y₁ - x₁| < ε` is removed, on the far side the horizontal strip `|y₂ - x₂| < ε`.
By Lemma B.1 in the four quadrants at the point (`PlanarQuadrantPrincipalValue`), removing a
vertical strip from a quadrant adds `(π/8) W(x)` to its principal value and removing a horizontal
strip subtracts `(π/8) W(x)`; the mixed truncation removes two of each, so its limit is the disc
principal value with no local term (`tendsto_setIntegral_mixed`).

Over the plane the integrand is absolutely integrable away from the point when `W` decays like
`(1 + |y|)^{-ε₀}` (`integrableOn_shearKernel_mul_of_decay`).

## Main results

* `integrableOn_shearKernel_mul_of_decay`: integrability away from the pole.
* `tendsto_setIntegral_mixed`: the mixed truncations converge to the disc principal value.
* `tendsto_setIntegral_pairTruncation`: the difference at the two points, truncated on the
  segment by vertical strips and outside it by horizontal strips.
* `exists_tendsto_setIntegral_diff_ball`: the disc principal value over the plane exists.
* `tendsto_setIntegral_strip_of_decay`: removing the whole vertical strip adds `(π/2) W(x)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.5, p. 29, Appendix B.1,
  Lemma B.1, p. 130, and Appendix B.2, (B.47), (B.51) and (B.54), pp. 137-139.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric Module
open PDE.Analysis (planeEquiv planeEquiv_symm_apply measurePreserving_planeEquiv)
open scoped ENNReal NNReal Topology

namespace IncompressibleFlow.SharpHolder

variable {K : ℝ^2 → ℝ}

/-- A horizontal line `{y₂ = c}` is a null set. -/
theorem volume_setOf_one_eq (c : ℝ) : volume {y : ℝ^2 | y 1 = c} = 0 := by
  have hs : MeasurableSet {y : ℝ^2 | y 1 = c} :=
    measurableSet_eq_fun (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable measurable_const
  rw [← measurePreserving_planeEquiv.symm.measure_preimage hs.nullMeasurableSet]
  have : planeEquiv.symm ⁻¹' {y : ℝ^2 | y 1 = c} = univ ×ˢ {c} := by
    ext p
    simp [planeEquiv_symm_apply]
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

/-- **Integrability away from the pole.** If `|W(y)| ≤ C (1 + |y|)^{-ε₀}` with `ε₀ > 0`, then
`K₂(x - y) W(y)` is integrable on `|y - x| ≥ r` for every `r > 0`. -/
theorem integrableOn_shearKernel_mul_of_decay
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) (x : ℝ^2) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun y ↦ K (x - y) * W y) {y | r ≤ ‖y - x‖} := by
  have hC : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hdec 0)
    have hp : 0 < (1 + ‖(0 : ℝ^2)‖) ^ (-ε₀) := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  set A : ℝ := 1 + (1 + ‖x‖) / r with hA
  have hA0 : 0 < A := by positivity
  have hmaj : Integrable fun y : ℝ^2 ↦ A ^ 2 / 2 * C * (1 + ‖y‖) ^ (-(2 + ε₀)) :=
    (integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul _
  have hSm : MeasurableSet {y : ℝ^2 | r ≤ ‖y - x‖} :=
    measurableSet_le measurable_const (measurable_id.sub measurable_const).norm
  refine hmaj.integrableOn.mono' (((measurable_shearKernel hK).comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable.mul hWm).restrict ?_
  filter_upwards [ae_restrict_mem hSm] with y (hy : r ≤ ‖y - x‖)
  have hd : 0 < ‖y - x‖ := hr.trans_le hy
  have h1 : 1 + ‖y‖ ≤ A * ‖y - x‖ := by
    have : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
      calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    have h2 : 1 + ‖x‖ ≤ (1 + ‖x‖) / r * ‖y - x‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr]
      exact mul_le_mul_of_nonneg_left hy (by positivity)
    rw [hA]
    nlinarith
  have hy1 : 0 < 1 + ‖y‖ := by positivity
  have hK' : |K (x - y)| ≤ A ^ 2 / 2 * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    refine (abs_shearKernel_le hK _).trans ?_
    rw [norm_sub_rev, Real.rpow_neg hy1.le, Real.rpow_two, div_le_iff₀ (by positivity)]
    have : (1 + ‖y‖) ^ 2 ≤ (A * ‖y - x‖) ^ 2 := pow_le_pow_left₀ hy1.le h1 2
    field_simp
    nlinarith
  rw [Real.norm_eq_abs, abs_mul]
  calc |K (x - y)| * |W y| ≤ (A ^ 2 / 2 * (1 + ‖y‖) ^ (-(2 : ℝ))) * (C * (1 + ‖y‖) ^ (-ε₀)) :=
        mul_le_mul hK' (hdec y) (abs_nonneg _) (by positivity)
    _ = A ^ 2 / 2 * C * (1 + ‖y‖) ^ (-(2 + ε₀)) := by
        rw [neg_add, Real.rpow_add hy1]
        ring

/-- `K₂` is the planar Hessian kernel `hessianKernel 0 0`. -/
theorem shearKernel_eq_hessianKernel (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) :
    K = PotentialTheory.Planar.hessianKernel 0 0 :=
  funext fun y ↦ by rw [hK, PotentialTheory.Planar.hessianKernel_zero_zero]

/-- Translating the pole to the origin: `∫_S K₂(x - y) W(y) dy = ∫_{S - x} K₂(u) W(u + x) du`. -/
theorem setIntegral_shearKernel_translate (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    (S : Set (ℝ^2)) (W : ℝ^2 → ℝ) (x : ℝ^2) :
    ∫ y in S, K (x - y) * W y =
      ∫ u in (· + x) ⁻¹' S, PotentialTheory.Planar.hessianKernel 0 0 u * W (u + x) := by
  rw [← (measurePreserving_add_right volume x).setIntegral_preimage_emb
    (MeasurableEquiv.addRight x).measurableEmbedding]
  congr 1
  ext u
  rw [show x - (u + x) = -u by abel, shearKernel_neg hK, shearKernel_eq_hessianKernel hK]

open PotentialTheory.Planar in
/-- The square `[-L, L]²` is the union of the four corner rectangles at the origin, which overlap
only on the axes. -/
private theorem setIntegral_square_eq {L : ℝ} (hL : 0 < L) {T : Set (ℝ^2)} (hT : MeasurableSet T)
    {F : ℝ^2 → ℝ} (hF : IntegrableOn F (box L L L 0 ∩ T)) :
    ∫ u in box L L L 0 ∩ T, F u =
      ((∫ u in cornerRectangle L L ∩ T, F u) + ∫ u in cornerRectangle (-L) L ∩ T, F u) +
      ((∫ u in cornerRectangle L (-L) ∩ T, F u) + ∫ u in cornerRectangle (-L) (-L) ∩ T, F u) := by
  have hm : ∀ a b : ℝ, MeasurableSet (cornerRectangle a b ∩ T) := fun a b ↦
    (measurableSet_cornerRectangle a b).inter hT
  have hu₀ : uIcc (0 : ℝ) L = Icc 0 L := uIcc_of_le hL.le
  have hu₁ : uIcc (0 : ℝ) (-L) = Icc (-L) 0 := uIcc_of_ge (by linarith)
  have hmem : ∀ u : ℝ^2, u ∈ box L L L 0 ↔ -L ≤ u 0 ∧ u 0 ≤ L ∧ -L ≤ u 1 ∧ u 1 ≤ L := fun u ↦ by
    simp only [box, mem_ofPred_eq, PiLp.zero_apply, zero_sub, zero_add]
  have hset : box L L L 0 ∩ T = ((cornerRectangle L L ∩ T) ∪ (cornerRectangle (-L) L ∩ T)) ∪
      ((cornerRectangle L (-L) ∩ T) ∪ (cornerRectangle (-L) (-L) ∩ T)) := by
    ext u
    simp only [mem_union, mem_inter_iff, cornerRectangle, mem_ofPred_eq, hu₀, hu₁, mem_Icc, hmem]
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, hT⟩
      rcases le_total 0 (u 0) with h0 | h0 <;> rcases le_total 0 (u 1) with h1' | h1'
      · exact Or.inl (Or.inl ⟨⟨⟨h0, h2⟩, ⟨h1', h4⟩⟩, hT⟩)
      · exact Or.inr (Or.inl ⟨⟨⟨h0, h2⟩, ⟨h3, h1'⟩⟩, hT⟩)
      · exact Or.inl (Or.inr ⟨⟨⟨h1, h0⟩, ⟨h1', h4⟩⟩, hT⟩)
      · exact Or.inr (Or.inr ⟨⟨⟨h1, h0⟩, ⟨h3, h1'⟩⟩, hT⟩)
    · rintro ((⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hT⟩ | ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hT⟩) |
        (⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hT⟩ | ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hT⟩)) <;>
      exact ⟨⟨by linarith, by linarith, by linarith, by linarith⟩, hT⟩
  have hsub : ∀ a b : ℝ, |a| = L → |b| = L → cornerRectangle a b ∩ T ⊆ box L L L 0 ∩ T := by
    intro a b ha hb u hu
    refine ⟨?_, hu.2⟩
    obtain ⟨⟨h0, h1⟩, -⟩ := hu
    rw [hmem]
    have e₀ := mem_uIcc.1 h0
    have e₁ := mem_uIcc.1 h1
    rcases abs_eq hL.le |>.1 ha with rfl | rfl <;> rcases abs_eq hL.le |>.1 hb with rfl | rfl <;>
      · rcases e₀ with e₀ | e₀ <;> rcases e₁ with e₁ | e₁ <;>
          exact ⟨by linarith [e₀.1, e₀.2], by linarith [e₀.1, e₀.2], by linarith [e₁.1, e₁.2],
            by linarith [e₁.1, e₁.2]⟩
  have hi : ∀ a b : ℝ, |a| = L → |b| = L → IntegrableOn F (cornerRectangle a b ∩ T) :=
    fun a b ha hb ↦ hF.mono_set (hsub a b ha hb)
  have hL' : |L| = L := abs_of_pos hL
  have hL'' : |-L| = L := by rw [abs_neg, hL']
  have hnull₀ : volume {u : ℝ^2 | u 0 = 0} = 0 := volume_setOf_zero_eq 0
  have hnull₁ : volume {u : ℝ^2 | u 1 = 0} = 0 := volume_setOf_one_eq 0
  have hd₀ : ∀ b, AEDisjoint volume (cornerRectangle L b ∩ T) (cornerRectangle (-L) b ∩ T) :=
    fun b ↦ measure_mono_null (fun u hu ↦ by
      have h1 := hu.1.1.1
      have h2 := hu.2.1.1
      rw [hu₀] at h1
      rw [hu₁] at h2
      exact le_antisymm h2.2 h1.1) hnull₀
  have hd₁ : AEDisjoint volume ((cornerRectangle L L ∩ T) ∪ (cornerRectangle (-L) L ∩ T))
      ((cornerRectangle L (-L) ∩ T) ∪ (cornerRectangle (-L) (-L) ∩ T)) := by
    refine measure_mono_null (fun u hu ↦ ?_) hnull₁
    have hup : 0 ≤ u 1 := by
      rcases hu.1 with h | h
      · have := h.1.2; rw [hu₀] at this; exact this.1
      · have := h.1.2; rw [hu₀] at this; exact this.1
    have hdn : u 1 ≤ 0 := by
      rcases hu.2 with h | h
      · have := h.1.2; rw [hu₁] at this; exact this.2
      · have := h.1.2; rw [hu₁] at this; exact this.2
    exact le_antisymm hdn hup
  rw [hset, setIntegral_union₀ hd₁ ((hm _ _).union (hm _ _)).nullMeasurableSet
      ((hi _ _ hL' hL').union (hi _ _ hL'' hL')) ((hi _ _ hL' hL'').union (hi _ _ hL'' hL'')),
    setIntegral_union₀ (hd₀ L) (hm _ _).nullMeasurableSet (hi _ _ hL' hL') (hi _ _ hL'' hL'),
    setIntegral_union₀ (hd₀ (-L)) (hm _ _).nullMeasurableSet (hi _ _ hL' hL'') (hi _ _ hL'' hL'')]

open PotentialTheory.Planar in
/-- Lemma B.1 with either strip: removing `|u_k| < ε` from a corner rectangle adds
`(π/8) f(0)` for `k = 0` and subtracts it for `k = 1`. -/
private theorem tendsto_cornerRectangle_strip {a b M α : ℝ} {f : ℝ^2 → ℝ} (ha : a ≠ 0)
    (hb : b ≠ 0) (hf : AEStronglyMeasurable f (volume.restrict (cornerRectangle a b)))
    (hα : 0 < α) (hhol : ∀ y ∈ cornerRectangle a b, |f y - f 0| ≤ M * ‖y‖ ^ α) (k : Fin 2) :
    Tendsto (fun ε ↦ ∫ y in cornerRectangle a b ∩ {y | ε ≤ |y k|}, hessianKernel 0 0 y * f y)
      (𝓝[>] 0)
      (𝓝 ((∫ y in cornerRectangle a b, hessianKernel 0 0 y * (f y - f 0)) +
        (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0 +
          (if k = 0 then 1 else -1) * (Real.pi / 8) * f 0)) := by
  match k with
  | 0 =>
    have := tendsto_setIntegral_hessianKernel_cornerRectangle_strip_zero hf hα hhol
    simpa using this
  | 1 =>
    have := tendsto_setIntegral_hessianKernel_cornerRectangle_strip_one ha hb hf hα hhol
    rw [ite_eq_right_iff.2 (fun h ↦ absurd h (by decide : (1 : Fin 2) ≠ 0))]
    convert this using 2
    ring

/-- The mixed truncation at the origin: vertical strips on the side `σ u₂ ≥ 0`, a horizontal
strip on the other side. -/
private def mixedSet (σ ε : ℝ) : Set (ℝ^2) :=
  {u | 0 ≤ σ * u 1 ∧ ε ≤ |u 0|} ∪ {u | ε ≤ -(σ * u 1)}

/-- The mixed truncation at the origin is measurable. -/
private theorem measurableSet_mixedSet (σ ε : ℝ) : MeasurableSet (mixedSet σ ε) := by
  have h₀ : Measurable fun u : ℝ^2 ↦ u 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  exact ((measurableSet_le measurable_const (h₁.const_mul σ)).inter
    (measurableSet_le measurable_const (continuous_abs.measurable.comp h₀))).union
    (measurableSet_le measurable_const (h₁.const_mul σ).neg)

open PotentialTheory.Planar in
/-- On a corner rectangle at the origin the mixed truncation is, up to the axis `u₂ = 0`, the
vertical-strip truncation (`σ b > 0`) or the horizontal-strip truncation (`σ b < 0`). -/
private theorem cornerRectangle_inter_mixedSet {σ a b ε : ℝ} (hσ : σ = 1 ∨ σ = -1) (hb : b ≠ 0)
    (hε : 0 < ε) :
    cornerRectangle a b ∩ mixedSet σ ε =ᵐ[volume]
      cornerRectangle a b ∩ {u | ε ≤ |u (if 0 < σ * b then 0 else 1)|} := by
  have hnull : ∀ᵐ u : ℝ^2, u 1 ≠ 0 := measure_eq_zero_iff_ae_notMem.1 (volume_setOf_one_eq 0)
  refine Filter.eventuallyEqSet_iff.2 ?_
  filter_upwards [hnull] with u hu
  simp only [mem_inter_iff, cornerRectangle, mixedSet, mem_union, mem_ofPred_eq]
  refine and_congr_right fun ⟨_, h1⟩ ↦ ?_
  have hsgn : 0 < σ * b ↔ 0 < σ * u 1 := by
    rcases lt_or_gt_of_ne hb with hb' | hb'
    · have hu1 : u 1 < 0 := by
        rw [uIcc_of_ge hb'.le] at h1
        exact lt_of_le_of_ne h1.2 hu
      rcases hσ with rfl | rfl <;> constructor <;> intro h <;> nlinarith
    · have hu1 : 0 < u 1 := by
        rw [uIcc_of_le hb'.le] at h1
        exact lt_of_le_of_ne h1.1 (Ne.symm hu)
      rcases hσ with rfl | rfl <;> constructor <;> intro h <;> nlinarith
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  by_cases h : 0 < σ * b
  · rw [ite_eq_left_iff.2 (fun h' ↦ absurd h h')]
    have hp := hsgn.1 h
    constructor
    · rintro (⟨-, h⟩ | h)
      · exact h
      · linarith
    · exact fun h' ↦ Or.inl ⟨hp.le, h'⟩
  · rw [ite_eq_right_iff.2 (fun h' ↦ absurd h' h)]
    have hp : σ * u 1 < 0 := by
      rcases lt_or_gt_of_ne (mul_ne_zero (by rcases hσ with rfl | rfl <;> norm_num) hu :
        σ * u 1 ≠ 0) with h' | h'
      · exact h'
      · exact absurd (hsgn.2 h') h
    have habs : |u 1| = -(σ * u 1) := by
      rw [← abs_of_neg hp, abs_mul, hσ1, one_mul]
    rw [habs]
    constructor
    · rintro (⟨h', -⟩ | h')
      · linarith
      · exact h'
    · exact fun h' ↦ Or.inr h'

/-- The mixed truncation sets at `w` are measurable. -/
private theorem measurableSet_mixedTruncation (w : ℝ^2) (σ ε : ℝ) : MeasurableSet
    ({y : ℝ^2 | 0 ≤ σ * (y 1 - w 1) ∧ ε ≤ |y 0 - w 0|} ∪ {y | ε ≤ -(σ * (y 1 - w 1))}) := by
  have h₀ : Measurable fun u : ℝ^2 ↦ u 0 - w 0 :=
    (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable.sub_const _
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 - w 1 :=
    (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable.sub_const _
  exact ((measurableSet_le measurable_const (h₁.const_mul σ)).inter
    (measurableSet_le measurable_const (continuous_abs.measurable.comp h₀))).union
    (measurableSet_le measurable_const (h₁.const_mul σ).neg)

/-- Points of a mixed truncation at `w` lie at distance at least `ε` from `w`. -/
private theorem le_norm_sub_of_mem_mixedTruncation {w y : ℝ^2} {σ ε : ℝ} (hσ : |σ| = 1)
    (hy : y ∈ {y : ℝ^2 | 0 ≤ σ * (y 1 - w 1) ∧ ε ≤ |y 0 - w 0|} ∪
      {y | ε ≤ -(σ * (y 1 - w 1))}) : ε ≤ ‖y - w‖ := by
  rcases hy with ⟨-, h⟩ | h
  · exact h.trans (abs_sub_apply_le_norm w y 0)
  · refine h.trans ((neg_le_abs _).trans ?_)
    rw [abs_mul, hσ, one_mul]
    exact abs_sub_apply_le_norm w y 1

open PotentialTheory.Planar in
/-- **Mixed truncation at a point.** Let `W` be measurable, Hölder at `x` on the square
`Q = box L L L x`, with `K₂(x - ·) W` integrable outside `Q`, and let the disc truncations of
`∫ K₂(x - y) W(y) dy` over the plane converge to `v`. Then the mixed truncations removing the
vertical strip `|y₁ - x₁| < ε` on the side `σ (y₂ - x₂) ≥ 0` and the horizontal strip
`|y₂ - x₂| < ε` on the other side (`σ = ± 1`) converge to the same `v`: the four quadrant
corrections `± (π/8) W(x)` of Lemma B.1 cancel. -/
theorem tendsto_setIntegral_mixed (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4))
    {W : ℝ^2 → ℝ} (hWm : AEStronglyMeasurable W) {x : ℝ^2} {L : ℝ} (hL : 0 < L) {M α : ℝ}
    (hα : 0 < α) (hhol : ∀ y ∈ box L L L x, |W y - W x| ≤ M * ‖y - x‖ ^ α)
    (hfar : IntegrableOn (fun y ↦ K (x - y) * W y) (box L L L x)ᶜ) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) {v : ℝ}
    (hv : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (fun ε ↦ ∫ y in {y | 0 ≤ σ * (y 1 - x 1) ∧ ε ≤ |y 0 - x 0|} ∪
        {y | ε ≤ -(σ * (y 1 - x 1))}, K (x - y) * W y) (𝓝[>] 0) (𝓝 v) := by
  set Q := box L L L x with hQ
  set F : ℝ^2 → ℝ := fun y ↦ K (x - y) * W y with hF
  set f : ℝ^2 → ℝ := fun u ↦ W (u + x) with hf
  set S : ℝ → Set (ℝ^2) := fun ε ↦ {y | 0 ≤ σ * (y 1 - x 1) ∧ ε ≤ |y 0 - x 0|} ∪
    {y | ε ≤ -(σ * (y 1 - x 1))} with hS
  have hQm : MeasurableSet Q := measurableSet_box x
  have hQb : Bornology.IsBounded Q := isBounded_box x
  obtain ⟨Mw, hWb⟩ := exists_bound_of_holder hQb hα hhol
  have hKm : Measurable fun y ↦ K (x - y) :=
    (measurable_shearKernel hK).comp (measurable_const.sub measurable_id)
  have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hpre : ∀ ε, (· + x) ⁻¹' S ε = mixedSet σ ε := fun ε ↦ by
    ext u
    simp only [hS, mixedSet, mem_preimage, mem_union, mem_ofPred_eq, PiLp.add_apply,
      add_sub_cancel_right]
  have hSm : ∀ ε, MeasurableSet (S ε) := measurableSet_mixedTruncation x σ
  -- points of the truncation are at distance at least `ε`
  have hSd : ∀ ε, ∀ y ∈ S ε, ε ≤ ‖x - y‖ := fun ε y hy ↦
    (le_norm_sub_of_mem_mixedTruncation hσ1 hy).trans_eq (norm_sub_rev _ _)
  have hKW : ∀ ε, 0 < ε → ∀ T ⊆ Q, MeasurableSet T → (∀ y ∈ T, ε ≤ ‖x - y‖) →
      IntegrableOn F T := by
    intro ε hε T hTQ hTm hTε
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2) * Mw)
      ((measure_mono hTQ).trans_lt hQb.measure_lt_top).ne
      (hKm.aestronglyMeasurable.mul hWm) ?_
    filter_upwards [ae_restrict_mem hTm] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ((abs_shearKernel_le hK _).trans ?_) (hWb y (hTQ hy)) (abs_nonneg _)
      (by positivity)
    have := hTε y hy
    gcongr
  -- the far part
  have hnull : ∀ᵐ y : ℝ^2, y 0 ≠ x 0 ∧ y 1 ≠ x 1 :=
    (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))).and
      (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_one_eq (x 1)))
  have hfarS : Tendsto (fun ε ↦ ∫ y in S ε \ Q, F y) (𝓝[>] 0) (𝓝 (∫ y in Qᶜ, F y)) := by
    have h : ∀ ε, ∫ y in S ε \ Q, F y = ∫ y in Qᶜ, (S ε).indicator F y := fun ε ↦ by
      rw [setIntegral_indicator (hSm ε), inter_comm, Set.sdiff_eq]
    simp_rw [h]
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖F y‖)
      (Eventually.of_forall fun ε ↦ hfar.aestronglyMeasurable.indicator (hSm ε))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self _ y)
      hfar.norm ?_
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    obtain ⟨h₀, h₁⟩ := hy
    refine tendsto_const_nhds.congr' ?_
    have hd₀ := abs_pos.2 (sub_ne_zero.2 h₀)
    have hd₁ : 0 < |σ * (y 1 - x 1)| := by
      rw [abs_mul, hσ1, one_mul]
      exact abs_pos.2 (sub_ne_zero.2 h₁)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (lt_min hd₀ hd₁))] with ε hε
    have hy : y ∈ S ε := by
      rcases le_or_gt 0 (σ * (y 1 - x 1)) with h | h
      exacts [Or.inl ⟨h, hε.trans (min_le_left _ _)⟩,
        Or.inr ((hε.trans (min_le_right _ _)).trans_eq (abs_of_neg h))]
    rw [indicator_of_mem hy]
  -- coordinates at `x`
  have hbox0 : ∀ u : ℝ^2, u + x ∈ Q ↔ u ∈ box L L L 0 := fun u ↦ by
    simp only [hQ, box, mem_ofPred_eq, PiLp.add_apply, PiLp.zero_apply, zero_sub, zero_add]
    constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> exact ⟨by linarith, by linarith, by linarith,
      by linarith⟩
  have hfm : AEStronglyMeasurable f volume :=
    hWm.comp_measurePreserving (measurePreserving_add_right volume x)
  have hCRbox : ∀ a b : ℝ, |a| = L → |b| = L → cornerRectangle a b ⊆ box L L L 0 := by
    have habs : ∀ t c : ℝ, t ∈ uIcc 0 c → |t| ≤ |c| := fun t c h ↦ by
      rcases mem_uIcc.1 h with h | h
      · rw [abs_of_nonneg h.1, abs_of_nonneg (h.1.trans h.2)]; exact h.2
      · rw [abs_of_nonpos h.2, abs_of_nonpos (h.1.trans h.2)]; linarith [h.1]
    intro a b ha hb u ⟨h0, h1⟩
    have e₀ := abs_le.1 ((habs _ _ h0).trans ha.le)
    have e₁ := abs_le.1 ((habs _ _ h1).trans hb.le)
    simp only [box, mem_ofPred_eq, PiLp.zero_apply, zero_sub, zero_add]
    exact ⟨e₀.1, e₀.2, e₁.1, e₁.2⟩
  have hfhol : ∀ a b : ℝ, |a| = L → |b| = L →
      ∀ u ∈ cornerRectangle a b, |f u - f 0| ≤ M * ‖u‖ ^ α := by
    intro a b ha hb u hu
    have h := hhol (u + x) ((hbox0 u).2 (hCRbox a b ha hb hu))
    simpa [hf, add_sub_cancel_right] using h
  have hfb : ∀ u ∈ box L L L 0, |f u| ≤ Mw := fun u hu ↦ hWb (u + x) ((hbox0 u).2 hu)
  have hKf : ∀ ε, 0 < ε → ∀ T : Set (ℝ^2), MeasurableSet T → (∀ u ∈ T, ε ≤ ‖u‖) →
      IntegrableOn (fun u ↦ hessianKernel 0 0 u * f u) (box L L L 0 ∩ T) := by
    intro ε hε T hTm hTε
    have hbm : MeasurableSet (box L L L 0) := measurableSet_box 0
    refine Measure.integrableOn_of_bounded (M := 1 / (2 * ε ^ 2) * Mw)
      ((measure_mono inter_subset_left).trans_lt (isBounded_box (a := L) (b₁ := L) (b₂ := L)
        (0 : ℝ^2)).measure_lt_top).ne
      ((measurable_hessianKernel 0 0).aestronglyMeasurable.mul hfm) ?_
    filter_upwards [ae_restrict_mem (hbm.inter hTm)] with u hu
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ((abs_hessianKernel_le 0 0 u).trans ?_) (hfb u hu.1) (abs_nonneg _)
      (by positivity)
    have := hTε u hu.2
    gcongr
  have hL' : |L| = L := abs_of_pos hL
  have hL'' : |-L| = L := by rw [abs_neg, hL']
  have hLne : L ≠ 0 := hL.ne'
  have hLne' : -L ≠ 0 := neg_ne_zero.2 hL.ne'
  set Lq : ℝ → ℝ → ℝ := fun a b ↦
    (∫ u in cornerRectangle a b, hessianKernel 0 0 u * (f u - f 0)) +
      (Real.arctan (|a| / |b|) / 2 - Real.pi / 8) * f 0 with hLq
  set Λ := (Lq L L + Lq (-L) L) + (Lq L (-L) + Lq (-L) (-L)) with hΛ
  -- the near part of the mixed truncation
  have hnear : Tendsto (fun ε ↦ ∫ y in S ε ∩ Q, F y) (𝓝[>] 0) (𝓝 Λ) := by
    set k : ℝ → Fin 2 := fun b ↦ if 0 < σ * b then 0 else 1 with hk
    have hlim : ∀ a b : ℝ, |a| = L → |b| = L → Tendsto (fun ε ↦ ∫ u in cornerRectangle a b ∩
        {u | ε ≤ |u (k b)|}, hessianKernel 0 0 u * f u) (𝓝[>] 0)
        (𝓝 (Lq a b + (if k b = 0 then 1 else -1) * (Real.pi / 8) * f 0)) := fun a b ha hb ↦
      tendsto_cornerRectangle_strip (by rw [← abs_ne_zero, ha]; exact hLne)
        (by rw [← abs_ne_zero, hb]; exact hLne) hfm.restrict hα (hfhol a b ha hb) (k b)
    have hsum := ((hlim L L hL' hL').add (hlim (-L) L hL'' hL')).add
      ((hlim L (-L) hL' hL'').add (hlim (-L) (-L) hL'' hL''))
    have hsign : ((if k L = 0 then (1 : ℝ) else -1) + (if k L = 0 then 1 else -1)) +
        ((if k (-L) = 0 then 1 else -1) + (if k (-L) = 0 then 1 else -1)) = 0 := by
      rcases hσ with rfl | rfl <;> norm_num [hk, hL, not_lt.2 hL.le]
    have hval : (Lq L L + (if k L = 0 then 1 else -1) * (Real.pi / 8) * f 0 +
        (Lq (-L) L + (if k L = 0 then 1 else -1) * (Real.pi / 8) * f 0)) +
        ((Lq L (-L) + (if k (-L) = 0 then 1 else -1) * (Real.pi / 8) * f 0) +
          (Lq (-L) (-L) + (if k (-L) = 0 then 1 else -1) * (Real.pi / 8) * f 0)) = Λ := by
      rw [hΛ]
      linear_combination (Real.pi / 8 * f 0) * hsign
    rw [hval] at hsum
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hT : (· + x) ⁻¹' (S ε ∩ Q) = box L L L 0 ∩ mixedSet σ ε := by
      rw [preimage_inter, hpre, inter_comm, show (· + x) ⁻¹' Q = box L L L 0 from Set.ext hbox0]
    rw [hF, setIntegral_shearKernel_translate hK, hT,
      setIntegral_square_eq hL (measurableSet_mixedSet σ ε) (hKf ε hε _
        (measurableSet_mixedSet σ ε) fun u hu ↦ by
          have hu' : u ∈ (· + x) ⁻¹' S ε := by rw [hpre]; exact hu
          have := hSd ε (u + x) hu'
          rwa [show x - (u + x) = -u by abel, norm_neg] at this)]
    rw [setIntegral_congr_set (cornerRectangle_inter_mixedSet hσ hLne hε),
      setIntegral_congr_set (cornerRectangle_inter_mixedSet (a := -L) hσ hLne hε),
      setIntegral_congr_set (cornerRectangle_inter_mixedSet (a := L) hσ hLne' hε),
      setIntegral_congr_set (cornerRectangle_inter_mixedSet (a := -L) hσ hLne' hε)]
  -- the near part of the disc truncation
  have hdisc : Tendsto (fun ε ↦ ∫ y in (univ \ ball x ε) ∩ Q, F y) (𝓝[>] 0) (𝓝 Λ) := by
    have hlim : ∀ a b : ℝ, |a| = L → |b| = L → Tendsto (fun ε ↦ ∫ u in cornerRectangle a b ∩
        {u | ε < ‖0 - u‖}, hessianKernel 0 0 u * f u) (𝓝[>] 0) (𝓝 (Lq a b)) := by
      intro a b ha hb
      have h := (hasPrincipalValueAt_hessianKernel_cornerRectangle
        (by rw [← abs_ne_zero, ha]; exact hLne) (by rw [← abs_ne_zero, hb]; exact hLne)
        hfm.restrict hα (hfhol a b ha hb)).2
      refine h.congr' (Eventually.of_forall fun ε ↦ ?_)
      simp only [PDE.Analysis.principalValueTruncation, zero_sub, hessianKernel_neg]
    have hsum := ((hlim L L hL' hL').add (hlim (-L) L hL'' hL')).add
      ((hlim L (-L) hL' hL'').add (hlim (-L) (-L) hL'' hL''))
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hT : (· + x) ⁻¹' ((univ \ ball x ε) ∩ Q) = box L L L 0 ∩ {u | ε ≤ ‖u‖} := by
      ext u
      simp only [mem_preimage, mem_inter_iff, Set.mem_sdiff, mem_univ, true_and, mem_ball,
        dist_eq_norm, add_sub_cancel_right, not_lt, mem_ofPred_eq, hbox0 u]
      exact and_comm
    have hsm : MeasurableSet {u : ℝ^2 | ε ≤ ‖u‖} :=
      measurableSet_le measurable_const measurable_norm
    have hae : ∀ a b : ℝ, cornerRectangle a b ∩ {u : ℝ^2 | ε ≤ ‖u‖} =ᵐ[volume]
        cornerRectangle a b ∩ {u | ε < ‖0 - u‖} := fun a b ↦ by
      have hsph : ∀ᵐ u : ℝ^2, ‖u‖ ≠ ε := by
        have h0 : volume (sphere (0 : ℝ^2) ε) = 0 := Measure.addHaar_sphere volume 0 ε
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with u hu
        simpa [mem_sphere, dist_eq_norm] using hu
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [hsph] with u hu
      simp only [mem_inter_iff, mem_ofPred_eq, zero_sub, norm_neg]
      exact and_congr_right fun _ ↦ ⟨fun h ↦ lt_of_le_of_ne h (Ne.symm hu), le_of_lt⟩
    rw [hF, setIntegral_shearKernel_translate hK, hT,
      setIntegral_square_eq hL hsm (hKf ε hε _ hsm fun u hu ↦ hu),
      setIntegral_congr_set (hae _ _), setIntegral_congr_set (hae _ _),
      setIntegral_congr_set (hae _ _), setIntegral_congr_set (hae _ _)]
  -- integrability on the truncations
  have hint : ∀ ε, 0 < ε → ∀ T : Set (ℝ^2), MeasurableSet T → (∀ y ∈ T, ε ≤ ‖x - y‖) →
      IntegrableOn F T := by
    intro ε hε T hTm hTε
    refine ((hKW ε hε (T ∩ Q) inter_subset_right (hTm.inter hQm) fun y hy ↦ hTε y hy.1).union
      hfar).mono_set fun y hy ↦ (em (y ∈ Q)).imp (fun h ↦ ⟨hy, h⟩) id
  have hballm : ∀ ε, MeasurableSet (univ \ ball x ε) := fun ε ↦
    MeasurableSet.univ.diff measurableSet_ball
  have hballd : ∀ ε, ∀ y ∈ univ \ ball x ε, ε ≤ ‖x - y‖ := fun ε y hy ↦ by
    simpa only [mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy.2
  have hballQ : ∀ ε, ε ≤ L → (univ \ ball x ε) \ Q = Qᶜ := by
    intro ε hεL
    ext y
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_compl_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun hb ↦ h ?_, h⟩⟩
    rw [mem_ball, dist_eq_norm] at hb
    have h0 := (abs_sub_apply_le_norm x y 0).trans_lt hb
    have h1 := (abs_sub_apply_le_norm x y 1).trans_lt hb
    rw [abs_lt] at h0 h1
    simp only [hQ, box, mem_ofPred_eq]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hv' : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, F y) (𝓝[>] 0)
      (𝓝 (Λ + ∫ y in Qᶜ, F y)) := by
    refine (hdisc.add tendsto_const_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds hL)] with ε (hε : 0 < ε) hεL
    rw [← integral_inter_add_sdiff hQm (hint ε hε _ (hballm ε) (hballd ε)), hballQ ε hεL]
  have hvΛ : v = Λ + ∫ y in Qᶜ, F y := tendsto_nhds_unique hv hv'
  rw [hvΛ]
  refine (hnear.add hfarS).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact integral_inter_add_sdiff hQm (hint ε hε _ (hSm ε) (hSd ε))

/-- Two families of truncation sets that agree outside a fixed set `R` on which `F` is
integrable, and agree eventually at almost every point, have asymptotically equal integrals. -/
theorem tendsto_setIntegral_sub_setIntegral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {F : X → ℝ} {A B : ℝ → Set X} {R : Set X} (hR : MeasurableSet R) (hFR : IntegrableOn F R μ)
    (hA : ∀ ε, MeasurableSet (A ε)) (hB : ∀ ε, MeasurableSet (B ε))
    (hAi : ∀ᶠ ε in 𝓝[>] 0, IntegrableOn F (A ε) μ) (hBi : ∀ᶠ ε in 𝓝[>] 0, IntegrableOn F (B ε) μ)
    (hAB : ∀ᶠ ε in 𝓝[>] 0, A ε \ R = B ε \ R)
    (hae : ∀ᵐ y ∂μ, ∀ᶠ ε in 𝓝[>] 0, (y ∈ A ε ↔ y ∈ B ε)) :
    Tendsto (fun ε ↦ (∫ y in A ε, F y ∂μ) - ∫ y in B ε, F y ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun ε ↦ ∫ y in R, ((A ε).indicator F y - (B ε).indicator F y) ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[>] (0 : ℝ))
      (μ := μ.restrict R) (f := fun _ ↦ (0 : ℝ))
      (F := fun ε y ↦ (A ε).indicator F y - (B ε).indicator F y) (fun y ↦ 2 * ‖F y‖)
      (Eventually.of_forall fun ε ↦ (hFR.aestronglyMeasurable.indicator (hA ε)).sub
        (hFR.aestronglyMeasurable.indicator (hB ε)))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ by
        refine (norm_sub_le _ _).trans ?_
        have h1 := norm_indicator_le_norm_self F (s := A ε) y
        have h2 := norm_indicator_le_norm_self F (s := B ε) y
        linarith)
      (hFR.norm.const_mul 2) (ae_restrict_of_ae (by
        filter_upwards [hae] with y hy
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hy] with ε hε
        by_cases h : y ∈ A ε
        · rw [indicator_of_mem h, indicator_of_mem (hε.1 h), sub_self]
        · rw [indicator_of_notMem h, indicator_of_notMem (fun h' ↦ h (hε.2 h')), sub_self]))
    rwa [integral_zero] at h
  refine hlim.congr' ?_
  filter_upwards [hAi, hBi, hAB] with ε hAε hBε hABε
  rw [← integral_inter_add_sdiff hR hAε, ← integral_inter_add_sdiff hR hBε, hABε,
    integral_sub (hFR.indicator (hA ε)) (hFR.indicator (hB ε)), setIntegral_indicator (hA ε),
    setIntegral_indicator (hB ε), inter_comm R, inter_comm R]
  ring

/-- The truncation of the difference at two points `x`, `z` of a vertical line, `x₂ < z₂`: the
vertical strip `|y₁ - x₁| < ε` is removed between the two heights, and the horizontal strips
`x₂ - ε < y₂ < x₂` and `z₂ < y₂ < z₂ + ε` beyond them. -/
def pairTruncation (x z : ℝ^2) (ε : ℝ) : Set (ℝ^2) :=
  {y | x 1 ≤ y 1 ∧ y 1 ≤ z 1 ∧ ε ≤ |y 0 - x 0|} ∪ {y | y 1 ≤ x 1 - ε} ∪ {y | z 1 + ε ≤ y 1}

/-- The truncation at two points of a vertical line is measurable. -/
theorem measurableSet_pairTruncation (x z : ℝ^2) (ε : ℝ) :
    MeasurableSet (pairTruncation x z ε) := by
  have h₀ : Measurable fun u : ℝ^2 ↦ u 0 := (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have h₁ : Measurable fun u : ℝ^2 ↦ u 1 := (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable
  exact (((measurableSet_le measurable_const h₁).inter ((measurableSet_le h₁ measurable_const).inter
    (measurableSet_le measurable_const (continuous_abs.measurable.comp
      (h₀.sub_const _))))).union (measurableSet_le h₁ measurable_const)).union
    (measurableSet_le measurable_const h₁)

/-- The truncation `pairTruncation x z ε` stays at distance at least `ε` from `x`. -/
theorem pairTruncation_subset_left {x z : ℝ^2} (hle : x 1 ≤ z 1) (ε : ℝ) :
    pairTruncation x z ε ⊆ {y | ε ≤ ‖y - x‖} := by
  intro y hy
  simp only [pairTruncation, mem_union, mem_ofPred_eq] at hy ⊢
  have := abs_sub_apply_le_norm x y 1
  rcases hy with (⟨-, -, h⟩ | h) | h
  · exact h.trans (abs_sub_apply_le_norm x y 0)
  · linarith [neg_le_abs (y 1 - x 1)]
  · linarith [le_abs_self (y 1 - x 1)]

/-- The truncation `pairTruncation x z ε` stays at distance at least `ε` from `z`. -/
theorem pairTruncation_subset_right {x z : ℝ^2} (hxz : x 0 = z 0) (hle : x 1 ≤ z 1) (ε : ℝ) :
    pairTruncation x z ε ⊆ {y | ε ≤ ‖y - z‖} := by
  intro y hy
  simp only [pairTruncation, mem_union, mem_ofPred_eq] at hy ⊢
  have := abs_sub_apply_le_norm z y 1
  rcases hy with (⟨-, -, h⟩ | h) | h
  · rw [hxz] at h
    exact h.trans (abs_sub_apply_le_norm z y 0)
  · linarith [neg_le_abs (y 1 - z 1)]
  · linarith [le_abs_self (y 1 - z 1)]

/-- Points outside a square `box L L L x` are at distance at least `L` from `x`. -/
theorem compl_box_subset (L : ℝ) (x : ℝ^2) : (box L L L x)ᶜ ⊆ {y | L ≤ ‖y - x‖} := by
  intro y hy
  simp only [mem_compl_iff, box, mem_ofPred_eq, not_and_or, not_le] at hy
  simp only [mem_ofPred_eq]
  have h0 := abs_sub_apply_le_norm x y 0
  have h1 := abs_sub_apply_le_norm x y 1
  rcases hy with h | h | h | h
  · linarith [neg_abs_le (y 0 - x 0)]
  · linarith [le_abs_self (y 0 - x 0)]
  · linarith [neg_abs_le (y 1 - x 1)]
  · linarith [le_abs_self (y 1 - x 1)]

/-- **The difference at two points of a vertical line.** Let `x₁ = z₁`, `x₂ < z₂`, let `W` be
measurable with `|W(y)| ≤ C (1 + |y|)^{-ε₀}`, Hölder at `x` and at `z` on squares of side `2L`,
and let the disc truncations of `∫ K₂(x - y) W(y) dy` and `∫ K₂(z - y) W(y) dy` over the plane
converge to `v_x` and `v_z`. Then the truncations `pairTruncation x z ε` of
`∫ (K₂(x - y) - K₂(z - y)) W(y) dy` converge to `v_x - v_z`. -/
theorem tendsto_setIntegral_pairTruncation
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {x z : ℝ^2} (hxz : x 0 = z 0) (hlt : x 1 < z 1)
    {L M α : ℝ} (hL : 0 < L) (hα : 0 < α)
    (hholx : ∀ y ∈ box L L L x, |W y - W x| ≤ M * ‖y - x‖ ^ α)
    (hholz : ∀ y ∈ box L L L z, |W y - W z| ≤ M * ‖y - z‖ ^ α) {vx vz : ℝ}
    (hvx : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 vx))
    (hvz : Tendsto (fun ε ↦ ∫ y in univ \ ball z ε, K (z - y) * W y) (𝓝[>] 0) (𝓝 vz)) :
    Tendsto (fun ε ↦ ∫ y in pairTruncation x z ε, (K (x - y) - K (z - y)) * W y) (𝓝[>] 0)
      (𝓝 (vx - vz)) := by
  set δ := z 1 - x 1 with hδ
  have hδ0 : 0 < δ := by linarith
  have hdist : ∀ (w : ℝ^2) (r : ℝ), MeasurableSet {y : ℝ^2 | r ≤ ‖y - w‖} := fun w r ↦
    measurableSet_le measurable_const (measurable_id.sub measurable_const).norm
  have hdecI : ∀ (w : ℝ^2) {r : ℝ}, 0 < r →
      IntegrableOn (fun y ↦ K (w - y) * W y) {y | r ≤ ‖y - w‖} := fun w r hr ↦
    integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec w hr
  have hMx := tendsto_setIntegral_mixed hK hWm hL hα hholx
    ((hdecI x hL).mono_set (compl_box_subset L x)) (Or.inl rfl) hvx
  have hMz := tendsto_setIntegral_mixed hK hWm hL hα hholz
    ((hdecI z hL).mono_set (compl_box_subset L z)) (Or.inr rfl) hvz
  have hA := measurableSet_pairTruncation x z
  have hAx : ∀ ε, 0 < ε → ∀ y ∈ pairTruncation x z ε, ε ≤ ‖y - x‖ := fun ε hε y hy ↦
    pairTruncation_subset_left hlt.le ε hy
  have hAz : ∀ ε, 0 < ε → ∀ y ∈ pairTruncation x z ε, ε ≤ ‖y - z‖ := fun ε hε y hy ↦
    pairTruncation_subset_right hxz hlt.le ε hy
  have hnull : ∀ᵐ y : ℝ^2, y 0 ≠ x 0 ∧ y 1 ≠ x 1 ∧ y 1 ≠ z 1 :=
    (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))).and
      ((measure_eq_zero_iff_ae_notMem.1 (volume_setOf_one_eq (x 1))).and
        (measure_eq_zero_iff_ae_notMem.1 (volume_setOf_one_eq (z 1))))
  -- the comparison at `x`
  have hcx : Tendsto (fun ε ↦ ∫ y in pairTruncation x z ε, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 vx) := by
    have h := tendsto_setIntegral_sub_setIntegral (F := fun y ↦ K (x - y) * W y)
      (A := pairTruncation x z) (B := fun ε ↦ {y : ℝ^2 | 0 ≤ 1 * (y 1 - x 1) ∧
        ε ≤ |y 0 - x 0|} ∪ {y | ε ≤ -(1 * (y 1 - x 1))}) (hdist x δ) (hdecI x hδ0) hA
      (measurableSet_mixedTruncation x 1)
      (eventually_mem_nhdsWithin.mono fun ε hε ↦ (hdecI x hε).mono_set (hAx ε hε))
      (eventually_mem_nhdsWithin.mono fun ε hε ↦ (hdecI x hε).mono_set fun y hy ↦
        le_norm_sub_of_mem_mixedTruncation (by norm_num) hy)
      (by
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        ext y
        simp only [Set.mem_sdiff, mem_ofPred_eq, not_le, pairTruncation, mem_union, one_mul]
        refine and_congr_left fun hy ↦ ?_
        have h1 : y 1 - x 1 < δ := (le_abs_self _).trans_lt
          ((abs_sub_apply_le_norm x y 1).trans_lt hy)
        constructor
        · rintro ((⟨h₁, -, h₂⟩ | h) | h)
          · exact Or.inl ⟨by linarith, h₂⟩
          · exact Or.inr (by linarith)
          · linarith
        · rintro (⟨h₁, h₂⟩ | h)
          · exact Or.inl (Or.inl ⟨by linarith, by linarith, h₂⟩)
          · exact Or.inl (Or.inr (by linarith)))
      (by
        filter_upwards [hnull] with y hy
        obtain ⟨h₀, -, h₂⟩ := hy
        have hd₀ := abs_pos.2 (sub_ne_zero.2 h₀)
        rcases lt_or_gt_of_ne h₂ with h | h
        · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
          simp only [pairTruncation, mem_union, mem_ofPred_eq, one_mul]
          constructor
          · rintro ((⟨h₁, -, h₃⟩ | h') | h')
            · exact Or.inl ⟨by linarith, h₃⟩
            · exact Or.inr (by linarith)
            · linarith
          · rintro (⟨h₁, h₃⟩ | h')
            · exact Or.inl (Or.inl ⟨by linarith, h.le, h₃⟩)
            · exact Or.inl (Or.inr (by linarith))
        · have hp : 0 < y 1 - z 1 := by linarith
          filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
            (eventually_le_nhds (lt_min hp hd₀))] with ε (hε : 0 < ε) hεm
          have e₁ := hεm.trans (min_le_left _ _)
          have e₂ := hεm.trans (min_le_right _ _)
          simp only [pairTruncation, mem_union, mem_ofPred_eq, one_mul]
          exact ⟨fun _ ↦ Or.inl ⟨by linarith, e₂⟩, fun _ ↦ Or.inr (by linarith)⟩)
    simpa using h.add hMx
  -- the comparison at `z`
  have hcz : Tendsto (fun ε ↦ ∫ y in pairTruncation x z ε, K (z - y) * W y) (𝓝[>] 0)
      (𝓝 vz) := by
    have h := tendsto_setIntegral_sub_setIntegral (F := fun y ↦ K (z - y) * W y)
      (A := pairTruncation x z) (B := fun ε ↦ {y : ℝ^2 | 0 ≤ -1 * (y 1 - z 1) ∧
        ε ≤ |y 0 - z 0|} ∪ {y | ε ≤ -(-1 * (y 1 - z 1))}) (hdist z δ) (hdecI z hδ0) hA
      (measurableSet_mixedTruncation z (-1))
      (eventually_mem_nhdsWithin.mono fun ε hε ↦ (hdecI z hε).mono_set (hAz ε hε))
      (eventually_mem_nhdsWithin.mono fun ε hε ↦ (hdecI z hε).mono_set fun y hy ↦
        le_norm_sub_of_mem_mixedTruncation (by norm_num) hy)
      (by
        filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        ext y
        simp only [Set.mem_sdiff, mem_ofPred_eq, not_le, pairTruncation, mem_union,
          neg_mul, one_mul, neg_neg, hxz]
        refine and_congr_left fun hy ↦ ?_
        have h1 : z 1 - y 1 < δ := by
          have := (abs_sub_apply_le_norm z y 1).trans_lt hy
          linarith [neg_le_abs (y 1 - z 1)]
        constructor
        · rintro ((⟨-, h₁, h₂⟩ | h) | h)
          · exact Or.inl ⟨by linarith, h₂⟩
          · linarith
          · exact Or.inr (by linarith)
        · rintro (⟨h₁, h₂⟩ | h)
          · exact Or.inl (Or.inl ⟨by linarith, by linarith, h₂⟩)
          · exact Or.inr (by linarith))
      (by
        filter_upwards [hnull] with y hy
        obtain ⟨h₀, h₁, -⟩ := hy
        have hd₀ := abs_pos.2 (sub_ne_zero.2 h₀)
        rw [hxz] at hd₀
        rcases lt_or_gt_of_ne h₁ with h | h
        · have hp : 0 < x 1 - y 1 := by linarith
          filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
            (eventually_le_nhds (lt_min hp hd₀))] with ε (hε : 0 < ε) hεm
          have e₁ := hεm.trans (min_le_left _ _)
          have e₂ := hεm.trans (min_le_right _ _)
          simp only [pairTruncation, mem_union, mem_ofPred_eq, neg_mul, one_mul, neg_neg]
          exact ⟨fun _ ↦ Or.inl ⟨by linarith, e₂⟩, fun _ ↦ Or.inl (Or.inr (by linarith))⟩
        · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
          simp only [pairTruncation, mem_union, mem_ofPred_eq, neg_mul, one_mul, neg_neg, hxz]
          constructor
          · rintro ((⟨-, h₂, h₃⟩ | h') | h')
            · exact Or.inl ⟨by linarith, h₃⟩
            · linarith
            · exact Or.inr (by linarith)
          · rintro (⟨h₂, h₃⟩ | h')
            · exact Or.inl (Or.inl ⟨h.le, by linarith, h₃⟩)
            · exact Or.inr (by linarith))
    simpa using h.add hMz
  refine (hcx.sub hcz).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [← integral_sub ((hdecI x hε).mono_set (hAx ε hε)) ((hdecI z hε).mono_set (hAz ε hε))]
  congr 1
  ext y
  ring

/-- **Existence of the disc principal value over the plane** of `∫ K₂(x - y) W(y) dy` for `W`
measurable, Hölder at `x` on a square around `x`, with `|W(y)| ≤ C (1 + |y|)^{-ε₀}`: the box
principal value of `exists_tendsto_setIntegral_box_diff_ball` plus the absolutely convergent
integral outside the box. -/
theorem exists_tendsto_setIntegral_diff_ball
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {x : ℝ^2} {L M α : ℝ} (hL : 0 < L)
    (hα : 0 < α) (hhol : ∀ y ∈ box L L L x, |W y - W x| ≤ M * ‖y - x‖ ^ α) :
    ∃ v, Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 v) := by
  obtain ⟨v₀, hv₀⟩ := exists_tendsto_setIntegral_box_diff_ball hK hL hL hL hWm hα hhol
  set Q := box L L L x with hQ
  have hQm : MeasurableSet Q := measurableSet_box x
  have hfar : IntegrableOn (fun y ↦ K (x - y) * W y) Qᶜ :=
    (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hL).mono_set (compl_box_subset L x)
  refine ⟨v₀ + ∫ y in Qᶜ, K (x - y) * W y, (hv₀.add tendsto_const_nhds).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_le_nhds hL)] with ε (hε : 0 < ε) hεL
  have hball : (univ \ ball x ε) \ Q = Qᶜ := by
    ext y
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_compl_iff]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun hb ↦ ?_, h⟩⟩
    have := compl_box_subset L x h
    rw [mem_ball, dist_eq_norm] at hb
    simp only [mem_ofPred_eq] at this
    linarith
  have hint : IntegrableOn (fun y ↦ K (x - y) * W y) (univ \ ball x ε) :=
    (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set fun y hy ↦ by
      have := hy.2
      rw [mem_ball, not_lt, dist_eq_norm] at this
      exact this
  have e : Q ∩ (univ \ ball x ε) = Q \ ball x ε := by
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff, mem_univ, true_and]
  rw [← integral_inter_add_sdiff hQm hint, hball, inter_comm, e]

/-- **Strip truncations over the plane.** Under the hypotheses of `tendsto_setIntegral_mixed`
(with the decay of `W` giving the integrability outside the square), removing the whole vertical
strip `|y₁ - x₁| < ε` gives the disc principal value plus `(π/2) W(x)` (Lemma B.1 in the four
quadrants, each adding `(π/8) W(x)`). -/
theorem tendsto_setIntegral_strip_of_decay
    (hK : ∀ y, K y = (y 0 ^ 2 - y 1 ^ 2) / (2 * ‖y‖ ^ 4)) {W : ℝ^2 → ℝ}
    (hWm : AEStronglyMeasurable W) {C ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hdec : ∀ y, |W y| ≤ C * (1 + ‖y‖) ^ (-ε₀)) {x : ℝ^2} {L M α : ℝ} (hL : 0 < L)
    (hα : 0 < α) (hhol : ∀ y ∈ box L L L x, |W y - W x| ≤ M * ‖y - x‖ ^ α) {v : ℝ}
    (hv : Tendsto (fun ε ↦ ∫ y in univ \ ball x ε, K (x - y) * W y) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (fun ε ↦ ∫ y in {y | ε ≤ |y 0 - x 0|}, K (x - y) * W y) (𝓝[>] 0)
      (𝓝 (v + Real.pi / 2 * W x)) := by
  set Q := box L L L x with hQ
  set F : ℝ^2 → ℝ := fun y ↦ K (x - y) * W y with hF
  have hQm : MeasurableSet Q := measurableSet_box x
  have hfar : IntegrableOn F Qᶜ :=
    (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hL).mono_set (compl_box_subset L x)
  have hSm : ∀ ε : ℝ, MeasurableSet {y : ℝ^2 | ε ≤ |y 0 - x 0|} := fun ε ↦
    measurableSet_le measurable_const (by fun_prop)
  have hSd : ∀ ε : ℝ, {y : ℝ^2 | ε ≤ |y 0 - x 0|} ⊆ {y | ε ≤ ‖y - x‖} := fun ε y hy ↦
    (show ε ≤ |y 0 - x 0| from hy).trans (abs_sub_apply_le_norm x y 0)
  -- the box principal value
  have hbox : Tendsto (fun ε ↦ ∫ y in Q \ ball x ε, F y) (𝓝[>] 0)
      (𝓝 (v - ∫ y in Qᶜ, F y)) := by
    refine (hv.sub tendsto_const_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds hL)] with ε (hε : 0 < ε) hεL
    have hint : IntegrableOn F (univ \ ball x ε) :=
      (integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set fun y hy ↦
        show ε ≤ ‖y - x‖ by simpa only [mem_ball, not_lt, dist_eq_norm] using hy.2
    have hball : (univ \ ball x ε) \ Q = Qᶜ := by
      ext y
      simp only [Set.mem_sdiff, mem_univ, true_and, mem_compl_iff]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨fun hb ↦ ?_, h⟩⟩
      have := compl_box_subset L x h
      rw [mem_ball, dist_eq_norm] at hb
      simp only [mem_ofPred_eq] at this
      linarith
    rw [← integral_inter_add_sdiff hQm hint, hball, inter_comm, ← inter_sdiff_assoc, inter_univ]
    ring
  have hstrip := tendsto_setIntegral_box_inter_strip hK hL hL hL hWm hα hhol hbox
  -- the strip outside the box
  have hnull : ∀ᵐ y : ℝ^2, y 0 ≠ x 0 := measure_eq_zero_iff_ae_notMem.1 (volume_setOf_zero_eq (x 0))
  have hout : Tendsto (fun ε ↦ ∫ y in {y | ε ≤ |y 0 - x 0|} \ Q, F y) (𝓝[>] 0)
      (𝓝 (∫ y in Qᶜ, F y)) := by
    have h : ∀ ε, ∫ y in {y | ε ≤ |y 0 - x 0|} \ Q, F y =
        ∫ y in Qᶜ, {y : ℝ^2 | ε ≤ |y 0 - x 0|}.indicator F y := fun ε ↦ by
      rw [setIntegral_indicator (hSm ε), inter_comm, Set.sdiff_eq]
    simp_rw [h]
    refine tendsto_integral_filter_of_dominated_convergence (fun y ↦ ‖F y‖)
      (Eventually.of_forall fun ε ↦ hfar.aestronglyMeasurable.indicator (hSm ε))
      (Eventually.of_forall fun ε ↦ ae_of_all _ fun y ↦ norm_indicator_le_norm_self _ y)
      hfar.norm ?_
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_le_nhds (abs_pos.2 (sub_ne_zero.2 hy)))] with ε hε
    rw [indicator_of_mem (show y ∈ {y : ℝ^2 | ε ≤ |y 0 - x 0|} from hε)]
  have heq : v + Real.pi / 2 * W x = (v - ∫ y in Qᶜ, F y) + Real.pi / 2 * W x +
      ∫ y in Qᶜ, F y := by ring
  rw [heq]
  refine (hstrip.add hout).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [inter_comm]
  exact integral_inter_add_sdiff hQm
    ((integrableOn_shearKernel_mul_of_decay hK hWm hε₀ hdec x hε).mono_set (hSd ε))

end IncompressibleFlow.SharpHolder
