/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearHolderTails

/-!
# Envelopes of the lower cost of the horizontal estimate of `v_x`

Bounds of the lower cost `S_low(B, A) = 4 ∫_0^9 ∫_0^{c(p)} |Δ_B(p, t)| t^{1/2} dt dp`, the second
part of the constant `S_{in,y}` of Chen and Hou, Part I, (B.39), by the cost at `B = 10` and by
integrals of the unlocalized kernel.

## Main definitions

* `shearEdgeCost`: the cost bound `E(B)` of the edge columns `B - 1 < p ≤ min(B + 1, 9)`.

## Main results

* `lintegral_shearDensity_mul_sqrt_le`: `∫_0^m K₂(a, t) t^{1/2} dt ≤ a^{-1/2}/7` for `0 < a` and
  `m ≤ a`.
* `shearLowerCost_le_add`: the edge columns cost at most `E(B)`, so
  `S_low(B, A) ≤ S_low(10, A) + E(B)` for `B ≥ 4`.
* `shearEdgeCost_nonneg`, `shearEdgeCost_anti`: `E` is nonnegative and decreasing on `[4, ∞)`.
* `shearLowerCost_le_region`, `shearLowerCost_le_region_top`: for `0 < l ≤ A ≤ u`, the cutoff of
  the column `p` is at most `min(u, T(p, l), s_c(p))`.
* `shearLowerCost_le_bottom`: `S_low(10, A) ≤ 6π √A`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.1, (B.39), p. 136.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-! ### The edge cost -/

/-- The cost bound `E(B)` of the edge columns `B - 1 < p ≤ min(B + 1, 9)` of the lower cost. -/
def shearEdgeCost (B : ℝ) : ℝ :=
  if B < 10 then 8 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2)) else 0

/-- `E(B) ≥ 0`. -/
theorem shearEdgeCost_nonneg (B : ℝ) : 0 ≤ shearEdgeCost B := by
  rw [shearEdgeCost]
  split_ifs with h
  · have : Real.sqrt (B - 2) ≤ Real.sqrt (min B 8) :=
      Real.sqrt_le_sqrt (le_min (by linarith) (by linarith))
    linarith
  · exact le_rfl

/-- `√y - √(y - 2) ≤ √x - √(x - 2)` for `2 ≤ x ≤ y`. -/
theorem sqrt_sub_sqrt_sub_two_le {x y : ℝ} (hx : 2 ≤ x) (h : x ≤ y) :
    Real.sqrt y - Real.sqrt (y - 2) ≤ Real.sqrt x - Real.sqrt (x - 2) := by
  have h₁ := Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)
  have h₂ := Real.sq_sqrt (show (0 : ℝ) ≤ x - 2 by linarith)
  have h₃ := Real.sq_sqrt (show (0 : ℝ) ≤ y by linarith)
  have h₄ := Real.sq_sqrt (show (0 : ℝ) ≤ y - 2 by linarith)
  have hx' : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt h
  have hy' : Real.sqrt (x - 2) ≤ Real.sqrt (y - 2) := Real.sqrt_le_sqrt (by linarith)
  have hx0 : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hy0 := Real.sqrt_nonneg (x - 2)
  have hd : Real.sqrt (x - 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hx' hy') (sub_nonneg.2 hd)]

/-- `E` decreases on `[4, ∞)`. -/
theorem shearEdgeCost_anti {B B' : ℝ} (hB : 4 ≤ B) (h : B ≤ B') :
    shearEdgeCost B' ≤ shearEdgeCost B := by
  rcases le_or_gt 10 B' with h' | h'
  · rw [shearEdgeCost, ite_eq_right (not_lt.2 h')]
    exact shearEdgeCost_nonneg B
  rw [shearEdgeCost, shearEdgeCost, ite_eq_left h', ite_eq_left (h.trans_lt h')]
  gcongr 8 / 7 * ?_
  rcases le_or_gt B 8 with h₁ | h₁
  · rw [min_eq_left h₁]
    rcases le_or_gt B' 8 with h₂ | h₂
    · rw [min_eq_left h₂]
      exact sqrt_sub_sqrt_sub_two_le (by linarith) h
    · rw [min_eq_right h₂.le]
      have e := sqrt_sub_sqrt_sub_two_le (by linarith) h₁
      have : Real.sqrt (8 - 2) ≤ Real.sqrt (B' - 2) := Real.sqrt_le_sqrt (by linarith)
      linarith
  · rw [min_eq_right h₁.le, min_eq_right (h₁.le.trans h)]
    have : Real.sqrt (B - 2) ≤ Real.sqrt (B' - 2) := Real.sqrt_le_sqrt (by linarith)
    linarith

/-! ### One kernel against `t^{1/2}` -/

/-- `∫_0^m K₂(a, t) t^{1/2} dt ≤ a^{-1/2}/7` for `0 < a` and `m ≤ a`: on `(0, a]` the kernel is
nonnegative and `K₂(a, t) t^{1/2}` is below the derivative of
`F(t) = t^{3/2}/(2(a² + t²)) - (2a² t^{3/2} - (2/7) t^{7/2})/(16a⁴)`, with `F(a) = a^{-1/2}/7`. -/
theorem lintegral_shearDensity_mul_sqrt_le {a m : ℝ} (ha : 0 < a) (hm : m ≤ a) :
    ∫⁻ t in Ioc 0 m, ‖shearDensity a t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (1 / (7 * Real.sqrt a)) := by
  have hK : ∀ t ∈ Ioc 0 a, 0 ≤ shearDensity a t := fun t ht ↦ by
    rw [shearDensity_eq]
    exact div_nonneg (by nlinarith [ht.1, ht.2]) (by positivity)
  have hpt : ∀ t ∈ Ioc 0 a, ‖shearDensity a t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal (shearDensity a t * Real.sqrt t +
        Real.sqrt t * (a ^ 2 - t ^ 2) ^ 2 / (16 * a ^ 4 * (a ^ 2 + t ^ 2))) := fun t ht ↦ by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hK t ht), ← Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_mul (hK t ht)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ Real.sqrt t * (a ^ 2 - t ^ 2) ^ 2 / (16 * a ^ 4 * (a ^ 2 + t ^ 2)) := by
      have := ht.1
      positivity
    linarith
  calc ∫⁻ t in Ioc 0 m, ‖shearDensity a t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ))
      ≤ ∫⁻ t in Ioc 0 a, ‖shearDensity a t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) :=
        lintegral_mono_set (Ioc_subset_Ioc_right hm)
    _ ≤ ∫⁻ t in Ioc 0 a, ENNReal.ofReal (shearDensity a t * Real.sqrt t +
        Real.sqrt t * (a ^ 2 - t ^ 2) ^ 2 / (16 * a ^ 4 * (a ^ 2 + t ^ 2))) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal (1 / (7 * Real.sqrt a)) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ t * Real.sqrt t / (2 * (a ^ 2 + t ^ 2)) -
          (2 * a ^ 2 * (t * Real.sqrt t) - 2 / 7 * (t ^ 3 * Real.sqrt t)) / (16 * a ^ 4))
          ha.le (by fun_prop (disch := intros; positivity)) (fun t ht ↦ ?_) (fun t ht ↦ ?_)]
        · congr 1
          obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ a = s ^ 2 :=
            ⟨Real.sqrt a, Real.sqrt_pos.2 ha, (Real.sq_sqrt ha.le).symm⟩
          rw [Real.sqrt_sq hs0.le, Real.sqrt_zero]
          field_simp
          ring
        · have ht0 : 0 < t := ht.1
          have hs := Real.hasDerivAt_sqrt ht0.ne'
          have h₁ := (hasDerivAt_id' t).fun_mul hs
          have h₂ := ((hasDerivAt_pow 2 t).const_add (a ^ 2)).const_mul 2
          have h₃ := (hasDerivAt_pow 3 t).fun_mul hs
          refine ((h₁.fun_div h₂ (by positivity)).sub (((h₁.const_mul (2 * a ^ 2)).sub
            (h₃.const_mul (2 / 7))).div_const (16 * a ^ 4))).congr_deriv ?_
          obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
            ⟨Real.sqrt t, Real.sqrt_pos.2 ht0, (Real.sq_sqrt ht0.le).symm⟩
          rw [Real.sqrt_sq hs0.le, shearDensity_eq]
          field_simp
          ring
        · have := ht.1
          have := hK t ht
          positivity

/-! ### The columns of the lower cost -/

/-- `s_c(±1) = 0`. -/
theorem shearThreshold_eq_zero_of_sq_eq_one {p : ℝ} (h : p ^ 2 = 1) : shearThreshold p = 0 := by
  have h4 : p ^ 4 = 1 := by rw [show p ^ 4 = (p ^ 2) ^ 2 by ring, h, one_pow]
  simp only [shearThreshold, h, h4]
  norm_num

/-- Inside the boxes the low cost reads the kernel, threshold and map of the whole plane. -/
theorem shearLowCost_of_le {B A p : ℝ} (hp : |p| + 1 ≤ B) :
    shearLowCost B A p = ∫⁻ t in Ioc 0 (if shearThreshold p < A then shearMap p A else A),
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
  simp only [shearLowCost, localShearThreshold, localShearMap, hp, ite_true,
    localShearDifference_of_le hp]

/-- Near the edge of the boxes, the column `B - 1 < p ≤ B + 1` costs at most `(p - 1)^{-1/2}/7`. -/
theorem shearLowCost_le_of_lt {B A p : ℝ} (hB : 2 ≤ B) (hA : 0 < A) (hp₁ : B < p + 1)
    (hp₂ : p ≤ B + 1) : shearLowCost B A p ≤ ENNReal.ofReal (1 / (7 * Real.sqrt (p - 1))) := by
  have hp : 0 < p := by linarith
  have he : 0 < p - 1 := by linarith
  have hc : (if p - 1 < A then (p - 1) ^ 2 / A else A) ≤ p - 1 := by
    split_ifs with h
    · rw [div_le_iff₀ hA]
      nlinarith
    · exact not_lt.1 h
  simp only [shearLowCost, localShearThreshold, localShearMap, abs_of_pos hp, not_le.2 hp₁,
    ite_false, localShearDifference_of_lt (by linarith : (1 : ℝ) ≤ B) hp₁ hp₂, enorm_neg]
  exact lintegral_shearDensity_mul_sqrt_le he hc

/-- Beyond the boxes, the column `p > B + 1` costs nothing. -/
theorem shearLowCost_eq_zero_of_gt {B A p : ℝ} (hp : B + 1 < p) : shearLowCost B A p = 0 := by
  simp only [shearLowCost, localShearDifference_of_gt hp, enorm_zero, zero_mul, lintegral_zero]

/-- **The lower cost against the boxes of half-width `10`**:
`S_low(B, A) ≤ S_low(10, A) + E(B)` for `B ≥ 4`. -/
theorem shearLowerCost_le_add {B A : ℝ} (hB : 4 ≤ B) (hA : 0 < A) :
    shearLowerCost B A ≤ shearLowerCost 10 A + ENNReal.ofReal (shearEdgeCost B) := by
  have heq : ∀ p ∈ Ioc (0 : ℝ) 9, p + 1 ≤ B → shearLowCost B A p = shearLowCost 10 A p := by
    intro p hp hpB
    have h₁ : |p| + 1 ≤ B := by rwa [abs_of_pos hp.1]
    have h₂ : |p| + 1 ≤ 10 := by
      rw [abs_of_pos hp.1]
      linarith [hp.2]
    rw [shearLowCost_of_le h₁, shearLowCost_of_le h₂]
  rcases le_or_gt 10 B with hB' | hB'
  · rw [shearEdgeCost, ite_eq_right (not_lt.2 hB'), ENNReal.ofReal_zero, add_zero,
      shearLowerCost, shearLowerCost]
    refine le_of_eq ?_
    congr 1
    exact setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦ heq p hp (by linarith [hp.2])
  set m := min (B + 1) 9 with hm
  have hm₁ : B - 1 ≤ m := le_min (by linarith) (by linarith)
  have hm₂ : m ≤ 9 := min_le_right _ _
  -- the edge columns
  have hedge : ∫⁻ p in Ioc (B - 1) 9, shearLowCost B A p ≤
      ENNReal.ofReal (2 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2))) := by
    rw [← Ioc_union_Ioc_eq_Ioc hm₁ hm₂]
    refine (lintegral_union_le _ _ _).trans ?_
    have hzero : ∫⁻ p in Ioc m 9, shearLowCost B A p = 0 := by
      refine (setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦
        shearLowCost_eq_zero_of_gt ?_).trans lintegral_zero
      rcases min_lt_iff.1 hp.1 with h | h
      · exact h
      · exact absurd hp.2 (not_le.2 h)
    rw [hzero, add_zero]
    calc ∫⁻ p in Ioc (B - 1) m, shearLowCost B A p
        ≤ ∫⁻ p in Ioc (B - 1) m, ENNReal.ofReal (1 / (7 * Real.sqrt (p - 1))) :=
          setLIntegral_mono' measurableSet_Ioc fun p hp ↦ shearLowCost_le_of_lt (by linarith)
            hA (by linarith [hp.1]) (hp.2.trans (min_le_left _ _))
      _ = ENNReal.ofReal (2 / 7 * Real.sqrt (m - 1) - 2 / 7 * Real.sqrt (B - 1 - 1)) := by
          refine lintegral_Ioc_ofReal_deriv (g := fun p ↦ 2 / 7 * Real.sqrt (p - 1)) hm₁
            (by fun_prop) (fun p hp ↦ ?_) (fun p _ ↦ by positivity)
          have hp1 : 0 < p - 1 := by linarith [hp.1]
          refine ((((hasDerivAt_id' p).sub_const 1).sqrt hp1.ne').const_mul (2 / 7)).congr_deriv ?_
          have hs := Real.sqrt_pos.2 hp1
          field_simp
      _ = ENNReal.ofReal (2 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2))) := by
          rw [hm, ← min_sub_sub_right, add_sub_cancel_right, show B - 1 - 1 = B - 2 by ring,
            show (9 : ℝ) - 1 = 8 by norm_num]
          congr 1
          ring
  -- the inner columns
  have hlow : ∫⁻ p in Ioc 0 (B - 1), shearLowCost B A p ≤
      ∫⁻ p in Ioc 0 9, shearLowCost 10 A p := by
    calc ∫⁻ p in Ioc 0 (B - 1), shearLowCost B A p
        = ∫⁻ p in Ioc 0 (B - 1), shearLowCost 10 A p :=
          setLIntegral_congr_fun measurableSet_Ioc fun p hp ↦
            heq p ⟨hp.1, by linarith [hp.2]⟩ (by linarith [hp.2])
      _ ≤ _ := lintegral_mono_set (Ioc_subset_Ioc_right (by linarith))
  have hsub : Ioc (0 : ℝ) 9 ⊆ Ioc 0 (B - 1) ∪ Ioc (B - 1) 9 :=
    (Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm.le
  rw [shearLowerCost, shearLowerCost, shearEdgeCost, ite_eq_left hB']
  calc 4 * ∫⁻ p in Ioc 0 9, shearLowCost B A p
      ≤ 4 * ((∫⁻ p in Ioc 0 9, shearLowCost 10 A p) +
          ENNReal.ofReal (2 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2)))) := by
        gcongr 4 * ?_
        exact (lintegral_mono_set hsub).trans ((lintegral_union_le _ _ _).trans
          (add_le_add hlow hedge))
    _ = _ := by
        rw [mul_add, show 8 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2)) =
          4 * (2 / 7 * (Real.sqrt (min B 8) - Real.sqrt (B - 2))) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]

/-! ### The region of the lower cost -/

/-- The cutoff of the column `p > 0` at a height `A ≥ l > 0` lies below `A`, `T(p, l)` and
`s_c(p)`. -/
theorem ite_shearThreshold_lt_le_min {p l A : ℝ} (hp : 0 < p) (hl : 0 < l) (hlA : l ≤ A) :
    (if shearThreshold p < A then shearMap p A else A) ≤
      min A (min (shearMap p l) (shearThreshold p)) := by
  have hA : 0 < A := hl.trans_le hlA
  split_ifs with h
  · have hT : shearMap p A ≤ shearThreshold p := by
      by_cases hp1 : p ^ 2 = 1
      · rw [shearMap_eq_zero_of_sq_eq_one hp1]
        exact Real.sqrt_nonneg _
      · exact (shearMap_lt_shearThreshold hp hp1 h).le
    exact le_min (hT.trans h.le) (le_min (antitoneOn_shearMap_right p hl hA hlA) hT)
  · have h' : A ≤ shearThreshold p := not_lt.1 h
    have hp1 : p ^ 2 ≠ 1 := fun hp1 ↦ by
      rw [shearThreshold_eq_zero_of_sq_eq_one hp1] at h'
      linarith
    refine le_min le_rfl (le_min ?_ h')
    calc A ≤ shearThreshold p := h'
      _ = shearMap p (shearThreshold p) := (shearMap_shearThreshold hp1).symm
      _ ≤ shearMap p l := antitoneOn_shearMap_right p hl (shearThreshold_pos hp1) (hlA.trans h')

/-- **The region of the lower cost**: for `0 < l ≤ A ≤ u`, the column `p` of `S_low(10, A)` is
cut at `min(u, T(p, l), s_c(p))`. -/
theorem shearLowerCost_le_region {l u A : ℝ} (hl : 0 < l) (hlA : l ≤ A) (hAu : A ≤ u) :
    shearLowerCost 10 A ≤ 4 * ∫⁻ p in Ioc 0 9, ∫⁻ t in Ioc 0
      (min u (min (shearMap p l) (shearThreshold p))),
        ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
  rw [shearLowerCost]
  gcongr 4 * ?_
  refine setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ?_
  have h₁ : |p| + 1 ≤ 10 := by
    rw [abs_of_pos hp.1]
    linarith [hp.2]
  have hc : (if shearThreshold p < A then shearMap p A else A) ≤
      min u (min (shearMap p l) (shearThreshold p)) :=
    (ite_shearThreshold_lt_le_min hp.1 hl hlA).trans (min_le_min hAu le_rfl)
  rw [shearLowCost_of_le h₁]
  exact lintegral_mono_set (Ioc_subset_Ioc_right hc)

/-- The region of the lower cost without the cap `u`. -/
theorem shearLowerCost_le_region_top {l A : ℝ} (hl : 0 < l) (hlA : l ≤ A) :
    shearLowerCost 10 A ≤ 4 * ∫⁻ p in Ioc 0 9, ∫⁻ t in Ioc 0
      (min (shearMap p l) (shearThreshold p)),
        ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
  refine (shearLowerCost_le_region hl hlA le_rfl).trans ?_
  gcongr 4 * ?_
  exact lintegral_mono fun p ↦ lintegral_mono_set (Ioc_subset_Ioc_right (min_le_right _ _))

/-- **The lower cost near the axis**: `S_low(10, A) ≤ 6π √A`. -/
theorem shearLowerCost_le_bottom {A : ℝ} (hA : 0 < A) :
    shearLowerCost 10 A ≤ ENNReal.ofReal (6 * Real.pi * Real.sqrt A) := by
  have hF : Measurable fun q : ℝ × ℝ ↦
      ‖shearDifference q.1 q.2‖ₑ * ENNReal.ofReal (q.2 ^ (1 / 2 : ℝ)) :=
    measurable_shearDifference.enorm.mul (measurable_snd.pow_const _).ennreal_ofReal
  have hpt : ∀ t ∈ Ioc (0 : ℝ) A, ∫⁻ p in Ioc (0 : ℝ) 9,
      ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) ≤
        ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← Real.sqrt_eq_rpow]
    calc (∫⁻ p in Ioc (0 : ℝ) 9, ‖shearDifference p t‖ₑ) * ENNReal.ofReal (Real.sqrt t)
        ≤ ENNReal.ofReal (3 * Real.pi / (4 * t)) * ENNReal.ofReal (Real.sqrt t) := by
          gcongr
          calc ∫⁻ p in Ioc (0 : ℝ) 9, ‖shearDifference p t‖ₑ
              ≤ ∫⁻ p in Ioi (0 : ℝ), ‖shearDifference p t‖ₑ :=
                lintegral_mono_set Ioc_subset_Ioi_self
            _ = ∫⁻ p in Ioi (0 : ℝ), ENNReal.ofReal |shearDifference p t| :=
                setLIntegral_congr_fun measurableSet_Ioi fun p _ ↦ by
                  rw [← ofReal_norm, Real.norm_eq_abs]
            _ ≤ _ := lintegral_Ioi_zero_abs_shearDifference_le ht0
      _ = ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ t = s ^ 2 :=
            ⟨Real.sqrt t, Real.sqrt_pos.2 ht0, (Real.sq_sqrt ht0.le).symm⟩
          rw [Real.sqrt_sq hs0.le]
          field_simp
  calc shearLowerCost 10 A
      ≤ 4 * ∫⁻ p in Ioc 0 9, ∫⁻ t in Ioc 0 A,
          ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
        refine (shearLowerCost_le_region hA le_rfl le_rfl).trans ?_
        gcongr with p
        exact min_le_left _ _
    _ = 4 * ∫⁻ t in Ioc 0 A, ∫⁻ p in Ioc 0 9,
          ‖shearDifference p t‖ₑ * ENNReal.ofReal (t ^ (1 / 2 : ℝ)) := by
        congr 1
        exact lintegral_lintegral_swap hF.aemeasurable
    _ ≤ 4 * ∫⁻ t in Ioc 0 A, ENNReal.ofReal (3 * Real.pi / 4 * (1 / Real.sqrt t)) := by
        gcongr 4 * ?_
        exact setLIntegral_mono' measurableSet_Ioc hpt
    _ = 4 * ENNReal.ofReal (3 * Real.pi / 2 * Real.sqrt A) := by
        congr 1
        rw [lintegral_Ioc_ofReal_deriv (g := fun t ↦ 3 * Real.pi / 2 * Real.sqrt t) hA.le
          (by fun_prop) (fun t ht ↦ ?_) (fun t _ ↦ by positivity)]
        · simp
        · have ht0 : 0 < t := ht.1
          refine ((Real.hasDerivAt_sqrt ht0.ne').const_mul (3 * Real.pi / 2)).congr_deriv ?_
          have hs := Real.sqrt_pos.2 ht0
          field_simp
          ring
    _ = ENNReal.ofReal (6 * Real.pi * Real.sqrt A) := by
        rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end IncompressibleFlow.SharpHolder
