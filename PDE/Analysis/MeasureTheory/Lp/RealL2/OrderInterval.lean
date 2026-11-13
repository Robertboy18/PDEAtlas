/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Order intervals and their normal cones in real L²

Order intervals are convex and norm bounded. Testing a variational inequality
with the pointwise projection of `l - b` onto `[0, g]` identifies the normal
cone: a strictly negative normal forces the upper endpoint, and a strictly
positive normal forces the lower endpoint.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace MeasureTheory.L2

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Order intervals in real `L²` are convex, expressed using almost-everywhere order. -/
theorem convex_Icc (a b : Lp ℝ 2 μ) : Convex ℝ (Icc a b) := by
  intro u hu v hv s t hs ht hst
  constructor
  all_goals
    rw [← Lp.coeFn_le]
    filter_upwards [(Lp.coeFn_le _ _).mpr hu.1, (Lp.coeFn_le _ _).mpr hu.2,
      (Lp.coeFn_le _ _).mpr hv.1, (Lp.coeFn_le _ _).mpr hv.2,
      Lp.coeFn_add (s • u) (t • v), Lp.coeFn_smul s u, Lp.coeFn_smul t v]
      with x hua hub hva hvb hadd hsx htx
    rw [hadd, Pi.add_apply, hsx, htx]
  · calc
      a x = s * a x + t * a x := by rw [← add_mul, hst, one_mul]
      _ ≤ s * u x + t * v x :=
        add_le_add (mul_le_mul_of_nonneg_left hua hs) (mul_le_mul_of_nonneg_left hva ht)
  · calc
      s * u x + t * v x ≤ s * b x + t * b x :=
        add_le_add (mul_le_mul_of_nonneg_left hub hs) (mul_le_mul_of_nonneg_left hvb ht)
      _ = b x := by rw [← add_mul, hst, one_mul]

/-- An order interval with nonnegative lower endpoint zero is norm bounded in `L²`. -/
theorem isBounded_Icc_zero (g : Lp ℝ 2 μ) : Bornology.IsBounded (Icc 0 g) := by
  apply (isBounded_iff_forall_norm_le.mpr ⟨‖g‖, ?_⟩)
  intro v hv
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [(Lp.coeFn_nonneg v).mpr hv.1, (Lp.coeFn_le v g).mpr hv.2]
    with x hx hxy
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy)]
    using hxy

/-- The normal cone of an `L²` order interval is pointwise: a negative
normal forces the upper constraint, and a positive normal the lower one. -/
theorem ae_eq_endpoints_of_box_variationalInequality
    (g l b : Lp ℝ 2 μ) (hl : l ∈ Icc 0 g)
    (hvi : ∀ v ∈ Icc 0 g, 0 ≤ inner ℝ b (v - l)) :
    ∀ᵐ x ∂μ, (b x < 0 → l x = g x) ∧ (0 < b x → l x = 0) := by
  let v := ((l - b) ⊔ 0) ⊓ g
  have hv : v ∈ Icc 0 g :=
    ⟨le_inf (le_sup_right) (hl.1.trans hl.2), inf_le_right⟩
  have hvrep : ∀ᵐ x ∂μ, v x = min (max (l x - b x) 0) (g x) := by
    filter_upwards [Lp.coeFn_inf ((l - b) ⊔ 0) g, Lp.coeFn_sup (l - b) 0,
      Lp.coeFn_sub l b, Lp.coeFn_zero ℝ 2 μ] with x hi hs hd hz
    simp only [v, hi, Pi.inf_apply, hs, Pi.sup_apply, hd, Pi.sub_apply, hz, Pi.zero_apply]
  have hsign : ∀ᵐ x ∂μ, inner ℝ (b x) ((v - l) x) ≤ 0 := by
    filter_upwards [hvrep, Lp.coeFn_sub v l, (Lp.coeFn_nonneg l).mpr hl.1,
      (Lp.coeFn_le l g).mpr hl.2] with x hvx hd hlx hlg
    simp only [hd, Pi.sub_apply, Real.inner_apply, hvx]
    by_cases hb : 0 ≤ b x
    · apply mul_nonpos_of_nonneg_of_nonpos hb
      exact sub_nonpos.mpr ((min_le_left _ _).trans
        (max_le (sub_le_self _ hb) hlx))
    · apply mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hb)
      exact sub_nonneg.mpr (le_min
        (le_max_of_le_left (le_sub_iff_add_le.mpr (add_le_of_nonpos_right (le_of_not_ge hb))))
        hlg)
  have hzero : ∀ᵐ x ∂μ, inner ℝ (b x) ((v - l) x) = 0 := by
    have hn : 0 ≤ᵐ[μ] fun x ↦ -inner ℝ (b x) ((v - l) x) := by
      filter_upwards [hsign] with x hx
      exact neg_nonneg.mpr hx
    have hi : ∫ x, -inner ℝ (b x) ((v - l) x) ∂μ = 0 := by
      apply le_antisymm
      · rw [integral_neg, ← L2.inner_def]
        exact neg_nonpos.mpr (hvi v hv)
      · exact integral_nonneg_of_ae hn
    have hz := (integral_eq_zero_iff_of_nonneg_ae hn (L2.integrable_inner b (v - l)).neg).mp hi
    filter_upwards [hz] with x hx
    exact neg_eq_zero.mp hx
  filter_upwards [hzero, hvrep, Lp.coeFn_sub v l, (Lp.coeFn_nonneg l).mpr hl.1,
    (Lp.coeFn_le l g).mpr hl.2] with x hz hvx hd hlx hlg
  simp only [hd, Pi.sub_apply, Real.inner_apply] at hz
  constructor
  · intro hb
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_lt hb))
    rw [hvx] at heq
    by_contra hne
    have hlt : l x < min (max (l x - b x) 0) (g x) :=
      lt_min (lt_max_of_lt_left (lt_sub_iff_add_lt.mpr (add_lt_of_neg_right _ hb)))
        (lt_of_le_of_ne hlg hne)
    exact (ne_of_lt hlt) heq.symm
  · intro hb
    have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt hb))
    rw [hvx] at heq
    by_contra hne
    have hlt : min (max (l x - b x) 0) (g x) < l x :=
      (min_le_left _ _).trans_lt
        (max_lt (sub_lt_self _ hb) (lt_of_le_of_ne hlx (Ne.symm hne)))
    exact (ne_of_lt hlt) heq

end MeasureTheory.L2
