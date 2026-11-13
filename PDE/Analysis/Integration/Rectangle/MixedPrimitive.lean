/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Common.Euclidean

/-!
# Integrals over rectangles from mixed primitives

For a function `H` of two real variables, `cornerSum H a b c d = H b d - H a d - H b c + H a c`
is its mixed difference over the rectangle `[a, b] × [c, d]`. When `k = ∂_y k₁` on the rectangle
and `k₁ = ∂_x H` on its two horizontal edges, the iterated integral of `k` over the rectangle is
`cornerSum H a b c d`; in the other order of integration the roles of the two variables are
exchanged. Only the derivative of `H` along the two edges enters, so `H` may be singular, or have
a jump in its other derivative, inside the rectangle.

For functions continuous on a closed rectangle the two iterated interval integrals agree, and on
the plane `ℝ^2` the integral over a product set `{y | y 0 ∈ s ∧ y 1 ∈ t}` is the iterated
integral in coordinates, in particular over the closed rectangle
`coordinateRectangle a b c d = [a, b] × [c, d]`, also for integrands with an integrable
singularity.

## Main definitions

* `cornerSum`: the mixed difference `H b d - H a d - H b c + H a c`.
* `planeEquiv`: the identification `ℝ^2 ≃ ℝ × ℝ`, `y ↦ (y 0, y 1)`.
* `coordinateRectangle`: the closed rectangle `[a, b] × [c, d]` of the plane.

## Main results

* `integral_integral_eq_cornerSum`: `∫_a^b ∫_c^d k = cornerSum H a b c d` when `∂_y k₁ = k` on
  the rectangle and `∂_x H = k₁` on the edges `y = c` and `y = d`.
* `integral_integral_eq_cornerSum_swap`: the same in the other order of integration.
* `intervalIntegral_intervalIntegral_swap`: Fubini on a closed rectangle for a continuous
  function.
* `setIntegral_coordinateProduct`: the integral over a product set of the plane is the iterated
  integral in coordinates.
* `setIntegral_coordinateRectangle`: Fubini on closed rectangles of the plane for a function
  continuous on the rectangle.
* `setIntegral_coordinateRectangle_of_integrableOn`: the same for a function integrable on the
  rectangle.
* `setIntegral_coordinateRectangle_swap`: exchanging the coordinates maps `[c, d] × [a, b]` onto
  `[a, b] × [c, d]`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- The mixed difference `H b d - H a d - H b c + H a c` of `H` over `[a, b] × [c, d]`. -/
def cornerSum (H : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ := H b d - H a d - H b c + H a c

/-- The mixed difference of a sum is the sum of the mixed differences. -/
theorem cornerSum_add (H K : ℝ → ℝ → ℝ) (a b c d : ℝ) :
    cornerSum (fun x y ↦ H x y + K x y) a b c d = cornerSum H a b c d + cornerSum K a b c d := by
  unfold cornerSum; ring

/-- The mixed difference of a difference is the difference of the mixed differences. -/
theorem cornerSum_sub (H K : ℝ → ℝ → ℝ) (a b c d : ℝ) :
    cornerSum (fun x y ↦ H x y - K x y) a b c d = cornerSum H a b c d - cornerSum K a b c d := by
  unfold cornerSum; ring

/-- The mixed difference of `r H` is `r` times the mixed difference of `H`. -/
theorem cornerSum_const_mul (r : ℝ) (H : ℝ → ℝ → ℝ) (a b c d : ℝ) :
    cornerSum (fun x y ↦ r * H x y) a b c d = r * cornerSum H a b c d := by
  unfold cornerSum; ring

/-- A function of one variable only has no mixed difference. -/
theorem cornerSum_left (f : ℝ → ℝ) (a b c d : ℝ) : cornerSum (fun x _ ↦ f x) a b c d = 0 := by
  unfold cornerSum; ring

/-- A function of one variable only has no mixed difference. -/
theorem cornerSum_right (f : ℝ → ℝ) (a b c d : ℝ) : cornerSum (fun _ y ↦ f y) a b c d = 0 := by
  unfold cornerSum; ring

/-- The mixed difference with the variables exchanged. -/
theorem cornerSum_swap (H : ℝ → ℝ → ℝ) (a b c d : ℝ) :
    cornerSum (fun x y ↦ H y x) c d a b = cornerSum H a b c d := by
  unfold cornerSum; ring

/-- **Rectangle integral from a mixed primitive.** If `∂_y k₁ = k` on `[[a, b]] × [[c, d]]`
and `∂_x H = k₁` on the two edges `y = c` and `y = d`, then
`∫_a^b ∫_c^d k = H b d - H a d - H b c + H a c`. -/
theorem integral_integral_eq_cornerSum {k k₁ H : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hk : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc c d, HasDerivAt (k₁ x) (k x y) y)
    (hki : ∀ x ∈ uIcc a b, IntervalIntegrable (k x) volume c d)
    (hc : ∀ x ∈ uIcc a b, HasDerivAt (fun x ↦ H x c) (k₁ x c) x)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt (fun x ↦ H x d) (k₁ x d) x)
    (hic : IntervalIntegrable (fun x ↦ k₁ x c) volume a b)
    (hid : IntervalIntegrable (fun x ↦ k₁ x d) volume a b) :
    ∫ x in a..b, ∫ y in c..d, k x y = cornerSum H a b c d := by
  have hinner : EqOn (fun x ↦ ∫ y in c..d, k x y) (fun x ↦ k₁ x d - k₁ x c) (uIcc a b) :=
    fun x hx ↦ intervalIntegral.integral_eq_sub_of_hasDerivAt (hk x hx) (hki x hx)
  rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_sub hid hic,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hid,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hc hic]
  unfold cornerSum; ring

/-- **Rectangle integral from a mixed primitive, the other order.** If `∂_x k₁ = k` on
`[[a, b]] × [[c, d]]` and `∂_y H = k₁` on the two edges `x = a` and `x = b`, then
`∫_c^d ∫_a^b k = H b d - H a d - H b c + H a c`. -/
theorem integral_integral_eq_cornerSum_swap {k k₁ H : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hk : ∀ y ∈ uIcc c d, ∀ x ∈ uIcc a b, HasDerivAt (fun x ↦ k₁ x y) (k x y) x)
    (hki : ∀ y ∈ uIcc c d, IntervalIntegrable (fun x ↦ k x y) volume a b)
    (ha : ∀ y ∈ uIcc c d, HasDerivAt (H a) (k₁ a y) y)
    (hb : ∀ y ∈ uIcc c d, HasDerivAt (H b) (k₁ b y) y)
    (hia : IntervalIntegrable (k₁ a) volume c d)
    (hib : IntervalIntegrable (k₁ b) volume c d) :
    ∫ y in c..d, ∫ x in a..b, k x y = cornerSum H a b c d := by
  rw [← cornerSum_swap]
  exact integral_integral_eq_cornerSum (k := fun y x ↦ k x y) (k₁ := fun y x ↦ k₁ x y)
    (H := fun y x ↦ H x y) hk hki ha hb hia hib

/-- A function continuous on `[a, b] × [c, d]` is integrable for the product of Lebesgue measure on
`(a, b]` and on `(c, d]`. -/
private theorem integrableOn_Ioc_prod_of_continuousOn {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    Integrable (Function.uncurry f)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- For `a ≤ b`, `c ≤ d` and `f` continuous on `[a, b] × [c, d]`, the two iterated interval
integrals of `f` agree. -/
private theorem intervalIntegral_intervalIntegral_swap_of_le {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap (integrableOn_Ioc_prod_of_continuousOn hf)

/-- **Fubini on a closed rectangle** for a function continuous there. -/
theorem intervalIntegral_intervalIntegral_swap {f : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hf : ContinuousOn (Function.uncurry f) (uIcc a b ×ˢ uIcc c d)) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  rcases le_total a b with hab | hab <;> rcases le_total c d with hcd | hcd
  · rw [uIcc_of_le hab, uIcc_of_le hcd] at hf
    exact intervalIntegral_intervalIntegral_swap_of_le hab hcd hf
  · rw [uIcc_of_le hab, uIcc_of_ge hcd] at hf
    simp only [intervalIntegral.integral_symm d c, intervalIntegral.integral_neg, neg_inj]
    exact intervalIntegral_intervalIntegral_swap_of_le hab hcd hf
  · rw [uIcc_of_ge hab, uIcc_of_le hcd] at hf
    simp only [intervalIntegral.integral_symm b a, intervalIntegral.integral_neg, neg_inj]
    exact intervalIntegral_intervalIntegral_swap_of_le hab hcd hf
  · rw [uIcc_of_ge hab, uIcc_of_ge hcd] at hf
    simp only [intervalIntegral.integral_symm b a, intervalIntegral.integral_symm d c,
      intervalIntegral.integral_neg, neg_neg]
    exact intervalIntegral_intervalIntegral_swap_of_le hab hcd hf

/-- The identification `ℝ^2 ≃ ℝ × ℝ`, `y ↦ (y 0, y 1)`. -/
def planeEquiv : ℝ^2 ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

/-- The inverse of `planeEquiv` sends `(p₁, p₂)` to `!₂[p₁, p₂]`. -/
theorem planeEquiv_symm_apply (p : ℝ × ℝ) : planeEquiv.symm p = !₂[p.1, p.2] := rfl

/-- `planeEquiv y = (y 0, y 1)`. -/
@[simp] theorem planeEquiv_apply (y : ℝ^2) : planeEquiv y = (y 0, y 1) := rfl

/-- The inverse of `planeEquiv` sends `(p₁, p₂)` to `p₁ e₀ + p₂ e₁`. -/
theorem planeEquiv_symm_apply_eq_add (p : ℝ × ℝ) :
    planeEquiv.symm p = EuclideanSpace.single 0 p.1 + EuclideanSpace.single 1 p.2 := by
  ext i
  fin_cases i <;> simp [planeEquiv_symm_apply]

/-- `planeEquiv` carries Lebesgue measure on `ℝ^2` to the product measure on `ℝ × ℝ`. -/
theorem measurePreserving_planeEquiv :
    MeasurePreserving (planeEquiv : ℝ^2 → ℝ × ℝ) volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

/-- The identification `ℝ × ℝ ≃ ℝ^2`, `(s, t) ↦ (t, s)`: the second product coordinate becomes
the first plane coordinate, so that Fubini integrates along horizontal lines inside. -/
def planeEquivSwap : ℝ × ℝ ≃ᵐ ℝ^2 :=
  MeasurableEquiv.prodComm.trans planeEquiv.symm

/-- `planeEquivSwap (s, t) = !₂[t, s]`. -/
theorem planeEquivSwap_apply (p : ℝ × ℝ) : planeEquivSwap p = !₂[p.2, p.1] := rfl

/-- `planeEquivSwap (s, t) = t e₀ + s e₁`. -/
theorem planeEquivSwap_apply_eq_add (p : ℝ × ℝ) :
    planeEquivSwap p = EuclideanSpace.single 0 p.2 + EuclideanSpace.single 1 p.1 :=
  planeEquiv_symm_apply_eq_add (p.2, p.1)

/-- `planeEquivSwap` carries the product measure on `ℝ × ℝ` to Lebesgue measure on `ℝ^2`. -/
theorem measurePreserving_planeEquivSwap :
    MeasurePreserving planeEquivSwap volume volume :=
  measurePreserving_planeEquiv.symm.comp Measure.measurePreserving_swap

/-- **Fubini on product sets of the plane**: the integral over `{y | y 0 ∈ s ∧ y 1 ∈ t}` is the
iterated integral in coordinates. -/
theorem setIntegral_coordinateProduct {f : ℝ^2 → ℝ} {s t : Set ℝ}
    (hf : IntegrableOn f {y : ℝ^2 | y 0 ∈ s ∧ y 1 ∈ t}) :
    ∫ y in {y : ℝ^2 | y 0 ∈ s ∧ y 1 ∈ t}, f y = ∫ p in s, ∫ q in t, f !₂[p, q] := by
  have hpre : {y : ℝ^2 | y 0 ∈ s ∧ y 1 ∈ t} = planeEquiv ⁻¹' (s ×ˢ t) := by
    ext y; simp [planeEquiv_apply]
  have hemb := planeEquiv.measurableEmbedding
  rw [hpre] at hf ⊢
  have h1 := measurePreserving_planeEquiv.setIntegral_preimage_emb hemb
    (fun p ↦ f (planeEquiv.symm p)) (s ×ˢ t)
  simp only [MeasurableEquiv.symm_apply_apply] at h1
  rw [h1]
  have hf' : IntegrableOn (fun p ↦ f (planeEquiv.symm p)) (s ×ˢ t) := by
    have := (measurePreserving_planeEquiv.integrableOn_comp_preimage hemb
      (f := fun p ↦ f (planeEquiv.symm p)) (s := s ×ˢ t)).mp
    simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply] at this
    exact this hf
  rw [Measure.volume_eq_prod] at hf' ⊢
  rw [setIntegral_prod _ hf']
  simp only [planeEquiv_symm_apply]

/-- The closed rectangle `[a, b] × [c, d]` of the plane. -/
def coordinateRectangle (a b c d : ℝ) : Set (ℝ^2) := {y | y 0 ∈ Icc a b ∧ y 1 ∈ Icc c d}

/-- `y` lies in `coordinateRectangle a b c d` exactly when `y 0 ∈ [a, b]` and `y 1 ∈ [c, d]`. -/
theorem mem_coordinateRectangle {a b c d : ℝ} {y : ℝ^2} :
    y ∈ coordinateRectangle a b c d ↔ y 0 ∈ Icc a b ∧ y 1 ∈ Icc c d := Iff.rfl

/-- The closed rectangle `[a, b] × [c, d]` of the plane is compact. -/
theorem isCompact_coordinateRectangle (a b c d : ℝ) :
    IsCompact (coordinateRectangle a b c d) := by
  have : coordinateRectangle a b c d = planeEquiv ⁻¹' (Icc a b ×ˢ Icc c d) := by
    ext y; exact Iff.rfl
  rw [this]
  have hc : Continuous (planeEquiv.symm : ℝ × ℝ → ℝ^2) := by
    rw [show (planeEquiv.symm : ℝ × ℝ → ℝ^2) = fun p ↦ !₂[p.1, p.2] from
      funext planeEquiv_symm_apply]
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp (continuous_pi fun i ↦ ?_)
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd
  have h := ((isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := c) (b := d))).image hc
  rwa [MeasurableEquiv.image_eq_preimage_symm, MeasurableEquiv.symm_symm] at h

/-- The closed rectangle `[a, b] × [c, d]` of the plane is measurable. -/
theorem measurableSet_coordinateRectangle (a b c d : ℝ) :
    MeasurableSet (coordinateRectangle a b c d) :=
  (isCompact_coordinateRectangle a b c d).isClosed.measurableSet

/-- **Fubini on closed rectangles of the plane** for a function integrable on the rectangle. -/
theorem setIntegral_coordinateRectangle_of_integrableOn {f : ℝ^2 → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : IntegrableOn f (coordinateRectangle a b c d)) :
    ∫ y in coordinateRectangle a b c d, f y = ∫ p in a..b, ∫ q in c..d, f !₂[p, q] := by
  rw [coordinateRectangle, setIntegral_coordinateProduct hf, intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun p _ ↦ ?_
  rw [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]

/-- **Fubini on closed rectangles of the plane** for a function continuous on the rectangle. -/
theorem setIntegral_coordinateRectangle {f : ℝ^2 → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (hf : ContinuousOn f (coordinateRectangle a b c d)) :
    ∫ y in coordinateRectangle a b c d, f y = ∫ p in a..b, ∫ q in c..d, f !₂[p, q] :=
  setIntegral_coordinateRectangle_of_integrableOn hab hcd
    (hf.integrableOn_compact (isCompact_coordinateRectangle a b c d))

/-- Exchanging the coordinates, `y ↦ (y₁, y₀)`, maps the rectangle `[c, d] × [a, b]` onto
`[a, b] × [c, d]`: the integral of `f ∘ swap` over the first is the integral of `f` over the
second. -/
theorem setIntegral_coordinateRectangle_swap (f : ℝ^2 → ℝ) (a b c d : ℝ) :
    ∫ y in coordinateRectangle c d a b,
        f (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) y) =
      ∫ y in coordinateRectangle a b c d, f y := by
  set e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)
  have he0 : ∀ y : ℝ^2, e y 0 = y 1 := fun y ↦ by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply]
  have he1 : ∀ y : ℝ^2, e y 1 = y 0 := fun y ↦ by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply]
  have hpre : (e : ℝ^2 → ℝ^2) ⁻¹' coordinateRectangle a b c d = coordinateRectangle c d a b := by
    ext y
    simp only [mem_preimage, mem_coordinateRectangle, he0, he1]
    exact And.comm
  rw [← hpre]
  exact (LinearIsometryEquiv.measurePreserving e).setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding f _

end PDE.Analysis


