/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# First-order regularity of piecewise maps

Jointly `C¹` branches defined near an interface point glue locally when their
values and full derivatives agree on the nearby parameter slice.
Two globally `C¹` branches glue across the hyperplane `p.1 = a` in `ℝ × E` to
a `C¹` map when their values and Fréchet derivatives agree there: the glued
derivative is continuous because the two candidate derivatives coincide on
the frontier, and differentiability at interface points comes from the two
one-sided `HasFDerivWithinAt` statements on the half-spaces.  On the real
line, `C¹` regularity of the two branches at the interface point alone is
enough.  As an application, a map that is `C¹` at every point of a closed
interval `[a, b]` extends to a globally `C¹` map by continuing it with its
tangent lines at `a` and `b`; the extension agrees with the original map on
`[a, b]`, including its derivative at both endpoints.

## Main results

* `contDiff_one_if_fst_le`: gluing two `C¹` maps along `{p.1 ≤ a}`.
* `contDiffAt_one_if_fst_le`: the corresponding local gluing of joint germs.
* `contDiffAt_one_if_le`: pointwise `C¹` gluing on the real line.
* `tangentLine`, `tangentExtension`: the affine tangent line at a point and
  the extension of `f` from `[a, b]` by its endpoint tangent lines.
* `hasFDerivAt_tangentExtension_of_mem_Icc`,
  `deriv_tangentExtension_eq_of_mem_Icc`: the extension has the derivative
  of `f` on `[a, b]`.
* `contDiff_tangentExtension`: the extension is globally `C¹`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter
open scoped Topology

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Equal values and equal derivatives permit differentiable gluing along an
arbitrary predicate. The shape of the interface is immaterial at a matching
point. -/
theorem hasFDerivAt_if_of_eq
    {f g : E → F} {x : E} {D : E →L[ℝ] F}
    (p : E → Prop) [DecidablePred p]
    (hf : HasFDerivAt f D x) (hg : HasFDerivAt g D x) (hvalue : f x = g x) :
    HasFDerivAt (fun y ↦ if p y then f y else g y) D x := by
  have hleft : HasFDerivWithinAt (fun y ↦ if p y then f y else g y)
      D {y | p y} x := by
    apply hf.hasFDerivWithinAt.congr
    · exact fun y hy ↦ ite_eq_left hy
    · simp [hvalue]
  have hright : HasFDerivWithinAt (fun y ↦ if p y then f y else g y)
      D {y | p y}ᶜ x := by
    apply hg.hasFDerivWithinAt.congr
    · exact fun y hy ↦ ite_eq_right hy
    · simp [hvalue]
  simpa only [Set.union_compl_self, hasFDerivWithinAt_univ] using hleft.union hright

/-- Joint `C¹` germs glue across a parameter slice when their values and full
derivatives agree on that slice near the base point. No global regularity or
agreement away from the construction neighborhood is required. -/
theorem contDiffAt_one_if_fst_le
    {f g : ℝ × E → F} {p₀ : ℝ × E} (a : ℝ)
    (hf : ContDiffAt ℝ 1 f p₀) (hg : ContDiffAt ℝ 1 g p₀)
    (hmatch : ∀ᶠ p in 𝓝 p₀, p.1 = a →
      f p = g p ∧ fderiv ℝ f p = fderiv ℝ g p) :
    ContDiffAt ℝ 1 (fun p ↦ if p.1 ≤ a then f p else g p) p₀ := by
  let derivative : (ℝ × E) → (ℝ × E) →L[ℝ] F :=
    fun p ↦ if p.1 ≤ a then fderiv ℝ f p else fderiv ℝ g p
  let regular : Set (ℝ × E) := {p | ContDiffAt ℝ 1 f p ∧ ContDiffAt ℝ 1 g p ∧
    (p.1 = a → f p = g p ∧ fderiv ℝ f p = fderiv ℝ g p)}
  have hfrontier : ∀ p ∈ frontier {q : ℝ × E | q.1 ≤ a}, p.1 = a := fun p hp ↦ by
    simpa using continuous_fst.frontier_preimage_subset (Set.Iic a) hp
  have hcontinuous : ContinuousOn derivative regular := by
    apply ContinuousOn.if
    · exact fun p hp ↦ (hp.1.2.2 (hfrontier p hp.2)).2
    · exact fun p hp ↦ (hp.1.1.continuousAt_fderiv one_ne_zero).continuousWithinAt
    · exact fun p hp ↦ (hp.1.2.1.continuousAt_fderiv one_ne_zero).continuousWithinAt
  refine contDiffAt_one_iff.2 ⟨derivative, regular,
    (hf.eventually (by simp)).and ((hg.eventually (by simp)).and hmatch), hcontinuous, ?_⟩
  rintro p ⟨hfp, hgp, hmatchp⟩
  rcases lt_trichotomy p.1 a with hlt | heq | hgt
  · simpa [derivative, hlt.le] using hfp.differentiableAt_one.hasFDerivAt.congr_of_eventuallyEq
      ((continuousAt_fst.eventually (gt_mem_nhds hlt)).mono fun q hq ↦ ite_eq_left hq.le)
  · simpa only [derivative, ite_eq_left heq.le] using
      hasFDerivAt_if_of_eq (fun q : ℝ × E ↦ q.1 ≤ a)
        hfp.differentiableAt_one.hasFDerivAt
        (hgp.differentiableAt_one.hasFDerivAt.congr_fderiv (hmatchp heq).2.symm)
        (hmatchp heq).1
  · simpa [derivative, not_le_of_gt hgt] using
      hgp.differentiableAt_one.hasFDerivAt.congr_of_eventuallyEq
        ((continuousAt_fst.eventually (lt_mem_nhds hgt)).mono fun q hq ↦
          ite_eq_right (not_le_of_gt hq))

/-- Two `C¹` maps whose values and first derivatives agree on the hyperplane
`p.1 = a` define a `C¹` map by gluing along the closed half-space
`p.1 ≤ a`. -/
theorem contDiff_one_if_fst_le
    {f g : ℝ × E → F} (a : ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hvalue : ∀ p, p.1 = a → f p = g p)
    (hderiv : ∀ p, p.1 = a → fderiv ℝ f p = fderiv ℝ g p) :
    ContDiff ℝ 1 (fun p ↦ if p.1 ≤ a then f p else g p) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  exact contDiffAt_one_if_fst_le a hf.contDiffAt hg.contDiffAt
    (Eventually.of_forall fun q hq ↦ ⟨hvalue q hq, hderiv q hq⟩)

/-! ## Local gluing on the real line -/

/-- Two maps that are `C¹` at `a`, with the same value and derivative there,
glue to a map that is `C¹` at `a`.

Unlike `contDiff_one_if_fst_le`, this pointwise theorem requires no regularity
away from the interface. The proof glues `f ∘ Prod.fst` and `g ∘ Prod.fst` with
`contDiffAt_one_if_fst_le` and restricts to the line `ℝ × {0}`. -/
theorem contDiffAt_one_if_le
    {f g : ℝ → F} (a : ℝ)
    (hf : ContDiffAt ℝ 1 f a) (hg : ContDiffAt ℝ 1 g a)
    (hvalue : f a = g a)
    (hderiv : fderiv ℝ f a = fderiv ℝ g a) :
    ContDiffAt ℝ 1 (fun x ↦ if x ≤ a then f x else g x) a := by
  have hmatch : ∀ p : ℝ × ℝ, p.1 = a → (f ∘ Prod.fst) p = (g ∘ Prod.fst) p ∧
      fderiv ℝ (f ∘ Prod.fst) p = fderiv ℝ (g ∘ Prod.fst) p := by
    rintro ⟨x, y⟩ (rfl : x = a)
    refine ⟨hvalue, ?_⟩
    rw [fderiv_comp _ hf.differentiableAt_one differentiableAt_fst,
      fderiv_comp _ hg.differentiableAt_one differentiableAt_fst, hderiv]
  exact (contDiffAt_one_if_fst_le (p₀ := (a, (0 : ℝ))) a (hf.comp _ contDiffAt_fst)
    (hg.comp _ contDiffAt_fst) (.of_forall hmatch)).comp a (contDiffAt_id.prodMk contDiffAt_const)

/-! ## Extension by endpoint tangent lines -/

/-- The affine tangent line to `f` at `a`, expressed using the Fréchet
derivative. This definition is meaningful even when `f` is not
differentiable; the analytic theorems below assume the required regularity. -/
def tangentLine (f : ℝ → F) (a x : ℝ) : F :=
  f a + fderiv ℝ f a (x - a)

/-- The tangent line at `a` passes through `f a`. -/
@[simp]
theorem tangentLine_self (f : ℝ → F) (a : ℝ) :
    tangentLine f a a = f a := by
  simp [tangentLine]

/-- The tangent line has the derivative used to define it at every point. -/
theorem hasFDerivAt_tangentLine (f : ℝ → F) (a x : ℝ) :
    HasFDerivAt (tangentLine f a) (fderiv ℝ f a) x := by
  change HasFDerivAt (fun y ↦ f a + fderiv ℝ f a (y - a)) (fderiv ℝ f a) x
  simpa using ((fderiv ℝ f a).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const a)).const_add (f a)

/-- Every endpoint tangent line is globally `C¹`. -/
theorem contDiff_tangentLine (f : ℝ → F) (a : ℝ) :
    ContDiff ℝ 1 (tangentLine f a) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_one_iff.2
    ⟨fun _ ↦ fderiv ℝ f a, Set.univ, univ_mem, continuousOn_const,
      fun y _ ↦ hasFDerivAt_tangentLine f a y⟩

/-- Extend `f` from `[a, b]` by the tangent line at `a` on the left and the
tangent line at `b` on the right. -/
def tangentExtension (f : ℝ → F) (a b x : ℝ) : F :=
  if x ≤ a then tangentLine f a x
  else if x ≤ b then f x
  else tangentLine f b x

/-- The tangent extension agrees with the original map on its closed
interval. -/
theorem tangentExtension_eq_of_mem_Icc
    {f : ℝ → F} {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    tangentExtension f a b x = f x := by
  rcases hx.1.eq_or_lt with rfl | hax
  · simp [tangentExtension]
  · simp [tangentExtension, not_le_of_gt hax, hx.2]

/-- Over a degenerate interval the tangent extension is the tangent line. -/
private theorem tangentExtension_self (f : ℝ → F) (a : ℝ) :
    tangentExtension f a a = tangentLine f a := by
  funext y
  simp only [tangentExtension]
  split_ifs <;> rfl

/-- On the original interval, the tangent extension has the same Fréchet
derivative as the original map, including at both endpoints. -/
theorem hasFDerivAt_tangentExtension_of_mem_Icc
    {f : ℝ → F} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (tangentExtension f a b) (fderiv ℝ f x) x := by
  rcases hab.eq_or_lt with rfl | hab
  · obtain rfl : x = a := le_antisymm hx.2 hx.1
    exact tangentExtension_self f x ▸ hasFDerivAt_tangentLine f x x
  rcases hx.1.eq_or_lt with hxa | hax
  · subst x
    refine (hasFDerivAt_if_of_eq (· ≤ a) (hasFDerivAt_tangentLine f a a) hf.hasFDerivAt
      (tangentLine_self f a)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hab] with y (hy : y < b)
    by_cases hya : y ≤ a <;> simp [tangentExtension, hya, hy.le]
  rcases hx.2.eq_or_lt with hxb | hxb
  · subst x
    refine (hasFDerivAt_if_of_eq (· ≤ b) hf.hasFDerivAt (hasFDerivAt_tangentLine f b b)
      (tangentLine_self f b).symm).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hax] with y (hy : a < y)
    by_cases hyb : y ≤ b <;> simp [tangentExtension, not_le_of_gt hy, hyb]
  · refine hf.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hax hxb] with y hy
    simp [tangentExtension, not_le_of_gt hy.1, hy.2.le]

/-- On the original interval, tangent extension preserves the one-variable
derivative. -/
theorem deriv_tangentExtension_eq_of_mem_Icc
    {f : ℝ → F} {a b x : ℝ} (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) (hf : DifferentiableAt ℝ f x) :
    deriv (tangentExtension f a b) x = deriv f x := by
  have hderiv :=
    (hasFDerivAt_tangentExtension_of_mem_Icc hab hx hf).hasDerivAt.deriv
  simpa [fderiv_eq_smul_deriv] using hderiv

/-- A map that is `C¹` at every point of `[a, b]` has a global `C¹`
extension obtained from its endpoint tangent lines. -/
theorem contDiff_tangentExtension
    {f : ℝ → F} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc a b, ContDiffAt ℝ 1 f x) :
    ContDiff ℝ 1 (tangentExtension f a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact tangentExtension_self f a ▸ contDiff_tangentLine f a
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  rcases lt_trichotomy x a with hxa | hxa | hax
  · refine (contDiff_tangentLine f a).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hxa] with y (hy : y < a)
    simp [tangentExtension, hy.le]
  · subst x
    refine (contDiffAt_one_if_le a (contDiff_tangentLine f a).contDiffAt (hf a ⟨le_rfl, hab.le⟩)
      (tangentLine_self f a) (hasFDerivAt_tangentLine f a a).fderiv).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hab] with y (hy : y < b)
    by_cases hya : y ≤ a <;> simp [tangentExtension, hya, hy.le]
  rcases lt_trichotomy x b with hxb | hxb | hbx
  · refine (hf x ⟨hax.le, hxb.le⟩).congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hax hxb] with y hy
    simp [tangentExtension, not_le_of_gt hy.1, hy.2.le]
  · subst x
    refine (contDiffAt_one_if_le b (hf b ⟨hab.le, le_rfl⟩) (contDiff_tangentLine f b).contDiffAt
      (tangentLine_self f b).symm (hasFDerivAt_tangentLine f b b).fderiv.symm).congr_of_eventuallyEq
      ?_
    filter_upwards [Ioi_mem_nhds hab] with y (hy : a < y)
    by_cases hyb : y ≤ b <;> simp [tangentExtension, not_le_of_gt hy, hyb]
  · refine (contDiff_tangentLine f b).contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hbx] with y (hy : b < y)
    simp [tangentExtension, not_le_of_gt (hab.trans hy), not_le_of_gt hy]

end PDE.Analysis
