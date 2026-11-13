/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Banach-valued fundamental theorem of calculus

Banach-valued fundamental-theorem-of-calculus facts for the measurable affine
ODE theory:

* an indefinite Bochner integral is absolutely continuous;
* an absolutely continuous curve is recovered from an almost-everywhere
  specified derivative by interval integration;
* integral increments with a continuous source determine the interior derivative
  of a field on a half-line.

The generic pointwise and composition rules for absolutely continuous curves
are in `PDE.Analysis.Evolution.Time.AbsoluteContinuity`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 1. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

section BanachFTC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/--
The indefinite Bochner integral of an interval-integrable Banach-valued
function is absolutely continuous.

Mathlib's theorem
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` is
stated for real-valued functions.  The same proof works for Bochner
integrals: disjoint interval increments are bounded by the integral of the
norm over their union, and absolute continuity of that scalar integral
forces the total variation to zero with the total interval length.

The Galerkin systems in the proof of Evans §7.1.2, Theorem 1 have `L²` forcing, hence `L¹`
on a finite interval, and need exactly this regularity; the forcing need not be pointwise
bounded.
-/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
    {f : ℝ → E} {a b c : ℝ}
    (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun I : ℕ × (ℕ → ℝ × ℝ) ↦
    ⋃ i ∈ Finset.range I.1, uIoc (I.2 i).1 (I.2 i).2
  have hfinite :
      Integrable f (volume.restrict (uIoc a b)) :=
    intervalIntegrable_iff.mp hf
  have htendsto :
      Tendsto
        (fun I ↦ ∫⁻ x in s I, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
        (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt hfinite.hasFiniteIntegral)
      (tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have htendstoReal :
      Tendsto
        (fun I ↦ ENNReal.toReal
          (∫⁻ x in s I, ‖f x‖ₑ ∂volume.restrict (uIoc a b)))
        (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) (𝓝 0) :=
    ENNReal.toReal_zero ▸
      (ENNReal.continuousAt_toReal (by simp)).tendsto.comp htendsto
  refine squeeze_zero' ?_ ?_ htendstoReal
  · filter_upwards with I
    exact Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  have hdisjoint :
      ∀ᶠ I : ℕ × (ℕ → ℝ × ℝ) in
          totalLengthFilter ⊓ 𝓟 (disjWithin a b),
        I ∈ disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hdisjoint] with I hI
  obtain ⟨hI_mem, hI_pairwise⟩ := Set.mem_ofPred_eq ▸ hI
  simp only [s]
  rw [← integral_norm_eq_lintegral_enorm
      (hf.aestronglyMeasurable_restrict_uIoc.restrict),
    integral_biUnion_finset _ (by simp +contextual [uIoc]) hI_pairwise]
  · refine Finset.sum_le_sum fun i hi ↦ ?_
    rw [dist_eq_norm,
      intervalIntegral.integral_interval_sub_left
        (by
          apply IntervalIntegrable.mono_set' hf
          grind [uIoc, uIcc])
        (by
          apply IntervalIntegrable.mono_set' hf
          grind [uIoc, uIcc]),
      Measure.restrict_restrict_of_subset
        (uIoc_subset_of_mem_disjWithin hI (Finset.mem_range.mp hi)),
      intervalIntegral.integral_symm, norm_neg,
      intervalIntegral.norm_intervalIntegral_eq]
    exact MeasureTheory.norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have hsubset :=
      uIoc_subset_of_mem_disjWithin hI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set hfinite.norm hsubset |>.integrable

/--
Banach-valued fundamental theorem of calculus for an absolutely continuous
curve with an almost-everywhere specified derivative.

Subtracting the Bochner primitive from the curve gives an absolutely
continuous function with derivative zero almost everywhere.  Mathlib's
Banach-valued zero-derivative constancy theorem then gives the identity

`∫ₐᵇ g(t) dt = u(b) - u(a)`.

The derivative hypothesis is stated on `Ioc a b`, matching the
Carathéodory solution structures of the affine ODE theory. It turns the
a.e. differential equation into the Volterra integral equation used for
uniqueness.
-/
theorem AbsolutelyContinuousOnInterval.intervalIntegral_eq_sub_of_ae_hasDerivAt_normedSpace
    {u g : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hg : IntegrableOn g (Set.Icc a b) volume)
    (hderiv :
      ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
        HasDerivAt u (g t) t) :
    ∫ t in a..b, g t = u b - u a := by
  have hgInterval : IntervalIntegrable g volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hg
  let primitive : ℝ → E := fun x ↦ ∫ t in a..x, g t
  let remainder : ℝ → E := u - primitive
  have hprimitive :
      AbsolutelyContinuousOnInterval primitive a b := by
    exact
      IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
        hgInterval Set.left_mem_uIcc
  have hremainder : AbsolutelyContinuousOnInterval remainder a b :=
    hu.sub hprimitive
  have hderiv' :
      ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → HasDerivAt u (g t) t := by
    rwa [ae_restrict_iff' measurableSet_Ioc] at hderiv
  have hprimitiveDeriv := hgInterval.ae_hasDerivAt_integral
  have hleft : ∀ᵐ t ∂volume, t ≠ a := by
    simp [ae_iff, measure_singleton]
  have hremainderDeriv :
      ∀ᵐ t ∂volume, t ∈ Set.uIcc a b → HasDerivAt remainder 0 t := by
    filter_upwards [hderiv', hprimitiveDeriv, hleft]
      with t hu' hprimitive' hta ht
    have htIoc : t ∈ Set.Ioc a b := by
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), ht.2⟩
    simpa only [remainder, primitive, Pi.sub_apply, sub_self] using
      (hu' htIoc).sub (hprimitive' ht a Set.left_mem_uIcc)
  obtain ⟨C, hC⟩ :=
    hremainder.const_of_ae_hasDerivAt_zero hremainderDeriv
  have ha := hC a Set.left_mem_uIcc
  have hb := hC b Set.right_mem_uIcc
  simp only [remainder, primitive, Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha
  rw [← ha] at hb
  simp only [remainder, primitive, Pi.sub_apply] at hb
  rw [eq_sub_iff_add_eq]
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp hb).symm

end BanachFTC

section HalfLineFTC

attribute [local instance] Measure.Subtype.measureSpace

/-- A continuous source and its integral increments determine the derivative of a
half-line field, extended constantly before its initial time. -/
theorem hasDerivAt_clamp_of_sub_eq_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b τ : ℝ} (f g : Ici a → E)
    (hg : Continuous (fun r : ℝ ↦ g ⟨max a r, le_max_left a r⟩))
    (hwindow : ∀ (r : ℝ) (hr : r ∈ Ioo a b),
      f ⟨r, hr.1.le⟩ - f ⟨a, le_rfl⟩ =
        ∫ z : Icc a r, g ⟨z, z.property.1⟩)
    (hτ : τ ∈ Ioo a b) :
    HasDerivAt (fun r : ℝ ↦ f ⟨max a r, le_max_left a r⟩)
      (g ⟨max a τ, le_max_left a τ⟩) τ := by
  let field : ℝ → E := fun r ↦ f ⟨max a r, le_max_left a r⟩
  let source : ℝ → E := fun r ↦ g ⟨max a r, le_max_left a r⟩
  change HasDerivAt field (source τ) τ
  have heq : field =ᶠ[𝓝 τ] (fun r ↦ field a + ∫ z in a..r, source z) := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with r hr
    have hsource : (fun z : Icc a r ↦ g ⟨z, z.property.1⟩) =
        (fun z : Icc a r ↦ source z) := by
      funext z
      simp only [source, max_eq_right z.property.1]
    have hIntegral : (∫ z : Icc a r, g ⟨z, z.property.1⟩) =
        ∫ z in a..r, source z := by
      rw [hsource]
      exact (integral_subtype measurableSet_Icc source).trans
        (integral_Icc_eq_integral_Ioc.trans (intervalIntegral.integral_of_le hr.1.le).symm)
    have hincrement : field r - field a = ∫ z in a..r, source z := by
      simpa only [field, max_eq_right hr.1.le, max_self] using
        (hwindow r hr).trans hIntegral
    exact sub_eq_iff_eq_add'.mp hincrement
  have hprimitive : HasDerivAt (fun r ↦ ∫ z in a..r, source z) (source τ) τ :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a τ)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  exact (hprimitive.const_add (field a)).congr_of_eventuallyEq heq

end HalfLineFTC

end PDE.Analysis.Evolution
