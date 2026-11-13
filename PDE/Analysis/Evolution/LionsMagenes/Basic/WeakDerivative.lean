/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous

/-!
# Weak derivatives of time primitives

The analytic calculus for the time primitives of Lions–Magenes theory:
absolute continuity and almost-everywhere derivative formulas, integrated
product and quadratic-form rules, and the distributional weak-derivative
identities for Bochner primitives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.2, proof of Theorem 4 (the test function `v`, the
  identity (39) and the forms `C` and `D`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open IsUnifLocDoublingMeasure
open scoped InnerProductSpace Interval Topology

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Bochner integral representation gives an absolutely continuous
trajectory. -/
theorem absolutelyContinuousOnInterval_of_eq_add_integral
    {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {w dw : ℝ → X} {a b : ℝ}
    (hdw : IntervalIntegrable dw volume a b)
    (hw : ∀ t ∈ uIcc a b, w t = w a + ∫ r in a..t, dw r) :
    AbsolutelyContinuousOnInterval w a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦
    ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have htendsto : Tendsto
      (fun E ↦ ∫⁻ x in s E, ‖dw x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp hdw |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
        _ _)
  have hprim : AbsolutelyContinuousOnInterval (fun t ↦ ∫ r in a..t, dw r) a b := by
    refine squeeze_zero' (.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_
      (ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp htendsto)
    have heventually : ∀ᶠ E : ℕ × (ℕ → ℝ × ℝ) in
        AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
          𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
        E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
      eventually_inf_principal.mpr (by simp)
    filter_upwards [heventually] with ⟨n, I⟩ hE
    obtain ⟨hI, hdisj⟩ := Set.mem_ofPred_eq ▸ hE
    simp only [Function.comp_apply, s]
    rw [← integral_norm_eq_lintegral_enorm (hdw.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hdisj]
    · refine Finset.sum_le_sum fun i hi ↦ ?_
      rw [dist_eq_norm,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' hdw; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' hdw; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
            hE (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, norm_neg,
        intervalIntegral.norm_intervalIntegral_eq]
      exact norm_integral_le_integral_norm _
    · intro i hi
      have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin
        hE (Finset.mem_range.mp hi)
      rw [IntegrableOn, Measure.restrict_restrict_of_subset hsubset]
      exact IntegrableOn.mono_set hdw.def'.norm hsubset |>.integrable
  exact ((LipschitzWith.const (w a)).lipschitzOnWith.absolutelyContinuousOnInterval.add
    hprim).congr fun t ht ↦ (hw t ht).symm

/--
The backward primitive is absolutely continuous on the time interval.

This is the regularity used in the backward-test-function argument of
Evans §7.2.2, Theorem 4. In particular, the identity `v'(t) = -u(t)` is interpreted
almost everywhere and is strong enough for scalar integration by parts,
without assuming that the original `L²` trajectory is pointwise
differentiable.
-/
theorem absolutelyContinuousOnInterval_backwardTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} {a b s : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval
      (backwardTimePrimitive u s) a b := by
  apply absolutelyContinuousOnInterval_of_eq_add_integral hu.neg
  intro t ht
  have hsub :=
    intervalIntegral.integral_interval_sub_left
      (hu.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs))
      (hu.mono_set
        (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht))
  change (∫ r in t..s, u r) =
    (∫ r in a..s, u r) + ∫ r in a..t, -u r
  rw [intervalIntegral.integral_neg]
  simpa only [sub_eq_add_neg] using hsub.symm

/--
The backward primitive has the expected strong derivative almost
everywhere:

`d/dt (∫_t^s u(r) dr) = -u(t)`.

This is a norm-valued statement in an arbitrary Banach space.  It connects
Bochner `L²` trajectories to the classical chain rule for the nonautonomous
quadratic energy used in weak-wave uniqueness.
-/
theorem ae_hasDerivAt_backwardTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : ℝ → E} {a b s : ℝ}
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ uIcc a b) :
    ∀ᵐ t ∂volume.restrict (uIoc a b),
      HasDerivAt (backwardTimePrimitive u s) (-u t) t := by
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hu.ae_hasDerivAt_integral] with t ht htI
  convert (ht (uIoc_subset_uIcc htI) s hs).neg using 1
  funext y
  rw [backwardTimePrimitive, intervalIntegral.integral_symm]
  rfl

/-- An integral primitive is absolutely continuous on every compact
interval, even when its chosen base point lies outside that interval.  The
standard library theorem uses a base point inside the interval; additivity
of interval integrals removes that inessential restriction. -/
theorem absolutelyContinuousOnInterval_intervalIntegral_any_base
    {q : ℝ → ℝ} (hq : Integrable q (volume : Measure ℝ))
    (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ r in c..t, q r) a b :=
  absolutelyContinuousOnInterval_of_eq_add_integral hq.intervalIntegrable fun _ _ ↦
    (intervalIntegral.integral_add_adjacent_intervals hq.intervalIntegrable
      hq.intervalIntegrable).symm

/-- The derivative of an integral primitive equals its integrand almost
everywhere on every compact interval, with no restriction on the base
point. -/
theorem ae_hasDerivAt_intervalIntegral_any_base
    {q : ℝ → ℝ} (hq : Integrable q (volume : Measure ℝ))
    (c a b : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt (fun x ↦ ∫ r in c..x, q r) (q t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hq.locallyIntegrable] with t ht _
    using ht c

/--
Product rule and integration by parts for two Bochner integral
representatives.

Let `c(t) ∈ E*` and `u(t) ∈ E` have interval-integrable derivatives `dc`
and `du`, respectively.  If both curves satisfy their endpoint-inclusive
fundamental theorem of calculus on `[[a,b]]`, then

`c(b)(u(b)) - c(a)(u(a))
  = ∫ₐᵇ (dc(t)(u(t)) + c(t)(du(t))) dt`.

The theorem is deliberately stated for a general Banach space.  Its proof
does not differentiate arbitrary almost-everywhere representatives:
it replaces both curves by their canonical Bochner primitives, applies the
ordinary continuous-linear-map product rule almost everywhere, and only then
uses the pointwise representative identities.  Evans's backward primitive
test for weak wave equations needs this low-regularity integration by parts.
-/
theorem integrated_duality_product_rule
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c dc : ℝ → StrongDual ℝ E} {u du : ℝ → E} {a b : ℝ}
    (hdc : IntervalIntegrable dc volume a b)
    (hdu : IntervalIntegrable du volume a b)
    (hc : ∀ t ∈ Set.uIcc a b,
      c t = c a + ∫ r in a..t, dc r)
    (hu : ∀ t ∈ Set.uIcc a b,
      u t = u a + ∫ r in a..t, du r)
    (hcDeriv : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt c (dc t) t)
    (huDeriv : ∀ᵐ t ∂volume, t ∈ Set.uIcc a b →
      HasDerivAt u (du t) t) :
    c b (u b) - c a (u a) =
      ∫ t in a..b, dc t (u t) + c t (du t) := by
  have hpairAC : AbsolutelyContinuousOnInterval (fun t ↦ c t (u t)) a b :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply
      (absolutelyContinuousOnInterval_of_eq_add_integral hdc hc)
      (absolutelyContinuousOnInterval_of_eq_add_integral hdu hu)
  rw [← hpairAC.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hcDeriv, huDeriv] with t hct hut htI
  exact ((hct (uIoc_subset_uIcc htI)).clm_apply (hut (uIoc_subset_uIcc htI))).deriv

/--
Integrated chain rule for a symmetric nonautonomous quadratic form.

Let `A(t) : E → E*` and `v(t) : E` be absolutely continuous, with
almost-everywhere derivatives `Adot` and `dv`.  If `A(t)` is symmetric, then

`d/dt [A(t)(v(t),v(t))]
  = Adot(t)(v(t),v(t)) + 2 A(t)(v(t),dv(t))`

almost everywhere.  Integrating gives the exact endpoint identity below.

The `Adot` term is indispensable.  Omitting it would silently replace
Evans's time-dependent principal coefficients by an autonomous operator.
The theorem is phrased for continuous linear maps into the strong dual, so
it applies directly to the variational forms used in Chapters 6 and 7.
-/
theorem integrated_symmetric_quadratic_form_chain_rule
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A Adot : ℝ → E →L[ℝ] StrongDual ℝ E}
    {v dv : ℝ → E} {a b : ℝ}
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hvAC : AbsolutelyContinuousOnInterval v a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      HasDerivAt A (Adot t) t)
    (hvderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      HasDerivAt v (dv t) t)
    (hAsymm : ∀ t ∈ Set.uIcc a b, ∀ x y : E,
      A t x y = A t y x) :
    A b (v b) (v b) - A a (v a) (v a) =
      ∫ t in a..b,
        Adot t (v t) (v t) + 2 * A t (v t) (dv t) := by
  have hquadraticAC : AbsolutelyContinuousOnInterval (fun t ↦ A t (v t) (v t)) a b :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply
      (PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply hAAC hvAC) hvAC
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ :=
    (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ)
  rw [← hquadraticAC.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae_restrict ?_
  filter_upwards [hAderiv, hvderiv, ae_restrict_mem measurableSet_uIoc] with t hAt hvt ht
  rw [((hAt.clm_apply hvt).clm_apply hvt).deriv, add_apply,
    hAsymm t (uIoc_subset_uIcc ht) (dv t) (v t)]
  ring

/--
Nonautonomous quadratic-energy identity for Evans's backward primitive.

For

`v(t) = ∫ₜˢ u(r) dr`,

the Banach-valued Lebesgue differentiation theorem gives `v'(t) = -u(t)`
almost everywhere.  Substitution into the symmetric quadratic-form chain
rule yields

`A(b)(v(b),v(b)) - A(a)(v(a),v(a))
  = ∫ₐᵇ [Ȧ(t)(v(t),v(t)) - 2 A(t)(v(t),u(t))] dt`.

This is the abstract form of the identity for `B[v, v; t]` in the proof of Evans
§7.2.2, Theorem 4, where the time derivatives of the coefficients enter through
`D[v, v; t]`. In particular, the `Ȧ` contribution is retained;
dropping it would only be valid for time-independent principal
coefficients.
-/
theorem integrated_symmetric_quadratic_form_chain_rule_backwardTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A Adot : ℝ → E →L[ℝ] StrongDual ℝ E}
    {u : ℝ → E} {a b s : ℝ}
    (hAAC : AbsolutelyContinuousOnInterval A a b)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a b),
      HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc a b, ∀ x y : E,
      A t x y = A t y x)
    (hu : IntervalIntegrable u volume a b)
    (hs : s ∈ Set.uIcc a b) :
    A b (backwardTimePrimitive u s b) (backwardTimePrimitive u s b) -
        A a (backwardTimePrimitive u s a) (backwardTimePrimitive u s a) =
      ∫ t in a..b,
        Adot t (backwardTimePrimitive u s t)
            (backwardTimePrimitive u s t) -
          2 * A t (backwardTimePrimitive u s t) (u t) := by
  rw [integrated_symmetric_quadratic_form_chain_rule (dv := fun t ↦ -u t) hAAC
    (absolutelyContinuousOnInterval_backwardTimePrimitive hu hs) hAderiv
    (ae_hasDerivAt_backwardTimePrimitive hu hs) hAsymm]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  simp only [map_neg]
  ring

/--
The principal-form calculation for a backward time primitive, as in the proof of
Evans §7.2.2, Theorem 4.

For `v(t) = ∫ₜˢ u(r) dr`, symmetry and `v(s) = 0` turn the
nonautonomous quadratic-form chain rule into

`∫ₐˢ A(t)(u(t),v(t)) dt
  = 1/2 A(a)(v(a),v(a))
      + 1/2 ∫ₐˢ Ȧ(t)(v(t),v(t)) dt`.

The two explicit integrability assumptions are scalar consequences of uniform
form bounds; this general Lions–Magenes lemma does not assume a particular PDE
coefficient class.  In wave applications those assumptions are discharged from the
coefficient bounds and the `L²` regularity of `u`.
-/
theorem integral_symmetric_form_backwardTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A Adot : ℝ → E →L[ℝ] StrongDual ℝ E}
    {u : ℝ → E} {a s : ℝ}
    (hAAC : AbsolutelyContinuousOnInterval A a s)
    (hAderiv : ∀ᵐ t ∂volume.restrict (Set.uIoc a s),
      HasDerivAt A (Adot t) t)
    (hAsymm : ∀ t ∈ Set.uIcc a s, ∀ x y : E,
      A t x y = A t y x)
    (hu : IntervalIntegrable u volume a s)
    (hAdotIntegrable :
      IntervalIntegrable
        (fun t ↦
          Adot t (backwardTimePrimitive u s t)
            (backwardTimePrimitive u s t))
        volume a s)
    (hAIntegrable :
      IntervalIntegrable
        (fun t ↦
          A t (u t) (backwardTimePrimitive u s t))
        volume a s) :
    (∫ t in a..s,
        A t (u t) (backwardTimePrimitive u s t)) =
      (1 / 2 : ℝ) *
          A a (backwardTimePrimitive u s a)
            (backwardTimePrimitive u s a) +
        (1 / 2 : ℝ) *
          ∫ t in a..s,
            Adot t (backwardTimePrimitive u s t)
              (backwardTimePrimitive u s t) := by
  have hchain := integrated_symmetric_quadratic_form_chain_rule_backwardTimePrimitive hAAC
    hAderiv hAsymm hu Set.right_mem_uIcc
  have hswap : (∫ t in a..s, A t (backwardTimePrimitive u s t) (u t)) =
      ∫ t in a..s, A t (u t) (backwardTimePrimitive u s t) :=
    intervalIntegral.integral_congr fun t ht ↦ hAsymm t ht _ _
  rw [intervalIntegral.integral_sub hAdotIntegrable
      ((IntervalIntegrable.congr (fun t ht ↦ hAsymm t (Set.uIoc_subset_uIcc ht) _ _)
        hAIntegrable).const_mul 2),
    intervalIntegral.integral_const_mul, hswap] at hchain
  simp only [backwardTimePrimitive_terminal, map_zero, zero_sub] at hchain
  linarith

/--
A Bochner-integrable trajectory is the Banach-valued distributional
derivative of each of its forward integral primitives:

`d/dt (x₀ + ∫ r in c..t, g r) = g(t)`.

The primitive is absolutely continuous on every compact interval and, by the
Lebesgue differentiation theorem, has derivative `g` almost everywhere, so
`HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval` applies.  Stating the result
for an arbitrary normed space avoids a dual-space-only primitive calculus and
is the common foundation for both Lions–Magenes evolutions and Evans's
backward wave test.
-/
theorem hasWeakTimeDerivativeOn_add_intervalIntegral
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E}
    (hg : Integrable g (volume : Measure ℝ))
    (x₀ : E) (c : ℝ) :
    HasWeakTimeDerivativeOn Set.univ
      (fun t ↦ x₀ + ∫ r in c..t, g r) g := by
  have hFcont : Continuous (fun t ↦ x₀ + ∫ r in c..t, g r) :=
    continuous_const.add (intervalIntegral.continuous_primitive (fun _ _ ↦ hg.intervalIntegrable) c)
  refine .of_absolutelyContinuousOnInterval hFcont.locallyIntegrable hg.locallyIntegrable
    (fun a b ↦ absolutelyContinuousOnInterval_of_eq_add_integral hg.intervalIntegrable
      fun t _ ↦ ?_) ?_
  · rw [add_assoc, intervalIntegral.integral_add_adjacent_intervals hg.intervalIntegrable
      hg.intervalIntegrable]
  · filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg.locallyIntegrable] with t ht
    exact (ht c).const_add x₀

/--
Evans's backward primitive has weak derivative `-u` on the real line:

`d/dt (∫ r in t..s, u r) = -u(t)`.

This is obtained from the general forward-primitive theorem by reversing the
oriented interval.  It gives the weak derivative of the backward primitive in an arbitrary
Banach space.
-/
theorem hasWeakTimeDerivativeOn_backwardTimePrimitive
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {u : ℝ → E}
    (hu : Integrable u (volume : Measure ℝ)) (s : ℝ) :
    HasWeakTimeDerivativeOn Set.univ
      (backwardTimePrimitive u s) (fun t ↦ -u t) := by
  refine (hasWeakTimeDerivativeOn_add_intervalIntegral hu.neg (0 : E) s).congr_ae
    (.of_forall fun t ↦ ?_) (.of_forall fun _ ↦ rfl)
  simp only [zero_add, backwardTimePrimitive, Pi.neg_apply, intervalIntegral.integral_neg]
  exact (intervalIntegral.integral_symm s t).symm

/-- A Bochner-integrable dual trajectory is the distributional derivative
of each of its integral primitives.  This is the converse direction to the
integrated fundamental theorem of calculus and is used to remove
the junction points in reflected endpoint extensions. -/
theorem hasWeakTimeDerivativeOn_add_dualPrimitive
    {g : ℝ → StrongDual ℝ V}
    (hg : Integrable g (volume : Measure ℝ))
    (x₀ : StrongDual ℝ V) (c : ℝ) :
    HasWeakTimeDerivativeOn Set.univ
      (fun t ↦ x₀ + dualPrimitive g c t) g := by
  simpa only [dualPrimitive] using
    (hasWeakTimeDerivativeOn_add_intervalIntegral hg x₀ c)

end PDE.Analysis.Evolution
