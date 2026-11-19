/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Volterra
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous -- shake: keep

/-!
# Picard construction for measurable affine systems

The Picard operator `u ↦ x₀ + ∫ₐᵗ (A(s) u(s) + f(s)) ds` acts on continuous curves
`[a, b] → E` in a real Banach space, for a measurable bounded operator coefficient
`A` and integrable forcing `f`.
The Volterra factorial estimate makes a sufficiently high iterate contracting
on every finite interval, without a small-time hypothesis.
-/

@[expose] public section

noncomputable section

open AbsolutelyContinuousOnInterval Filter Function MeasureTheory Set
open scoped Topology

open PDE.Analysis.ODE

namespace PDE.Analysis.Evolution

section MeasurableAffinePicard

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

/-!
## The measurable affine Picard operator

The state space is the ordinary Mathlib continuous-map space
`C(Set.Icc a b, E)`. We extend a curve by clamping its time
argument to `[a,b]`, and extend the affine vector field by zero outside that
interval.  The latter extension is globally Bochner integrable, which makes
the Picard primitive continuous on all of `ℝ`.
-/

omit [CompleteSpace E] in
/--
A bounded strongly measurable operator applied to a continuous trajectory is
Bochner integrable on a compact time interval.
-/
theorem integrableOn_operator_apply_continuousOn
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {u : ℝ → E}
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (hu : ContinuousOn u (Set.Icc a b)) :
    IntegrableOn (fun t ↦ A t (u t)) (Set.Icc a b) volume := by
  have huMeas :
      AEStronglyMeasurable u (volume.restrict (Set.Icc a b)) :=
    hu.aestronglyMeasurable measurableSet_Icc
  have hAuMeas :
      AEStronglyMeasurable (fun t ↦ A t (u t))
        (volume.restrict (Set.Icc a b)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hA.prodMk huMeas)
  obtain ⟨R, hR⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hu
  have hR_nonnegative : 0 ≤ R :=
    (norm_nonneg (u a)).trans (hR a ⟨le_rfl, hab⟩)
  apply IntegrableOn.of_bound measure_Icc_lt_top hAuMeas
    ((MA : ℝ) * R)
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Filter.Eventually.of_forall fun t ht ↦ by
    calc
      ‖A t (u t)‖ ≤ ‖A t‖ * ‖u t‖ :=
        (A t).le_opNorm _
      _ ≤ (MA : ℝ) * R :=
        mul_le_mul (hA_bound t ht) (hR t ht)
          (norm_nonneg _) MA.2

/--
The affine vector field along a curve, extended by zero outside `[a,b]`.

The indicator turns measurability and boundedness on `[a, b]` into global Bochner
integrability, and the coefficients are only evaluated on `[a, b]`.
-/
def affineIntegrandOn {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (u : C(Set.Icc a b, E)) : ℝ → E :=
  Set.indicator (Set.Icc a b)
    (fun t ↦ A t (Set.IccExtend hab u t) + f t)

omit [CompleteSpace E] in
/-- The zero-extended affine integrand `t ↦ A(t) u(t) + f(t)` is a.e. strongly measurable
on `ℝ` as soon as `A` and `f` are a.e. strongly measurable on `[a, b]`; the curve `u` is
continuous, and operator application is a continuous bilinear map. -/
theorem aestronglyMeasurable_affineIntegrandOn
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc a b)))
    (u : C(Set.Icc a b, E)) :
    AEStronglyMeasurable (affineIntegrandOn hab A f u) volume := by
  have hu : AEStronglyMeasurable (Set.IccExtend hab u)
      (volume.restrict (Set.Icc a b)) :=
    (u.continuous.Icc_extend' (h := hab)).aestronglyMeasurable.restrict
  have happly : AEStronglyMeasurable
      (fun t ↦ A t (Set.IccExtend hab u t))
        (volume.restrict (Set.Icc a b)) :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hA hu
  exact (aestronglyMeasurable_indicator_iff measurableSet_Icc).2
    (happly.add hf)

omit [CompleteSpace E] in
/-- The zero-extended affine integrand is Bochner integrable on `ℝ`. The operator term is
bounded by `M_A ‖u‖_∞` on the compact interval and the forcing is integrable there, so the
indicator of `[a, b]` makes the sum globally integrable. -/
theorem integrable_affineIntegrandOn
    {a b : ℝ} (hab : a ≤ b)
    {A : ℝ → E →L[ℝ] E} {f : ℝ → E}
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (u : C(Set.Icc a b, E)) :
    Integrable (affineIntegrandOn hab A f u) volume := by
  let Au : ℝ → E := fun t ↦ A t (Set.IccExtend hab u t)
  have hAuMeas : AEStronglyMeasurable Au
      (volume.restrict (Set.Icc a b)) := by
    have hu : AEStronglyMeasurable (Set.IccExtend hab u)
        (volume.restrict (Set.Icc a b)) :=
      (u.continuous.Icc_extend' (h := hab)).aestronglyMeasurable.restrict
    exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      hA hu
  have hAuBound :
      ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        ‖Au t‖ ≤ (MA : ℝ) * ‖u‖ := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t
    intro ht
    calc
      ‖Au t‖ ≤ ‖A t‖ * ‖Set.IccExtend hab u t‖ :=
        (A t).le_opNorm _
      _ ≤ (MA : ℝ) * ‖u‖ := by
        exact mul_le_mul (hA_bound t ht)
          (by
            rw [Set.IccExtend_of_mem hab u ht]
            exact ContinuousMap.norm_coe_le_norm u ⟨t, ht⟩)
          (norm_nonneg _) MA.2
  have hAu : IntegrableOn Au (Set.Icc a b) volume :=
    IntegrableOn.of_bound measure_Icc_lt_top hAuMeas
      ((MA : ℝ) * ‖u‖) hAuBound
  let raw : ℝ → E := fun t ↦ Au t + f t
  have hrawOn : IntegrableOn raw (Set.Icc a b) volume :=
    hAu.add hf
  change Integrable (Set.indicator (Set.Icc a b) raw) volume
  exact hrawOn.integrable_indicator measurableSet_Icc

/-- The Picard integral operator on ordinary continuous curves. -/
def affinePicardMap
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) :
    C(Set.Icc a b, E) → C(Set.Icc a b, E) :=
  fun u ↦
    let g := affineIntegrandOn hab A f u
    let hg := integrable_affineIntegrandOn hab hA hf MA hA_bound u
    ⟨fun t ↦ x₀ + ∫ s in a..t.1, g s,
      continuous_const.add
        ((hg.continuous_primitive a).comp continuous_subtype_val)⟩

omit [CompleteSpace E] in
/-- Evaluation of the Picard map: `(Φ u)(t) = x₀ + ∫ₐᵗ (A(s) u(s) + f(s)) ds`, with the
integrand extended by zero outside `[a, b]`. -/
@[simp]
theorem affinePicardMap_apply
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) (u : C(Set.Icc a b, E)) (t : Set.Icc a b) :
    affinePicardMap hab A f hA hf MA hA_bound x₀ u t =
      x₀ + ∫ s in a..t.1, affineIntegrandOn hab A f u s :=
  rfl

omit [CompleteSpace E] in
/--
Pointwise Lipschitz estimate for the zero-extended affine integrand.  The
forcing cancels, leaving only the operator coefficient.
-/
theorem norm_affineIntegrandOn_sub_le
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E) (MA : NNReal)
    (hA_bound : ∀ s ∈ Set.Icc a b, ‖A s‖ ≤ MA)
    (u v : C(Set.Icc a b, E)) :
    ‖affineIntegrandOn hab A f u t -
        affineIntegrandOn hab A f v t‖ ≤
      (MA : ℝ) * dist (u ⟨t, ht⟩) (v ⟨t, ht⟩) := by
  have hdiff :
      affineIntegrandOn hab A f u t -
          affineIntegrandOn hab A f v t =
        A t (u ⟨t, ht⟩ - v ⟨t, ht⟩) := by
    simp [affineIntegrandOn, ht, Set.IccExtend,
      Set.projIcc_of_mem hab ht, map_sub]
  rw [hdiff, dist_eq_norm]
  calc
    ‖A t (u ⟨t, ht⟩ - v ⟨t, ht⟩)‖ ≤
        ‖A t‖ * ‖u ⟨t, ht⟩ - v ⟨t, ht⟩‖ :=
      (A t).le_opNorm _
    _ ≤ (MA : ℝ) * ‖u ⟨t, ht⟩ - v ⟨t, ht⟩‖ := by
      gcongr
      exact hA_bound t ht

omit [CompleteSpace E] in
/--
Factorial pointwise estimate for the iterated affine Picard operator.

This is the Volterra estimate

`dist(P^[n] u(t), P^[n] v(t))
  ≤ (MA * |t-a|)^n / n! * dist(u,v)`.

Its factorial denominator is what removes the local small-time restriction:
although one Picard step need not contract on a long interval, a sufficiently
high iterate always does.
-/
theorem dist_iterate_affinePicardMap_apply_le
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) (u v : C(Set.Icc a b, E)) (n : ℕ)
    (t : Set.Icc a b) :
    let P := affinePicardMap hab A f hA hf MA hA_bound x₀
    dist ((P^[n]) u t) ((P^[n]) v t) ≤
      (((MA : ℝ) * |t.1 - a|) ^ n / n.factorial) * dist u v := by
  exact dist_iterate_volterra_apply_le ⟨_, le_rfl, hab⟩
    (affinePicardMap hab A f hA hf MA hA_bound x₀) (affineIntegrandOn hab A f) x₀ MA
    (fun u ↦ (integrable_affineIntegrandOn hab hA hf MA hA_bound u).integrableOn)
    (affinePicardMap_apply hab A f hA hf MA hA_bound x₀)
    (fun u v t ↦ norm_affineIntegrandOn_sub_le hab t.2 A f MA hA_bound u v) u v n t

omit [CompleteSpace E] in
/-- Uniform-norm version of the factorial Picard estimate. -/
theorem dist_iterate_affinePicardMap_le
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) (u v : C(Set.Icc a b, E)) (n : ℕ) :
    let P := affinePicardMap hab A f hA hf MA hA_bound x₀
    dist ((P^[n]) u) ((P^[n]) v) ≤
      (((MA : ℝ) * (b - a)) ^ n / n.factorial) * dist u v := by
  exact dist_iterate_volterra_le ⟨_, le_rfl, hab⟩
    (affinePicardMap hab A f hA hf MA hA_bound x₀) (affineIntegrandOn hab A f) x₀ MA
    (fun u ↦ (integrable_affineIntegrandOn hab hA hf MA hA_bound u).integrableOn)
    (affinePicardMap_apply hab A f hA hf MA hA_bound x₀)
    (fun u v t ↦ norm_affineIntegrandOn_sub_le hab t.2 A f MA hA_bound u v) u v n

omit [CompleteSpace E] in
/--
Some iterate of the affine Picard operator is contracting on every finite
interval.  The contraction constant is

`((MA * (b-a))^n) / n!`

for a sufficiently large `n`.
-/
theorem exists_contractingWith_iterate_affinePicardMap
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) :
    let P := affinePicardMap hab A f hA hf MA hA_bound x₀
    ∃ (n : ℕ) (C : NNReal), ContractingWith C (P^[n]) := by
  exact exists_contractingWith_iterate_volterra ⟨_, le_rfl, hab⟩
    (affinePicardMap hab A f hA hf MA hA_bound x₀) (affineIntegrandOn hab A f) x₀ MA
    (fun u ↦ (integrable_affineIntegrandOn hab hA hf MA hA_bound u).integrableOn)
    (affinePicardMap_apply hab A f hA hf MA hA_bound x₀)
    (fun u v t ↦ norm_affineIntegrandOn_sub_le hab t.2 A f MA hA_bound u v)

/--
Global fixed-point existence and uniqueness for the measurable affine
Picard operator on an arbitrary finite interval.

Some iterate of the operator is a contraction, so `b - a` may be arbitrary.
-/
theorem existsUnique_isFixedPt_affinePicardMap
    {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → E →L[ℝ] E) (f : ℝ → E)
    (hA : AEStronglyMeasurable A (volume.restrict (Set.Icc a b)))
    (hf : IntegrableOn f (Set.Icc a b) volume)
    (MA : NNReal)
    (hA_bound : ∀ t ∈ Set.Icc a b, ‖A t‖ ≤ MA)
    (x₀ : E) :
    ∃! u : C(Set.Icc a b, E),
      IsFixedPt
        (affinePicardMap hab A f hA hf MA hA_bound x₀) u := by
  exact existsUnique_isFixedPt_volterra ⟨_, le_rfl, hab⟩
    (affinePicardMap hab A f hA hf MA hA_bound x₀) (affineIntegrandOn hab A f) x₀ MA
    (fun u ↦ (integrable_affineIntegrandOn hab hA hf MA hA_bound u).integrableOn)
    (affinePicardMap_apply hab A f hA hf MA hA_bound x₀)
    (fun u v t ↦ norm_affineIntegrandOn_sub_le hab t.2 A f MA hA_bound u v)

end MeasurableAffinePicard

end PDE.Analysis.Evolution
