/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded continuous functions on a finite-measure subset

A bounded continuous function on a measurable subset extends by zero to an Lᵖ class on
the ambient space. Only the measure of the subset must be finite; its boundary need not
be regular. Continuity is used to establish measurability on the subset, not continuity
of the zero extension across its boundary.

The construction first takes the class for the restricted measure and then extends it
isometrically by zero. Its bounded linearity lets compact-family
differentiation in the supremum norm pass to Lᵖ without choosing point evaluations of
arbitrary Lᵖ classes.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace BoundedContinuousFunction

variable {α E : Type*} [TopologicalSpace α] [NormedAddCommGroup E] {s : Set α}

/-- Extension from a subtype takes the original value on that subtype. -/
private theorem subtype_extend_apply (f : s →ᵇ E) (x : s) :
    Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) x = f x :=
  Subtype.coe_injective.extend_apply _ _ x

/-- Outside the subtype the extension takes its prescribed zero value. -/
private theorem subtype_extend_eq_zero (f : s →ᵇ E) {x : α} (hx : x ∉ s) :
    Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

/-- The zero extension is bounded everywhere by the supremum norm on the subtype. -/
private theorem norm_subtype_extend_le (f : s →ᵇ E) (x : α) :
    ‖Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ s
  · calc
      ‖Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) x‖ = ‖f ⟨x, hx⟩‖ :=
        congrArg norm (subtype_extend_apply f ⟨x, hx⟩)
      _ ≤ ‖f‖ := f.norm_coe_le_norm ⟨x, hx⟩
  · rw [subtype_extend_eq_zero f hx, norm_zero]
    exact norm_nonneg f

variable [MeasurableSpace α] [BorelSpace α] [SecondCountableTopologyEither s E]
  {p : ℝ≥0∞} {μ : Measure α} [IsFiniteMeasure (μ.restrict s)]

/-- Measurability and the uniform bound put the extension in Lᵖ for the restricted measure. -/
theorem memLp_subtype_extend (hs : MeasurableSet s) (f : s →ᵇ E) :
    MemLp (Function.extend Subtype.val f (fun _ : α ↦ (0 : E)))
      p (μ.restrict s) := by
  have hmeas :
      StronglyMeasurable (Function.extend Subtype.val f (fun _ : α ↦ (0 : E))) :=
    (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend
      f.continuous.stronglyMeasurable stronglyMeasurable_const
  exact MemLp.of_bound hmeas.aestronglyMeasurable ‖f‖
    (Eventually.of_forall (norm_subtype_extend_le f))

/-- The Lᵖ class of the extension for the restricted measure. -/
def subtypeRestrictedLp (hs : MeasurableSet s) (f : s →ᵇ E) :
    Lp E p (μ.restrict s) :=
  (memLp_subtype_extend hs f).toLp _

variable [NormedSpace ℝ E] [Fact (1 ≤ p)]

/-- The restricted class is linear in the bounded continuous function. -/
def subtypeRestrictedLpLinear (hs : MeasurableSet s) :
    (s →ᵇ E) →ₗ[ℝ] Lp E p (μ.restrict s) where
  toFun := subtypeRestrictedLp hs
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_subtype_extend (p := p) (μ := μ) hs (f + g)).coeFn_toLp,
      (memLp_subtype_extend (p := p) (μ := μ) hs f).coeFn_toLp,
      (memLp_subtype_extend (p := p) (μ := μ) hs g).coeFn_toLp,
      Lp.coeFn_add (subtypeRestrictedLp (p := p) (μ := μ) hs f)
        (subtypeRestrictedLp (p := p) (μ := μ) hs g), ae_restrict_mem hs] with
      x hfg hf hg hadd hx
    rw [hadd, Pi.add_apply]
    dsimp only [subtypeRestrictedLp]
    rw [hfg, hf, hg]
    rw [subtype_extend_apply (f + g) ⟨x, hx⟩,
      subtype_extend_apply f ⟨x, hx⟩, subtype_extend_apply g ⟨x, hx⟩]
    rfl
  map_smul' c f := by
    change subtypeRestrictedLp (p := p) (μ := μ) hs (c • f) =
      c • subtypeRestrictedLp (p := p) (μ := μ) hs f
    apply Lp.ext
    filter_upwards [(memLp_subtype_extend (p := p) (μ := μ) hs (c • f)).coeFn_toLp,
      (memLp_subtype_extend (p := p) (μ := μ) hs f).coeFn_toLp,
      Lp.coeFn_smul c (subtypeRestrictedLp (p := p) (μ := μ) hs f),
      ae_restrict_mem hs] with x hcf hf hsmul hx
    rw [hsmul, Pi.smul_apply]
    dsimp only [subtypeRestrictedLp]
    rw [hcf, hf]
    rw [subtype_extend_apply (c • f) ⟨x, hx⟩,
      subtype_extend_apply f ⟨x, hx⟩]
    rfl

omit [NormedSpace ℝ E] [Fact (1 ≤ p)] in
/-- The restricted Lᵖ norm is bounded by the finite-measure constant times the sup norm. -/
theorem norm_subtypeRestrictedLp_le (hs : MeasurableSet s) (f : s →ᵇ E) :
    ‖subtypeRestrictedLp (p := p) (μ := μ) hs f‖ ≤
      (measureUnivNNReal (μ.restrict s) : ℝ) ^ p.toReal⁻¹ * ‖f‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg f)
  filter_upwards [(memLp_subtype_extend (p := p) (μ := μ) hs f).coeFn_toLp] with x hx
  dsimp only [subtypeRestrictedLp]
  rw [hx]
  exact norm_subtype_extend_le f x

/-- Extend a bounded continuous function on a measurable finite-measure subset by zero,
as a bounded linear map into the ambient Lᵖ space. -/
def subtypeToLp (hs : MeasurableSet s) : (s →ᵇ E) →L[ℝ] Lp E p μ :=
  (Lp.extendByZeroₗᵢ (𝕜 := ℝ) (p := p) (μ := μ) hs).toContinuousLinearMap.comp
    ((subtypeRestrictedLpLinear (p := p) (μ := μ) hs).mkContinuous
      ((measureUnivNNReal (μ.restrict s) : ℝ) ^ p.toReal⁻¹)
      (norm_subtypeRestrictedLp_le hs))

/-- The ambient Lᵖ class is represented by the pointwise zero extension from the subtype. -/
theorem coeFn_subtypeToLp (hs : MeasurableSet s) (f : s →ᵇ E) :
    (subtypeToLp (p := p) (μ := μ) hs f : α → E) =ᵐ[μ]
      Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) := by
  change (Lp.extendByZeroₗᵢ (𝕜 := ℝ) hs
      (subtypeRestrictedLp (p := p) (μ := μ) hs f) : α → E) =ᵐ[μ]
    Function.extend Subtype.val f (fun _ : α ↦ (0 : E))
  have hrestr :
      (subtypeRestrictedLp (p := p) (μ := μ) hs f : α → E) =ᵐ[μ.restrict s]
        Function.extend Subtype.val f (fun _ : α ↦ (0 : E)) :=
    (memLp_subtype_extend (p := p) (μ := μ) hs f).coeFn_toLp
  have hind := (ae_eq_restrict_iff_indicator_ae_eq hs).1 hrestr
  refine (Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) hs
    (subtypeRestrictedLp (p := p) (μ := μ) hs f)).trans ?_
  refine hind.trans (Eventually.of_forall ?_)
  intro x
  by_cases hx : x ∈ s
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, subtype_extend_eq_zero f hx]

end BoundedContinuousFunction
