/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Bochner integration from measurable real-line representatives

Rational evaluations determine a continuous H¹ representative. They give a
continuous injection of the complete, separable Sobolev graph into a countable
product of real lines. Mathlib's measurable embedding theorem therefore
recovers strong measurability of a graph family from its rational evaluations.

Uniform graph bounds then give Bochner integrability on a finite measure
space, and bounded evaluation commutes with the integral. In particular,
neither continuity in the H¹ norm nor a spatial support bound is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- Measurability of rational evaluations suffices for strong measurability
of a family in the real-line H¹ graph. -/
theorem stronglyMeasurable_of_realLineRepresentative
    {α : Type*} [MeasurableSpace α] (F : α → W^{1,2}(ℝ^1))
    (hF : ∀ q : ℚ, Measurable (fun t ↦ realLineRepresentative (F t) q)) :
    StronglyMeasurable F := by
  have : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp 1 2 univ) := Lp.SecondCountableTopology
  have : SecondCountableTopology (W^{1,2}(ℝ^1)) := inferInstance
  have : PolishSpace (W^{1,2}(ℝ^1)) := inferInstance
  let : MeasurableSpace (W^{1,2}(ℝ^1)) := borel _
  have : BorelSpace (W^{1,2}(ℝ^1)) := ⟨rfl⟩
  let e : W^{1,2}(ℝ^1) → ℚ → ℝ := fun U q ↦ realLineRepresentative U q
  have he : Continuous e :=
    continuous_pi (fun q ↦ (realLineRepresentativeEvalCLM (q : ℝ)).continuous)
  have hinj : Function.Injective e := by
    intro U V hUV
    have hrep : realLineRepresentative U = realLineRepresentative V :=
      Rat.denseRange_cast.equalizer (continuous_realLineRepresentative U)
        (continuous_realLineRepresentative V) hUV
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    apply oneDimensionalPushforwardL2.injective
    apply Lp.ext
    exact (realLineCoordinate_ae_representative U).trans
      ((Filter.EventuallyEq.of_eq hrep).trans
        (realLineCoordinate_ae_representative V).symm)
  exact ((he.measurableEmbedding hinj).measurable_comp_iff.mp
    (Measurable.of_eval hF)).stronglyMeasurable

/-- Evaluation of the continuous H¹ representative commutes with a Bochner
integral, at every spatial point. -/
theorem realLineRepresentative_integral
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → W^{1,2}(ℝ^1)} (hF : Integrable F μ) :
    realLineRepresentative (∫ t, F t ∂μ) =
      (fun x ↦ ∫ t, realLineRepresentative (F t) x ∂μ) := by
  funext x
  exact ((realLineRepresentativeEvalCLM x).integral_comp_comm hF).symm

/-- A uniformly bounded family of H¹ representatives with measurable rational
evaluations admits an integrable graph lift. Its L² integral is the base
coordinate of the H¹ integral, whose representative is the pointwise integral. -/
theorem exists_integrable_h1_of_measurable_representative
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {D : α → ℝ → ℝ} {C : ℝ}
    (hD : ∀ q : ℚ, Measurable (fun t ↦ D t q))
    (hgraph : ∀ t, ∃ U : W^{1,2}(ℝ^1),
      ‖U‖ ≤ C ∧ realLineRepresentative U = D t) :
    ∃ F : α → W^{1,2}(ℝ^1), Integrable F μ ∧
      (∀ t, ‖F t‖ ≤ C ∧ realLineRepresentative (F t) = D t) ∧
      Integrable (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (F t)) μ ∧
      ‖∫ t, F t ∂μ‖ ≤ C * μ.real univ ∧
      realLineCoordinateCLM (baseIndex 1 1) (∫ t, F t ∂μ) =
        (∫ t, realLineCoordinateCLM (baseIndex 1 1) (F t) ∂μ) ∧
      realLineRepresentative (∫ t, F t ∂μ) = (fun x ↦ ∫ t, D t x ∂μ) := by
  choose F hbound hrep using hgraph
  have hmeas : StronglyMeasurable F :=
    stronglyMeasurable_of_realLineRepresentative F (by simpa only [hrep] using hD)
  have hF : Integrable F μ :=
    Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  refine ⟨F, hF, fun t ↦ ⟨hbound t, hrep t⟩,
    (realLineCoordinateCLM (baseIndex 1 1)).integrable_comp hF,
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound),
    ((realLineCoordinateCLM (baseIndex 1 1)).integral_comp_comm hF).symm, ?_⟩
  simp only [realLineRepresentative_integral hF, hrep]

end SobolevSpace.GraphSpace
