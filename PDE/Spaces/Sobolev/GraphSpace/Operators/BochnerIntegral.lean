/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import PDE.Analysis.MeasureTheory.Lp.ContinuousExtension

/-!
# Time integration of local Sobolev graphs

Suppose a continuous field has an H^k representative on a spatial ball at each
instant, with a uniform Sobolev bound. Its time integral has the same spatial
regularity. The point is to construct a measurable curve in the Sobolev graph,
not to assume one: weak-derivative uniqueness makes the base-coordinate map
injective, and Mathlib's measurable embedding theorem lifts L² measurability.

For a compact time space, joint continuity gives a continuous curve in the
continuous functions on the closed spatial ball. Bounded linear maps then
identify its L² integral with the pointwise time integral. This allows the
spatial recovery estimates for a PDE source to pass to its time defect.
-/

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace Set
open scoped ENNReal Sobolev

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Sobolev spaces of finite Hilbert order are second countable. -/
private theorem hkSecondCountable : SecondCountableTopology (W^{k,2}(Ω)) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 Ω) :=
    Lp.SecondCountableTopology
  infer_instance

/-- The complete Sobolev graph is a Polish space. -/
private theorem hkPolish : PolishSpace (W^{k,2}(Ω)) := by
  have : SecondCountableTopology (W^{k,2}(Ω)) := hkSecondCountable
  infer_instance

/-- Base-coordinate measurability lifts to the Sobolev graph. -/
theorem stronglyMeasurable_of_wkpBaseCoordinateCLM {T : Type*} [MeasurableSpace T] (hΩ : IsOpen Ω)
    (f : T → W^{k,2}(Ω))
    (hf : StronglyMeasurable fun t ↦ wkpBaseCoordinateCLM (f t)) :
    StronglyMeasurable f := by
  have : SecondCountableTopology (W^{k,2}(Ω)) := hkSecondCountable
  have : PolishSpace (W^{k,2}(Ω)) := hkPolish
  let : MeasurableSpace (W^{k,2}(Ω)) := borel _
  have : BorelSpace (W^{k,2}(Ω)) := ⟨rfl⟩
  let : MeasurableSpace (DerivLp n 2 Ω) := borel _
  have : BorelSpace (DerivLp n 2 Ω) := ⟨rfl⟩
  have he := (wkpBaseCoordinateCLM (n := n) (m := k) (p := 2)
    (Ω := Ω)).continuous.measurableEmbedding (wkpBaseCoordinateCLM_injective hΩ)
  exact (he.measurable_comp_iff.mp hf.measurable).stronglyMeasurable

/-- Almost-everywhere base-coordinate measurability also lifts to the complete
Sobolev graph; no measurable higher derivative bundle needs to be supplied. -/
theorem aestronglyMeasurable_of_wkpBaseCoordinateCLM {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (hΩ : IsOpen Ω) (f : T → W^{k,2}(Ω))
    (hf : AEStronglyMeasurable (fun t ↦ wkpBaseCoordinateCLM (f t)) μ) :
    AEStronglyMeasurable f μ := by
  have : SecondCountableTopology (W^{k,2}(Ω)) := hkSecondCountable
  have : PolishSpace (W^{k,2}(Ω)) := hkPolish
  let : MeasurableSpace (W^{k,2}(Ω)) := borel _
  have : BorelSpace (W^{k,2}(Ω)) := ⟨rfl⟩
  let : MeasurableSpace (DerivLp n 2 Ω) := borel _
  have : BorelSpace (DerivLp n 2 Ω) := ⟨rfl⟩
  have he := (wkpBaseCoordinateCLM (n := n) (m := k) (p := 2)
    (Ω := Ω)).continuous.measurableEmbedding (wkpBaseCoordinateCLM_injective hΩ)
  exact (he.aemeasurable_comp_iff.mp hf.aemeasurable).aestronglyMeasurable

/-- Compact continuous fields give L2 curves whose integrals are their pointwise integrals. -/
private theorem compactLpCurve {T : Type*} [TopologicalSpace T] [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] (η : Measure T) [IsFiniteMeasure η]
    (r : ℝ) (f : T → ℝ^n → ℝ)
    (hf : Continuous (fun z : T × ℝ^n ↦ f z.1 z.2)) :
    ∃ F : T → DerivLp n 2 (Metric.ball 0 r), Continuous F ∧
      (∀ t, (F t : ℝ^n → ℝ) =ᵐ[domainMeasure n (Metric.ball 0 r)] f t) ∧
      ((∫ t, F t ∂η : DerivLp n 2 (Metric.ball 0 r)) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (Metric.ball 0 r)]
        fun x ↦ ∫ t, f t x ∂η := by
  let K := Metric.closedBall (0 : ℝ^n) r
  have hK : IsCompact K := isCompact_closedBall (0 : ℝ^n) r
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : IsFiniteMeasure ((domainMeasure n (Metric.ball 0 r)).restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let G : C(T, C(K, ℝ)) := (⟨fun z : T × K ↦ f z.1 z.2,
    hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩ :
      C(T × K, ℝ)).curry
  let L : C(K, ℝ) →L[ℝ] DerivLp n 2 (Metric.ball 0 r) :=
    (BoundedContinuousFunction.subtypeToLp (p := 2)
      (μ := domainMeasure n (Metric.ball 0 r)) hK.isClosed.measurableSet).comp
        ((ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ).toContinuousLinearEquiv
          |>.toContinuousLinearMap)
  have hL (g : C(K, ℝ)) : (L g : ℝ^n → ℝ) =ᵐ[domainMeasure n (Metric.ball 0 r)]
      Function.extend Subtype.val g (fun _ ↦ 0) :=
    BoundedContinuousFunction.coeFn_subtypeToLp (p := 2)
      (μ := domainMeasure n (Metric.ball 0 r)) hK.isClosed.measurableSet
      (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ g)
  refine ⟨fun t ↦ L (G t), L.continuous.comp G.continuous, ?_, ?_⟩
  · intro t
    filter_upwards [hL (G t), ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    have hxK : x ∈ K := Metric.ball_subset_closedBall hball
    exact Subtype.coe_injective.extend_apply _ _ (⟨x, hxK⟩ : K)
  · have hG : Integrable (fun t ↦ G t) η :=
      G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [L.integral_comp_comm hG]
    filter_upwards [hL (∫ t, G t ∂η), ae_restrict_mem measurableSet_ball] with x hx hball
    rw [hx]
    have hxK : x ∈ K := Metric.ball_subset_closedBall hball
    rw [Subtype.coe_injective.extend_apply _ _ (⟨x, hxK⟩ : K)]
    exact ContinuousMap.integral_apply hG (⟨x, hxK⟩ : K)

/-- Uniform Sobolev bounds pass to the time integral of a continuous field. -/
theorem exists_hk_integral_of_continuous {T : Type*} [TopologicalSpace T]
    [CompactSpace T]
    [MeasurableSpace T] [BorelSpace T] (η : Measure T) [IsFiniteMeasure η]
    (r : ℝ) (f : T → ℝ^n → ℝ)
    (hf : Continuous (fun z : T × ℝ^n ↦ f z.1 z.2)) (C : ℝ)
    (hSob : ∀ t, ∃ U : W^{k,2}(Metric.ball (0 : ℝ^n) r),
      baseRepresentative U =ᵐ[domainMeasure n (Metric.ball 0 r)] f t ∧ ‖U‖ ≤ C) :
    ∃ U : W^{k,2}(Metric.ball (0 : ℝ^n) r),
      baseRepresentative U =ᵐ[domainMeasure n (Metric.ball 0 r)]
        (fun x ↦ ∫ t, f t x ∂η) ∧ ‖U‖ ≤ C * η.real univ := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (DerivLp n 2 (Metric.ball 0 r)) :=
    Lp.SecondCountableTopology
  choose F hF hbound using hSob
  obtain ⟨G, hGcont, hG, hGint⟩ := compactLpCurve η r f hf
  have hbase (t : T) : wkpBaseCoordinateCLM (F t) = G t :=
    Lp.ext ((hF t).trans (hG t).symm)
  have hmeas : StronglyMeasurable F := by
    apply stronglyMeasurable_of_wkpBaseCoordinateCLM Metric.isOpen_ball
    simpa only [hbase] using hGcont.stronglyMeasurable
  have hFi : Integrable F η :=
    (integrable_const C).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨∫ t, F t ∂η, ?_, norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hbound)⟩
  change (wkpBaseCoordinateCLM (∫ t, F t ∂η) : ℝ^n → ℝ) =ᵐ[_] _
  rw [← (wkpBaseCoordinateCLM (n := n) (m := k) (p := 2)
    (Ω := Metric.ball 0 r)).integral_comp_comm hFi]
  simpa only [hbase] using hGint

end SobolevSpace.GraphSpace
