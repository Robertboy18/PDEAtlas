/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Naturality
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Scalar
public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Boundary.C1
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Boundary restriction and finite-exponent trace compatibility

Restricting the closure representative to the frontier gives a continuous linear boundary
trace with Lipschitz values. It is independent of the whole-space extension.

On bounded C¹ graph domains this restriction agrees with the finite-exponent
surface trace whenever the two Sobolev classes have the same physical base. The proof
uses the scalar continuous-representative theorem and codomain naturality. Essential
separability, supplied by strong measurability, permits the dual tests to identify the
Banach-valued functions almost everywhere. No separability or Radon–Nikodym assumption
on the Banach space, and no W¹,∞ smooth norm density, is needed.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace Boundary.Geometry.SurfaceMeasure

variable {n : ℕ} {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The endpoint boundary trace is restriction of the closure representative
to the frontier, with values in the usual bounded continuous function space. -/
def boundaryLipschitzTrace
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) :
    W^{1,∞}(Ω; F) →L[ℝ] (frontier (Ω : Set ℝ^n) →ᵇ F) :=
  (BoundedContinuousFunction.compContinuousCLM F ℝ
    ⟨Set.inclusion frontier_subset_closure, continuous_inclusion _⟩).comp
      (closureLipschitzEmbedding E)

/-- The boundary value is evaluated on the whole-space Lipschitz representative. -/
@[simp] theorem boundaryLipschitzTrace_apply
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (U : W^{1,∞}(Ω; F)) (x : frontier (Ω : Set ℝ^n)) :
    boundaryLipschitzTrace E U x = lipschitzRepresentative (E U) x := rfl

/-- The boundary inherits the Euclidean Lipschitz bound with its extension constant. -/
theorem lipschitzWith_boundaryLipschitzTrace
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F)) :
    LipschitzWith (n * ‖E‖₊ * ‖U‖₊) (boundaryLipschitzTrace E U) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (lipschitzWith_closureLipschitzEmbedding_norm E U).dist_le_mul
    ⟨x, frontier_subset_closure x.property⟩ ⟨y, frontier_subset_closure y.property⟩

/-- Restriction to the frontier does not increase the bound for the closure representative. -/
theorem norm_boundaryLipschitzTrace_apply_le
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) (U : W^{1,∞}(Ω; F)) :
    ‖boundaryLipschitzTrace E U‖ ≤ ‖E‖ * ‖U‖ :=
  (BoundedContinuousFunction.norm_compContinuous_le (closureLipschitzEmbedding E U)
    ⟨Set.inclusion frontier_subset_closure, continuous_inclusion _⟩).trans
      (norm_closureLipschitzEmbedding_apply_le E U)

/-- The continuous boundary trace has norm at most the chosen extension norm. -/
theorem norm_boundaryLipschitzTrace_le
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F)) :
    ‖boundaryLipschitzTrace E‖ ≤ ‖E‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E)
    (norm_boundaryLipschitzTrace_apply_le E)

/-- The boundary trace is independent of the choice of bounded Sobolev extension. -/
theorem boundaryLipschitzTrace_eq
    (E D : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U)
    (hD : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (D U) = U) :
    boundaryLipschitzTrace E = boundaryLipschitzTrace D := by
  unfold boundaryLipschitzTrace
  rw [closureLipschitzEmbedding_eq E D hE hD]

/-- Any continuous representative on the closure has these same pointwise boundary values. -/
theorem boundaryLipschitzTrace_eq_of_continuousOn
    (E : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U)
    (U : W^{1,∞}(Ω; F)) {f : ℝ^n → F}
    (hf : ContinuousOn f (closure (Ω : Set ℝ^n)))
    (hU : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f)
    (x : frontier (Ω : Set ℝ^n)) :
    boundaryLipschitzTrace E U x = f x :=
  lipschitzRepresentative_eqOn_closure (E U) U (hE U) hf hU
    (frontier_subset_closure x.property)

section SurfaceTrace

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Continuous ambient representatives agree with the Banach-valued surface trace.
Local C¹ graph geometry supplies the scalar inward approximation theorem; strong
measurability supplies the separable range needed to pass from dual tests to AE equality. -/
theorem Trace.C1.traceLp_coeFn_ae_of_continuous
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set ℝ^(m + 1)))
    (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F)) {f : ℝ^(m + 1) → F}
    (hf : Continuous f)
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] f) :
    (Trace.C1.traceLp p hp U : ℝ^(m + 1) → F)
      =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] f := by
  obtain ⟨P⟩ := Approximation.UpToBoundary.exists_inwardPartition Ω.isOpen hΩ.bounded
    (Boundary.hasC1Boundary_of_local_graph hgraph)
  have hdual (L : F →L[ℝ] ℝ) :
      (fun x ↦ L (Trace.C1.traceLp p hp U x))
        =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] fun x ↦ L (f x) := by
    have hbase := (mapCLM_apply_ae L U (baseIndex (m + 1) 1)).trans (hU.fun_comp L)
    have h := SobolevSpace.Trace.C1.traceLp_eq_ae_of_continuousOn P p
      (scalarEquiv (mapCLM L U)) (L.continuous.comp hf).continuousOn hbase
    rw [← Trace.C1.traceLp_eq_scalar_traceLp hp (mapCLM L U),
      Trace.C1.traceLp_mapCLM hp L U] at h
    exact (L.coeFn_compLpL (Trace.C1.traceLp p hp U)).symm.trans h
  have hmeas := (Lp.aestronglyMeasurable (Trace.C1.traceLp p hp U)).sub
    hf.stronglyMeasurable.aestronglyMeasurable
  obtain ⟨s, hs, hmem⟩ := hmeas.isSeparable_ae_range
  have hzero := ae_eq_zero_of_forall_dual_of_isSeparable ℝ hs (fun L ↦ ?_) hmem
  · filter_upwards [hzero] with x hx
    exact sub_eq_zero.mp hx
  · filter_upwards [hdual L] with x hx
    simpa only [Pi.sub_apply, map_sub, Pi.zero_apply, sub_eq_zero] using hx

/-- If a finite-exponent class and a whole-space endpoint class have the same base on the
domain, the finite surface trace is the endpoint representative on the boundary. -/
theorem traceLp_ae_lipschitzRepresentative
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set ℝ^(m + 1)))
    (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F))
    (V : W^{1,∞}(ℝ^(m + 1); F))
    (hUV : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] (V.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)) :
    (Trace.C1.traceLp p hp U : ℝ^(m + 1) → F)
      =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] lipschitzRepresentative V := by
  apply Trace.C1.traceLp_coeFn_ae_of_continuous hgraph hp U
    (lipschitzRepresentative V).continuous
  exact hUV.trans ((lipschitzRepresentative_ae V).filter_mono
    (ae_mono Measure.restrict_le_self)).symm

/-- For the C¹ extension, the continuous boundary values agree with every finite
surface trace of the same physical Sobolev function, including the exponent one. -/
theorem traceLp_ae_c1ClosureLipschitzEmbedding
    (hgraph : Boundary.HasC1GraphBoundary (Ω : Set ℝ^(m + 1)))
    (hp : 1 ≤ p) (U : W^{1,∞}(Ω; F)) (V : W^{1,ENNReal.ofReal p}(Ω; F))
    (hVU : (V.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)) :
    ∀ᵐ x ∂surfaceMeasure (Ω : Set ℝ^(m + 1)),
      ∀ hx : x ∈ closure (Ω : Set ℝ^(m + 1)),
        Trace.C1.traceLp p hp V x = c1ClosureLipschitzEmbedding U ⟨x, hx⟩ := by
  have hrep := (lipschitzRepresentative_ae_of_restrict_eq
    (GeometricExtension.extensionSobolev (by decide)
      hΩ.chart_contDiff hΩ.chart_symm_contDiff U) U
    (GeometricExtension.restrict_extensionSobolev (by decide)
      hΩ.chart_contDiff hΩ.chart_symm_contDiff U)).symm
  have h := Trace.C1.traceLp_coeFn_ae_of_continuous hgraph hp V
    (lipschitzRepresentative _).continuous (hVU.trans hrep)
  filter_upwards [h] with x hx
  exact fun _ ↦ hx

end SurfaceTrace

end SobolevSpace.VectorValued
