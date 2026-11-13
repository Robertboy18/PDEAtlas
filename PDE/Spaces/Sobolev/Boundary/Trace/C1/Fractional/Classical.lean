/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Operator
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.ClassicalRepresentative

/-!
# Physical traces of C¹ representatives

A C¹ chart preserves first-order regularity but need not preserve smoothness.
These identities extend the classical agreement of the curved trace to any
globally C¹ representative of an H¹ field. Compact support is supplied by the
atlas cutoffs, so it is not required of the representative.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The flat trace of a localized C¹ representative is its chart expression. -/
theorem localFlatTrace_apply_ae_of_contDiff (i : Fin hΩ.N)
    (u : H¹(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) Ω] f) :
    (localFlatTrace i u : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)]
      fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y *
        (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
        f ((hΩ.chart i).symm y) := by
  let q : HalfSpace.CompactSupport.c1CompactSubmodule m :=
    ⟨fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y *
        (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
        f ((hΩ.chart i).symm y),
      (((targetSupportCutoff (Ω := Ω) i).contDiff.of_le (by simp)).mul
        (((hΩ.boundaryCutoff i).contDiff.of_le (by simp)).comp
          (hΩ.chart_symm_contDiff i))).mul (hf.comp (hΩ.chart_symm_contDiff i)),
      (targetSupportCutoff (Ω := Ω) i).hasCompactSupport.mul_right.mul_right⟩
  have heq : Extension.C1.BoundaryPiece.flattenCLM (p := 2) i u =
      HalfSpace.CompactSupport.toUpperH1 q := by
    apply GraphSpace.WkpSpaceOn.ext_of_base_ae (SobolevSpace.HalfSpace.isOpen_upper _)
    have hflat := Extension.C1.BoundaryPiece.flattenCLM_base_eq_classical_ae
      (p := 2) i u f hu
    have hq := HalfSpace.CompactSupport.toUpperH1_coordinate_ae q
      (GraphSpace.baseIndex (m + 1) 1)
    exact hflat.trans (by
      simpa only [GraphSpace.baseIndex_toList, iteratedPartialDeriv] using hq.symm)
  change (flatTrace (n := m)
    (Extension.C1.BoundaryPiece.flattenCLM (p := 2) i u) : ℝ^(m + 1) → ℝ) =ᵐ[_] _
  rw [heq]
  exact HalfSpace.CompactSupport.flatTrace_c1_apply_ae q

/-- One physical chart contribution is the partition factor times a C¹ representative. -/
theorem localPhysicalTrace_apply_ae_of_contDiff (i : Fin hΩ.N)
    (u : H¹(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) Ω] f) :
    (localPhysicalTrace i u : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      fun x ↦ (hΩ.boundaryCutoff i).toFun x * f x := by
  let A := chartBoundaryPatch (Ω := Ω) i
  have hA : MeasurableSet A := measurableSet_chartBoundaryPatch i
  have hflat := localFlatTrace_apply_ae_of_contDiff i u hf hu
  have hcomp := (measurePreserving_chart_boundaryPatch i).quasiMeasurePreserving.ae
    ((Measure.absolutelyContinuous_of_le_smul (chartPushedSurfaceMeasure_le i)).ae_eq hflat)
  have hlocal :
      (fun x ↦ localFlatTrace i u (hΩ.chart i x)) =ᵐ[(surfaceMeasure Ω).restrict A]
        fun x ↦ (hΩ.boundaryCutoff i).toFun x * f x := by
    filter_upwards [hcomp, ae_restrict_mem hA] with x hx hxA
    rw [hx, (hΩ.chart i).left_inv hxA.1]
    by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
    · simp [hψ]
    · rw [targetSupportCutoff_eq_one_on_boundarySupportInTarget i
        (hΩ.chart i x) ⟨x, subset_tsupport _ hψ, rfl⟩, one_mul]
  have hind := (ae_eq_restrict_iff_indicator_ae_eq hA).mp hlocal
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [localPhysicalTrace_apply_ae i u, hind, hfrontier]
    with x hx hi hxfrontier
  rw [hx, hi]
  by_cases hxA : x ∈ A
  · exact indicator_of_mem hxA _
  · rw [indicator_of_notMem hxA]
    have hψ : (hΩ.boundaryCutoff i).toFun x = 0 := by
      by_contra hne
      exact hxA ⟨hΩ.boundaryCutoff_support i (subset_tsupport _ hne), hxfrontier⟩
    simp [hψ]

/-- The curved trace of an H¹ field with a globally C¹ representative is its boundary value. -/
theorem trace_apply_ae_of_contDiff
    (u : H¹(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContDiff ℝ 1 f)
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) Ω] f) :
    (trace u : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  have hlocal : ∀ᵐ x ∂surfaceMeasure Ω, ∀ i : Fin hΩ.N,
      (chartBoundaryPatch i).indicator (fun z ↦ localFlatTrace i u (hΩ.chart i z)) x =
        (hΩ.boundaryCutoff i).toFun x * f x := by
    apply ae_all_iff.mpr
    intro i
    exact (localPhysicalTrace_apply_ae i u).symm.trans
      (localPhysicalTrace_apply_ae_of_contDiff i u hf hu)
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [trace_apply_ae u, hlocal, hfrontier] with x hx hi hxfrontier
  rw [hx]
  simp_rw [hi, ← Finset.sum_mul]
  rw [sum_boundary_partition_eq_one hxfrontier, one_mul]

end SobolevSpace.Trace.C1.Fractional
