/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Operator
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace.CompactSupport
import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Assembly

/-!
# Naturality of Banach-valued C¹ traces

Continuous linear maps of the codomain commute with the physical surface trace.
Ambient compact smooth representatives are dense in the first-order Sobolev graph:
extend by the finite C¹ atlas, approximate in the whole space, and restrict back.
The classical boundary law identifies the two operators on this core.

The exponent is finite and may equal one. Both codomains may be infinite-dimensional
real Banach spaces, and tangential dimension zero is included.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Compact ambient smooth representatives are dense in the first-order graph
on a domain with a finite C¹ extension atlas. Their supports may meet the boundary. -/
theorem dense_compact_smooth {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Dense {U : W^{1,p}(Ω; F) | ∃ f : ℝ^(m + 1) → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
        =ᵐ[domainMeasure (m + 1) Ω] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  let E : W^{1,p}(Ω; F) →L[ℝ] W^{1,p}(ℝ^(m + 1); F) :=
    GeometricExtension.extensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff
  let R := restrictCLM (k := 1) (p := p) (F := F) (le_top : Ω ≤ ⊤)
  obtain ⟨V, ⟨f, hf, hfc, hbase⟩, hV⟩ :=
    Metric.mem_closure_iff.mp (dense_compact_smooth_univ hp (E U)) δ hδ
  have hRE : R (E U) = U :=
    GeometricExtension.restrict_extensionSobolev (by decide)
      hΩ.chart_contDiff hΩ.chart_symm_contDiff U
  refine ⟨R V, ⟨f, hf, hfc, ?_⟩, ?_⟩
  · exact (restrictCLM_apply_ae le_top V (baseIndex (m + 1) 1)).trans
      (hbase.filter_mono (ae_mono Measure.restrict_le_self))
  · rw [dist_eq_norm] at hV ⊢
    rw [← hRE, ← map_sub]
    exact (norm_restrictCLM_apply_le _ (E U - V)).trans_lt hV

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A continuous linear codomain map commutes with the physical C¹ surface trace. -/
theorem traceLp_mapCLM (hp : 1 ≤ p) (L : F →L[ℝ] G)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    traceLp p hp (mapCLM L U) =
      L.compLpL (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))
        (traceLp p hp U) := by
  refine (dense_compact_smooth ENNReal.ofReal_ne_top).induction ?_
    (isClosed_eq ((traceLp p hp).continuous.comp (mapCLM L).continuous)
      ((L.compLpL (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))).continuous.comp
        (traceLp p hp).continuous)) U
  rintro V ⟨f, hf, _, hbase⟩
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hLf : ContDiff ℝ 1 (L ∘ f) := L.contDiff.comp hf1
  have hLbase := (mapCLM_apply_ae L V (baseIndex (m + 1) 1)).trans (hbase.fun_comp L)
  apply Lp.ext
  exact (traceLp_coeFn_ae hp (mapCLM L V) hLf hLbase).trans
    (((traceLp_coeFn_ae hp V hf1 hbase).fun_comp L).symm.trans
      (L.coeFn_compLpL _).symm)

/-- Naturality as an equality of continuous linear operators on the Sobolev graph. -/
theorem traceLp_comp_mapCLM (hp : 1 ≤ p) (L : F →L[ℝ] G) :
    (traceLp (Ω := Ω) p hp).comp (mapCLM L) =
      (L.compLpL (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))).comp
        (traceLp p hp) := by
  ext U : 1
  exact traceLp_mapCLM hp L U

end SobolevSpace.VectorValued.Trace.C1
