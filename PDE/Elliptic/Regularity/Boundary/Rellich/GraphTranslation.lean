/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.WeakTranslation
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphCover
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport

/-!
# Admissible inward translations in a graph patch

A compact subset of the closure of a local epigraph moves strictly into the
open domain under a sufficiently small vertical translation. Applied to the
literal zero extension of an `H¹₀` base coordinate, this makes its translated
restriction an admissible energy test. The weak Poisson translation estimate
then follows from graph geometry, without an assumed gradient translation bound.

Support is required to lie compactly inside one graph patch. No boundary-strip
integral or surface trace is asserted here.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Rellich

open MeasureTheory Set Function
open ZeroTrace
open scoped ENNReal InnerProductSpace Sobolev

variable {m : ℕ} {Ω P : Set (ℝ^(m + 1))}

/-- Compact support in the closure of a local epigraph enters the domain under
small positive vertical shifts. Only continuity of the graph height is needed. -/
theorem exists_tsupport_inward_translate_subset
    (hP : IsOpen P) (A : ℝ^(m + 1) ≃L[ℝ] (ℝ^m × ℝ))
    (g : ℝ^m → ℝ) (hg : Continuous g)
    (hside : ∀ x ∈ P, x ∈ Ω ↔ g (A x).1 < (A x).2)
    (F : ℝ^(m + 1) → ℝ) (hF : HasCompactSupport F)
    (hFP : tsupport F ⊆ P) (hFΩ : tsupport F ⊆ closure Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ,
      tsupport (fun x ↦ F (x + -(t • A.symm (0, 1)))) ⊆ Ω := by
  let v := A.symm (0, 1)
  obtain ⟨r, hr, hrP⟩ := hF.exists_cthickening_subset_open hP hFP
  have hclosed : IsClosed {x | g (A x).1 ≤ (A x).2} :=
    isClosed_le (hg.comp A.continuous.fst) A.continuous.snd
  have hclosure : ∀ x ∈ P ∩ closure Ω, g (A x).1 ≤ (A x).2 := by
    intro x hx
    exact closure_minimal (fun y hy ↦ ((hside y hy.1).mp hy.2).le)
      hclosed (hP.inter_closure hx)
  refine ⟨r / (‖v‖ + 1), div_pos hr (by positivity), ?_⟩
  intro t ht y hy
  have hx : y + -(t • v) ∈ tsupport F := by
    change y ∈ tsupport (F ∘ Homeomorph.addRight (-(t • v))) at hy
    rw [tsupport_comp_eq_preimage] at hy
    exact hy
  let x := y + -(t • v)
  have hxy : y = x + t • v := by dsimp only [x]; abel
  have hnorm : dist y x ≤ r := by
    rw [dist_eq_norm, hxy, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht.1]
    have ht' := (lt_div_iff₀ (show 0 < ‖v‖ + 1 by positivity)).mp ht.2
    nlinarith [ht.1]
  have hyP : y ∈ P := hrP (Metric.mem_cthickening_of_dist_le y x r _ hx hnorm)
  have hnonneg := hclosure x ⟨hFP hx, hFΩ hx⟩
  have hcoordinates : A y = A x + (0, t) := by
    rw [hxy, map_add, map_smul]
    simp only [v, A.apply_symm_apply, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one]
  apply (hside y hyP).mpr
  simpa only [hcoordinates, Prod.fst_add, Prod.snd_add, add_zero] using
    lt_add_of_le_of_pos hnonneg ht.1

/-- A compactly localized zero extension has admissible inward translates in its
C¹ graph patch. Localization is imposed on a chosen representative, so the
support condition is independent of exceptional values of the `L²` representative. -/
theorem exists_inward_translation_admissible_of_graph
    (cover : Boundary.C1GraphBoundaryCover m Ω) (i : Fin cover.N) (z : H¹₀(Ω))
    (u : ℝ^(m + 1) → ℝ)
    (hu : (baseCoordCLM z : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] u)
    (hpatch : tsupport (Ω.indicator u) ⊆ cover.boundaryPatch i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ,
      restrictCLM cover.isOpen.measurableSet (subset_univ Ω)
        (translateH1 (-(t • (cover.coordinates i).symm (0, 1)))
          (zeroExtendH10 cover.isOpen.measurableSet z)) ∈ h10Submodule (Ω := Ω) := by
  let F : ℝ^(m + 1) → ℝ := Ω.indicator u
  have hcompact : HasCompactSupport F := Metric.isCompact_of_isClosed_isBounded
    (isClosed_tsupport _) ((cover.boundaryPatch_bounded i).subset hpatch)
  have hsupport : tsupport F ⊆ closure Ω :=
    closure_mono support_indicator_subset
  obtain ⟨δ, hδ, hδΩ⟩ := exists_tsupport_inward_translate_subset
    (cover.boundaryPatch_open i) (cover.coordinates i) (cover.height i)
    (cover.height_contDiff i).continuous (cover.mem_iff_epigraph i)
    F hcompact hpatch hsupport
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  let a := -(t • (cover.coordinates i).symm (0, 1))
  let Z := zeroExtendH10 cover.isOpen.measurableSet z
  have hbase : (wkpBaseCoordinateCLM Z : ℝ^(m + 1) → ℝ) =ᵐ[volume] F :=
    (zeroExtendH10_coordinate_apply_ae cover.isOpen.measurableSet z
      (baseIndex (m + 1) 1)).trans
        ((ae_eq_restrict_iff_indicator_ae_eq cover.isOpen.measurableSet).mp hu)
  have hshift := (translationMeasurePreserving a).quasiMeasurePreserving.ae_eq_comp
    (by simpa only [domainMeasure, Measure.restrict_univ] using hbase)
  have htranslate := translateLp_apply_ae 2 a (wkpBaseCoordinateCLM Z)
  have htranslated : (wkpBaseCoordinateCLM (translateH1 a Z) : ℝ^(m + 1) → ℝ)
      =ᵐ[volume] fun x ↦ F (x + a) := by
    have hcoord : wkpBaseCoordinateCLM (translateH1 a Z) =
        translateLp 2 a (wkpBaseCoordinateCLM Z) := translateH1_apply a Z _
    rw [hcoord]
    simpa only [domainMeasure, Measure.restrict_univ, Function.comp_def,
      translationContinuousMap_apply] using htranslate.trans hshift
  exact restrict_mem_H10_of_tsupport_subset cover.isOpen (translateH1 a Z)
    (fun x ↦ F (x + a)) htranslated
    (hcompact.comp_homeomorph (Homeomorph.addRight a)) (hδΩ t ht)

/-- The squared gradient translation defect of a weak Poisson solution localized
in one C¹ graph patch is bounded linearly in the inward step. Graph geometry
supplies translated-test admissibility. -/
theorem exists_gradient_inward_translation_bound_of_graph
    (cover : Boundary.C1GraphBoundaryCover m Ω) (i : Fin cover.N) (z : H¹₀(Ω))
    (u : ℝ^(m + 1) → ℝ)
    (hu : (baseCoordCLM z : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] u)
    (hpatch : tsupport (Ω.indicator u) ⊆ cover.boundaryPatch i)
    (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ φ : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure (m + 1) Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure (m + 1) Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ,
      ‖∇ (zeroExtendH10 cover.isOpen.measurableSet z) -
        ∇ (translateH1 (-(t • (cover.coordinates i).symm (0, 1)))
          (zeroExtendH10 cover.isOpen.measurableSet z))‖ ^ 2 ≤
        2 * (m + 1 : ℕ) * t * ‖(cover.coordinates i).symm (0, 1)‖ * ‖f‖ * ‖z‖ := by
  obtain ⟨δ, hδ, hadmissible⟩ :=
    exists_inward_translation_admissible_of_graph cover i z u hu hpatch
  exact ⟨δ, hδ, fun t ht ↦ norm_gradient_zeroExtend_sub_inward_translate_sq_le
    cover.isOpen.measurableSet z f hweak _ ht.1.le (hadmissible t ht)⟩

end SobolevSpace.GraphSpace.Rellich
