/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Rellich.GraphTranslation

/-!
# Weak Poisson gradient energy in a graph strip

An inward translate of a zero extension has zero weak gradient on the thin strip
that it has left behind. The energy of the original gradient in that strip is
therefore bounded by the whole-space gradient translation defect. Local C¹ graph
geometry supplies both admissibility and the required exterior-shift property.

The resulting estimate is linear in the vertical strip width. It uses only the
weak Poisson equation and `H¹₀` membership, without a boundary value of the gradient
or a global `L²` Laplacian for the zero extension.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.Rellich

open MeasureTheory Set
open ZeroTrace
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The gradient of a translated Sobolev zero extension vanishes almost everywhere
at points whose inverse translate lies outside the original domain. -/
theorem gradient_translate_zeroExtend_eq_zero_ae
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (a : ℝ^n) :
    ∀ᵐ x ∂volume, x + a ∉ Ω → ∇ (translateH1 a (zeroExtendH10 hΩ z)) x = 0 := by
  let Z := zeroExtendH10 hΩ z
  have hcoordinate (i : Fin n) :
      (fun x ↦ ((translateH1 a Z : H¹(ℝ^n)) : WkpAmbientOn n 1 2 univ)
        (singleDerivIndex n i) x) =ᵐ[volume]
      fun x ↦ (Ω.indicator fun y ↦ ((z : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
        (singleDerivIndex n i) y) (x + a) := by
    have hzero := zeroExtendH10_coordinate_apply_ae hΩ z (singleDerivIndex n i)
    have hshift := (translationMeasurePreserving a).quasiMeasurePreserving.ae_eq_comp
      (by simpa only [domainMeasure, Measure.restrict_univ] using hzero)
    have htranslate := translateLp_apply_ae 2 a
      ((Z : WkpAmbientOn n 1 2 univ) (singleDerivIndex n i))
    simpa only [translateH1_apply, domainMeasure, Measure.restrict_univ,
      Function.comp_def, translationContinuousMap_apply] using htranslate.trans hshift
  have hgradient : ∀ᵐ x ∂volume, ∀ i : Fin n,
      (∇ (translateH1 a Z) x) i =
        ((translateH1 a Z : H¹(ℝ^n)) : WkpAmbientOn n 1 2 univ)
          (singleDerivIndex n i) x := by
    simpa only [domainMeasure, Measure.restrict_univ] using
      wkpGradientCLM_apply_ae (translateH1 a Z)
  filter_upwards [hgradient, ae_all_iff.mpr hcoordinate] with x hx hxi houtside
  ext i
  rw [hx i, hxi i, indicator_of_notMem houtside, PiLp.zero_apply]

/-- On a measurable region vacated by an admissible inward translation, the weak
Poisson gradient energy is bounded by the whole-space translation estimate. -/
theorem integral_gradient_sq_le_of_translate_outside
    (hΩ : MeasurableSet Ω) (z : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure n Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (a : ℝ^n)
    (hadmissible : restrictCLM hΩ (subset_univ Ω)
      (translateH1 a (zeroExtendH10 hΩ z)) ∈ h10Submodule (Ω := Ω))
    (S : Set (ℝ^n)) (hS : MeasurableSet S)
    (houtside : ∀ x ∈ S, x + a ∉ Ω) :
    (∫ x in S, ‖∇ (zeroExtendH10 hΩ z) x‖ ^ 2) ≤
      2 * (n : ℝ) * ‖a‖ * ‖f‖ * ‖z‖ := by
  let G := ∇ (zeroExtendH10 hΩ z)
  let H := ∇ (translateH1 a (zeroExtendH10 hΩ z))
  let D := G - H
  have hzero := gradient_translate_zeroExtend_eq_zero_ae hΩ z a
  have hsub : (D : ℝ^n → ℝ^n) =ᵐ[volume] fun x ↦ G x - H x := by
    have h := Lp.coeFn_sub G H
    simp only [domainMeasure, Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    simpa only [Pi.sub_apply] using hx
  have hint : Integrable (fun x ↦ ‖D x‖ ^ 2) volume := by
    simpa only [real_inner_self_eq_norm_sq, domainMeasure, Measure.restrict_univ] using
      L2.integrable_inner (𝕜 := ℝ) D D
  calc
    (∫ x in S, ‖G x‖ ^ 2) = ∫ x in S, ‖D x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hzero,
        ae_restrict_of_ae hsub, ae_restrict_mem hS] with x hx hd hxS
      rw [hd, show H x = 0 from hx (houtside x hxS), sub_zero]
    _ ≤ ∫ x, ‖D x‖ ^ 2 :=
      setIntegral_le_integral hint (Filter.Eventually.of_forall fun x ↦ sq_nonneg ‖D x‖)
    _ = ‖D‖ ^ 2 := by
      simpa only [L2.inner_def, real_inner_self_eq_norm_sq,
        domainMeasure, Measure.restrict_univ] using real_inner_self_eq_norm_sq D
    _ ≤ _ := norm_gradient_zeroExtend_sub_translate_sq_le hΩ z f hweak a hadmissible

variable {m : ℕ} {Ω P K : Set (ℝ^(m + 1))}

/-- In a compact part of a graph patch, shifting a point outward by more than its
vertical height above the graph places it outside the domain. The admissible step
range follows from the distance of the compact set to the edge of the patch. -/
theorem exists_translate_outside_of_graph_strip
    (hP : IsOpen P) (A : ℝ^(m + 1) ≃L[ℝ] (ℝ^m × ℝ)) (g : ℝ^m → ℝ)
    (hside : ∀ x ∈ P, x ∈ Ω ↔ g (A x).1 < (A x).2)
    (hK : IsCompact K) (hKP : K ⊆ P) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, ∀ x ∈ K,
      (A x).2 - g (A x).1 < t → x + -(t • A.symm (0, 1)) ∉ Ω := by
  let v := A.symm (0, 1)
  obtain ⟨r, hr, hrP⟩ := hK.exists_cthickening_subset_open hP hKP
  refine ⟨r / (‖v‖ + 1), div_pos hr (by positivity), ?_⟩
  intro t ht x hx hheight
  have hnorm : dist (x + -(t • v)) x ≤ r := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht.1]
    have ht' := (lt_div_iff₀ (show 0 < ‖v‖ + 1 by positivity)).mp ht.2
    nlinarith [ht.1]
  have hyP : x + -(t • v) ∈ P :=
    hrP (Metric.mem_cthickening_of_dist_le _ x r K hx hnorm)
  have hcoordinates : A (x + -(t • v)) = A x + (0, -t) := by
    rw [map_add, map_neg, map_smul]
    simp only [v, A.apply_symm_apply, Prod.smul_mk, smul_zero, smul_eq_mul,
      mul_one, Prod.neg_mk, neg_zero]
  intro hyΩ
  have hpositive := (hside _ hyP).mp hyΩ
  rw [hcoordinates] at hpositive
  simp only [Prod.fst_add, Prod.snd_add, add_zero] at hpositive
  linarith

/-- A localized weak Poisson solution has `O(t)` gradient energy in vertical
strips of a C¹ graph patch. Both translated-test admissibility and vanishing on
the strip are derived from the graph and compact localization. -/
theorem exists_integral_gradient_sq_graph_strip_le
    (cover : Boundary.C1GraphBoundaryCover m Ω) (i : Fin cover.N) (z : H¹₀(Ω))
    (u : ℝ^(m + 1) → ℝ)
    (hu : (baseCoordCLM z : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω] u)
    (hpatch : tsupport (Ω.indicator u) ⊆ cover.boundaryPatch i)
    (f : DerivLp (m + 1) 2 Ω)
    (hweak : ∀ φ : TestFunctionOn (m + 1) Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * PDE.laplacian φ.1.toFun x
        ∂domainMeasure (m + 1) Ω) = ∫ x, f x * φ.1.toFun x ∂domainMeasure (m + 1) Ω)
    (hK : IsCompact K) (hKP : K ⊆ cover.boundaryPatch i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ,
      (∫ x in {x ∈ K | 0 < (cover.coordinates i x).2 -
          cover.height i (cover.coordinates i x).1 ∧
        (cover.coordinates i x).2 - cover.height i (cover.coordinates i x).1 < t},
        ‖∇ (zeroExtendH10 cover.isOpen.measurableSet z) x‖ ^ 2) ≤
        2 * (m + 1 : ℕ) * t * ‖(cover.coordinates i).symm (0, 1)‖ * ‖f‖ * ‖z‖ := by
  obtain ⟨δ₁, hδ₁, hadmissible⟩ :=
    exists_inward_translation_admissible_of_graph cover i z u hu hpatch
  obtain ⟨δ₂, hδ₂, houtside⟩ := exists_translate_outside_of_graph_strip
    (cover.boundaryPatch_open i) (cover.coordinates i) (cover.height i)
    (cover.mem_iff_epigraph i) hK hKP
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht
  have ht₁ : t ∈ Ioo 0 δ₁ := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  have ht₂ : t ∈ Ioo 0 δ₂ := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
  let d : ℝ^(m + 1) → ℝ := fun x ↦
    (cover.coordinates i x).2 - cover.height i (cover.coordinates i x).1
  have hd : Continuous d := (cover.coordinates i).continuous.snd.sub
    ((cover.height_contDiff i).continuous.comp (cover.coordinates i).continuous.fst)
  let S : Set (ℝ^(m + 1)) := {x ∈ K | 0 < d x ∧ d x < t}
  have hS : MeasurableSet S := hK.isClosed.measurableSet.inter
    ((isOpen_lt continuous_const hd).measurableSet.inter
      (isOpen_lt hd continuous_const).measurableSet)
  have hbound := integral_gradient_sq_le_of_translate_outside
    cover.isOpen.measurableSet z f hweak (-(t • (cover.coordinates i).symm (0, 1)))
    (hadmissible t ht₁) S hS (fun x hx ↦ houtside t ht₂ x hx.1 hx.2.2)
  simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, mul_assoc]
    using hbound

end SobolevSpace.GraphSpace.Rellich
