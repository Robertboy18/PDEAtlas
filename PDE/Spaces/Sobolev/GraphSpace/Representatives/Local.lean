/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Analysis.MeasureTheory.Function.Gluing
import PDE.Analysis.MeasureTheory.Function.LocalL2

/-!
# Weak derivatives of local Sobolev representatives

H¹ representatives of one function have the same weak derivatives on
open overlaps. A countable cover therefore gives measurable derivative
representatives on the whole domain. These representatives are locally L²
and satisfy the global weak derivative identities.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {ι : Type*} [Countable ι] {Ω : Set (ℝ^n)}

/-- Local H¹ representatives of the same function determine
locally L² weak derivatives on the covered domain. No compatibility of
derivative representatives is assumed: uniqueness supplies it. -/
theorem exists_weak_derivatives_of_native_cover
    (U : ι → Set (ℝ^n)) (hU : ∀ i, IsOpen (U i))
    (hcover : Ω ⊆ ⋃ i, U i) (f : ℝ^n → ℝ)
    (w : ∀ i, W^{1,2}(U i))
    (hbase : ∀ i, baseRepresentative (w i) =ᵐ[domainMeasure n (U i)] f) :
    ∃ g : Fin n → ℝ^n → ℝ,
      (∀ k, AEStronglyMeasurable (g k) (domainMeasure n Ω)) ∧
      (∀ k, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp (g k) 2 (domainMeasure n K)) ∧
      ∀ k, HasWeakDerivativeOn Ω [k] f (g k) := by
  have hmem (i : ι) (k : Fin n) :
      MemLp (fun x ↦ ∇ (w i) x k) 2 (domainMeasure n (U i)) := by
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (EuclideanSpace.proj (𝕜 := ℝ) k).comp_memLp'
        (Lp.memLp (∇ (w i)))
  have hw (i : ι) (k : Fin n) :
      HasWeakDerivativeOn (U i) [k] f (fun x ↦ ∇ (w i) x k) :=
    (hasWeakDerivativeOn_wkpGradientCLM (w i) k).congr_ae (hbase i)
      Filter.EventuallyEq.rfl
  have hex (k : Fin n) :
      ∃ g : ℝ^n → ℝ, AEStronglyMeasurable g (domainMeasure n Ω) ∧
        (∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
          MemLp g 2 (domainMeasure n K)) ∧ HasWeakDerivativeOn Ω [k] f g := by
    have hpair (i j : ι) :
        (fun x ↦ ∇ (w i) x k)
          =ᵐ[domainMeasure n (U i ∩ U j)] fun x ↦ ∇ (w j) x k :=
      ((hw i k).mono ((hU i).inter (hU j)).measurableSet inter_subset_left).unique_ae
        ((hU i).inter (hU j))
        ((hw j k).mono ((hU i).inter (hU j)).measurableSet inter_subset_right)
    obtain ⟨g, hg, hgw⟩ := exists_aestronglyMeasurable_of_ae_eq_on_intersections
      U (fun i ↦ (hU i).measurableSet) (fun i x ↦ ∇ (w i) x k)
      (fun i ↦ (hmem i k).aestronglyMeasurable) hpair
    have hgΩ : AEStronglyMeasurable g (domainMeasure n Ω) :=
      hg.mono_measure (Measure.restrict_mono hcover le_rfl)
    have hgU (i : ι) : MemLp g 2 (domainMeasure n (U i)) :=
      (memLp_congr_ae (hgw i)).mpr (hmem i k)
    refine ⟨g, hgΩ, ?_, ?_⟩
    · intro K hK hKΩ
      exact memLp_two_on_compact_of_open_cover U hU hcover hgU hK hKΩ
    · exact hasWeakDerivativeOn_single_of_open_cover U hU hcover k
        (fun i ↦ (hw i k).congr_ae Filter.EventuallyEq.rfl (hgw i).symm)
  choose g hg hmemg hweak using hex
  exact ⟨g, hg, hmemg, hweak⟩

/-- H¹ representatives on neighborhoods of each point yield global
weak derivative representatives. Euclidean second countability supplies the
countable subcover needed for measurable gluing. -/
theorem exists_weak_derivatives_of_local_representatives
    {Ω : Set (ℝ^n)} (f : ℝ^n → ℝ)
    (hlocal : ∀ x ∈ Ω, ∃ U : Set (ℝ^n), IsOpen U ∧ x ∈ U ∧
      ∃ w : W^{1,2}(U), baseRepresentative w =ᵐ[domainMeasure n U] f) :
    ∃ g : Fin n → ℝ^n → ℝ,
      (∀ k, AEStronglyMeasurable (g k) (domainMeasure n Ω)) ∧
      (∀ k, ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Ω →
        MemLp (g k) 2 (domainMeasure n K)) ∧
      ∀ k, HasWeakDerivativeOn Ω [k] f (g k) := by
  choose U hU hmem w hw using fun x : Ω ↦ hlocal x.val x.property
  obtain ⟨c, hc, hcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover U hU
      (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hmem ⟨x, hx⟩⟩)
  have : Countable c := hc.to_subtype
  have hcov : Ω ⊆ ⋃ i : c, U i.val := by
    intro x hxΩ
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hxΩ)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  exact exists_weak_derivatives_of_native_cover
    (fun i : c ↦ U i.val) (fun i ↦ hU i.val) hcov f
    (fun i ↦ w i.val) (fun i ↦ hw i.val)

end SobolevSpace.GraphSpace
