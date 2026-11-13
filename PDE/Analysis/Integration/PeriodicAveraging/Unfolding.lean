/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Periodization
public import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Unfolding a periodic test integral

The half-open unit cells indexed by integer vectors partition Euclidean space.
For an integrable compactly supported function, its periodization integrates
on one cell to its integral on the whole space. Local finiteness provides a
single finite sum on the cell, so no series-exchange hypothesis is required.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The integer translates of the unit cell cover Euclidean space. -/
theorem iUnion_unitCell_integer (n : ℕ) :
    (⋃ k : Fin n → ℤ, unitCell (fun i ↦ (k i : ℝ))) = univ := by
  apply eq_univ_of_forall
  intro x
  have hi (i : Fin n) : ∃ k : ℤ, x i ∈ Ioc (k : ℝ) (k + 1) := by
    apply mem_iUnion.mp
    rw [iUnion_Ioc_intCast]
    trivial
  choose k hk using hi
  exact mem_iUnion.mpr ⟨k, hk⟩

/-- Distinct integer translates of the half-open cell are disjoint. -/
theorem pairwise_disjoint_unitCell_integer (n : ℕ) :
    Pairwise (Disjoint on fun k : Fin n → ℤ ↦ unitCell (fun i ↦ (k i : ℝ))) := by
  intro k l hkl
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hkl
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (pairwise_disjoint_Ioc_intCast ℝ hi) (hx i) (hy i)

/-- Translating to the cell indexed by an integer vector preserves the cell integral. -/
theorem integral_unitCell_translate {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ^n → E) (k : Fin n → ℤ) :
    (∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)), f (x + integerVector n k)) =
      ∫ x in unitCell (fun i ↦ (k i : ℝ)), f x := by
  have hset : (fun x : ℝ^n ↦ x + integerVector n k) ⁻¹'
      unitCell (fun i ↦ (k i : ℝ)) = unitCell (fun _ ↦ 0) := by
    ext x
    change (∀ i, x i + (k i : ℝ) ∈ Ioc (k i : ℝ) ((k i : ℝ) + 1)) ↔
      ∀ i, x i ∈ Ioc (0 : ℝ) (0 + 1)
    simp only [mem_Ioc]
    constructor <;> intro h i <;> obtain ⟨h₁, h₂⟩ := h i <;> constructor <;> linarith
  have hm := measurePreserving_add_right (volume : Measure (ℝ^n)) (integerVector n k)
  have hp := hm.restrict_preimage (measurableSet_unitCell (fun i ↦ (k i : ℝ)))
  rw [hset] at hp
  exact hp.integral_comp (Homeomorph.addRight (integerVector n k)).measurableEmbedding f

/-- Integration on Euclidean space decomposes over the integer cells. -/
theorem hasSum_integral_unitCell_translate {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (hf : Integrable f) :
    HasSum (fun k : Fin n → ℤ ↦ ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)),
      f (x + integerVector n k)) (∫ x, f x) := by
  simp_rw [integral_unitCell_translate]
  have h := hasSum_integral_iUnion (fun k : Fin n → ℤ ↦
    measurableSet_unitCell (fun i ↦ (k i : ℝ))) (pairwise_disjoint_unitCell_integer n)
    (f := f) (μ := volume)
  have hfi : IntegrableOn f (⋃ k : Fin n → ℤ, unitCell (fun i ↦ (k i : ℝ))) := by
    simpa only [iUnion_unitCell_integer, IntegrableOn, Measure.restrict_univ] using hf
  simpa only [iUnion_unitCell_integer, Measure.restrict_univ] using h hfi

/-- A single finite set of translates suffices everywhere on the unit cell. -/
theorem exists_finset_periodize_unitCell {n : ℕ} {E : Type*} [Zero E]
    {f : ℝ^n → E} (hf : HasCompactSupport f) :
    ∃ s : Finset (Fin n → ℤ), ∀ x ∈ unitCell (fun _ : Fin n ↦ (0 : ℝ)),
      ∀ k ∉ s, f (x + integerVector n k) = 0 := by
  classical
  let K := (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)) ⁻¹'
    (Set.pi univ fun _ : Fin n ↦ Icc (0 : ℝ) 1)
  have hK : IsCompact K :=
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isClosedEmbedding.isCompact_preimage
      (isCompact_univ_pi fun _ : Fin n ↦ isCompact_Icc)
  have hfin := finite_integer_translates hf hK
  refine ⟨hfin.toFinset, fun x hx k hk ↦ ?_⟩
  by_contra h
  apply hk
  rw [hfin.mem_toFinset]
  refine ⟨x, ?_, subset_tsupport f h⟩
  intro i _
  change x i ∈ Icc (0 : ℝ) 1
  exact ⟨(hx i).1.le, by simpa only [zero_add] using (hx i).2⟩

/-- Integrating the periodization over one cell gives the full Euclidean integral. -/
theorem integral_periodize_unitCell {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (hf : Integrable f) (hfc : HasCompactSupport f) :
    (∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)), periodize f x) = ∫ x, f x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_periodize_unitCell hfc
  have hi (k : Fin n → ℤ) : Integrable (fun x ↦ f (x + integerVector n k)) :=
    (measurePreserving_add_right volume (integerVector n k)).integrable_comp_of_integrable hf
  calc
    _ = ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)),
        ∑ k ∈ s, f (x + integerVector n k) := by
      apply setIntegral_congr_fun (measurableSet_unitCell _)
      intro x hx
      apply finsum_eq_sum_of_support_subset
      intro k hk
      by_contra hks
      exact hk (hs x hx k hks)
    _ = ∑ k ∈ s, ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)),
        f (x + integerVector n k) := integral_finsetSum _ (fun k _ ↦ (hi k).restrict)
    _ = ∑' k : Fin n → ℤ, ∫ x in unitCell (fun _ : Fin n ↦ (0 : ℝ)),
        f (x + integerVector n k) := by
      symm
      apply tsum_eq_sum
      intro k hk
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun x hx ↦ hs x hx k hk
    _ = ∫ x, f x := (hasSum_integral_unitCell_translate hf).tsum_eq

end PDE.Analysis.PeriodicAveraging
