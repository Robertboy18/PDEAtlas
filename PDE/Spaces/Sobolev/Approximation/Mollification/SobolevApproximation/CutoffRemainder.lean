/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.PowerCutoff
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.QuantitativeCutoff
public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives
import PDE.Spaces.Sobolev.Calculus.Product.ClassicalLeibniz
import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.DerivativeSplits

/-!
# Cutoff remainders for mollified Sobolev functions

A derivative of the power χ^(2m) retains a factor χ^m whenever its order is at
most m. A larger compact collar makes the remaining factor bounded without dividing
by χ. In the Leibniz remainder of order k+1, all derivatives of the mollified field
have order at most k. Their L² norms are therefore bounded uniformly in the
mollification scale by the original H^k norm.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set Function
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n k : ℕ}

/-- Every derivative of order at most m of χ^(2m) is χ^m times a compact smooth
coefficient. The larger collar preserves the factorization even where χ vanishes. -/
theorem exists_ballCutoff_pow_derivative_factor (a : ℝ^n) {R : ℝ} (hR : 0 < R)
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hα : α.length ≤ m) :
    ∃ g : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      iteratedPartialDeriv α (fun x ↦ ballCutoff a hR x ^ (2 * m)) =
        fun x ↦ ballCutoff a hR x ^ m * g x := by
  let χ := ballCutoff a hR
  let η := ballCutoff a (show 0 < 2 * R by positivity)
  obtain ⟨g, hg, hfactor⟩ := exists_iteratedPartialDeriv_pow_factor χ.contDiff α
    (m + (m - α.length))
  have horder : m + (m - α.length) + α.length = 2 * m := by omega
  rw [horder] at hfactor
  refine ⟨fun x ↦ η x * (χ x ^ (m - α.length) * g x),
    η.contDiff.mul ((χ.contDiff.pow _).mul hg), η.hasCompactSupport.mul_right, ?_⟩
  funext x
  change _ = χ x ^ m * (η x * (χ x ^ (m - α.length) * g x))
  rw [congrFun hfactor x, pow_add]
  by_cases hx : χ x = 0
  · simp only [hx, zero_pow hm.ne', zero_mul]
  · have hη : η x = 1 := ballCutoff_eq_one a _
      (tsupport_ballCutoff_subset a hR (subset_tsupport _ hx))
    simp only [hη, one_mul, mul_assoc]

/-- Mollification of a Sobolev coordinate is represented by the corresponding
classical derivative of the mollified base, for every derivative already in the graph. -/
theorem mollifierRowCLM_coordinate_ae_iteratedPartialDeriv
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (U : W^{k,2}(ℝ^n))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    (mollifierRowCLM μ hε (wkpCoordinateCLM (derivIndexOfList α hα) U) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n univ] iteratedPartialDeriv α (mollify μ ε (baseRepresentative U)) := by
  let u := wkpCoordinateCLM (derivIndexOfList α hα) U
  have hu := wholeSpaceL2Equiv_ae u
  have hconv := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (EventuallyEq.rfl : scaled μ ε =ᵐ[volume] scaled μ ε) hu
  have hrow := (wholeSpaceL2Equiv_ae (mollifierRowCLM μ hε u)).symm
  rw [wholeSpaceL2Equiv_mollifierRowCLM] at hrow
  have hJ : (mollifierRowCLM μ hε u : ℝ^n → ℝ) =ᵐ[volume] mollify μ ε u :=
    hrow.trans ((PDE.Analysis.convolutionL2CLM_ae_eq (scaled μ ε)
      (integrable_scaled μ hε) (wholeSpaceL2Equiv u)).trans
        (Eventually.of_forall (congrFun hconv)))
  have hcomm : iteratedPartialDeriv α (mollify μ ε (baseRepresentative U)) =
      mollify μ ε u := by
    by_cases hnil : α = []
    · subst α
      simp only [iteratedPartialDeriv, u, derivIndexOfList_nil]
      rfl
    · have hbase : MemLp (baseRepresentative U) 2 volume := by
        exact (memLp_congr_ae (wholeSpaceL2Equiv_ae _)).mp
          (MeasureTheory.Lp.memLp (wholeSpaceL2Equiv (wkpCoordinateCLM (baseIndex n k) U)))
      exact iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ μ hε hnil
        (hbase.locallyIntegrable (by norm_num))
        (U.property.hasWeakDerivativeOn_list α hα)
  rw [hcomm]
  simpa only [domainMeasure, Measure.restrict_univ] using hJ

/-- The order-(k+1) Leibniz remainder of a cutoff mollification factors through
χ^(k+1), with an L² bound uniform in the mollifier, its positive scale, and the
H^k input. Every derivative of the field in this remainder is a graph row. -/
theorem exists_cutoff_mollified_derivative_remainder (a : ℝ^n) {R : ℝ} (hR : 0 < R)
    (α : List (Fin n)) (hα : α.length = k + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ : Mollifier n) (ε : ℝ), 0 < ε →
      ∀ U : W^{k,2}(ℝ^n), ∃ r : DerivLp n 2 univ,
        ‖r‖ ≤ C * ‖U‖ ∧
        (iteratedPartialDeriv α (fun x ↦ ballCutoff a hR x ^ (2 * (k + 1)) *
          mollify μ ε (baseRepresentative U) x)) =ᵐ[domainMeasure n univ]
          fun x ↦ ballCutoff a hR x ^ (2 * (k + 1)) *
            iteratedPartialDeriv α (mollify μ ε (baseRepresentative U)) x +
              ballCutoff a hR x ^ (k + 1) * r x := by
  classical
  let χ := ballCutoff a hR
  let S := (derivativeSplits α).tail
  have hleft (i : Fin S.length) : (S.get i).1.length ≤ k + 1 := by
    have hlen := derivativeSplits_length (List.mem_of_mem_tail (S.get_mem i))
    omega
  have hright (i : Fin S.length) : (S.get i).2.length ≤ k := by
    have hlen := derivativeSplits_length (List.mem_of_mem_tail (S.get_mem i))
    have hne := derivativeSplits_tail_first_ne_nil α (S.get i) (S.get_mem i)
    have hpos := List.length_pos_iff.mpr hne
    omega
  choose g hg hgc hfactor using fun i : Fin S.length ↦
    exists_ballCutoff_pow_derivative_factor a hR (S.get i).1 (Nat.succ_pos k) (hleft i)
  let A (i : Fin S.length) : DerivLp n ∞ univ :=
    toLpOfContCompact (g i) (hg i).continuous (hgc i)
  let C := ∑ i : Fin S.length, ‖A i‖
  refine ⟨C, Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _), ?_⟩
  intro μ ε hε U
  let V (i : Fin S.length) : DerivLp n 2 univ :=
    mollifierRowCLM μ hε (wkpCoordinateCLM (derivIndexOfList (S.get i).2 (hright i)) U)
  let r : DerivLp n 2 univ := ∑ i : Fin S.length, A i • V i
  have hV (i : Fin S.length) : ‖V i‖ ≤ ‖U‖ :=
    (norm_mollifierRowCLM_apply_le μ hε _).trans (wkpCoordinateCLM_norm_le _ U)
  refine ⟨r, ?_, ?_⟩
  · calc
      ‖r‖ ≤ ∑ i : Fin S.length, ‖A i • V i‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin S.length, ‖A i‖ * ‖U‖ := Finset.sum_le_sum fun i _ ↦
        (Lp.norm_smul_le (A i) (V i)).trans
          (mul_le_mul_of_nonneg_left (hV i) (norm_nonneg _))
      _ = C * ‖U‖ := (Finset.sum_mul _ _ _).symm
  · have hterm (i : Fin S.length) :
        (A i • V i : DerivLp n 2 univ) =ᵐ[domainMeasure n univ]
          fun x ↦ g i x * iteratedPartialDeriv (S.get i).2
            (mollify μ ε (baseRepresentative U)) x := by
      filter_upwards [Lp.coeFn_lpSMul (r := 2) (A i) (V i),
        toLpOfContCompact_coeFn (hg i).continuous (hgc i),
        mollifierRowCLM_coordinate_ae_iteratedPartialDeriv μ hε U
          (S.get i).2 (hright i)] with x hx hA hV
      change A i x = g i x at hA
      change V i x = iteratedPartialDeriv (S.get i).2
        (mollify μ ε (baseRepresentative U)) x at hV
      simpa only [Pi.smul_apply', smul_eq_mul, hA, hV] using hx
    have hr : (r : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
        fun x ↦ ∑ i : Fin S.length, g i x * iteratedPartialDeriv (S.get i).2
          (mollify μ ε (baseRepresentative U)) x := by
      filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i ↦ A i • V i),
        ae_all_iff.mpr hterm] with x hx ht
      change r x = _ at hx
      rw [hx]
      simp only [Finset.sum_apply]
      exact Finset.sum_congr rfl fun i _ ↦ ht i
    filter_upwards [hr] with x hx
    have hbase : MemLp (baseRepresentative U) 2 volume :=
      (memLp_congr_ae (wholeSpaceL2Equiv_ae _)).mp
        (MeasureTheory.Lp.memLp (wholeSpaceL2Equiv (wkpCoordinateCLM (baseIndex n k) U)))
    have hs := iteratedPartialDeriv_mul_eq_sum_split
      (α := α) (f := fun y ↦ χ y ^ (2 * (k + 1)))
      (g := mollify μ ε (baseRepresentative U))
      (χ.contDiff.pow _)
      (mollify_contDiff_of_pos μ hε _ (hbase.locallyIntegrable (by norm_num))) x
    have hhead : ([], α) :: S = derivativeSplits α :=
      List.cons_head?_tail (by simp only [derivativeSplits_head?, Option.mem_some_iff])
    rw [← hhead, List.map_cons, List.sum_cons] at hs
    simp only [iteratedPartialDeriv] at hs
    rw [hs, hx]
    congr 1
    have hsum := congrArg (fun l ↦ (l.map (fun q ↦
      iteratedPartialDeriv q.1 (fun y ↦ χ y ^ (2 * (k + 1))) x *
        iteratedPartialDeriv q.2 (mollify μ ε (baseRepresentative U)) x)).sum)
      (List.ofFn_get S)
    rw [List.map_ofFn, List.sum_ofFn] at hsum
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change iteratedPartialDeriv (S.get i).1 (fun y ↦ χ y ^ (2 * (k + 1))) x * _ = _
    rw [congrFun (hfactor i) x]
    exact mul_assoc _ _ _

end SobolevSpace.Approximation
