/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Partition
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Cutoff
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.LocalApproximation

/-!
# Banach-valued smooth approximation up to a C¹ boundary

On a bounded open set with C¹ boundary, ambient compactly supported smooth functions
approximate every Banach-valued Sobolev function of finite order at every finite
exponent `p ≥ 1`. All derivative coordinates of the approximating Sobolev elements
are represented by the classical derivatives of the ambient smooth functions.

The finite inward partition is the one used in the scalar proof of Evans §5.3.3.
Local inward mollification and bounded boundary-relative cutoffs give a convergent
finite sum in the Sobolev graph. Weak-derivative uniqueness identifies
its derivative rows. No Sobolev extension across the physical boundary is used.
The ambient compact supports may meet that boundary. Neither the dimension nor
the derivative order is required to be positive.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to a C¹ boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter Function MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation.UpToBoundary Boundary GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A finite inward partition gives convergent compact smooth approximants in the
Banach Sobolev graph, with every derivative coordinate represented. -/
theorem smooth_approximation_of_inwardPartition (P : InwardPartition (Ω : Set ℝ^n))
    (hp : p ≠ ∞) (U : W^{k,p}(Ω; F)) :
    ∃ A : ℕ → W^{k,p}(Ω; F), ∃ f : ℕ → ℝ^n → F,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m)) ∧
      (∀ m, HasCompactSupport (f m)) ∧
      (∀ m a, ((A m).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        iteratedPartialDeriv a.toList (f m)) ∧
      Tendsto A atTop (𝓝 U) := by
  classical
  let V (i : Fin P.N) : Opens ℝ^n := ⟨P.patch i, P.patch_open i⟩
  choose f hf A hAderiv hA using fun i ↦
    UpToBoundary.local_approximation (V := V i) hp U (P.direction i)
      (P.radius_pos i) (P.interior_ball i)
  have hAbase (i : Fin P.N) (m : ℕ) :
      ((A i m).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n (V i ⊓ Ω)] f i m := by
    simpa only [baseIndex_toList, iteratedPartialDeriv] using
      hAderiv i m (baseIndex n k)
  let W (i : Fin P.N) : W^{k,p}(V i ⊓ Ω; F) := restrictCLM inf_le_right U
  let M (i : Fin P.N) : W^{k,p}(V i ⊓ Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
    interMultiplier (P.cutoff i) (P.cutoff_support i)
  let B (m : ℕ) := ∑ i, M i (A i m)
  let g (m : ℕ) (x : ℝ^n) := ∑ i, (P.cutoff i).toFun x • f i m x
  have hg (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g m) :=
    ContDiff.sum fun i _ ↦ (P.cutoff i).contDiff.smul (hf i m)
  have hc (m : ℕ) : HasCompactSupport (g m) := by
    convert
      HasCompactSupport.finset_sum (s := Finset.univ)
        (fun i _ ↦ ((P.cutoff i).hasCompactSupport.smul_right :
          HasCompactSupport ((P.cutoff i).toFun • f i m))) using 1
    ext x
    simp only [g, Finset.sum_apply]
    rfl
  have hbaseSum (E : Fin P.N → W^{k,p}(Ω; F)) :
      ((∑ i, E i).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        fun x ↦ ∑ i, (E i).val (baseIndex n k) x := by
    change (fun x ↦ coordinateCLM (baseIndex n k) (∑ i, E i) x) =ᵐ[_] _
    rw [map_sum]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i ↦ (E i).val (baseIndex n k))] with x hx
    simpa only [coordinateCLM_apply, Finset.sum_apply] using hx
  have hBbase (m : ℕ) :
      ((B m).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω] g m := by
    have hi (i : Fin P.N) := interMultiplier_base_ae (Ω := Ω) (V := V i)
      (P.cutoff i) (P.cutoff_support i) (A i m) (hAbase i m)
    filter_upwards [hbaseSum (fun i ↦ M i (A i m)), ae_all_iff.mpr hi]
      with x hx hxi
    exact hx.trans (Finset.sum_congr rfl fun i _ ↦ hxi i)
  have hsum : ∑ i, M i (W i) = U := by
    apply WkpSpaceOn.ext_of_base_ae
    have hi (i : Fin P.N) := interMultiplier_base_ae (Ω := Ω) (V := V i)
      (P.cutoff i) (P.cutoff_support i) (W i)
      (restrictCLM_apply_ae inf_le_right U (baseIndex n k))
    filter_upwards [hbaseSum (fun i ↦ M i (W i)), ae_all_iff.mpr hi,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxi hxΩ
    calc
      _ = ∑ i, (P.cutoff i).toFun x • U.val (baseIndex n k) x :=
        hx.trans (Finset.sum_congr rfl fun i _ ↦ hxi i)
      _ = U.val (baseIndex n k) x := by
        rw [← Finset.sum_smul, P.sum_eq_one x (subset_closure hxΩ), one_smul]
  have hB : Tendsto B atTop (𝓝 U) := by
    rw [← hsum]
    exact tendsto_finsetSum _ fun i _ ↦
      (M i).continuous.continuousAt.tendsto.comp (hA i)
  refine ⟨B, g, hg, hc, ?_, hB⟩
  intro m a
  exact (((B m).property a).congr_ae (hBbase m) Filter.EventuallyEq.rfl).ae_eq
    (hasWeakDerivativeOn_iteratedPartialDeriv (hg m) a.toList)

/-- Every Sobolev function on a bounded C¹ domain is the graph-norm limit of ambient
compact smooth representatives with all classical derivative rows. The C¹ hypothesis
is sufficient for every finite Sobolev order. -/
theorem smooth_approximation_of_hasC1Boundary
    (hb : Bornology.IsBounded (Ω : Set ℝ^n))
    (hC : HasC1Boundary (Ω : Set ℝ^n)) (hp : p ≠ ∞) (U : W^{k,p}(Ω; F)) :
    ∃ A : ℕ → W^{k,p}(Ω; F), ∃ f : ℕ → ℝ^n → F,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (f m)) ∧
      (∀ m, HasCompactSupport (f m)) ∧
      (∀ m a, ((A m).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        iteratedPartialDeriv a.toList (f m)) ∧
      Tendsto A atTop (𝓝 U) := by
  obtain ⟨P⟩ := exists_inwardPartition Ω.isOpen hb hC
  exact smooth_approximation_of_inwardPartition P hp U

/-- An ambient compactly supported smooth function approximates a Banach-valued
Sobolev element to arbitrary positive accuracy, representing every derivative row.
Its compact support need not lie inside the domain. -/
theorem exists_compact_smooth_approximation_of_hasC1Boundary
    (hb : Bornology.IsBounded (Ω : Set ℝ^n))
    (hC : HasC1Boundary (Ω : Set ℝ^n)) (hp : p ≠ ∞) (U : W^{k,p}(Ω; F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : W^{k,p}(Ω; F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ a : DerivIndex n k,
        (V.val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
          iteratedPartialDeriv a.toList f) ∧
      ‖V - U‖ < ε := by
  obtain ⟨A, f, hf, hc, hderiv, hA⟩ := smooth_approximation_of_hasC1Boundary hb hC hp U
  have hnorm : Tendsto (fun m ↦ ‖A m - U‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hA.sub (tendsto_const_nhds (x := U))).norm
  obtain ⟨m, hm⟩ := (hnorm.eventually (gt_mem_nhds hε)).exists
  exact ⟨A m, f m, hf m, hc m, hderiv m, hm⟩

/-- Ambient compact smooth representatives form a dense subset of the Banach Sobolev
graph on a bounded C¹ domain. The derivative-row condition uses the graph. -/
theorem dense_compact_smooth_of_hasC1Boundary
    (hb : Bornology.IsBounded (Ω : Set ℝ^n))
    (hC : HasC1Boundary (Ω : Set ℝ^n)) (hp : p ≠ ∞) :
    Dense {U : W^{k,p}(Ω; F) | ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      ∀ a : DerivIndex n k,
        (U.val a : ℝ^n → F) =ᵐ[domainMeasure n Ω] iteratedPartialDeriv a.toList f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨V, f, hf, hc, hderiv, hnorm⟩ :=
    exists_compact_smooth_approximation_of_hasC1Boundary hb hC hp U hε
  exact ⟨V, ⟨f, hf, hc, hderiv⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

end SobolevSpace.VectorValued
