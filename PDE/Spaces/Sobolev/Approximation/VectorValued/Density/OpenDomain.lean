/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain.LocalizedApproximation
public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.OpenDomain.Summation
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Smooth density on open domains with Banach codomain

A countable smooth partition of unity reduces approximation on an arbitrary open domain
to whole-space mollification of interior cutoff pieces. Choose the localized errors to
have summable graph norms. Their sum lies in the complete Sobolev graph, and its base,
added to the original representative, is the locally finite sum of the smooth pieces.

The resulting approximants are smooth on the domain. No boundary regularity, extension
operator, finite-dimensional codomain, or compact support of the input is required.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation.OpenDomain GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every Banach-valued Sobolev element on an open domain has an arbitrarily close
Sobolev element with a smooth representative on that domain. The order is any natural
number, and the exponent is any finite `p ≥ 1`. -/
theorem exists_smooth_approximation (hp : p ≠ ∞) (U : W^{k,p}(Ω; F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ V : W^{k,p}(Ω; F), ∃ f : ℝ^n → F,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
      (V.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f ∧ ‖V - U‖ < ε := by
  obtain ⟨ψ, hψ, hfin, hone⟩ := exists_testFunction_partition Ω
  let δ (i : ℕ) : ℝ := (ε / 4) * (1 / 2) ^ i
  have hδ (i : ℕ) : 0 < δ i := mul_pos (by positivity) (by positivity)
  have hsδ : Summable δ := summable_geometric_two.mul_left (ε / 4)
  have htδ : (∑' i, δ i) = ε / 2 := by
    rw [show δ = (fun i ↦ (ε / 4) * (1 / 2 : ℝ) ^ i) from rfl,
      tsum_mul_left, hasSum_geometric_two.tsum_eq]
    ring
  choose v hv E hEbase hE using fun i ↦
    exists_localized_smooth_error hp U (ψ i) (hψ i) (hδ i)
  have hsE : Summable (fun i ↦ ‖E i‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ (hE i).le) hsδ
  let V := U + ∑' i, E i
  let f (x : ℝ^n) := ∑ᶠ i, (ψ i).toFun x • v i x
  have hprod : LocallyFinite
      (fun i ↦ (Subtype.val : Ω → ℝ^n) ⁻¹' support (fun x ↦ (ψ i).toFun x • v i x)) :=
    hfin.subset fun i ↦ Set.preimage_mono (support_smul_subset_left (ψ i).toFun (v i))
  refine ⟨V, f, contDiffOn_finsum_of_locallyFinite Ω _ (fun i ↦ (ψ i).contDiff.smul (hv i))
    hprod, ?_, ?_⟩
  · have hall : ∀ᵐ x ∂domainMeasure n Ω, ∀ i,
        (E i).val (baseIndex n k) x =
          (ψ i).toFun x • (v i x - U.val (baseIndex n k) x) :=
      ae_all_iff.mpr hEbase
    have hadd : ((U + ∑' i, E i).val (baseIndex n k) : ℝ^n → F)
        =ᵐ[domainMeasure n Ω] fun x ↦
          U.val (baseIndex n k) x + (∑' i, E i).val (baseIndex n k) x :=
      Lp.coeFn_add _ _
    filter_upwards [hadd, coordinate_tsum_ae E hsE (baseIndex n k), hall,
      ae_restrict_mem Ω.isOpen.measurableSet] with x hadd hsum hx hxΩ
    change (U + ∑' i, E i).val (baseIndex n k) x = f x
    rw [hadd, hsum, tsum_congr hx]
    have hfinite : HasFiniteSupport (fun i ↦ (ψ i).toFun x) :=
      hfin.point_finite ⟨x, hxΩ⟩
    rw [tsum_eq_finsum
      (hfinite.fun_smul_left (fun i ↦ v i x - U.val (baseIndex n k) x))]
    simp_rw [smul_sub]
    rw [finsum_sub_distrib (hfinite.fun_smul_left (fun i ↦ v i x))
      (hfinite.fun_smul_left (fun _ ↦ U.val (baseIndex n k) x)),
      ← finsum_smul' hfinite, hone ⟨x, hxΩ⟩, one_smul]
    simp only [← add_sub_assoc, add_sub_cancel_left, f]
  · change ‖(U + ∑' i, E i) - U‖ < ε
    rw [add_sub_cancel_left]
    calc
      ‖∑' i, E i‖ ≤ ∑' i, ‖E i‖ := norm_tsum_le_tsum_norm hsE
      _ ≤ ∑' i, δ i := hsE.tsum_le_tsum (fun i ↦ (hE i).le) hsδ
      _ = ε / 2 := htδ
      _ < ε := half_lt_self hε

/-- Smooth-on-domain representatives form a dense subset of every finite-order
Banach-valued Sobolev graph at every finite exponent at least one. -/
theorem dense_smooth (hp : p ≠ ∞) :
    Dense {U : W^{k,p}(Ω; F) | ∃ f : ℝ^n → F,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
        (U.val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨V, f, hf, hbase, hnorm⟩ := exists_smooth_approximation hp U hε
  exact ⟨V, ⟨f, hf, hbase⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

/-- Sequential Meyers–Serrin approximation for an arbitrary complete real Banach codomain
and arbitrary open domain. The approximants lie in the Sobolev graph and converge
in its full graph norm. -/
theorem meyers_serrin (hp : p ≠ ∞) (U : W^{k,p}(Ω; F)) :
    ∃ V : ℕ → W^{k,p}(Ω; F), ∃ f : ℕ → ℝ^n → F,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) Ω) ∧
      (∀ j, ((V j).val (baseIndex n k) : ℝ^n → F) =ᵐ[domainMeasure n Ω] f j) ∧
      Filter.Tendsto (fun j ↦ ‖V j - U‖) Filter.atTop (𝓝 0) := by
  obtain ⟨V, hV, ht⟩ := mem_closure_iff_seq_limit.mp (dense_smooth hp U)
  choose f hf hbase using hV
  refine ⟨V, f, hf, hbase, ?_⟩
  simpa only [sub_self, norm_zero] using
    (ht.sub (tendsto_const_nhds (x := U))).norm

end SobolevSpace.VectorValued
