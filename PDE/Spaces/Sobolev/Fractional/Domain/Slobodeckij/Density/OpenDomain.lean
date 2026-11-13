/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Density.OpenDomain.LocalizedApproximation
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph.Summation
import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.LocallyFinite
import PDE.Spaces.Sobolev.Approximation.Density.OpenDomain.Partition
import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Smooth density on arbitrary open domains

A smooth partition of unity breaks the domain into interior pieces. Each piece
can be smoothed with a prescribed error, and we choose these errors to be
summable in the full fractional norm. Adding their sum to the original function
gives the locally finite sum of the smooth pieces.

This proves smooth density for Banach-valued functions without a regular
boundary or an extension operator. The approximants are smooth inside the
domain; their support need not stay away from its boundary.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal FractionalSobolev Topology

namespace SobolevSpace.Fractional.GagliardoSpace

open Approximation.OpenDomain

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every intrinsic fractional Sobolev element on an open domain has an
arbitrarily close element represented by a function smooth on that domain.
The codomain may be any real Banach space. -/
theorem exists_smooth_approximation_on {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (u : W^{s,p}(Ω; F))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : W^{s,p}(Ω; F), ∃ f : ℝ^n → F,
      ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
      (toLp n s Ω v : ℝ^n → F) =ᵐ[volume.restrict Ω] f ∧ ‖v - u‖ < ε := by
  let O : Opens (ℝ^n) := ⟨Ω, hΩ⟩
  obtain ⟨ψ, hψ, hfin, hone⟩ := exists_testFunction_partition O
  let δ (i : ℕ) : ℝ := (ε / 4) * (1 / 2) ^ i
  have hδ (i : ℕ) : 0 < δ i := mul_pos (by positivity) (by positivity)
  have hsδ : Summable δ := summable_geometric_two.mul_left (ε / 4)
  have htδ : (∑' i, δ i) = ε / 2 := by
    rw [show δ = (fun i ↦ (ε / 4) * (1 / 2 : ℝ) ^ i) from rfl,
      tsum_mul_left, hasSum_geometric_two.tsum_eq]
    ring
  choose f hf e heBase he using fun i ↦
    exists_localized_smooth_error hΩ hs0 hs1 hp u (ψ i) (hψ i) (hδ i)
  have hse : Summable (fun i ↦ ‖e i‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun i ↦ (he i).le) hsδ
  let v := u + ∑' i, e i
  let g (x : ℝ^n) := ∑ᶠ i, (ψ i).toFun x • f i x
  have hprod : LocallyFinite
      (fun i ↦ (Subtype.val : O → ℝ^n) ⁻¹' support (fun x ↦ (ψ i).toFun x • f i x)) :=
    hfin.subset fun i ↦ Set.preimage_mono (support_smul_subset_left (ψ i).toFun (f i))
  refine ⟨v, g, contDiffOn_finsum_of_locallyFinite O _
    (fun i ↦ (ψ i).contDiff'.smul (hf i)) hprod, ?_, ?_⟩
  · have hsum := toLp_tsum_ae_of_representatives e hse _ heBase
    filter_upwards [toLp_add_apply_ae u (∑' i, e i), hsum,
      ae_restrict_mem hΩ.measurableSet] with x hadd hsum hxΩ
    change toLp n s Ω (u + ∑' i, e i) x = g x
    rw [hadd, hsum]
    have hfinite : HasFiniteSupport (fun i ↦ (ψ i).toFun x) :=
      hfin.point_finite ⟨x, hxΩ⟩
    rw [tsum_eq_finsum (hfinite.fun_smul_left (fun i ↦ f i x - toLp n s Ω u x))]
    simp_rw [smul_sub]
    rw [finsum_sub_distrib (hfinite.fun_smul_left (fun i ↦ f i x))
      (hfinite.fun_smul_left (fun _ ↦ toLp n s Ω u x)),
      ← finsum_smul' hfinite, hone ⟨x, hxΩ⟩, one_smul]
    simp only [← add_sub_assoc, add_sub_cancel_left, g]
  · change ‖(u + ∑' i, e i) - u‖ < ε
    rw [add_sub_cancel_left]
    calc
      ‖∑' i, e i‖ ≤ ∑' i, ‖e i‖ := norm_tsum_le_tsum_norm hse
      _ ≤ ∑' i, δ i := hse.tsum_le_tsum (fun i ↦ (he i).le) hsδ
      _ = ε / 2 := htδ
      _ < ε := half_lt_self hε

/-- Smooth-on-domain representatives are dense in the intrinsic fractional
space for `0 < s < 1` and every finite exponent at least one. -/
theorem dense_smooth_on {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    Dense {u : W^{s,p}(Ω; F) | ∃ f : ℝ^n → F, ContDiffOn ℝ (⊤ : ℕ∞) f Ω ∧
      (toLp n s Ω u : ℝ^n → F) =ᵐ[volume.restrict Ω] f} := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨v, f, hf, hbase, hnorm⟩ :=
    exists_smooth_approximation_on hΩ hs0 hs1 hp u hε
  exact ⟨v, ⟨f, hf, hbase⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

/-- A sequence of representatives smooth on the domain converges to any given
fractional Sobolev element in its full norm. -/
theorem exists_smooth_approximation_sequence_on {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) (u : W^{s,p}(Ω; F)) :
    ∃ v : ℕ → W^{s,p}(Ω; F), ∃ f : ℕ → ℝ^n → F,
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (f j) Ω) ∧
      (∀ j, (toLp n s Ω (v j) : ℝ^n → F) =ᵐ[volume.restrict Ω] f j) ∧
      Filter.Tendsto (fun j ↦ ‖v j - u‖) Filter.atTop (𝓝 0) := by
  obtain ⟨v, hv, ht⟩ :=
    mem_closure_iff_seq_limit.mp (dense_smooth_on hΩ hs0 hs1 hp u)
  choose f hf hbase using hv
  refine ⟨v, f, hf, hbase, ?_⟩
  simpa only [sub_self, norm_zero] using (ht.sub (tendsto_const_nhds (x := u))).norm

end SobolevSpace.Fractional.GagliardoSpace
