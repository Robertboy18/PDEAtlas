/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.WholeSpace
public import PDE.Spaces.Sobolev.Extension.HigherOrder.Bounded
import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData

/-!
# Smooth composition on bounded graph domains

Extend a bounded Sobolev function by the bounded geometric extension, compose
on Euclidean space, and restrict back to the domain. Subtracting the reaction's
value at zero makes whole-space composition integrable. The constant is restored
only on the bounded domain. This argument has no restriction on the dimension.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev
open scoped Topology

namespace SobolevSpace.Composition

open GraphSpace

variable {n k : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- Smooth composition preserves bounded `H^k` on a bounded `C^k` graph domain,
without a dimension-dependent embedding assumption or a condition at zero. -/
theorem exists_hk_composition_on_domain_of_bounded
    (hk : 0 < k) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary k Ω)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (u : W^{k,2}(Ω)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n Ω, ‖baseRepresentative u x‖ ≤ B) :
    ∃ W : W^{k,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] fun x ↦ f (baseRepresentative u x) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt (Fact.out : 0 < n)⟩
  obtain ⟨U, hU, C, _, hC⟩ :=
    Extension.HigherOrder.exists_bounded_extension hk hopen hbounded hgraph u hB
  obtain ⟨V, hV⟩ := exists_hk_composition_of_bounded k
    (hf.sub contDiff_const) (sub_self (f 0)) (toRepresentative U) hC
  let R := restrictCLM hopen.measurableSet (subset_univ Ω) V
  let K : W^{k,2}(Ω) :=
    (ContDiffUpToBoundary.const (f 0)).toWkpSpaceOn hopen hbounded 2
  refine ⟨R + K, ?_⟩
  have hR : baseRepresentative R =ᵐ[domainMeasure n Ω] baseRepresentative V :=
    restrictCLM_apply_ae hopen.measurableSet (subset_univ Ω) V (baseIndex n k)
  have hUbase : baseRepresentative u =ᵐ[domainMeasure n Ω] baseRepresentative U := by
    rw [← hU]
    exact restrictCLM_apply_ae hopen.measurableSet (subset_univ Ω) U (baseIndex n k)
  have hVΩ := ae_restrict_of_ae (s := Ω) hV
  have hK := (ContDiffUpToBoundary.const (k := k) (f 0)).toWkpSpaceOn_base_ae
    hopen hbounded 2
  change (wkpBaseCoordinateCLM (R + K) : ℝ^n → ℝ) =ᵐ[_] _
  rw [map_add]
  filter_upwards [Lp.coeFn_add (wkpBaseCoordinateCLM R) (wkpBaseCoordinateCLM K),
    hR, hUbase, hVΩ, hK] with x hadd hr hu hv hc
  rw [hadd]
  change baseRepresentative R x + baseRepresentative K x = _
  change baseRepresentative K x = f 0 at hc
  change baseRepresentative V x = f (baseRepresentative U x) - f 0 at hv
  rw [hr, hv, ← hu, hc]
  exact sub_add_cancel _ _

private theorem exists_smooth_extension_on_Icc
    {f : ℝ → ℝ} {left right : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hinterval : Icc left right ⊆ s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ EqOn g f (Icc left right) := by
  obtain ⟨t, ht, hIt, hts⟩ := normal_exists_closure_subset isClosed_Icc hs hinterval
  obtain ⟨χ, hχ, _, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) ht isClosed_Icc hIt
  refine ⟨fun x ↦ χ x * f x, ?_, fun x hx ↦ ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · have hxs : x ∈ s := hts (by simpa only [tsupport, hsupp] using hx)
      exact hχ.contDiffAt.mul (hf.contDiffAt (hs.mem_nhds hxs))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · change χ x * f x = f x
    rw [(hone x).mp hx, one_mul]

/-- Only smoothness near the bounded essential value range is needed for
higher Sobolev composition. The smooth extension of the reaction is constructed
and agrees with the original reaction on the whole closed interval. -/
theorem exists_hk_composition_on_domain_of_contDiffOn
    (hk : 0 < k) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary k Ω)
    {f : ℝ → ℝ} {left right : ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hinterval : Icc left right ⊆ s)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f s)
    (u : W^{k,2}(Ω))
    (hrange : ∀ᵐ x ∂domainMeasure n Ω, baseRepresentative u x ∈ Icc left right) :
    ∃ W : W^{k,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] fun x ↦ f (baseRepresentative u x) := by
  obtain ⟨g, hg, hgf⟩ := exists_smooth_extension_on_Icc hs hinterval hf
  have hB : ∀ᵐ x ∂domainMeasure n Ω,
      ‖baseRepresentative u x‖ ≤ max |left| |right| := by
    filter_upwards [hrange] with x hx
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(neg_le_neg (le_max_left |left| |right|)).trans
      ((neg_abs_le left).trans hx.1), hx.2.trans ((le_abs_self right).trans (le_max_right _ _))⟩
  obtain ⟨W, hW⟩ :=
    exists_hk_composition_on_domain_of_bounded hk hopen hbounded hgraph hg u hB
  refine ⟨W, ?_⟩
  filter_upwards [hW, hrange] with x hx hr
  exact hx.trans (hgf hr)

end SobolevSpace.Composition
