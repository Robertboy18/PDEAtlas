/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.Classical.Data
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ClassicalZero

/-!
# Zero-boundary time curves from smooth classical data

A smooth function with literal zero lateral values has zero lateral values for
every canonical time derivative. The continuous trace/kernel theorem places
each spatial slice in `H¹₀`. The resulting curves are continuous in that
space and have their adjacent weak derivatives.

This construction uses only the raw function and its boundary values; it does
not depend on an evolution equation.
-/

@[expose] public noncomputable section

open PDE (SpaceTime)

namespace SobolevSpace.Evolution.Classical

open Filter MeasureTheory Set PDE.Common GraphSpace PDE.Analysis.Evolution
open scoped Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : SpaceTime n → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)
local notation "K" => splitSpaceTime ⁻¹' Set.prod (closure Ω) (Icc a b)

/-- Every time derivative inherits zero lateral values, including at
the initial and terminal times, from the original smooth function. -/
theorem derivativeSlice_eq_zero_on_frontier
    (hopen : IsOpen Ω) (hab : a < b) (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω,
      derivativeSlice hopen hf (List.replicate j 0) t x = 0 := by
  induction j with
  | zero =>
    intro t ht x hx
    exact (derivativeSlice_nil hopen hab hf hc ht (frontier_subset_closure hx)).trans
      (hzero t ht x hx)
  | succ j ih =>
    intro t ht x hx
    have hcont : Continuous (fun s ↦ derivativeSlice hopen hf
        (List.replicate (j + 1) 0) s x) :=
      (continuous_derivativeSlice hopen hf _).comp (continuous_id.prodMk continuous_const)
    have heq : EqOn (fun s ↦ derivativeSlice hopen hf
        (List.replicate (j + 1) 0) s x) (fun _ ↦ (0 : ℝ)) (Ioo a b) := by
      intro s hs
      have hval : (fun r ↦ derivativeSlice hopen hf (List.replicate j 0) r x)
          =ᶠ[nhds s] fun _ ↦ (0 : ℝ) :=
        (show EqOn _ _ (Ioo a b) from
          fun r hr ↦ ih r (Ioo_subset_Icc_self hr) x hx).eventuallyEq_of_mem
            (isOpen_Ioo.mem_nhds hs)
      have hd := hasDerivAt_derivativeSlice hopen hf (List.replicate j 0) hs
        (frontier_subset_closure hx)
      simpa only [List.replicate_succ] using
        hd.unique ((hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hval)
    have hclosure := heq.of_subset_closure hcont.continuousOn
      continuousOn_const subset_closure Subset.rfl
    apply hclosure
    rwa [closure_Ioo hab.ne]

/-- The canonical first-order Sobolev slice belongs to the zero-boundary
space. This includes the zero extension outside the time interval. -/
theorem sobolevCurve_mem_h10Submodule [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) (t : ℝ) :
    sobolevCurve hopen hbounded hab hf 1 j t ∈ h10Submodule (n := n) (Ω := Ω) := by
  by_cases ht : t ∈ Icc a b
  · have hslice := derivativeSlice_regular hopen hbounded hab hf (List.replicate j 0) 1 ht
    obtain ⟨v, hv, _⟩ := hslice.exists_H10_of_eq_zero_on_frontier hopen hbounded hgraph
      (((continuous_derivativeSlice hopen hf _).comp
        (continuous_const.prodMk continuous_id)).continuousOn)
      (fun x hx ↦ derivativeSlice_eq_zero_on_frontier hopen hab hf hc hzero j t ht x hx)
    have heq : sobolevCurve hopen hbounded hab hf 1 j t = h10SubtypeL v := by
      apply wkpBaseCoordinateCLM_injective hopen
      exact Lp.ext ((wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf 1 j ht).trans
        hv.symm)
    rw [heq]
    exact v.property
  · simp only [sobolevCurve, dite_eq_right ht]
    exact Submodule.zero_mem _

/-- The `H¹₀` curve of the `j`-th time derivative of smooth data
with zero lateral values. -/
def zeroBoundaryCurve [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) (t : ℝ) : H¹₀(Ω) :=
  ⟨sobolevCurve hopen hbounded hab hf 1 j t,
    sobolevCurve_mem_h10Submodule hopen hbounded hgraph hab hf hc hzero j t⟩

/-- Forgetting the zero trace recovers the original Sobolev derivative curve. -/
@[simp]
theorem coe_zeroBoundaryCurve [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) (t : ℝ) :
    (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j t : W^{1,2}(Ω)) =
      sobolevCurve hopen hbounded hab hf 1 j t :=
  rfl

/-- The raw-data curve is continuous in the zero-boundary norm. -/
theorem continuousOn_zeroBoundaryCurve [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    ContinuousOn (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j) (Icc a b) :=
  Topology.IsEmbedding.subtypeVal.continuousOn_iff.mpr
    (continuousOn_sobolevCurve hopen hbounded hab hf 1 j)

/-- Adjacent zero-boundary curves are weak time derivatives. -/
theorem hasWeakTimeDerivativeOn_zeroBoundaryCurve [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j)
      (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero (j + 1)) := by
  have : SecondCountableTopologyEither ℝ (H¹₀(Ω)) := ⟨Or.inl inferInstance⟩
  apply HasWeakTimeDerivativeOn.of_map h10SubtypeL Subtype.val_injective
  · exact ((continuousOn_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j).mono
      Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  · exact ((continuousOn_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero (j + 1)).mono
      Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  · exact hasWeakTimeDerivativeOn_sobolevCurve hopen hbounded hab hf 1 j

/-- Every constructed derivative curve is square-integrable in time. -/
theorem memLp_zeroBoundaryCurve [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    MemLp (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j) 2
      (volume.restrict (Ioc a b)) := by
  have : SecondCountableTopologyEither ℝ (H¹₀(Ω)) := ⟨Or.inl inferInstance⟩
  have hcont := continuousOn_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  apply MemLp.of_bound ((hcont.mono Ioc_subset_Icc_self).aestronglyMeasurable
    measurableSet_Ioc) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t (Ioc_subset_Icc_self ht)

/-- The Bochner class of the zero-boundary time derivative. -/
def zeroBoundaryTimeDerivative [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)) :=
  (memLp_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j).toLp
    (zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j)

/-- The Bochner class represents the concrete continuous curve. -/
theorem zeroBoundaryTimeDerivative_ae [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    (zeroBoundaryTimeDerivative hopen hbounded hgraph hab hf hc hzero j :
        ℝ → H¹₀(Ω)) =ᵐ[volume.restrict (Ioc a b)]
      zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j :=
  (memLp_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j).coeFn_toLp

/-- The Bochner classes retain every adjacent weak time link. -/
theorem hasWeakTimeDerivativeOn_zeroBoundaryTimeDerivative [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0)
    (j : ℕ) :
    HasWeakTimeDerivativeOn (Ioo a b)
      (zeroBoundaryTimeDerivative hopen hbounded hgraph hab hf hc hzero j)
      (zeroBoundaryTimeDerivative hopen hbounded hgraph hab hf hc hzero (j + 1)) := by
  have hweak := hasWeakTimeDerivativeOn_zeroBoundaryCurve hopen hbounded hgraph hab hf hc hzero j
  apply hweak.congr_ae_restrict measurableSet_Ioo
  · exact (zeroBoundaryTimeDerivative_ae hopen hbounded hgraph hab hf hc hzero j).symm.filter_mono
      (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))
  · exact (zeroBoundaryTimeDerivative_ae hopen hbounded hgraph hab hf hc hzero
      (j + 1)).symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))

/-- The zeroth derivative class represents the original scalar function
at almost every interior time and almost every spatial point. -/
theorem zeroBoundaryTimeDerivative_represents [Fact (0 < n)]
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasC1GraphBoundary Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (hc : ContinuousOn f K)
    (hzero : ∀ t ∈ Icc a b, ∀ x ∈ frontier Ω, f (timeSpaceCons t x) = 0) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ f (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω]
        baseRepresentative (h10SubtypeL
          (zeroBoundaryTimeDerivative hopen hbounded hgraph hab hf hc hzero 0 t)) := by
  have hae := zeroBoundaryTimeDerivative_ae hopen hbounded hgraph hab hf hc hzero 0
  filter_upwards [hae.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)),
    ae_restrict_mem measurableSet_Ioo] with t ht htm
  rw [ht, h10SubtypeL_apply, coe_zeroBoundaryCurve]
  filter_upwards [wkpBaseCoordinate_sobolevCurve_ae hopen hbounded hab hf 1 0
    (Ioo_subset_Icc_self htm), ae_restrict_mem hopen.measurableSet] with x hx hxΩ
  exact (derivativeSlice_nil hopen hab hf hc (Ioo_subset_Icc_self htm)
    (subset_closure hxΩ)).symm.trans hx.symm

end SobolevSpace.Evolution.Classical
