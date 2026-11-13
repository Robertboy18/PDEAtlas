/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Representative
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Algebra
public import PDE.FDeriv.SpaceTime
import PDE.Analysis.Calculus.CompactCurry.Boundary

/-!
# Canonical slices of smooth spacetime data

One function smooth up to the boundary of an open cylinder determines continuous
mixed derivative fields. Their spatial derivative identities persist at both
time endpoints by closure of the derivative graph in the supremum norm. Thus
endpoint slices are smooth up to the spatial boundary. A smooth ambient
extension of the data, or of the cylinder, is not assumed.
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

namespace SobolevSpace.Evolution.Classical

open Filter Set PDE.Common
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ} {f : ℝ^(n + 1) → ℝ}

local notation "Q" => splitSpaceTime ⁻¹' Set.prod Ω (Ioo a b)

private theorem isOpen_cylinder (hopen : IsOpen Ω) : IsOpen Q :=
  (hopen.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous

/-- Continuous values of one mixed derivative of raw spacetime data, built from the
single raw function. -/
def derivativeField (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    ℝ^(n + 1) → ℝ :=
  ((hf α.length).iteratedPartialDeriv_of_le
    ((hopen.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous) α
    (r := 0) (by simp)).continuousRepresentative

/-- Every constructed derivative field is continuous in the ambient space. -/
theorem continuous_derivativeField (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    Continuous (derivativeField hopen hf α) :=
  ContDiffUpToBoundary.continuous_continuousRepresentative _

/-- In the open cylinder the continuous field is the derivative. -/
theorem derivativeField_eqOn (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    EqOn (derivativeField hopen hf α) (iteratedPartialDeriv α f) Q :=
  ContDiffUpToBoundary.continuousRepresentative_eqOn _

/-- The continuous field retains every finite order of raw closure regularity. -/
theorem derivativeField_regular (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) (k : ℕ) :
    ContDiffUpToBoundary k (derivativeField hopen hf α) Q :=
  ((hf (k + α.length)).iteratedPartialDeriv_of_le
    (isOpen_cylinder hopen) α le_rfl).congr
      (isOpen_cylinder hopen) (derivativeField_eqOn hopen hf α)

/-- Adjacent continuous fields are coordinate derivatives in the cylinder. -/
theorem partialDeriv_derivativeField (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    (i : Fin (n + 1)) {z : ℝ^(n + 1)} (hz : z ∈ Q) :
    (∂[i] (derivativeField hopen hf α)) z =
      derivativeField hopen hf (i :: α) z := by
  have heq := (derivativeField_eqOn hopen hf α).eventuallyEq_of_mem
    ((isOpen_cylinder hopen).mem_nhds hz)
  rw [derivativeField_eqOn hopen hf (i :: α) hz]
  exact congrArg (fun L : ℝ^(n + 1) →L[ℝ] ℝ ↦
    L (EuclideanSpace.single i 1)) heq.fderiv_eq

/-- The canonical mixed derivative on a fixed-time slice. -/
def derivativeSlice (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (α : List (Fin (n + 1))) (t : ℝ) (x : ℝ^n) : ℝ :=
  derivativeField hopen hf α (timeSpaceCons t x)

/-- Canonical slices form a jointly continuous scalar field. -/
theorem continuous_derivativeSlice (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) :
    Continuous (Function.uncurry (derivativeSlice hopen hf α)) :=
  (continuous_derivativeField hopen hf α).comp
    (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous

/-- A continuous function on the closed cylinder has its literal values as
the canonical zeroth derivative, including at both time endpoints. -/
theorem derivativeSlice_nil (hopen : IsOpen Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    (hc : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ closure Ω) :
    derivativeSlice hopen hf [] t x = f (timeSpaceCons t x) := by
  have hcl : closure Q = splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b) := by
    change closure ((spaceTimeContinuousLinearEquiv n).toHomeomorph ⁻¹'
      Ω.prod (Ioo a b)) = _
    have hp : closure (Ω.prod (Ioo a b)) =
        (closure Ω).prod (closure (Ioo a b)) := closure_prod_eq
    rw [← (spaceTimeContinuousLinearEquiv n).toHomeomorph.preimage_closure,
      hp, closure_Ioo hab.ne]
    rfl
  have heq : EqOn (derivativeField hopen hf []) f (closure Q) :=
    (derivativeField_eqOn hopen hf []).of_subset_closure
      (continuous_derivativeField hopen hf []).continuousOn (hcl ▸ hc)
      subset_closure Subset.rfl
  apply heq
  rw [hcl]
  change splitSpaceTime (joinSpaceTime (x, t)) ∈ closure Ω ×ˢ Icc a b
  rw [split_joinSpaceTime]
  exact ⟨hx, ht⟩

/-- Spatial differentials of the canonical slices remain differentials
at both time endpoints. -/
theorem hasFDerivAt_derivativeSlice (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ Ω) :
    HasFDerivAt (derivativeSlice hopen hf α t)
      (∑ i : Fin n, derivativeSlice hopen hf (i.succ :: α) t x •
        (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ))
      x := by
  let K : TopologicalSpace.Compacts (ℝ^n) := ⟨closure Ω, hbounded.isCompact_closure⟩
  let D (s : ℝ) (y : ℝ^n) : ℝ^n →L[ℝ] ℝ :=
    ∑ i : Fin n, derivativeSlice hopen hf (i.succ :: α) s y • EuclideanSpace.proj i
  have hD : Continuous (Function.uncurry D) :=
    continuous_finsetSum _ fun i _ ↦
      (continuous_derivativeSlice hopen hf (i.succ :: α)).smul continuous_const
  apply BoundedContinuousFunction.hasFDerivAt_slice_closure_parameter K hopen
    subset_closure (derivativeSlice hopen hf α) D
    (continuous_derivativeSlice hopen hf α) hD ?_ (by rwa [closure_Ioo hab.ne]) hx
  intro s hs y hy
  have hys : timeSpaceCons s y ∈ Q := by
    change splitSpaceTime (joinSpaceTime (y, s)) ∈ Ω.prod (Ioo a b)
    rw [split_joinSpaceTime]
    exact ⟨hy, hs⟩
  have hdiff := ((derivativeField_regular hopen hf α 1).contDiffOn.contDiffAt
    ((isOpen_cylinder hopen).mem_nhds hys)).differentiableAt (by simp)
  have hslice := hdiff.comp y (hasFDerivAt_timeSpaceCons_spatial n s y).differentiableAt
  have hgrad : D s y = fderiv ℝ (derivativeSlice hopen hf α s) y := by
    ext v
    simp only [D, sum_apply, smul_apply, smul_eq_mul,
      PDE.fderiv_apply_eq_sum_partialDeriv_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (PDE.partialDeriv_timeSpaceCons_spatial i _ s y hdiff).trans
      (partialDeriv_derivativeField hopen hf α i.succ hys) |>.symm
  rw [hgrad]
  exact hslice.hasFDerivAt

/-- Every spatial coordinate successor is the corresponding classical partial,
including for the initial and final time slices. -/
theorem partialDeriv_derivativeSlice (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    (i : Fin n) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ Ω) :
    (∂[i] (derivativeSlice hopen hf α t)) x =
      derivativeSlice hopen hf (i.succ :: α) t x := by
  unfold partialDeriv
  rw [(hasFDerivAt_derivativeSlice hopen hbounded hab hf α ht hx).fderiv]
  simp [sum_apply, smul_apply]

/-- Every canonical time slice is smooth up to the spatial boundary, including
the two endpoint slices. -/
theorem derivativeSlice_regular (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1))) (k : ℕ)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ContDiffUpToBoundary k (derivativeSlice hopen hf α t) Ω := by
  have hu (β : List (Fin (n + 1))) :
      UniformContinuousOn (derivativeSlice hopen hf β t) Ω :=
    (hbounded.isCompact_closure.uniformContinuousOn_of_continuous
      ((continuous_derivativeSlice hopen hf β).comp
        (continuous_const.prodMk continuous_id)).continuousOn).mono subset_closure
  induction k generalizing α with
  | zero => exact ContDiffUpToBoundary.of_uniformContinuousOn (hu α)
  | succ k ih =>
    have hc : ContDiffOn ℝ (k + 1) (derivativeSlice hopen hf α t) Ω := by
      rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hopen.uniqueDiffOn]
      refine ⟨by simp, (fun x ↦ ∑ i : Fin n,
        derivativeSlice hopen hf (i.succ :: α) t x •
          (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ)), ?_, ?_⟩
      · exact ContDiffOn.sum fun i _ ↦
          (ih (i.succ :: α)).contDiffOn.smul contDiffOn_const
      · intro x hx
        exact (hasFDerivAt_derivativeSlice hopen hbounded hab hf α ht hx).hasFDerivWithinAt
    apply ContDiffUpToBoundary.of_partialDeriv hc (hu α)
    intro i
    exact (ih (i.succ :: α)).congr hopen fun x hx ↦
      partialDeriv_derivativeSlice hopen hbounded hab hf α i ht hx

/-- Spatial derivative words of a canonical slice are the corresponding
continuous mixed fields, in the same order of differentiation. -/
theorem iteratedPartialDeriv_derivativeSlice (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    (β : List (Fin n)) {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ Ω) :
    iteratedPartialDeriv β (derivativeSlice hopen hf α t) x =
      derivativeSlice hopen hf (β.map Fin.succ ++ α) t x := by
  induction β generalizing x with
  | nil => rfl
  | cons i β ih =>
    have heq : iteratedPartialDeriv β (derivativeSlice hopen hf α t) =ᶠ[𝓝 x]
        derivativeSlice hopen hf (β.map Fin.succ ++ α) t :=
      (show EqOn _ _ Ω from fun y hy ↦ ih hy).eventuallyEq_of_mem (hopen.mem_nhds hx)
    change (∂[i] (iteratedPartialDeriv β (derivativeSlice hopen hf α t))) x = _
    rw [show (∂[i] (iteratedPartialDeriv β (derivativeSlice hopen hf α t))) x =
        (∂[i] (derivativeSlice hopen hf (β.map Fin.succ ++ α) t)) x from
      congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) heq.fderiv_eq]
    exact partialDeriv_derivativeSlice hopen hbounded hab hf _ i ht hx

/-- Time differentiation of a canonical slice remains valid at spatial boundary
points. This follows by closing the time derivative graph over the compact interval. -/
theorem hasDerivAt_derivativeSlice (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q) (α : List (Fin (n + 1)))
    {t : ℝ} (ht : t ∈ Ioo a b) {x : ℝ^n} (hx : x ∈ closure Ω) :
    HasDerivAt (fun s ↦ derivativeSlice hopen hf α s x)
      (derivativeSlice hopen hf (0 :: α) t x) t := by
  let K : TopologicalSpace.Compacts ℝ := ⟨Icc a b, isCompact_Icc⟩
  let F (y : ℝ^n) (s : ℝ) := derivativeSlice hopen hf α s y
  let D (y : ℝ^n) (s : ℝ) : ℝ →L[ℝ] ℝ :=
    (1 : ℝ →L[ℝ] ℝ).smulRight (derivativeSlice hopen hf (0 :: α) s y)
  have hF : Continuous F.uncurry :=
    (continuous_derivativeSlice hopen hf α).comp continuous_swap
  have hD : Continuous D.uncurry :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp
      ((continuous_derivativeSlice hopen hf (0 :: α)).comp continuous_swap)
  change HasFDerivAt (F x) (D x t) t
  apply BoundedContinuousFunction.hasFDerivAt_slice_closure_parameter K
    isOpen_Ioo Ioo_subset_Icc_self F D hF hD ?_ hx ht
  intro y hy s hs
  have hys : timeSpaceCons s y ∈ Q := by
    change splitSpaceTime (joinSpaceTime (y, s)) ∈ Ω.prod (Ioo a b)
    rw [split_joinSpaceTime]
    exact ⟨hy, hs⟩
  have hd := ((derivativeField_regular hopen hf α 1).contDiffOn.contDiffAt
    ((isOpen_cylinder hopen).mem_nhds hys)).differentiableAt (by simp)
  have h := hd.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_timeSpaceCons_time n s y)
  have heq : fderiv ℝ (derivativeField hopen hf α) (timeSpaceCons s y)
      (EuclideanSpace.single 0 1) = derivativeSlice hopen hf (0 :: α) s y :=
    partialDeriv_derivativeField hopen hf α 0 hys
  rw [heq] at h
  exact h.hasFDerivAt

/-- Permuting derivative coordinates preserves the canonical continuous field
on the cylinder closure. -/
theorem derivativeField_eqOn_of_perm (hopen : IsOpen Ω)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    {α β : List (Fin (n + 1))} (hperm : α.Perm β) :
    EqOn (derivativeField hopen hf α) (derivativeField hopen hf β) (closure Q) := by
  have heq : EqOn (derivativeField hopen hf α) (derivativeField hopen hf β) Q :=
    (derivativeField_eqOn hopen hf α).trans
      ((iteratedPartialDeriv_congr_perm_of_contDiffOn (isOpen_cylinder hopen)
        (hf α.length).contDiffOn le_rfl hperm).trans (derivativeField_eqOn hopen hf β).symm)
  exact heq.of_subset_closure
    (continuous_derivativeField hopen hf α).continuousOn
    (continuous_derivativeField hopen hf β).continuousOn subset_closure Subset.rfl

/-- The canonical mixed fields commute also on initial and final spatial slices. -/
theorem derivativeSlice_eq_of_perm (hopen : IsOpen Ω) (hab : a < b)
    (hf : ∀ k, ContDiffUpToBoundary k f Q)
    {α β : List (Fin (n + 1))} (hperm : α.Perm β)
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ closure Ω) :
    derivativeSlice hopen hf α t x = derivativeSlice hopen hf β t x := by
  apply derivativeField_eqOn_of_perm hopen hf hperm
  change timeSpaceCons t x ∈ closure
    ((spaceTimeContinuousLinearEquiv n).toHomeomorph ⁻¹' Ω.prod (Ioo a b))
  rw [← (spaceTimeContinuousLinearEquiv n).toHomeomorph.preimage_closure]
  change splitSpaceTime (joinSpaceTime (x, t)) ∈ closure (Ω.prod (Ioo a b))
  have hcl : closure (Ω.prod (Ioo a b)) = (closure Ω).prod (closure (Ioo a b)) :=
    closure_prod_eq
  rw [split_joinSpaceTime, hcl, closure_Ioo hab.ne]
  exact ⟨hx, ht⟩

end SobolevSpace.Evolution.Classical
