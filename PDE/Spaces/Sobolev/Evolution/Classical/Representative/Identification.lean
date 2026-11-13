/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Evolution.Classical.Data

/-!
# Identifying joint representatives and their canonical derivatives

A joint continuous representative agrees on the closed cylinder with the
canonical zeroth derivative of its interior smooth function. Its canonical
slices recover the entire spatial Sobolev class, and adjacent time fields are
within-interval derivatives even at the two endpoints.
-/

@[expose] public noncomputable section

open PDE (SpaceTime iteratedPartialDeriv)

open scoped Sobolev

namespace SobolevSpace.Evolution.Classical

open Filter MeasureTheory Set PDE.Common SobolevSpace.GraphSpace
open PDE.Analysis.Evolution

variable {n r : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hab : a < b)
  {f : SpaceTime n → ℝ}
  (hf : ∀ k, ContDiffUpToBoundary k f (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)))

include hab in
/-- When a classical derivative already has continuous literal closure values,
those values agree with the canonical mixed field at both time endpoints. -/
theorem derivativeSlice_eq_of_continuousOn
    (α : List (Fin (n + 1)))
    (hα : ContinuousOn (iteratedPartialDeriv α f)
      (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {t : ℝ} (ht : t ∈ Icc a b) {x : ℝ^n} (hx : x ∈ closure Ω) :
    derivativeSlice hopen hf α t x = iteratedPartialDeriv α f (timeSpaceCons t x) := by
  have hcl : closure (splitSpaceTime ⁻¹' Ω.prod (Ioo a b)) =
      splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b) := by
    change closure ((spaceTimeContinuousLinearEquiv n).toHomeomorph ⁻¹'
      Ω.prod (Ioo a b)) = _
    have hp : closure (Ω.prod (Ioo a b)) = (closure Ω).prod (closure (Ioo a b)) :=
      closure_prod_eq
    rw [← (spaceTimeContinuousLinearEquiv n).toHomeomorph.preimage_closure,
      hp, closure_Ioo hab.ne]
    rfl
  have heq := (derivativeField_eqOn hopen hf α).of_subset_closure
    (continuous_derivativeField hopen hf α).continuousOn (hcl ▸ hα)
    subset_closure Subset.rfl
  apply heq
  rw [hcl]
  change splitSpaceTime (joinSpaceTime (x, t)) ∈ closure Ω ×ˢ Icc a b
  rw [split_joinSpaceTime]
  exact ⟨hx, ht⟩

/-- Scalar almost-everywhere identification of a smooth joint representative
determines its entire spatial Sobolev class at almost every time. -/
theorem sobolevCurve_ae_of_representative
    (hcont : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {v : ℝ → W^{r,2}(Ω)}
    (hae : ∀ᵐ t ∂volume.restrict (Ioo a b),
      (fun x ↦ f (timeSpaceCons t x)) =ᵐ[domainMeasure n Ω] baseRepresentative (v t)) :
    sobolevCurve hopen hbounded hab hf r 0 =ᵐ[volume.restrict (Ioc a b)] v := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with t ht hti
  apply wkpBaseCoordinateCLM_injective hopen
  exact wkpBaseCoordinate_sobolevCurve_zero_eq hopen hbounded hab hf hcont r
    (Ioo_subset_Icc_self hti) ht

include hab in
/-- Canonical mixed derivative fields are time derivatives within the
closed interval, at spatial boundary points as well as interior points. -/
theorem hasDerivWithinAt_derivativeSlice
    (α : List (Fin (n + 1))) {x : ℝ^n} (hx : x ∈ closure Ω)
    {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s ↦ derivativeSlice hopen hf α s x)
      (derivativeSlice hopen hf (0 :: α) t x) (Icc a b) t := by
  have hc (β : List (Fin (n + 1))) :
      Continuous (fun s ↦ derivativeSlice hopen hf β s x) :=
    (continuous_derivativeSlice hopen hf β).comp
      (continuous_id.prodMk continuous_const)
  have hd := hasWeakTimeDerivativeOn_of_continuousOn_hasDerivAt
    (hc α).continuousOn (hc (0 :: α)).continuousOn
    (fun s hs ↦ hasDerivAt_derivativeSlice hopen hf α hs hx)
  exact hd.hasDerivWithinAt_of_continuousOn hab (hc α).continuousOn
    (hc (0 :: α)).continuousOn ht

include hab in
/-- The original continuous joint representative has its canonical first time
derivative throughout the closed interval, including spatial boundary points. -/
theorem hasDerivWithinAt_timeSlice
    (hcont : ContinuousOn f (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)))
    {x : ℝ^n} (hx : x ∈ closure Ω) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s ↦ f (timeSpaceCons s x))
      (derivativeSlice hopen hf [0] t x) (Icc a b) t := by
  exact (hasDerivWithinAt_derivativeSlice hopen hab hf [] hx ht).congr_of_mem
    (fun s hs ↦ (derivativeSlice_nil hopen hab hf hcont hs hx).symm) ht

end SobolevSpace.Evolution.Classical
