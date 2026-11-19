/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.Spaces.Holder.Evolution.Derivatives
public import PDE.Spaces.Holder.HigherOrder.Norm
import PDE.FDeriv.Calculus

/-!
# Classical spacetime fields on the closed cylinder

We write the mixed fields `mixedField R j α` in spacetime coordinates, with time in coordinate `0`:
`spaceTimeField R j α z = mixedField R j α (splitSpaceTime z)`. Let `Ω` be open and let the curves
`R j` be continuous on `[a, b]` with `R j.succ` the derivative of `R j.castSucc` within `[a, b]`. On
the open cylinder, for `j < k` and `α.order < k`, `∂_0` takes the field of `(j, α)` to that of
`(j + 1, α)` and `∂_{i+1}` takes it to that of `(j, α.succ hα i)`, so every derivative word `w` with
`j + α.order + w.length ≤ k` takes a field to another field there
(`exists_iteratedPartialDeriv_eq_spaceTimeField`). For bounded `Ω` the closed cylinder is compact,
so the fields are uniformly continuous on it, and the derivative words of the fields are uniformly
continuous on the open cylinder (`uniformContinuousOn_iteratedPartialDeriv_spaceTimeField`); we use
no smooth extension across the boundary.
-/

@[expose] public section

open PDE (SpaceTime partialDeriv time iteratedPartialDeriv)

noncomputable section

open Set PDE.Common
open scoped Topology

namespace HolderSpace.CKGammaOn

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent} {a b : ℝ}

/-- The mixed field in canonical spacetime coordinates, with time in coordinate zero. -/
def spaceTimeField (R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ)
    (j : Fin (k + 1)) (α : MultiIndex n k) (z : SpaceTime n) : ℝ :=
  mixedField R j α (splitSpaceTime z)

/-- If every `R j` is continuous on `[a, b]`, then `spaceTimeField R j α` is continuous on the
closed cylinder `splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)`. -/
theorem continuousOn_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ}
    (hR : ∀ j, ContinuousOn (R j) (Icc a b))
    (j : Fin (k + 1)) (α : MultiIndex n k) :
    ContinuousOn (spaceTimeField R j α)
      (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) :=
  (continuousOn_mixedField hR j α).comp
    (spaceTimeContinuousLinearEquiv n).continuous.continuousOn
    (fun _ hz ↦ hz)

/-- For open `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, `spaceTimeField R j α` is `C^m` on the open cylinder
`splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)` whenever `j + α.order + m ≤ k`. -/
theorem contDiffOn_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (m : ℕ) (j : Fin (k + 1)) (α : MultiIndex n k)
    (hm : j.val + α.order + m ≤ k) :
    ContDiffOn ℝ m (spaceTimeField R j α) (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) :=
  (contDiffOn_mixedField hΩ hcontinuous hderiv m j α hm).comp
    (spaceTimeContinuousLinearEquiv n).contDiff.contDiffOn (fun _ hz ↦ hz)

/-- For open `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, `α.order < k` and `z` in the open cylinder,
`∂[0] (spaceTimeField R j.castSucc α) z = spaceTimeField R j.succ α z`. -/
theorem partialDeriv_spaceTimeField_zero
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (j : Fin k) (α : MultiIndex n k) (hα : α.order < k)
    {z : SpaceTime n} (hz : splitSpaceTime z ∈ Ω ×ˢ Ioo a b) :
    (∂[0] (spaceTimeField R j.castSucc α)) z = spaceTimeField R j.succ α z := by
  have hd := (hasFDerivAt_mixedField hΩ hcontinuous hderiv j α hα hz).comp z
    (spaceTimeContinuousLinearEquiv n).hasFDerivAt
  change HasFDerivAt (spaceTimeField R j.castSucc α) _ z at hd
  rw [partialDeriv, hd.fderiv]
  have he : splitSpaceTime (EuclideanSpace.single (0 : Fin (n + 1)) 1) =
      ((0 : ℝ^n), (1 : ℝ)) := by
    apply Prod.ext
    · exact (spatialPartCLM_eq_spatialPart n _).symm.trans (spatialPartCLM_single_zero n)
    · simp [splitSpaceTime, time]
  simp [he, spaceTimeField]

/-- For open `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, `α.order < k` and `z` in the open cylinder,
`∂[i.succ] (spaceTimeField R j.castSucc α) z = spaceTimeField R j.castSucc (α.succ hα i) z`. -/
theorem partialDeriv_spaceTimeField_succ
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (j : Fin k) (α : MultiIndex n k) (hα : α.order < k) (i : Fin n)
    {z : SpaceTime n} (hz : splitSpaceTime z ∈ Ω ×ˢ Ioo a b) :
    (∂[i.succ] (spaceTimeField R j.castSucc α)) z =
      spaceTimeField R j.castSucc (α.succ hα i) z := by
  have hd := (hasFDerivAt_mixedField hΩ hcontinuous hderiv j α hα hz).comp z
    (spaceTimeContinuousLinearEquiv n).hasFDerivAt
  change HasFDerivAt (spaceTimeField R j.castSucc α) _ z at hd
  rw [partialDeriv, hd.fderiv]
  have he : splitSpaceTime (EuclideanSpace.single i.succ 1) =
      (EuclideanSpace.single i (1 : ℝ), (0 : ℝ)) := by
    apply Prod.ext
    · exact (spatialPartCLM_eq_spatialPart n _).symm.trans (spatialPartCLM_single_succ n i)
    · simp [splitSpaceTime, time]
  simp [he, spaceTimeField]

/-- For open `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, if `j + α.order + w.length ≤ k`, then
`iteratedPartialDeriv w (spaceTimeField R j α)` agrees on the open cylinder
`splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)` with `spaceTimeField R l β` for some `l` and `β` with
`l + β.order = j + α.order + w.length`. -/
theorem exists_iteratedPartialDeriv_eq_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (w : List (Fin (n + 1))) (j : Fin (k + 1)) (α : MultiIndex n k)
    (hw : j.val + α.order + w.length ≤ k) :
    ∃ l : Fin (k + 1), ∃ β : MultiIndex n k,
      l.val + β.order = j.val + α.order + w.length ∧
      EqOn (iteratedPartialDeriv w (spaceTimeField R j α)) (spaceTimeField R l β)
        (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) := by
  have hQ : IsOpen (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) :=
    (hΩ.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous
  induction w with
  | nil => exact ⟨j, α, by simp, fun _ _ ↦ rfl⟩
  | cons i w ih =>
    obtain ⟨l, β, horder, heq⟩ := ih (by simp only [List.length_cons] at hw; omega)
    have hl : l.val < k := by simp only [List.length_cons] at hw; omega
    have hβ : β.order < k := by simp only [List.length_cons] at hw; omega
    let l' : Fin k := ⟨l.val, hl⟩
    cases i using Fin.cases with
    | zero =>
      refine ⟨l'.succ, β, ?_, ?_⟩
      · simp only [List.length_cons, Fin.val_succ]
        dsimp [l']
        omega
      · intro z hz
        change (∂[0] (iteratedPartialDeriv w (spaceTimeField R j α))) z = _
        rw [PDE.partialDeriv_congr_nhds 0 (heq.eventuallyEq_of_mem (hQ.mem_nhds hz))]
        exact partialDeriv_spaceTimeField_zero hΩ hcontinuous hderiv l' β hβ hz
    | succ i =>
      refine ⟨l, β.succ hβ i, ?_, ?_⟩
      · simp only [MultiIndex.order_succ, List.length_cons]
        omega
      · intro z hz
        change (∂[i.succ] (iteratedPartialDeriv w (spaceTimeField R j α))) z = _
        rw [PDE.partialDeriv_congr_nhds i.succ (heq.eventuallyEq_of_mem (hQ.mem_nhds hz))]
        exact partialDeriv_spaceTimeField_succ hΩ hcontinuous hderiv l' β hβ i hz

/-- If `Ω` is bounded and every `R j` is continuous on `[a, b]`, then `spaceTimeField R j α` is
uniformly continuous on the closed cylinder `splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)`. -/
theorem uniformContinuousOn_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ}
    (hbounded : Bornology.IsBounded Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (j : Fin (k + 1)) (α : MultiIndex n k) :
    UniformContinuousOn (spaceTimeField R j α)
      (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) := by
  have hK : IsCompact (splitSpaceTime ⁻¹' (closure Ω ×ˢ Icc a b)) :=
    (spaceTimeContinuousLinearEquiv n).toHomeomorph.isCompact_preimage.mpr
      (hbounded.isCompact_closure.prod isCompact_Icc)
  exact hK.uniformContinuousOn_of_continuous (continuousOn_spaceTimeField hcontinuous j α)

/-- For open bounded `Ω` and curves `R j` continuous on `[a, b]` with `R j.succ` the derivative of
`R j.castSucc` within `[a, b]`, if `j + α.order + w.length ≤ k`, then
`iteratedPartialDeriv w (spaceTimeField R j α)` is uniformly continuous on the open cylinder
`splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)`. -/
theorem uniformContinuousOn_iteratedPartialDeriv_spaceTimeField
    {R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hcontinuous : ∀ j, ContinuousOn (R j) (Icc a b))
    (hderiv : ∀ j : Fin k, ∀ t ∈ Icc a b,
      HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t)
    (w : List (Fin (n + 1))) (j : Fin (k + 1)) (α : MultiIndex n k)
    (hw : j.val + α.order + w.length ≤ k) :
    UniformContinuousOn (iteratedPartialDeriv w (spaceTimeField R j α))
      (splitSpaceTime ⁻¹' (Ω ×ˢ Ioo a b)) := by
  obtain ⟨l, β, _, heq⟩ :=
    exists_iteratedPartialDeriv_eq_spaceTimeField hΩ hcontinuous hderiv w j α hw
  exact ((uniformContinuousOn_spaceTimeField hbounded hcontinuous l β).mono
    (preimage_mono (prod_mono subset_closure Ioo_subset_Icc_self))).congr heq.symm

/-- If the spatial part of `z` lies in `closure Ω`, then
`‖spaceTimeField R j α z‖ ≤ ‖R j (time z)‖`. -/
theorem norm_spaceTimeField_le
    (R : Fin (k + 1) → ℝ → CKGammaOn n k Ω γ)
    (j : Fin (k + 1)) (α : MultiIndex n k) {z : SpaceTime n}
    (hz : spatialPart z ∈ closure Ω) :
    ‖spaceTimeField R j α z‖ ≤ ‖R j (time z)‖ := by
  rw [spaceTimeField, mixedField, splitSpaceTime, interiorDerivative_apply _ _ hz]
  exact ((R j (time z)).derivative α).norm_coe_le_norm ⟨spatialPart z, hz⟩
    |>.trans ((R j (time z)).norm_derivative_le α)

end HolderSpace.CKGammaOn
