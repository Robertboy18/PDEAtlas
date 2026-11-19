/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Differentiable.Supporting
public import PDE.Analysis.Convolution.DirectionalDerivative
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Weak second derivatives of convex compositions

The supporting-hyperplane inequality gives a maximum of an integrated translation defect.
Convolution differentiates that defect by differentiating the smooth state and test function.
The convex function itself only needs one continuous derivative.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped Convolution Topology

namespace PDE.DistributionTheory

open PDE.Analysis

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weak convex chain inequality for a compactly supported `C²` state.
The convex function needs only a continuous first derivative. -/
theorem integral_mul_fderiv_second_le_of_convex_compactSupport
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hconvex : ConvexOn ℝ univ η)
    {u : ℝ^n → E} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ x, 0 ≤ φ x) (v : ℝ^n) :
    (∫ x, φ x * fderiv ℝ η (u x)
      (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v)) ≤
      ∫ x, η (u x) * fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v := by
  let a : ℝ^n → ℝ := fun x ↦ η (u (-x))
  let b : ℝ^n → E →L[ℝ] ℝ := fun x ↦ φ (-x) • fderiv ℝ η (u (-x))
  let L : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ := ContinuousLinearMap.id ℝ _
  let A : ℝ^n → ℝ := a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ
  let B : ℝ^n → ℝ := b ⋆[L, volume] u
  have ha : Continuous a := hη.continuous.comp (hu.continuous.comp continuous_neg)
  have hb : Continuous b :=
    (hφ.continuous.comp continuous_neg).smul
      ((hη.continuous_fderiv one_ne_zero).comp (hu.continuous.comp continuous_neg))
  have hA : ContDiff ℝ 2 A :=
    hφc.contDiff_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) ha.locallyIntegrable hφ
  have hB : ContDiff ℝ 2 B := huc.contDiff_convolution_right (L := L) hb.locallyIntegrable hu
  have hAi (z : ℝ^n) : A z = ∫ x, φ x * η (u (x - z)) := by
    rw [show A z = (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) z from rfl,
      convolution_eq_swap]
    apply integral_congr_ae
    filter_upwards with x
    simp [a, neg_sub, mul_comm]
  have hBi (z : ℝ^n) : B (-z) =
      ∫ x, φ x * fderiv ℝ η (u x) (u (x - z)) := by
    change (∫ x, L (b x) (u (-z - x))) = _
    rw [← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with x
    simp [b, L, sub_eq_add_neg, add_comm]
  have hi (z : ℝ^n) :
      Integrable (fun x ↦ φ x * fderiv ℝ η (u x) (u (x - z))) := by
    apply Continuous.integrable_of_hasCompactSupport _ hφc.mul_right
    exact hφ.continuous.mul
      (((hη.continuous_fderiv one_ne_zero).comp hu.continuous).clm_apply
        (hu.continuous.comp (continuous_id.sub continuous_const)))
  have hj (z : ℝ^n) : Integrable (fun x ↦ φ x * η (u (x - z))) :=
    (hφ.continuous.mul (hη.continuous.comp
      (hu.continuous.comp (continuous_id.sub continuous_const)))).integrable_of_hasCompactSupport
        hφc.mul_right
  have hrepr (z : ℝ^n) :
      B (-z) - A z = ∫ x, φ x *
        (fderiv ℝ η (u x) (u (x - z)) - η (u (x - z))) := by
    rw [hAi, hBi, ← integral_sub (hi z) (hj z)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hmax : IsLocalMax (fun z ↦ B (-z) - A z) (0 : ℝ^n) := by
    apply Eventually.of_forall
    intro z
    change B (-z) - A z ≤ B (-0) - A 0
    rw [hrepr, hrepr]
    apply integral_mono
    · exact ((hi z).sub (hj z)).congr (Eventually.of_forall fun x ↦ (mul_sub ..).symm)
    · exact ((hi 0).sub (hj 0)).congr (Eventually.of_forall fun x ↦ (mul_sub ..).symm)
    · intro x
      have hs := fderiv_apply_sub_le_sub_of_convex hconvex
        (hη.differentiable_one (u x)).hasFDerivAt (u (x - z)) (mem_univ _) (mem_univ _)
      rw [map_sub] at hs
      apply mul_le_mul_of_nonneg_left _ (hφ0 x)
      simp only [sub_zero]
      linarith
  have hBneg : ContDiff ℝ 2 (fun z ↦ B (-z)) := hB.comp contDiff_neg
  have hcurv := secondDirectionalDerivative_nonpos_at_localMax hmax
    (hBneg.sub hA).continuous.continuousAt v
  change secondDirectionalDerivative (fun z ↦ B (-z) + -A z) 0 v ≤ 0 at hcurv
  rw [secondDirectionalDerivative_add hBneg.contDiffAt hA.neg.contDiffAt,
    secondDirectionalDerivative_neg] at hcurv
  have hrev : secondDirectionalDerivative (fun z ↦ B (-z)) 0 v =
      secondDirectionalDerivative B 0 (-v) := by
    simp only [secondDirectionalDerivative, zero_add, smul_neg]
  rw [hrev, secondDirectionalDerivative_neg_direction hB.contDiffAt] at hcurv
  have hAsecond : secondDirectionalDerivative A 0 v =
      ∫ x, η (u x) * fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v := by
    rw [hφc.secondDirectionalDerivative_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) ha.locallyIntegrable hφ]
    rw [convolution_def, ← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with x
    simp [a]
  have hBsecond : secondDirectionalDerivative B 0 v =
      ∫ x, φ x * fderiv ℝ η (u x)
        (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v) := by
    rw [huc.secondDirectionalDerivative_convolution_right L hb.locallyIntegrable hu]
    rw [convolution_def, ← integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with x
    simp [b, L]
  rw [hAsecond, hBsecond] at hcurv
  linarith

/-- The weak convex chain inequality on an open set. Only the state near the compact
support of the test is differentiated, and the convex function remains merely `C¹`. -/
theorem integral_mul_fderiv_second_le_of_convex
    {η : E → ℝ} (hη : ContDiff ℝ 1 η) (hconvex : ConvexOn ℝ univ η)
    {U : Set (ℝ^n)} (hU : IsOpen U) {u : ℝ^n → E} (hu : ContDiffOn ℝ 2 u U)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ U) (hφ0 : ∀ x, 0 ≤ φ x) (v : ℝ^n) :
    (∫ x, φ x * fderiv ℝ η (u x)
      (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v)) ≤
      ∫ x, η (u x) * fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v := by
  obtain ⟨ψ, hψU, _, hψone, _⟩ := TestFunction.exists_eq_one_on_compact hU hφc hsupp
  let g : ℝ^n → E := fun x ↦ ψ x • u x
  have hg : ContDiff ℝ 2 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport ψ
    · exact (ψ.contDiff.of_le (by simp)).contDiffAt.smul
        (hu.contDiffAt (hU.mem_nhds (hψU hx)))
    · have heq : g =ᶠ[𝓝 x] fun _ ↦ (0 : E) := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hx] with y hy
        simp [g, image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  have hgc : HasCompactSupport g := ψ.hasCompactSupport.smul_right
  have heq (x : ℝ^n) (hx : x ∈ tsupport φ) : u =ᶠ[𝓝 x] g := by
    filter_upwards [hψone x hx] with y hy
    change ψ y = (1 : ℝ) at hy
    simp [g, hy]
  have hleft :
      (∫ x, φ x * fderiv ℝ η (u x)
        (fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v)) =
      ∫ x, φ x * fderiv ℝ η (g x)
        (fderiv ℝ (fun y ↦ fderiv ℝ g y v) x v) := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · have hfirst : (fun y ↦ fderiv ℝ u y v) =ᶠ[𝓝 x]
          (fun y ↦ fderiv ℝ g y v) :=
        ((heq x hx).fderiv (𝕜 := ℝ)).mono fun y hy ↦ congrArg (fun A ↦ A v) hy
      rw [(heq x hx).eq_of_nhds, hfirst.fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hright :
      (∫ x, η (u x) * fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v) =
      ∫ x, η (g x) * fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [(heq x hx).eq_of_nhds]
    · have hz : φ =ᶠ[𝓝 x] (0 : ℝ^n → ℝ) :=
        notMem_tsupport_iff_eventuallyEq.mp hx
      have hfirst : (fun y ↦ fderiv ℝ φ y v) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
        filter_upwards [hz.fderiv (𝕜 := ℝ)] with y hy
        simp [hy]
      simp [hfirst.fderiv_eq]
  rw [hleft, hright]
  exact integral_mul_fderiv_second_le_of_convex_compactSupport hη hconvex hg hgc hφ hφc hφ0 v

end PDE.DistributionTheory
