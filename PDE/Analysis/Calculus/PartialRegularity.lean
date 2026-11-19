/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
# Joint regularity from partial derivatives

On an arbitrary open subset of a product of real normed spaces, continuous
partial Fréchet derivatives give joint C¹ regularity. The joint differential
is the coproduct of the two partial continuous linear maps.

Openness makes the partial derivative identities available on a neighborhood
of each point. Mathlib's `hasStrictFDerivAt_uncurry_coprod` then supplies the
joint derivative. No separate continuity assumption on the original function,
completeness or finite dimensionality is needed.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Set
open scoped Topology

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Continuous partial derivatives determine the joint differential on an open set. -/
theorem hasFDerivAt_of_partial_derivatives
    {f : E × F → G} {S : Set (E × F)}
    {D₁ : E × F → E →L[ℝ] G} {D₂ : E × F → F →L[ℝ] G}
    (hS : IsOpen S)
    (hD₁ : ContinuousOn D₁ S) (hD₂ : ContinuousOn D₂ S)
    (h₁ : ∀ p ∈ S, HasFDerivAt (fun x ↦ f (x, p.2)) (D₁ p) p.1)
    (h₂ : ∀ p ∈ S, HasFDerivAt (fun y ↦ f (p.1, y)) (D₂ p) p.2)
    {p : E × F} (hp : p ∈ S) :
    HasFDerivAt f
      ((D₁ p).comp (ContinuousLinearMap.fst ℝ E F) +
        (D₂ p).comp (ContinuousLinearMap.snd ℝ E F)) p := by
  have hnhds : S ∈ 𝓝 p := hS.mem_nhds hp
  have hfirst : ∀ᶠ z in 𝓝 p,
      HasFDerivAt (fun x ↦ f (x, z.2)) (D₁ z) z.1 := by
    filter_upwards [hnhds] with z hz
    exact h₁ z hz
  have hsecond : ∀ᶠ z in 𝓝 p,
      HasFDerivAt (fun y ↦ f (z.1, y)) (D₂ z) z.2 := by
    filter_upwards [hnhds] with z hz
    exact h₂ z hz
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun x y ↦ f (x, y))
    (f₁ := fun x y ↦ D₁ (x, y)) (f₂ := fun x y ↦ D₂ (x, y))
    hfirst hsecond (hD₁.continuousAt hnhds) (hD₂.continuousAt hnhds)).hasFDerivAt

/-- Partial derivatives of class `Cᵐ` give joint regularity of class `Cᵐ⁺¹`. -/
theorem contDiffOn_succ_of_partial_derivatives
    {f : E × F → G} {S : Set (E × F)}
    {D₁ : E × F → E →L[ℝ] G} {D₂ : E × F → F →L[ℝ] G} {m : ℕ}
    (hS : IsOpen S)
    (hD₁ : ContDiffOn ℝ m D₁ S) (hD₂ : ContDiffOn ℝ m D₂ S)
    (h₁ : ∀ p ∈ S, HasFDerivAt (fun x ↦ f (x, p.2)) (D₁ p) p.1)
    (h₂ : ∀ p ∈ S, HasFDerivAt (fun y ↦ f (p.1, y)) (D₂ p) p.2) :
    ContDiffOn ℝ (m + 1 : ℕ) f S := by
  let D : E × F → (E × F) →L[ℝ] G :=
    fun p ↦ (D₁ p).comp (ContinuousLinearMap.fst ℝ E F) +
      (D₂ p).comp (ContinuousLinearMap.snd ℝ E F)
  have hD : ContDiffOn ℝ m D S :=
    (hD₁.clm_comp contDiffOn_const).add (hD₂.clm_comp contDiffOn_const)
  rw [Nat.cast_add, Nat.cast_one,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS.uniqueDiffOn]
  exact ⟨by simp, D, hD, fun p hp ↦
    (hasFDerivAt_of_partial_derivatives hS hD₁.continuousOn hD₂.continuousOn
      h₁ h₂ hp).hasFDerivWithinAt⟩

/-- Continuous partial Fréchet derivatives on an open set give joint C¹
regularity. The set need not be a product, and the function's continuity
follows from the derivative hypotheses. -/
theorem contDiffOn_one_of_partial_derivatives
    {f : E × F → G} {S : Set (E × F)}
    {D₁ : E × F → E →L[ℝ] G} {D₂ : E × F → F →L[ℝ] G}
    (hS : IsOpen S)
    (hD₁ : ContinuousOn D₁ S) (hD₂ : ContinuousOn D₂ S)
    (h₁ : ∀ p ∈ S, HasFDerivAt (fun x ↦ f (x, p.2)) (D₁ p) p.1)
    (h₂ : ∀ p ∈ S, HasFDerivAt (fun y ↦ f (p.1, y)) (D₂ p) p.2) :
    ContDiffOn ℝ 1 f S :=
  contDiffOn_succ_of_partial_derivatives hS
    (contDiffOn_zero.mpr hD₁) (contDiffOn_zero.mpr hD₂) h₁ h₂

/-- Joint continuity with a time subtype is continuity on the corresponding slab. -/
theorem continuousOn_of_continuous_slab
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X × Y → Z} {I : Set Y}
    (hf : Continuous (fun z : X × I ↦ f (z.1, z.2))) :
    ContinuousOn f (univ ×ˢ I) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hf.comp (continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk fun z ↦ z.property.2))

/-- Scalar partial derivatives of class `Cᵐ` give joint class `Cᵐ⁺¹`. -/
theorem contDiffOn_succ_of_scalar_partial_derivatives
    {f dx dt : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {m : ℕ}
    (hS : IsOpen S) (hx : ContDiffOn ℝ m dx S) (ht : ContDiffOn ℝ m dt S)
    (hdx : ∀ z ∈ S, HasDerivAt (fun x ↦ f (x, z.2)) (dx z) z.1)
    (hdt : ∀ z ∈ S, HasDerivAt (fun t ↦ f (z.1, t)) (dt z) z.2) :
    ContDiffOn ℝ (m + 1 : ℕ) f S :=
  PDE.Analysis.contDiffOn_succ_of_partial_derivatives hS
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).contDiff.comp_contDiffOn hx)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).contDiff.comp_contDiffOn ht)
    (fun z hz ↦ (hdx z hz).hasFDerivAt) (fun z hz ↦ (hdt z hz).hasFDerivAt)

/-- Continuous second scalar partial derivatives imply joint C² regularity.
The two mixed traces may be supplied separately. -/
theorem contDiffOn_two_of_continuous_second_partials
    {f dx dt dxx dxt dtx dtt : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)}
    (hS : IsOpen S)
    (hxx : ContinuousOn dxx S) (hxt : ContinuousOn dxt S)
    (htx : ContinuousOn dtx S) (htt : ContinuousOn dtt S)
    (hdx : ∀ z ∈ S, HasDerivAt (fun x ↦ f (x, z.2)) (dx z) z.1)
    (hdt : ∀ z ∈ S, HasDerivAt (fun t ↦ f (z.1, t)) (dt z) z.2)
    (hdxx : ∀ z ∈ S, HasDerivAt (fun x ↦ dx (x, z.2)) (dxx z) z.1)
    (hdxt : ∀ z ∈ S, HasDerivAt (fun t ↦ dx (z.1, t)) (dxt z) z.2)
    (hdtx : ∀ z ∈ S, HasDerivAt (fun x ↦ dt (x, z.2)) (dtx z) z.1)
    (hdtt : ∀ z ∈ S, HasDerivAt (fun t ↦ dt (z.1, t)) (dtt z) z.2) :
    ContDiffOn ℝ 2 f S :=
  contDiffOn_succ_of_scalar_partial_derivatives hS
    (contDiffOn_succ_of_scalar_partial_derivatives (m := 0) hS
      (contDiffOn_zero.mpr hxx) (contDiffOn_zero.mpr hxt) hdxx hdxt)
    (contDiffOn_succ_of_scalar_partial_derivatives (m := 0) hS
      (contDiffOn_zero.mpr htx) (contDiffOn_zero.mpr htt) hdtx hdtt) hdx hdt


/-- Joint continuity on every finite closed time slab gives joint continuity
on the forward half-line, including its initial boundary. -/
theorem continuousOn_Ici_of_closed_time_slabs
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → ℝ → Y}
    (hf : ∀ T : ℝ, 0 < T → Continuous (fun q : X × Icc (0 : ℝ) T ↦ f q.1 q.2)) :
    ContinuousOn (Function.uncurry f) (univ ×ˢ Ici 0) := by
  intro p hp
  have hT : 0 < p.2 + 1 := by linarith [show 0 ≤ p.2 from hp.2]
  have hc : Continuous (fun q : X × ℝ ↦ f q.1 (projIcc 0 (p.2 + 1) hT.le q.2)) :=
    (hf (p.2 + 1) hT).comp
      (continuous_fst.prodMk ((continuous_projIcc (h := hT.le)).comp continuous_snd))
  apply hc.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem _ hp
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (continuous_snd.tendsto p (Iio_mem_nhds (lt_add_one p.2)))] with q hq hsmall
  simp only [Function.uncurry, projIcc_of_mem hT.le
    (show q.2 ∈ Icc 0 (p.2 + 1) from ⟨hq.2, hsmall.le⟩)]

end PDE.Analysis
