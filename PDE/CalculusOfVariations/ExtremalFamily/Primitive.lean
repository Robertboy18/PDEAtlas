/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ParametricIntervalRegularity
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
public import PDE.Analysis.Integration.ParametricInterval
/-!
# Primitives of parameterized fluxes

The interval integral of a jointly `C¹` flux remains `C¹` when the endpoint varies
in space. Its differential includes both the endpoint term and the integral of
the spatial differential. Compactness of the parameter interval supplies the
bounds for differentiation under the integral.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace PDE.CalculusOfVariations.ExtremalFamily

open Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

private theorem contDiffAt_intervalAverage
    {H : E × ℝ → F} {x : E}
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 H (x, t)) :
    ContDiffAt ℝ 1 (fun y ↦ ∫ t in (0 : ℝ)..1, H (y, t)) x := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 1 H (y, t) :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht ↦ (hH t ht).eventually (by norm_num))
  obtain ⟨U, hUsub, hU, hx⟩ := mem_nhds_iff.mp hnear
  apply (contDiffOn_intervalIntegral (n := 1) (a := 0) (b := 1) hU ?_).contDiffAt
    (hU.mem_nhds hx)
  intro p hp
  exact (hUsub hp.1 p.2 (by simpa using hp.2)).contDiffWithinAt

/-- The primitive of the family flux, evaluated at a spatially varying parameter. -/
def parameterPrimitive (H : E × ℝ → F) (θ : E → ℝ) (x : E) : F :=
  ∫ t in (0 : ℝ)..θ x, H (x, t)

/-- Integrating a `C¹` flux to a `C¹` endpoint preserves local `C¹` regularity. -/
theorem contDiffAt_parameterPrimitive
    {H : E × ℝ → F} {θ : E → ℝ} {x : E}
    (hH : ∀ t ∈ uIcc (0 : ℝ) (θ x), ContDiffAt ℝ 1 H (x, t))
    (hθ : ContDiffAt ℝ 1 θ x) :
    ContDiffAt ℝ 1 (parameterPrimitive H θ) x := by
  have hg : ContDiffAt ℝ 1
      (fun y ↦ ∫ t in (0 : ℝ)..1, H (y, t * θ y)) x := by
    apply contDiffAt_intervalAverage (H := fun p : E × ℝ ↦ H (p.1, p.2 * θ p.1))
    intro t ht
    have htx : t * θ x ∈ uIcc (0 : ℝ) (θ x) := by
      by_cases h : 0 ≤ θ x
      · rw [uIcc_of_le h]
        exact ⟨mul_nonneg ht.1 h, mul_le_of_le_one_left h ht.2⟩
      · rw [uIcc_of_ge (le_of_not_ge h)]
        constructor
        · nlinarith [ht.2]
        · exact mul_nonpos_of_nonneg_of_nonpos ht.1 (le_of_not_ge h)
    exact (hH _ htx).comp (x, t)
      (contDiffAt_fst.prodMk
        (contDiffAt_snd.mul (hθ.comp (x, t) contDiffAt_fst)))
  have h := hθ.smul hg
  convert h using 1
  funext y
  change (∫ t in (0 : ℝ)..θ y, H (y, t)) =
    θ y • ∫ t in (0 : ℝ)..1, H (y, t * θ y)
  symm
  simpa only [zero_mul, one_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (f := fun t ↦ H (y, t)) (a := 0) (b := 1) (θ y))

/-- The differential of a moving-endpoint primitive is its endpoint contribution
plus the integral of the spatial differential. An open parameter interval suffices. -/
theorem hasFDerivAt_parameterPrimitive
    {H : E × ℝ → F} {θ : E → ℝ} {x : E} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : OrdConnected J) (h0 : 0 ∈ J) (hθJ : θ x ∈ J)
    (hH : ∀ t ∈ J, ContDiffAt ℝ 1 H (x, t))
    (hθ : DifferentiableAt ℝ θ x) :
    HasFDerivAt (parameterPrimitive H θ)
      ((fderiv ℝ θ x).smulRight (H (x, θ x)) +
        ∫ t in (0 : ℝ)..θ x,
          (fderiv ℝ H (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  obtain ⟨lo, hi, hθI, hInhds, hIJ⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (hJ.mem_nhds hθJ)
  have hloJ : lo ∈ J := hIJ ⟨le_rfl, hθI.1.trans hθI.2⟩
  have hhiJ : hi ∈ J := hIJ ⟨hθI.1.trans hθI.2, le_rfl⟩
  let K := Icc (min 0 lo) (max 0 hi)
  have hKJ : K ⊆ J := by
    apply hJc.out
    · rcases le_total 0 lo with h | h
      · simpa [min_eq_left h] using h0
      · simpa [min_eq_right h] using hloJ
    · rcases le_total 0 hi with h | h
      · simpa [max_eq_right h] using hhiJ
      · simpa [max_eq_left h] using h0
  have h0K : (0 : ℝ) ∈ K := ⟨min_le_left _ _, le_max_left _ _⟩
  have hIK : Icc lo hi ⊆ K :=
    fun _ ht ↦ ⟨(min_le_right _ _).trans ht.1, ht.2.trans (le_max_right _ _)⟩
  have hθK : θ x ∈ K := hIK hθI
  have hseg : uIcc (0 : ℝ) (θ x) ⊆ K := uIcc_subset_Icc h0K hθK
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ K, ContDiffAt ℝ 1 H (y, t) :=
    isCompact_Icc.eventually_forall_of_forall_eventually
      (fun t ht ↦ (hH t (hKJ ht)).eventually (by norm_num))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  let D : E → ℝ → E →L[ℝ] F := fun y t ↦
    (fderiv ℝ H (y, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hHC : ContinuousOn H (U ×ˢ K) :=
    fun p hp ↦ (hUsub hp.1 p.2 hp.2).continuousAt.continuousWithinAt
  have hDC : ContinuousOn D.uncurry (U ×ˢ K) := by
    intro p hp
    exact (((hUsub hp.1 p.2 hp.2).fderiv_right
      (m := 0) (by norm_num)).continuousAt.clm_comp
        continuousAt_const).continuousWithinAt
  have hd (y : E) (hy : y ∈ U) (t : ℝ) (ht : t ∈ K) :
      HasFDerivAt (fun z ↦ H (z, t)) (D y t) y :=
    ((hUsub hy t ht).differentiableAt (by norm_num)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y t)
  have hfixed : HasFDerivAt (fun y ↦ ∫ t in (0 : ℝ)..θ x, H (y, t))
      (∫ t in (0 : ℝ)..θ x, D x t) x :=
    hasFDerivAt_intervalIntegral_of_continuousOn
      (F := fun y t ↦ H (y, t)) (D := D) (a := 0) (b := θ x) hU
      (hHC.mono (prod_mono_right hseg))
      (hDC.mono (prod_mono_right hseg))
      (fun y hy t ht ↦ hd y hy t (hseg ht)) hxU
  have hslice (y : E) (hy : y ∈ U) : ContinuousOn (fun t ↦ H (y, t)) K :=
    hHC.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht ↦ ⟨hy, ht⟩)
  have hsliceJ : ContinuousOn (fun t ↦ H (x, t)) J :=
    fun t ht ↦ ((hH t ht).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  apply hasFDerivAt_intervalIntegral_moving_right
    (fun y t ↦ H (y, t)) 0 θ x hθ.hasFDerivAt hfixed (hH _ hθJ).continuousAt
    (hsliceJ.stronglyMeasurableAtFilter hJ _ hθJ)
  filter_upwards [hU.mem_nhds hxU, hθ.continuousAt hInhds] with y hy hθy
  exact ⟨((hslice y hy).mono hseg).intervalIntegrable,
    ((hslice y hy).mono (uIcc_subset_Icc hθK (hIK hθy))).intervalIntegrable,
    ((hslice x hxU).mono (uIcc_subset_Icc hθK (hIK hθy))).intervalIntegrable⟩

end PDE.CalculusOfVariations.ExtremalFamily
