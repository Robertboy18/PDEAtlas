/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Constant
public import PDE.Analysis.Fourier.CompactSupport.Parameter
public import PDE.Analysis.Fourier.CompactSupport.TimeDerivative
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Fourier

/-!
# Fourier evolution of compactly supported classical systems

The space and time derivatives of a jointly `C¹` field give the
inhomogeneous Fourier ODE. A common compact spatial support supplies the
integrability needed for differentiation and integration by parts.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis

variable {V E ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Fintype ι]

/-- A compactly supported classical first-order system gives the
Fourier ODE, with no spectral hypothesis on its constant operators. -/
theorem hasDerivAt_fourier_of_firstOrder
    (v : ι → V) (A : ι → E →L[ℂ] E)
    {u : ℝ × V → E} {F : V → E} {I : Set ℝ} {K : Set V}
    (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (I ×ˢ univ))
    (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0)
    {t : ℝ} (ht : t ∈ I) (hF : Integrable F)
    (heq : ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, v j)) = F x) (ξ : V) :
    HasDerivAt (fun s ↦ 𝓕 (fun x ↦ u (s, x)) ξ)
      (((-(2 * Real.pi * Complex.I)) • ∑ j, ⟪v j, ξ⟫ • A j)
        (𝓕 (fun x ↦ u (t, x)) ξ) + 𝓕 F ξ) t := by
  have hopen : IsOpen (I ×ˢ (univ : Set V)) := hI.prod isOpen_univ
  have hud (s : ℝ) (hsI : s ∈ I) (x : V) : DifferentiableAt ℝ u (s, x) :=
    (hu.contDiffAt (hopen.mem_nhds ⟨hsI, mem_univ x⟩)).differentiableAt one_ne_zero
  have hD : ContinuousOn (fun p : ℝ × V ↦ fderiv ℝ u p (1, 0)) (I ×ˢ univ) :=
    (hu.continuousOn_fderiv_of_isOpen hopen le_rfl).clm_apply continuousOn_const
  have hd := Fourier.hasDerivAt_fourier_of_locally_uniform_compact_support
    (u := fun s x ↦ u (s, x)) (D := fun s x ↦ fderiv ℝ u (s, x) (1, 0))
    hI hK hu.continuousOn hD
    (fun s hsI x ↦ (hud s hsI x).hasFDerivAt.comp_hasDerivAt s
      (hasFDerivAt_prodMk_left s x).hasDerivAt)
    hs ht ξ
  have hslice : ContDiff ℝ 1 (fun x ↦ u (t, x)) :=
    contDiffOn_univ.mp (hu.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ ↦ ⟨ht, mem_univ x⟩))
  have hsupport : HasCompactSupport (fun x ↦ u (t, x)) :=
    HasCompactSupport.of_support_subset_isCompact hK
      (Function.support_subset_iff'.mpr (hs t ht))
  have hsliceD (x : V) :
      fderiv ℝ (fun y ↦ u (t, y)) x =
        (fderiv ℝ u (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ V) :=
    ((hud t ht x).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  let P : V → E := fun x ↦ ∑ j, A j (fderiv ℝ (fun y ↦ u (t, y)) x (v j))
  have hPi : Integrable P := by
    apply integrable_finsetSum
    intro j _
    exact (A j).integrable_comp
      (((hslice.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
        (hsupport.fderiv ℝ)).apply_continuousLinearMap (v j))
  have hsplit : (fun x ↦ fderiv ℝ u (t, x) (1, 0)) = fun x ↦ F x - P x := by
    funext x
    apply eq_sub_iff_add_eq.mpr
    simpa only [P, hsliceD, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply] using heq x
  apply hd.congr_deriv
  rw [hsplit]
  have hsub : 𝓕 (fun x ↦ F x - P x) ξ = 𝓕 F ξ - 𝓕 P ξ := by
    simp only [Real.fourier_eq, smul_sub]
    exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hF)
      ((Real.fourierIntegral_convergent_iff ξ).2 hPi)
  rw [hsub, fourier_firstOrder_of_contDiff_hasCompactSupport v A hslice hsupport]
  simp [sub_eq_add_neg, add_comm]

attribute [local instance] Evolution.normedAlgebraRatLinearEndomorphism

/-- The inhomogeneous Fourier evolution formula follows from a classical
system on the open time interval and continuity at both time faces. -/
theorem fourier_eq_exp_add_integral_of_firstOrder
    (v : ι → V) (A : ι → E →L[ℂ] E)
    {u F : ℝ × V → E} {a b : ℝ} {K : Set V}
    (hab : a ≤ b) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ))
    (huc : ContinuousOn u (Icc a b ×ˢ univ))
    (hFc : ContinuousOn F (Icc a b ×ˢ univ))
    (hsu : ∀ t ∈ Icc a b, ∀ x ∉ K, u (t, x) = 0)
    (hsF : ∀ t ∈ Icc a b, ∀ x ∉ K, F (t, x) = 0)
    (heq : ∀ t ∈ Ioo a b, ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, v j)) = F (t, x)) (ξ : V) :
    let G := (-(2 * Real.pi * Complex.I)) • ∑ j, ⟪v j, ξ⟫ • A j
    𝓕 (fun x ↦ u (b, x)) ξ =
      NormedSpace.exp ((b - a) • G) (𝓕 (fun x ↦ u (a, x)) ξ) +
        ∫ s in a..b, NormedSpace.exp ((b - s) • G) (𝓕 (fun x ↦ F (s, x)) ξ) := by
  have hc (g : ℝ × V → E) (hg : ContinuousOn g (Icc a b ×ˢ univ))
      (hs : ∀ t ∈ Icc a b, ∀ x ∉ K, g (t, x) = 0) :
      ContinuousOn (fun s ↦ 𝓕 (fun x ↦ g (s, x)) ξ) (Icc a b) := by
    have hj : ContinuousOn (fun p : ℝ × V ↦ 𝓕 (fun x ↦ g (p.1, x)) p.2)
        (Icc a b ×ˢ univ) :=
      Fourier.continuousOn_fourier_of_uniform_compact_support hK hg hs
    have hp : Continuous (fun s : ℝ ↦ (s, ξ)) := continuous_id.prodMk continuous_const
    have hm : MapsTo (fun s : ℝ ↦ (s, ξ)) (Icc a b) (Icc a b ×ˢ univ) :=
      fun _ ht ↦ ⟨ht, mem_univ ξ⟩
    have hcomp := hj.comp hp.continuousOn hm
    exact hcomp
  apply Evolution.eq_exp_apply_add_integral_of_hasDerivAt _ hab (hc u huc hsu) (hc F hFc hsF)
  intro t ht
  have hFi : Integrable (fun x ↦ F (t, x)) := by
    have hcont : Continuous (fun x ↦ F (t, x)) :=
      hFc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x ↦ ⟨Ioo_subset_Icc_self ht, mem_univ x⟩)
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK
        (Function.support_subset_iff'.mpr (hsF t (Ioo_subset_Icc_self ht))))
  exact hasDerivAt_fourier_of_firstOrder v A isOpen_Ioo hK hu
    (fun s hs ↦ hsu s (Ioo_subset_Icc_self hs)) ht hFi (heq t ht) ξ

end PDE.Analysis
