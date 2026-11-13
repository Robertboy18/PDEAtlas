/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convolution.ParameterDerivative
public import PDE.Common.Euclidean.Cylinder
public import PDE.Hyperbolic.Models.Wave.Regularization.Spatial
import PDE.Analysis.Calculus.PartialRegularity
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Joint regularity of spatially smoothed waves

A C¹ field satisfying the tested wave equation becomes jointly C² after
spatial convolution with a compact C² kernel. The tested equation supplies
the second time derivative; spatial derivatives fall on the kernel. The
force remains convolved, which keeps the result applicable to nonlinear
waves before the approximation error has been estimated.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology Convolution

namespace WaveEquation

/-- Spatial smoothing of a C¹ tested wave gives a jointly C² field. Both the
field and its continuous force have a common compact spatial support on the
open time band. -/
theorem contDiffOn_two_convolution_of_tested_wave {n : ℕ} {u F : ℝ × ℝ^n → ℝ} {I : Set ℝ}
    {K : Set (ℝ^n)} (hI : IsOpen I) (hK : IsCompact K) (hu : ContDiffOn ℝ 1 u (I ×ˢ univ))
    (hF : ContinuousOn F (I ×ˢ univ)) (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0)
    (hsF : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0)
    (hw : ∀ t ∈ I, ∀ φ : ℝ^n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      HasDerivAt (deriv (fun s ↦ ∫ y, u (s, y) * φ y))
      ((∫ y, u (t, y) * PDE.laplacian φ y) + ∫ y, F (t, y) * φ y) t)
    {κ : ℝ^n → ℝ} (hκ : ContDiff ℝ 2 κ) (hκs : HasCompactSupport κ) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ^n ↦ ((fun y ↦ u (p.1, y)) ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) p.2)
      (I ×ˢ univ) := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  let v : ℝ × ℝ^n → ℝ := fun p ↦ fderiv ℝ u p (1, 0)
  let U : ℝ × ℝ^n → ℝ := fun p ↦ ((fun y ↦ u (p.1, y)) ⋆[L] κ) p.2
  let V : ℝ × ℝ^n → ℝ := fun p ↦ ((fun y ↦ v (p.1, y)) ⋆[L] κ) p.2
  let A : ℝ × ℝ^n → ℝ := fun p ↦ ((fun y ↦ u (p.1, y)) ⋆[L] PDE.laplacian κ) p.2 +
      ((fun y ↦ F (p.1, y)) ⋆[L] κ) p.2
  let Du : ℝ × ℝ^n → ℝ^n →L[ℝ] ℝ := fun p ↦
    ((fun y ↦ u (p.1, y)) ⋆[L.precompR (ℝ^n)] fderiv ℝ κ) p.2
  let Dv : ℝ × ℝ^n → ℝ^n →L[ℝ] ℝ := fun p ↦
    ((fun y ↦ v (p.1, y)) ⋆[L.precompR (ℝ^n)] fderiv ℝ κ) p.2
  have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by norm_num)
  have hDκ : Continuous (fderiv ℝ κ) := hκ1.continuous_fderiv one_ne_zero
  have hΔκ : Continuous (PDE.laplacian κ) := continuous_finsetSum _ fun i _ ↦
    (PDE.contDiff_partialDeriv_of_succ (m := 0)
      (PDE.contDiff_partialDeriv_of_succ (m := 1) hκ)).continuous
  have huloc (t : ℝ) (ht : t ∈ I) : LocallyIntegrable (fun y ↦ u (t, y)) volume :=
    (hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨ht, mem_univ _⟩)).locallyIntegrable
  have hvc : ContinuousOn v (I ×ˢ univ) :=
    (hu.continuousOn_fderiv_of_isOpen (hI.prod isOpen_univ) le_rfl).clm_apply continuousOn_const
  have hvs (t : ℝ) (ht : t ∈ I) (y : ℝ^n) (hy : y ∉ K) : v (t, y) = 0 := by
    have hz : fderiv ℝ u (t, y) = 0 := (hasFDerivAt_zero_of_eventually_const (0 : ℝ) <| by
      filter_upwards [(hI.prod hK.isClosed.isOpen_compl).mem_nhds ⟨ht, hy⟩] with q hq
        using hs q.1 hq.1 q.2 hq.2).fderiv
    simp only [v, hz, zero_apply]
  have hAc : ContinuousOn A (I ×ˢ univ) := by
    simpa only [Pi.add_def, convolution_flip, A] using
      (continuousOn_convolution_right_with_param (μ := volume) L.flip hK
        (fun t y ht hy ↦ hs t ht y hy) hΔκ.locallyIntegrable hu.continuousOn).add
      (continuousOn_convolution_right_with_param (μ := volume) L.flip hK
        (fun t y ht hy ↦ hsF t ht y hy) hκ.continuous.locallyIntegrable hF)
  have hUt (t : ℝ) (ht : t ∈ I) (x : ℝ^n) : HasDerivAt (fun s ↦ U (s, x)) (V (t, x)) t :=
    hasDerivAt_convolution_left_with_param L hI hK hu hs hκ.continuous.locallyIntegrable ht x
  -- The tested equation supplies the time derivative missing from C¹ regularity.
  have hVt (t : ℝ) (ht : t ∈ I) (x : ℝ^n) : HasDerivAt (fun s ↦ V (s, x)) (A (t, x)) t := by
    have hd := hasDerivAt_deriv_convolution_of_tested_wave
      (u := fun s y ↦ u (s, y)) (F := fun s y ↦ F (s, y)) (huloc t ht) (hw t ht) hκ hκs x
    rw [PDE.laplacian_convolution_right (huloc t ht) hκs hκ] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [hI.mem_nhds ht] with s hsI using (hUt s hsI x).deriv.symm
  have hDvc : ContinuousOn Dv (I ×ˢ univ) := by
    simpa only [convolution_flip] using
      continuousOn_convolution_right_with_param (μ := volume) (L.precompR (ℝ^n)).flip hK
        (fun t y ht hy ↦ hvs t ht y hy) hDκ.locallyIntegrable hvc
  -- Joint regularity follows by combining the time and spatial derivatives.
  have hV : ContDiffOn ℝ 1 V (I ×ˢ univ) :=
    PDE.Analysis.contDiffOn_one_of_partial_derivatives (hI.prod isOpen_univ)
      (D₁ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (A p)) (D₂ := Dv)
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp_continuousOn hAc) hDvc
      (fun p hp ↦ (hVt p.1 hp.1 p.2).hasFDerivAt)
      (fun p hp ↦ hκs.hasFDerivAt_convolution_right L ((hvc.comp_continuous
        (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨hp.1, mem_univ _⟩)).locallyIntegrable)
        hκ1 p.2)
  exact PDE.Analysis.contDiffOn_succ_of_partial_derivatives (m := 1) (hI.prod isOpen_univ)
    (D₁ := fun p ↦ ContinuousLinearMap.toSpanSingleton ℝ (V p)) (D₂ := Du)
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).contDiff.comp_contDiffOn hV)
    (contDiffOn_convolution_left_with_param (L.precompR (ℝ^n)) hI hK
      (fun t y ht hy ↦ hs t ht y hy) hDκ.locallyIntegrable hu)
    (fun p hp ↦ (hUt p.1 hp.1 p.2).hasFDerivAt)
    (fun p hp ↦ hκs.hasFDerivAt_convolution_right L (huloc p.1 hp.1) hκ1 p.2)

/-- A spatial smoothing of a C¹ tested wave is C² in canonical
Euclidean spacetime. The continuous force is allowed to be independent of the field. -/
theorem contDiffOn_two_convolution_timeSpace_of_tested_wave {n : ℕ} {u F : ℝ × ℝ^n → ℝ} {I : Set ℝ}
    {K : Set (ℝ^n)} (hI : IsOpen I) (hK : IsCompact K) (hu : ContDiffOn ℝ 1 u (I ×ˢ univ))
    (hF : ContinuousOn F (I ×ˢ univ)) (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0)
    (hsF : ∀ t ∈ I, ∀ x ∉ K, F (t, x) = 0)
    (hw : ∀ t ∈ I, ∀ ψ : ℝ^n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      HasDerivAt (deriv (fun s ↦ ∫ y, u (s, y) * ψ y))
      ((∫ y, u (t, y) * PDE.laplacian ψ y) + ∫ y, F (t, y) * ψ y) t)
    {κ : ℝ^n → ℝ} (hκ : ContDiff ℝ 2 κ) (hκs : HasCompactSupport κ) :
    let e := PDE.Common.timeSpaceContinuousLinearEquiv n; ContDiffOn ℝ 2
      (fun p : ℝ^(n + 1) ↦ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y ↦ u ((e p).1, y))) (e p).2)
      (PDE.Common.spaceTimeCylinder univ I) := by
  have hprod : ContDiffOn ℝ 2 (fun p : ℝ × ℝ^n ↦
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ] (fun y ↦ u (p.1, y))) p.2) (I ×ˢ univ) :=
    (contDiffOn_two_convolution_of_tested_wave hI hK hu hF hs hsF hw hκ hκs).congr fun p _ ↦ by
      simp only [convolution_mul_swap, convolution_lsmul, smul_eq_mul, mul_comm]
  exact hprod.comp_continuousLinearMap
    (PDE.Common.timeSpaceContinuousLinearEquiv n).toContinuousLinearMap

end WaveEquation
