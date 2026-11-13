/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of spatial convolution with parameters

A C¹ family with a common compact spatial support can be differentiated under
convolution with a locally integrable kernel. Mathlib supplies the joint
Fréchet derivative. Evaluating it in a direction gives the formulas below,
including the ordinary time derivative, without differentiating the kernel.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology Convolution

namespace MeasureTheory

variable {G E F H : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

/-- The full derivative of a compactly supported C¹ family can be moved
under spatial convolution, in any parameter or spatial direction. -/
theorem fderiv_convolution_left_with_param_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : E →L[ℝ] F →L[ℝ] H)
    {u : P × G → E} {S : Set P} {K : Set G}
    (hS : IsOpen S) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (S ×ˢ univ))
    (hs : ∀ p ∈ S, ∀ x ∉ K, u (p, x) = 0)
    {κ : G → F} (hκ : LocallyIntegrable κ μ)
    {p : P × G} (hp : p.1 ∈ S) (v : P × G) :
    fderiv ℝ (fun q : P × G ↦ ((fun y ↦ u (q.1, y)) ⋆[L, μ] κ) q.2) p v =
      (((fun y ↦ fderiv ℝ u (p.1, y) v) ⋆[L, μ] κ) p.2) := by
  have hDu : ContinuousOn (fderiv ℝ u) (S ×ˢ univ) :=
    hu.continuousOn_fderiv_of_isOpen (hS.prod isOpen_univ) le_rfl
  have hc : Continuous (fun y ↦ fderiv ℝ u (p.1, y)) :=
    hDu.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ ↦ ⟨hp, mem_univ _⟩)
  have hz (y : G) (hy : y ∉ K) : fderiv ℝ u (p.1, y) = 0 := by
    apply (hasFDerivAt_zero_of_eventually_const (0 : E) ?_).fderiv
    filter_upwards [(hS.prod hK.isClosed.isOpen_compl).mem_nhds ⟨hp, hy⟩]
      with q hq
    exact hs q.1 hq.1 q.2 hq.2
  have hsD : HasCompactSupport (fun y ↦ fderiv ℝ u (p.1, y)) :=
    hK.of_isClosed_subset isClosed_closure
      (closure_minimal (Function.support_subset_iff'.mpr hz) hK.isClosed)
  have hd : HasFDerivAt
      (fun q : P × G ↦ (κ ⋆[L.flip, μ] (fun y ↦ u (q.1, y))) q.2)
      ((κ ⋆[L.flip.precompR (P × G), μ] (fun y ↦ fderiv ℝ u (p.1, y))) p.2) p :=
    hasFDerivAt_convolution_right_with_param L.flip hS hK
      (fun s y hsS hy ↦ hs s hsS y hy) hκ hu p hp
  have he := congrArg (fun A : (P × G) →L[ℝ] H ↦ A v) hd.fderiv
  rw [convolution_precompR_apply L.flip hκ hsD hc p.2 v] at he
  simpa only [convolution_flip] using he

/-- The time derivative falls on a C¹ family with common compact spatial
support. The fixed convolution kernel only needs local integrability. -/
theorem hasDerivAt_convolution_left_with_param
    (L : E →L[ℝ] F →L[ℝ] H)
    {u : ℝ × G → E} {I : Set ℝ} {K : Set G}
    (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (I ×ˢ univ))
    (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0)
    {κ : G → F} (hκ : LocallyIntegrable κ μ)
    {t : ℝ} (ht : t ∈ I) (x : G) :
    HasDerivAt (fun s ↦ ((fun y ↦ u (s, y)) ⋆[L, μ] κ) x)
      (((fun y ↦ fderiv ℝ u (t, y) (1, 0)) ⋆[L, μ] κ) x) t := by
  have hU : ContDiffOn ℝ 1
      (fun q : ℝ × G ↦ ((fun y ↦ u (q.1, y)) ⋆[L, μ] κ) q.2) (I ×ˢ univ) :=
    contDiffOn_convolution_left_with_param L hI hK
      (fun s y hsI hy ↦ hs s hsI y hy) hκ hu
  have hd := ((hU.contDiffAt ((hI.prod isOpen_univ).mem_nhds
    ⟨ht, mem_univ x⟩)).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have he := fderiv_convolution_left_with_param_apply L hI hK hu hs hκ
    (p := (t, x)) ht (1, 0)
  simpa only [Function.comp_def, id_eq] using hd.congr_deriv he

end MeasureTheory
