/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Zero
public import PDE.Analysis.Fourier.StationaryPhase.Morse
public import PDE.Analysis.Matrix.Determinant.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Compact amplitudes in smooth local coordinates

An amplitude supported inside a smooth chart transforms by the absolute
Jacobian of the inverse. Its extension by zero is smooth and compactly supported:
the compact image of the original support stays inside the open target.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology Matrix.Norms.Elementwise

namespace PDE.Analysis.StationaryPhase

variable {n : ℕ}

/-- The determinant of a Euclidean continuous linear map is smooth. -/
theorem contDiff_clm_det :
    ContDiff ℝ (⊤ : ℕ∞) (fun L : ℝ^n →L[ℝ] ℝ^n ↦ L.det) := by
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun L : ℝ^n →L[ℝ] ℝ^n ↦
        fun i j : Fin n ↦ L (EuclideanSpace.single j 1) i) := by
    apply contDiff_pi.mpr
    intro i
    apply contDiff_pi.mpr
    intro j
    exact (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.comp
      (contDiff_id.clm_apply contDiff_const)
  have h := PDE.Analysis.Matrix.contDiff_det.comp hm
  convert h using 1
  ext L
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  congr 1

/-- The compactly supported density induced by the inverse Jacobian. -/
def chartAmplitude (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (a : ℝ^n → ℂ) : ℝ^n → ℂ :=
  e.target.indicator (fun y ↦ |(fderiv ℝ e.symm y).det| • a (e.symm y))

/-- The transformed density has support inside the compact image of the amplitude support. -/
theorem support_chartAmplitude_subset
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) {a : ℝ^n → ℂ} :
    Function.support (chartAmplitude e a) ⊆ e '' tsupport a := by
  classical
  intro y hy
  by_cases hyt : y ∈ e.target
  · have hay : a (e.symm y) ≠ 0 := by
      intro h
      exact hy (by simp [chartAmplitude, hyt, h])
    exact ⟨e.symm y, subset_tsupport a hay, e.right_inv hyt⟩
  · exact (hy (by simp [chartAmplitude, hyt])).elim

/-- Compact support survives the local coordinate change. -/
theorem hasCompactSupport_chartAmplitude
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) {a : ℝ^n → ℂ}
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source) :
    HasCompactSupport (chartAmplitude e a) :=
  HasCompactSupport.of_support_subset_isCompact
    (hc.isCompact.image_of_continuousOn (e.continuousOn.mono hs))
    (support_chartAmplitude_subset e)

/-- The transformed density is smooth on all of Euclidean space. -/
theorem contDiff_chartAmplitude
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {a : ℝ^n → ℂ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ e.source) :
    ContDiff ℝ (⊤ : ℕ∞) (chartAmplitude e a) := by
  classical
  refine ContDiffOn.indicator_of_tsupport_subset ?_ e.open_target ?_
  · apply e.open_target.contDiffOn_iff.mpr
    intro y hy
    have hiy := hi.contDiffAt (e.open_target.mem_nhds hy)
    have hey := he.contDiffAt (e.open_source.mem_nhds (e.map_target hy))
    have hnonzero : (fderiv ℝ e.symm y).det ≠ 0 := by
      have h := PDE.Analysis.inverse_chart_det_mul e hy
        (hey.differentiableAt (by simp)) (hiy.differentiableAt (by simp))
      rw [PDE.Analysis.det_jacobianMatrix (hiy.differentiableAt (by simp))] at h
      exact right_ne_zero_of_mul_eq_one h
    have hdet := contDiff_clm_det.contDiffAt.comp y
      (hiy.fderiv_right (m := (⊤ : ℕ∞)) (by simp))
    exact (hdet.abs hnonzero).smul (ha.contDiffAt.comp y hiy)
  · have hclosed :=
      (hc.isCompact.image_of_continuousOn (e.continuousOn.mono hs)).isClosed
    refine (closure_minimal (support_chartAmplitude_subset e) hclosed).trans ?_
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hs hx)

/-- An identity derivative at the base point leaves the leading amplitude unchanged. -/
theorem chartAmplitude_apply
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) {p : ℝ^n} (hp : p ∈ e.source)
    (hd : HasFDerivAt e (ContinuousLinearMap.id ℝ (ℝ^n)) p)
    (hi : DifferentiableAt ℝ e.symm (e p)) (a : ℝ^n → ℂ) :
    chartAmplitude e a (e p) = a p := by
  classical
  have hD := PDE.Analysis.inverse_chart_fderiv_comp e (e.map_source hp)
    (by simpa only [e.left_inv hp] using hd.differentiableAt) hi
  rw [e.left_inv hp, hd.fderiv, ContinuousLinearMap.id_comp] at hD
  simp [chartAmplitude, e.map_source hp, e.left_inv hp, hD,
    ContinuousLinearMap.det]

/-- Change of variables with the constructed density, including extension by zero. -/
theorem integral_mul_eq_integral_chartAmplitude
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hi : DifferentiableOn ℝ e.symm e.target)
    {a : ℝ^n → ℂ} (hs : tsupport a ⊆ e.source) (w : ℝ^n → ℂ) :
    (∫ x, w x * a x) = ∫ y, w (e.symm y) * chartAmplitude e a y := by
  classical
  calc
    (∫ x, w x * a x) = ∫ x in e.source, w x * a x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hx' ↦ hx (hs hx')), mul_zero]
    _ = ∫ y in e.target, |(fderiv ℝ e.symm y).det| •
        (w (e.symm y) * a (e.symm y)) :=
      integral_target_eq_integral_abs_det_fderiv_smul volume
        (fun y hy ↦ (hi.differentiableAt (e.open_target.mem_nhds hy)).hasFDerivAt) _
    _ = ∫ y in e.target, w (e.symm y) * chartAmplitude e a y := by
      apply setIntegral_congr_fun e.open_target.measurableSet
      intro y hy
      simp only [chartAmplitude, indicator_of_mem hy, Algebra.smul_def]
      ring
    _ = ∫ y, w (e.symm y) * chartAmplitude e a y := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      simp [chartAmplitude, hy]

end PDE.Analysis.StationaryPhase
