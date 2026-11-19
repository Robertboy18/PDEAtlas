/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.ParametricIntervalRegularity
public import PDE.FDeriv.Operators

/-!
# Derivatives of smooth interval averages

For a jointly smooth family `f : ℝ^n × ℝ → F`, the average `x ↦ ∫₀¹ f (x, t) dt` is smooth, and
its Fréchet derivative, its coordinate partial derivatives and its coordinate Laplacian are the
averages of the corresponding derivatives of the slices `y ↦ f (y, t)`. The spatial derivatives
of the slices are again jointly smooth in `(x, t)`, which is what the iteration needs.
-/

@[expose] public section
noncomputable section

namespace PDE.Calculus

open MeasureTheory Set
open PDE (partialDeriv)

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ^n × ℝ → F}

/-- The spatial derivative of the slices of a jointly smooth family is jointly smooth. -/
theorem contDiff_fderiv_slice (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^n × ℝ ↦ fderiv ℝ (fun y ↦ f (y, q.2)) q.1) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry fun (q : ℝ^n × ℝ) (y : ℝ^n) ↦ f (y, q.2)) :=
    hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst))
  exact h.fderiv contDiff_fst (by simp)

/-- A spatial coordinate partial derivative of the slices of a jointly smooth family is
jointly smooth. -/
theorem contDiff_partialDeriv_slice (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ^n × ℝ ↦ partialDeriv i (fun y ↦ f (y, q.2)) q.1) :=
  (contDiff_fderiv_slice hf).clm_apply contDiff_const

/-- The coordinate Laplacian of the slices of a jointly smooth family is jointly continuous. -/
theorem continuous_laplacian_slice (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun q : ℝ^n × ℝ ↦ PDE.laplacian (fun y ↦ f (y, q.2)) q.1) := by
  unfold PDE.laplacian
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (contDiff_partialDeriv_slice (contDiff_partialDeriv_slice hf i) i).continuous

/-- The average over `[0,1]` of a jointly smooth family is smooth. The codomain lies in the
universe of `ℝ^n`, as in `contDiffAt_intervalAverage_of_joint`. -/
theorem contDiff_intervalAverage {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : ℝ^n × ℝ → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t)) := by
  refine contDiff_infty.mpr fun k ↦ contDiff_iff_contDiffAt.mpr fun x ↦ ?_
  exact contDiffAt_intervalAverage_of_joint k f isOpen_univ
    (fun _ _ _ _ ↦ (hf.of_le (by exact_mod_cast le_top)).contDiffAt) (mem_univ x)

/-- The derivative of the average of a jointly smooth family is the average of the spatial
derivatives of its slices. -/
theorem hasFDerivAt_intervalAverage (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ^n) :
    HasFDerivAt (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t))
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ f (y, t)) x) x := by
  have hD := contDiff_fderiv_slice hf
  refine hasFDerivAt_intervalAverage_of_joint f
    (fun q ↦ fderiv ℝ (fun y ↦ f (y, q.2)) q.1) isOpen_univ
    (fun _ _ _ _ ↦ hf.continuous.continuousAt) (fun _ _ _ _ ↦ hD.continuous.continuousAt)
    (fun p _ t _ ↦ ?_) (mem_univ x)
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f (y, t)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  exact (hslice.differentiable (by simp) p).hasFDerivAt

/-- The derivative of the average of a jointly smooth family is the average of the spatial
derivatives of its slices. -/
theorem fderiv_intervalAverage (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ^n) :
    fderiv ℝ (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t)) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ f (y, t)) x :=
  (hasFDerivAt_intervalAverage hf x).fderiv

/-- Coordinate partial derivatives commute with the average of a jointly smooth family. -/
theorem partialDeriv_intervalAverage (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin n) (x : ℝ^n) :
    partialDeriv i (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t)) x =
      ∫ t in (0 : ℝ)..1, partialDeriv i (fun y ↦ f (y, t)) x := by
  rw [partialDeriv, fderiv_intervalAverage hf x]
  have hc : Continuous (fun t : ℝ ↦ fderiv ℝ (fun y ↦ f (y, t)) x) :=
    (contDiff_fderiv_slice hf).continuous.comp (continuous_const.prodMk continuous_id)
  exact ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable 0 1) _

/-- The coordinate Laplacian commutes with the average of a jointly smooth family. -/
theorem laplacian_intervalAverage (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ℝ^n) :
    PDE.laplacian (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t)) x =
      ∫ t in (0 : ℝ)..1, PDE.laplacian (fun y ↦ f (y, t)) x := by
  unfold PDE.laplacian
  have hfirst (i : Fin n) : partialDeriv i (fun x ↦ ∫ t in (0 : ℝ)..1, f (x, t)) =
      fun y ↦ ∫ t in (0 : ℝ)..1, partialDeriv i (fun z ↦ f (z, t)) y :=
    funext (partialDeriv_intervalAverage hf i)
  simp_rw [hfirst]
  have hsecond (i : Fin n) := partialDeriv_intervalAverage
    (f := fun q : ℝ^n × ℝ ↦ partialDeriv i (fun z ↦ f (z, q.2)) q.1)
    (contDiff_partialDeriv_slice hf i) i x
  simp only [hsecond]
  rw [intervalIntegral.integral_finsetSum fun i _ ↦ ?_]
  exact ((contDiff_partialDeriv_slice (contDiff_partialDeriv_slice hf i) i).continuous.comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1

end PDE.Calculus
