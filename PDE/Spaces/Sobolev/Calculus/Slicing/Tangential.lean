/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialEmbedding
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Tangential slices

At a fixed height, a tangential slice is a function on the boundary coordinate space.
Its derivatives are the corresponding tangential derivatives of the original function.
The inclusion of tangent vectors preserves Euclidean length, so restricting the derivative
to these vectors does not increase its operator norm.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open Set
open scoped ContDiff

variable {n : ℕ}

/-- Restrict a function to the horizontal plane at height `t`. -/
def tangentialSlice {F : Type*} (f : ℝ^(n + 1) → F) (t : ℝ) (y : ℝ^n) : F :=
  f (joinTangentialNormal (y, t))

/-- A horizontal slice of a compactly supported function has compact support. -/
theorem tangentialSlice_hasCompactSupport {F : Type*} [Zero F] {f : ℝ^(n + 1) → F}
    (hfc : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (tangentialSlice f t) := by
  let K : Set (ℝ^n) := (fun x ↦ (splitTangentialNormal x).1) '' tsupport f
  have hcoord : Continuous (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).1) :=
    (tangentialNormalContinuousLinearEquiv (n := n)).continuous.fst
  apply HasCompactSupport.intro (hfc.image hcoord : IsCompact K)
  intro y hy
  by_contra hne
  apply hy
  exact ⟨joinTangentialNormal (y, t), subset_tsupport _ hne, by simp⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taking a tangential slice preserves every order of continuous differentiability. -/
theorem tangentialSlice_contDiff {f : ℝ^(n + 1) → F} {k : ℕ∞ω}
    (hf : ContDiff ℝ k f) (t : ℝ) :
    ContDiff ℝ k (tangentialSlice f t) := by
  change ContDiff ℝ k (f ∘ fun y ↦ joinTangentialNormal (y, t))
  apply hf.comp
  rw [show (fun y : ℝ^n ↦ joinTangentialNormal (y, t)) =
      (fun y ↦ tangentialEmbedding y + normalAxisContinuousLinearMap (n := n) t) from
    funext fun y ↦ joinTangentialNormal_eq_base_add_normal y t]
  exact (tangentialEmbedding (n := n)).toContinuousLinearMap.contDiff.add contDiff_const

/-- The derivative of a tangential slice is the ambient derivative restricted to tangent
vectors. Differentiability is required only at the point in question. -/
theorem fderiv_tangentialSlice {f : ℝ^(n + 1) → F} (t : ℝ) (y : ℝ^n)
    (hf : DifferentiableAt ℝ f (joinTangentialNormal (y, t))) :
    fderiv ℝ (tangentialSlice f t) y =
      (fderiv ℝ f (joinTangentialNormal (y, t))).comp
        (tangentialEmbedding (n := n)).toContinuousLinearMap := by
  have he : HasFDerivAt (fun z : ℝ^n ↦ joinTangentialNormal (z, t))
      (tangentialEmbedding (n := n)).toContinuousLinearMap y := by
    rw [show (fun z : ℝ^n ↦ joinTangentialNormal (z, t)) =
        (fun z ↦ tangentialEmbedding z + normalAxisContinuousLinearMap (n := n) t) from
      funext fun z ↦ joinTangentialNormal_eq_base_add_normal z t]
    exact (tangentialEmbedding (n := n)).toContinuousLinearMap.hasFDerivAt.add_const _
  exact (hf.hasFDerivAt.comp y he).fderiv

/-- Tangential coordinate derivatives agree with the first `n` ambient derivatives. -/
theorem partialDeriv_tangentialSlice {f : ℝ^(n + 1) → F} (t : ℝ) (y : ℝ^n)
    (hf : DifferentiableAt ℝ f (joinTangentialNormal (y, t))) (i : Fin n) :
    (∂[i] (tangentialSlice f t)) y =
      (∂[i.castSucc] f) (joinTangentialNormal (y, t)) := by
  simp only [partialDeriv, fderiv_tangentialSlice t y hf,
    ContinuousLinearMap.comp_apply]
  congr 1
  ext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j <;> simp

/-- Restricting a derivative to tangent vectors cannot increase its operator norm. -/
theorem norm_fderiv_tangentialSlice_le {f : ℝ^(n + 1) → F} (t : ℝ) (y : ℝ^n)
    (hf : DifferentiableAt ℝ f (joinTangentialNormal (y, t))) :
    ‖fderiv ℝ (tangentialSlice f t) y‖ ≤ ‖fderiv ℝ f (joinTangentialNormal (y, t))‖ := by
  rw [fderiv_tangentialSlice t y hf]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  change ‖(fderiv ℝ f (joinTangentialNormal (y, t))) (tangentialEmbedding v)‖ ≤ _
  simpa only [LinearIsometry.norm_map] using
    (fderiv ℝ f (joinTangentialNormal (y, t))).le_opNorm (tangentialEmbedding v)

end SobolevSpace.Trace.HalfSpace
