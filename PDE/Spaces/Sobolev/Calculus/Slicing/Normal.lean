/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Normal slices in tangential-normal coordinates

We study the one-dimensional normal slices associated with the
tangential-normal decomposition of `ℝ^(n + 1)`. We identify the derivative
of a normal slice with the final-coordinate partial derivative and record
the continuity and compact-support properties needed by trace and Hardy
inequalities on the upper half-space. The codomain may be any real normed
space; completeness is not needed for these classical slice properties.
-/

@[expose] public section

open PDE (partialDeriv coordinateLine)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.HalfSpace

open Set

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restriction of a function to the normal line above a tangential point. -/
def normalSlice (f : ℝ^(n + 1) → F) (y : ℝ^n) (t : ℝ) : F :=
  f (joinTangentialNormal (y, t))

/-- The final-coordinate partial derivative written in tangential-normal
coordinates. -/
def normalDerivativeInSplit (f : ℝ^(n + 1) → F) (p : ℝ^n × ℝ) : F :=
  (∂[Fin.last n] f) (joinTangentialNormal p)

private theorem coordinateLine_last_joinTangentialNormal (y : ℝ^n) (t s : ℝ) :
    coordinateLine (Fin.last n) (joinTangentialNormal (y, t)) s =
      joinTangentialNormal (y, s) := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [coordinateLine]
  · simp [coordinateLine]

/-- Differentiating a normal slice gives the final-coordinate partial
derivative in split coordinates. -/
theorem deriv_normalSlice {f : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ 1 f) (y : ℝ^n) (t : ℝ) :
    deriv (normalSlice f y) t = normalDerivativeInSplit f (y, t) := by
  let x := joinTangentialNormal (y, t)
  have hdiff : DifferentiableAt ℝ f x :=
    (hf.differentiable (by norm_num)).differentiableAt
  have hpartial := PDE.partialDeriv_eq_deriv_coordinateLine
    (Fin.last n) x hdiff
  have hxlast : x (Fin.last n) = t := by simp [x]
  have hline : f ∘ coordinateLine (Fin.last n) x = normalSlice f y := by
    funext s
    simp [x, normalSlice, coordinateLine_last_joinTangentialNormal]
  rw [hxlast, hline] at hpartial
  exact hpartial.symm

/-- A normal slice of a `C¹` function is `C¹`. -/
theorem normalSlice_contDiff {f : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ 1 f) (y : ℝ^n) :
    ContDiff ℝ 1 (normalSlice f y) := by
  apply hf.comp
  rw [show (fun t ↦ joinTangentialNormal (y, t)) =
      fun t ↦
        joinTangentialNormal (y, 0) + normalAxisContinuousLinearMap (n := n) t by
    funext t
    exact joinTangentialNormal_eq_base_add_normal y t]
  exact contDiff_const.add (normalAxisContinuousLinearMap (n := n)).contDiff

omit [NormedSpace ℝ F] in
/-- A normal slice of a compactly supported function has compact support. -/
theorem normalSlice_hasCompactSupport {f : ℝ^(n + 1) → F}
    (hfc : HasCompactSupport f) (y : ℝ^n) :
    HasCompactSupport (normalSlice f y) := by
  let K : Set ℝ :=
    (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).2) '' tsupport f
  have hcoord : Continuous
      (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).2) := by
    simpa [splitTangentialNormal] using
      (EuclideanSpace.proj (Fin.last n)).continuous
  have hK : IsCompact K := hfc.image hcoord
  apply HasCompactSupport.intro hK
  intro t ht
  by_contra hne
  apply ht
  refine ⟨joinTangentialNormal (y, t), subset_tsupport _ hne, ?_⟩
  simp [splitTangentialNormal]

omit [NormedSpace ℝ F] in
/-- The split-coordinate representation of a continuous function is
continuous on the product space. -/
theorem normalSlice_product_continuous {f : ℝ^(n + 1) → F}
    (hf : Continuous f) :
    Continuous (fun p : ℝ^n × ℝ ↦ normalSlice f p.1 p.2) := by
  change Continuous
    (f ∘ (tangentialNormalContinuousLinearEquiv (n := n)).symm)
  exact hf.comp (tangentialNormalContinuousLinearEquiv (n := n)).symm.continuous

omit [NormedSpace ℝ F] in
/-- The split-coordinate representation preserves compact support. -/
theorem normalSlice_product_hasCompactSupport {f : ℝ^(n + 1) → F}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (fun p : ℝ^n × ℝ ↦ normalSlice f p.1 p.2) := by
  change HasCompactSupport
    (f ∘ (tangentialNormalContinuousLinearEquiv (n := n)).symm)
  exact hfc.comp_homeomorph
    (tangentialNormalContinuousLinearEquiv (n := n)).symm.toHomeomorph

/-- The final-coordinate partial derivative of a `C¹` function is continuous
in tangential-normal coordinates. -/
theorem normalDerivativeInSplit_continuous {f : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ 1 f) :
    Continuous (normalDerivativeInSplit (n := n) f) := by
  have hd : Continuous
      (fun x ↦ (∂[Fin.last n] f) x) := by
    have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    simpa [partialDeriv] using
      hfd.clm_apply
        (continuous_const : Continuous
          (fun _ : ℝ^(n + 1) ↦ EuclideanSpace.single (Fin.last n) (1 : ℝ)))
  change Continuous
    ((fun x ↦ (∂[Fin.last n] f) x) ∘
      (tangentialNormalContinuousLinearEquiv (n := n)).symm)
  exact hd.comp (tangentialNormalContinuousLinearEquiv (n := n)).symm.continuous

/-- The final-coordinate partial derivative of a compactly supported `C¹`
function has compact support in tangential-normal coordinates. -/
theorem normalDerivativeInSplit_hasCompactSupport {f : ℝ^(n + 1) → F}
    (hfc : HasCompactSupport f) :
    HasCompactSupport (normalDerivativeInSplit (n := n) f) := by
  have hd : HasCompactSupport
      (fun x ↦ (∂[Fin.last n] f) x) := by
    simpa [partialDeriv] using
      hfc.fderiv_apply (𝕜 := ℝ)
        (v := EuclideanSpace.single (Fin.last n) (1 : ℝ))
  change HasCompactSupport
    ((fun x ↦ (∂[Fin.last n] f) x) ∘
      (tangentialNormalContinuousLinearEquiv (n := n)).symm)
  exact hd.comp_homeomorph
    (tangentialNormalContinuousLinearEquiv (n := n)).symm.toHomeomorph

end Trace.HalfSpace
end SobolevSpace
