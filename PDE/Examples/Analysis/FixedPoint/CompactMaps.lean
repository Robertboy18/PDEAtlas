/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Schaefer
public import Mathlib.Topology.ContinuousMap.Compact
import CAS.ExactTactic

/-!
# Nonlinear compact maps on a Banach function space

The map `A x = w + sin (10 * ℓ x) • v` has a compact global image and a bounded
Schaefer homotopy set, with no small-gain condition. Both Schaefer and nonempty Schauder
apply. The concrete specialization on `ℝ × C([0,1], ℝ)` has a nonzero offset and is
nonconstant.
-/

@[expose] public noncomputable section

open Set Metric Function Bornology

namespace PDE.Examples.FixedPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact affine segment containing the entire nonlinear image. -/
def rankOneSegment (w v : E) : Set E :=
  (fun t : ℝ ↦ w + t • v) '' Icc (-1 : ℝ) 1

/-- The containing segment is compact in any real normed space. -/
theorem isCompact_rankOneSegment (w v : E) : IsCompact (rankOneSegment w v) :=
  isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))

/-- The containing segment is nonempty even when the direction is zero. -/
theorem rankOneSegment_nonempty (w v : E) : (rankOneSegment w v).Nonempty :=
  ⟨w + (0 : ℝ) • v, mem_image_of_mem _ (by norm_num)⟩

/-- Convexity is inherited from the scalar interval by a linear image and translation. -/
theorem convex_rankOneSegment (w v : E) : Convex ℝ (rankOneSegment w v) := by
  have h := ((convex_Icc (-1 : ℝ) 1 : Convex ℝ (Icc (-1 : ℝ) 1)).linear_image
    ((LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight v)).translate w
  simpa only [rankOneSegment, image_image, comp_def, LinearMap.smulRight_apply,
    LinearMap.id_apply] using h

/-- A nonlinear rank-one map with unrestricted offset and gain ten. -/
def oscillatoryRankOne (ℓ : E →L[ℝ] ℝ) (w v : E) (x : E) : E :=
  w + Real.sin (10 * ℓ x) • v

/-- Continuity uses only the continuous linear functional and scalar sine. -/
theorem continuous_oscillatoryRankOne (ℓ : E →L[ℝ] ℝ) (w v : E) :
    Continuous (oscillatoryRankOne ℓ w v) :=
  continuous_const.add ((Real.continuous_sin.comp
    (continuous_const.mul ℓ.continuous)).smul continuous_const)

/-- Every value lies in the same compact affine segment. -/
theorem oscillatoryRankOne_mem_segment (ℓ : E →L[ℝ] ℝ) (w v x : E) :
    oscillatoryRankOne ℓ w v x ∈ rankOneSegment w v :=
  mem_image_of_mem _ ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

/-- In particular the image of every set has compact closure. -/
theorem isCompact_closure_oscillatoryRankOne_image (ℓ : E →L[ℝ] ℝ) (w v : E)
    (s : Set E) : IsCompact (closure (oscillatoryRankOne ℓ w v '' s)) := by
  apply (isCompact_rankOneSegment w v).of_isClosed_subset isClosed_closure
  apply closure_minimal _ (isCompact_rankOneSegment w v).isClosed
  rintro _ ⟨x, _, rfl⟩
  exact oscillatoryRankOne_mem_segment ℓ w v x

/-- The global norm bound does not involve the norm of the functional or its gain. -/
theorem norm_oscillatoryRankOne_le (ℓ : E →L[ℝ] ℝ) (w v x : E) :
    ‖oscillatoryRankOne ℓ w v x‖ ≤ ‖w‖ + ‖v‖ := by
  calc
    ‖oscillatoryRankOne ℓ w v x‖ ≤ ‖w‖ + ‖Real.sin (10 * ℓ x) • v‖ := norm_add_le _ _
    _ ≤ ‖w‖ + 1 * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg v))
    _ = ‖w‖ + ‖v‖ := by rw [one_mul]

/-- All homotopy solutions, for every parameter in `[0,1]`, satisfy one uniform bound. -/
theorem isBounded_oscillatoryRankOne_homotopy (ℓ : E →L[ℝ] ℝ) (w v : E) :
    IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, x = t • oscillatoryRankOne ℓ w v x} := by
  apply (isBounded_closedBall (x := (0 : E)) (r := ‖w‖ + ‖v‖)).subset
  rintro x ⟨t, ht, hx⟩
  rw [mem_closedBall_zero_iff]
  calc
    ‖x‖ = ‖t • oscillatoryRankOne ℓ w v x‖ := congrArg norm hx
    _ = t * ‖oscillatoryRankOne ℓ w v x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    _ ≤ 1 * ‖oscillatoryRankOne ℓ w v x‖ :=
      mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ ≤ ‖w‖ + ‖v‖ := by
      rw [one_mul]
      exact norm_oscillatoryRankOne_le ℓ w v x

/-- Schaefer's theorem gives a fixed point of the nonlinear map. -/
theorem oscillatoryRankOne_fixedPoint (ℓ : E →L[ℝ] ℝ) (w v : E) :
    ∃ x, IsFixedPt (oscillatoryRankOne ℓ w v) x :=
  PDE.FixedPoint.exists_isFixedPt_of_bounded_homotopy
    (continuous_oscillatoryRankOne ℓ w v)
    (fun s _ ↦ isCompact_closure_oscillatoryRankOne_image ℓ w v s)
    (isBounded_oscillatoryRankOne_homotopy ℓ w v)

/-- Schauder's theorem on a nonempty compact convex set applies to the same map. -/
theorem oscillatoryRankOne_fixedPoint_in_segment (ℓ : E →L[ℝ] ℝ) (w v : E) :
    ∃ x ∈ rankOneSegment w v, IsFixedPt (oscillatoryRankOne ℓ w v) x := by
  let f : C(rankOneSegment w v, rankOneSegment w v) :=
    ⟨fun x ↦ ⟨oscillatoryRankOne ℓ w v x, oscillatoryRankOne_mem_segment ℓ w v x⟩,
      ((continuous_oscillatoryRankOne ℓ w v).comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨x, hx⟩ := PDE.FixedPoint.exists_isFixedPt_of_isCompact_convex
    (rankOneSegment_nonempty w v) (isCompact_rankOneSegment w v)
    (convex_rankOneSegment w v) f
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- A continuous nonlinear map on a Banach function space. -/
def functionSpaceMap (x : ℝ × C(Icc (0 : ℝ) 1, ℝ)) :
    ℝ × C(Icc (0 : ℝ) 1, ℝ) :=
  oscillatoryRankOne (ContinuousLinearMap.fst ℝ ℝ C(Icc (0 : ℝ) 1, ℝ))
    (1, 0) (1, 1) x

/-- The offset is nonzero; this map cannot be linear. -/
theorem functionSpaceMap_zero_ne : functionSpaceMap 0 ≠ 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  norm_num [functionSpaceMap, oscillatoryRankOne] at hfst

/-- The map is nonconstant, with two explicitly different values. -/
theorem functionSpaceMap_values_ne :
    functionSpaceMap (Real.pi / 20, 0) ≠ functionSpaceMap 0 := by
  intro h
  have hfst := congrArg Prod.fst h
  have hangle : (10 : ℝ) * (Real.pi / 20) = Real.pi / 2 := by cas
  norm_num [functionSpaceMap, oscillatoryRankOne, hangle] at hfst

/-- Schaefer's theorem gives a fixed point on the infinite-dimensional space
`ℝ × C([0,1], ℝ)`. -/
theorem functionSpaceMap_fixedPoint : ∃ x, IsFixedPt functionSpaceMap x :=
  oscillatoryRankOne_fixedPoint _ _ _

end PDE.Examples.FixedPoint
