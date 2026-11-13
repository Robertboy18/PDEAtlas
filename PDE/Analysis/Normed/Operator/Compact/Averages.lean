/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.TotallyBounded
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PDE.Analysis.Operator.CompactConvergence

/-!
# Compactness from uniform approximation and from averages

A continuous linear map into a Banach space is compact if, for every `ε > 0`, the image of the
unit ball lies within `ε` of some compact set.

An interval integral of a function with values in a set `Q` lies in the length of the interval
times the closed convex hull of `Q`. In a Banach space the closed convex hull of a compact set is
compact, so integrals over a fixed interval of functions with values in a fixed compact set form
a relatively compact set.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped Pointwise Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous linear map into a Banach space is compact if, for every `ε > 0`, the image of
the unit ball lies within `ε` of a compact set. -/
theorem isCompactOperator_of_forall_exists_dist_lt (T : E →L[ℝ] F)
    (h : ∀ ε > 0, ∃ Q : Set F, IsCompact Q ∧ ∀ u ∈ ball (0 : E) 1, ∃ y ∈ Q, dist (T u) y < ε) :
    IsCompactOperator T := by
  have htb : TotallyBounded (T '' ball (0 : E) 1) := by
    apply totallyBounded_of_uniformly_approximated
    intro ε hε
    obtain ⟨Q, hQ, hTQ⟩ := h ε hε
    refine ⟨Q, hQ.totallyBounded, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact hTQ u hu
  exact (isCompactOperator_iff_exists_mem_nhds_image_subset_compact (T : E → F)).mpr
    ⟨ball (0 : E) 1, ball_mem_nhds 0 one_pos, closure (T '' ball (0 : E) 1),
      htb.closure.isCompact_of_isClosed isClosed_closure, subset_closure⟩

/-- The interval integral of a function with values in `Q` lies in the length of the interval
times the closed convex hull of `Q`. -/
theorem intervalIntegral_mem_smul_closedConvexHull [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b) {Q : Set E}
    (hQ : ∀ s ∈ Ioc a b, f s ∈ Q) :
    (∫ s in a..b, f s) ∈ (b - a) • closedConvexHull ℝ Q := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hμ : volume (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc
  have h0 : volume (Ioc a b) ≠ 0 := by
    rw [hμ]
    exact ENNReal.ofReal_ne_zero_iff.mpr hba
  have hfin : volume (Ioc a b) ≠ ⊤ := by
    rw [hμ]
    exact ENNReal.ofReal_ne_top
  have hfs : ∀ᵐ s ∂volume.restrict (Ioc a b), f s ∈ closedConvexHull ℝ Q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact subset_closedConvexHull (hQ s hs)
  have havg := convex_closedConvexHull.set_average_mem isClosed_closedConvexHull h0 hfin hfs
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf)
  rw [setAverage_eq, measureReal_def, hμ, ENNReal.toReal_ofReal hba.le] at havg
  rw [intervalIntegral.integral_of_le hab.le, ← smul_inv_smul₀ hba.ne' (∫ s in Ioc a b, f s)]
  exact smul_mem_smul_set havg

/-- In a Banach space the closed convex hull of a compact set is compact. -/
theorem isCompact_closedConvexHull [CompleteSpace E] {Q : Set E} (hQ : IsCompact Q) :
    IsCompact (closedConvexHull ℝ Q) := by
  rw [closedConvexHull_eq_closure_convexHull]
  exact hQ.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure

end PDE.Analysis
