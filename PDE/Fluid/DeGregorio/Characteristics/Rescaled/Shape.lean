/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Characteristics.Rescaled.Oddness
public import PDE.Fluid.DeGregorio.Characteristics.Rescaled.Support
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative.Trace
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.GraphBound
import CAS.ExactTactic

/-!
# Closed-interval shape from open-slab regularity and bounded weak H¹

The rescaled equation and joint C¹ regularity are assumed on the open slab
`ℝ × (a, b)`. The continuous L² base curve and uniformly bounded H¹ graphs give
pointwise vorticity traces at the endpoints, and the velocity is assumed continuous
in time at `a` and `b`.

Initial oddness and support then persist on the closed interval `[a, b]`.
The weak H¹ graph bounds both the velocity gradient and the L² vorticity
derivative through the spectral Hilbert relation.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution SobolevSpace.GraphSpace
open scoped Sobolev

namespace DeGregorio

/-- Initial oddness and support persist up to both endpoint traces for an
endpoint-normalized rescaled solution with bounded weak H¹ graphs
and a continuous L² base curve. The enclosing radius `R` is assumed only for
`t ∈ (a, b)` and may exceed `L`. -/
theorem IsClassicalRescaledSolutionOn.odd_support_on_closed_slab_of_bounded_h1
    {fields : Fields} {cl cw : ℝ → ℝ} {a b L R : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Ioo a b))
    (hω : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ 1 (Function.uncurry fields.velocity) (univ ×ˢ Ioo a b))
    (hab : a < b) (hL : 0 < L) (hR : 0 ≤ R)
    (hcl : ContinuousOn cl (Icc a b)) (hcw : ContinuousOn cw (Icc a b))
    (htraceu : ∀ x, ContinuousWithinAt (fields.velocity x) (Icc a b) a ∧
      ContinuousWithinAt (fields.velocity x) (Icc a b) b)
    (henclosure : ∀ t ∈ Ioo a b, ∀ x, x ∉ Ioo (-R) R → fields.vorticity x t = 0)
    (hnormalized : ∀ t ∈ Ioo a b, fields.velocity 0 t = 0)
    (hendpoint : ∀ t ∈ Ioo a b, cl t = -fields.velocity L t / L)
    (g : Icc a b → W^{1,2}((Set.univ : Set (ℝ^1)))) (B : NNReal)
    (hrep : ∀ t, realLineRepresentative (g t) = fun x ↦ fields.vorticity x t)
    (hbound : ∀ t, ‖g t‖ ≤ B)
    (hbase : Continuous (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (g t)))
    (hodd₀ : Function.Odd (fun x ↦ fields.vorticity x a))
    (hsupp₀ : Function.support (fun x ↦ fields.vorticity x a) ⊆ Icc (-L) L) :
    ∀ t ∈ Icc a b,
      Function.Odd (fun x ↦ fields.vorticity x t) ∧
      Function.Odd (fun x ↦ fields.velocity x t) ∧
      tsupport (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L ∧
      HasCompactSupport (fun x ↦ fields.vorticity x t) ∧
      ∀ x ∉ Icc (-L) L, fields.vorticity x t = 0 := by
  have hspace (t : ℝ) (ht : t ∈ Icc a b) :
      Continuous (fun x ↦ fields.vorticity x t) := by
    rw [← hrep ⟨t, ht⟩]
    exact continuous_realLineRepresentative _
  have htraceω (x : ℝ) : ContinuousOn (fields.vorticity x) (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun t : Icc a b ↦ fields.vorticity x t)
    simpa only [hrep] using
      continuous_realLineRepresentative_eval_of_L2_continuous hbound hbase x
  have hvalue (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      |fields.vorticity x t| ≤ 2 * (B : ℝ) := by
    change ‖fields.vorticity x t‖ ≤ _
    rw [← congrFun (hrep ⟨t, ht⟩) x]
    exact (norm_realLineRepresentative_le _ x).trans
      (mul_le_mul_of_nonneg_left (hbound ⟨t, ht⟩) (by norm_num))
  have hgradient (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) :
      |deriv (fun y ↦ fields.velocity y t) x| ≤ 2 * (B : ℝ) := by
    let t' : Icc a b := ⟨t, Ioo_subset_Icc_self ht⟩
    have hp : IsHilbertPair (realLineRepresentative (g t'))
        (deriv (fun y ↦ fields.velocity y t)) := by
      rw [hrep t']
      exact hsol.biotSavart ht
    exact (norm_hilbertPair_right_le_h1 (g t') hp
      ((contDiff_slice_of_contDiffOn_cylinder hu ht).continuous_deriv le_rfl) x).trans
      (mul_le_mul_of_nonneg_left (hbound t') (by norm_num))
  have hderiv (t : ℝ) (ht : t ∈ Ioo a b) :
      MemLp (deriv (fun x ↦ fields.vorticity x t)) 2 volume ∧
        (∫ x, deriv (fun y ↦ fields.vorticity y t) x ^ 2) ≤ (B : ℝ) ^ 2 := by
    let t' : Icc a b := ⟨t, Ioo_subset_Icc_self ht⟩
    have hd := deriv_realLineRepresentative_L2_bound (g t')
    rw [hrep t'] at hd
    exact ⟨hd.1, hd.2.trans (pow_le_pow_left₀ (norm_nonneg _) (hbound t') 2)⟩
  have hodd := hsol.odd_on_closed_slab_of_initialData hω hu hab
    hcl hcw hspace htraceω
    (continuousOn_time_of_contDiffOn_slab_of_endpoint_traces hu htraceu)
    hvalue hgradient hderiv henclosure hnormalized hodd₀
  have hright (t : ℝ) (ht : t ∈ Ioo a b) :
      fields.velocity L t + cl t * L = 0 := by
    rw [hendpoint t ht]
    cas using hL.ne'
  have hleft (t : ℝ) (ht : t ∈ Ioo a b) :
      fields.velocity (-L) t + cl t * (-L) = 0 := by
    rw [show fields.velocity (-L) t = -fields.velocity L t from
      (hodd t (Ioo_subset_Icc_self ht)).2 L,
      mul_neg, ← neg_add, hright t ht, neg_zero]
  have hsupp := hsol.support_on_closed_slab_of_initialData hω hu hab hL hR
    hcl hcw hspace htraceω hvalue hgradient henclosure hleft hright hsupp₀
  intro t ht
  have hs : Function.support (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L := by
    intro x hx
    by_contra hout
    exact hx (hsupp t ht x hout)
  have hclosed : tsupport (fun x ↦ fields.vorticity x t) ⊆ Icc (-L) L :=
    closure_minimal hs isClosed_Icc
  exact ⟨(hodd t ht).1, (hodd t ht).2, hclosed,
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hclosed, hsupp t ht⟩

end DeGregorio
