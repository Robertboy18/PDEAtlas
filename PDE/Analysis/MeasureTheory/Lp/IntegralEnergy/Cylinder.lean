/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.Representations.Similarity.Dynamic

/-!
# Energy differentiation in an open time cylinder

Interior joint C¹ regularity gives continuous spatial slices and the local
domination needed to differentiate a bounded spatial square integral.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

/-- A classical function on an open time cylinder has classical spatial slices. -/
theorem contDiff_slice_of_contDiffOn_cylinder {f : ℝ → ℝ → ℝ} {a b t : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b))
    (ht : t ∈ Ioo a b) : ContDiff ℝ 1 (fun x ↦ f x t) :=
  contDiffOn_univ.mp <| hf.comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun x _ ↦ ⟨mem_univ x, ht⟩)

/-- Interior joint C¹ regularity makes the time derivative continuous there. -/
theorem continuousOn_time_deriv_of_contDiffOn_cylinder
    {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ deriv (f p.1) p.2) (univ ×ˢ Ioo a b) := by
  have hD := (hf.continuousOn_fderiv_of_isOpen
    (isOpen_univ.prod isOpen_Ioo) (by simp)).clm_apply
      (continuousOn_const (c := ((0, 1) : ℝ × ℝ)))
  apply hD.congr
  rintro ⟨x, t⟩ hp
  change deriv (f x) t = fderiv ℝ (Function.uncurry f) (x, t) (0, 1)
  rw [PDE.Representations.Similarity.fderiv_uncurry_apply_prod f x 0 t 1
    ((hf.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).differentiableAt
      (by simp))]
  simp [fderiv_eq_smul_deriv]

/-- Differentiation of a square integral needs joint C¹ regularity only in
the open time cylinder surrounding the evaluation time. -/
theorem hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder
    {f : ℝ → ℝ → ℝ} {a b t : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b))
    (ht : t ∈ Ioo a b) (l r : ℝ) :
    HasDerivAt (fun s ↦ ∫ x in Icc l r, f x s ^ 2)
      (2 * ∫ x in Icc l r, f x t * deriv (f x) t) t := by
  let α := (a + t) / 2
  let β := (t + b) / 2
  have hα : a < α ∧ α < t := by dsimp [α]; constructor <;> linarith [ht.1]
  have hβ : t < β ∧ β < b := by dsimp [β]; constructor <;> linarith [ht.2]
  have hsub : Icc l r ×ˢ Icc α β ⊆ univ ×ˢ Ioo a b := by
    intro p hp
    exact ⟨mem_univ _, hα.1.trans_le hp.2.1, hp.2.2.trans_lt hβ.2⟩
  have htime := continuousOn_time_deriv_of_contDiffOn_cylinder hf
  obtain ⟨A, hA⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hf.continuousOn.mono hsub)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (htime.mono hsub)
  apply hasDerivAt_integral_sq_of_memLp_bounds
    (s := Ioo α β) (A := fun _ ↦ A) (B := fun _ ↦ B)
  · exact Ioo_mem_nhds hα.2 hβ.1
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (contDiff_slice_of_contDiffOn_cylinder hf hs).continuous.aestronglyMeasurable
  · have hc : Continuous (fun x ↦ deriv (f x) t) :=
      continuousOn_univ.mp <| htime.comp (continuousOn_id.prodMk continuousOn_const)
        (fun x _ ↦ ⟨mem_univ x, ht⟩)
    exact hc.aestronglyMeasurable
  · exact memLp_const A
  · exact memLp_const B
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro s hs
    exact ⟨hA (x, s) ⟨hx, hs.1.le, hs.2.le⟩, hB (x, s) ⟨hx, hs.1.le, hs.2.le⟩⟩
  · filter_upwards with x
    intro s hs
    have hxs : (x, s) ∈ univ ×ˢ Ioo a b :=
      ⟨mem_univ x, hα.1.trans hs.1, hs.2.trans hβ.2⟩
    have hfs := (hf.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hxs)).differentiableAt (by simp)
    exact (hfs.comp s
      ((hasDerivAt_const s x).prodMk (hasDerivAt_id s)).differentiableAt).hasDerivAt

end PDE.Analysis.Evolution
