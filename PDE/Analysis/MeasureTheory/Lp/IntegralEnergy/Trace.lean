/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Cylinder
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Continuous traces of compact integral energies

Pointwise time traces and a uniform spatial bound make a compact square
integral continuous on a closed interval. Interior identities therefore
pass to the two endpoint traces.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace PDE.Analysis

/-- Interior joint C¹ regularity and two pointwise endpoint traces give
continuity of each time slice on the closed slab. -/
theorem continuousOn_time_of_contDiffOn_slab_of_endpoint_traces
    {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b))
    (htrace : ∀ x, ContinuousWithinAt (f x) (Icc a b) a ∧
      ContinuousWithinAt (f x) (Icc a b) b) (x : ℝ) :
    ContinuousOn (f x) (Icc a b) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact (htrace x).1
  rcases eq_or_lt_of_le ht.2 with rfl | htb
  · exact (htrace x).2
  have hc := hf.contDiffAt (x := (x, t))
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, hat, htb⟩)
  exact (hc.comp t (contDiffAt_const.prodMk contDiffAt_id)).continuousAt.continuousWithinAt

/-- Pointwise time traces and a uniform spatial bound make every fixed compact
square integral continuous on the closed time interval. -/
theorem continuousOn_integral_sq_Icc_of_traces {f : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hspace : ∀ t ∈ Icc a b, Continuous (fun x ↦ f x t))
    (htime : ∀ x, ContinuousOn (f x) (Icc a b))
    (hbound : ∀ t ∈ Icc a b, ∀ x, |f x t| ≤ C) (l r : ℝ) :
    ContinuousOn (fun t ↦ ∫ x in Icc l r, f x t ^ 2) (Icc a b) := by
  apply continuousOn_of_dominated (bound := fun _ ↦ C ^ 2)
  · intro t ht
    exact ((hspace t ht).pow 2).aestronglyMeasurable
  · intro t ht
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hbound t ht x) 2
  · exact integrable_const _
  · exact Eventually.of_forall fun x ↦ (htime x).pow 2

/-- A continuous identity on a nonempty open time interval holds at its two
endpoint traces as well. -/
theorem eqOn_Icc_of_eqOn_Ioo_of_continuousOn {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (heq : EqOn f g (Ioo a b)) : EqOn f g (Icc a b) := by
  intro t ht
  apply sub_eq_zero.mp
  apply ((hf t ht).sub (hg t ht)).mono Ioo_subset_Icc_self |>.eq_const_of_mem_closure
  · rwa [closure_Ioo hab.ne]
  · intro s hs
    exact sub_eq_zero.mpr (heq hs)

/-- Zero square energy on a nondegenerate interval forces a continuous field to
vanish at every point of that interval. -/
theorem eq_zero_on_Icc_of_integral_sq_eq_zero {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (hf : Continuous f) (hzero : (∫ x in Icc l r, f x ^ 2) = 0) :
    ∀ x ∈ Icc l r, f x = 0 := by
  have hae : f =ᵐ[volume.restrict (Icc l r)] 0 := by
    have hsq := (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (f x))
      (hf.pow 2).integrableOn_Icc).mp hzero
    exact hsq.mono fun _ hx ↦ sq_eq_zero_iff.mp hx
  exact fun _ hx ↦ Measure.eqOn_Icc_of_ae_eq volume hlr.ne hae hf.continuousOn
    continuousOn_const hx

/-- Signed spatial reflection preserves joint C¹ regularity on an open slab. -/
theorem contDiffOn_neg_reflect_slab {f : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) (univ ×ˢ Ioo a b)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ ↦ -f (-p.1) p.2) (univ ×ˢ Ioo a b) :=
  (hf.comp (contDiffOn_fst.neg.prodMk contDiffOn_snd)
    (fun _ hp ↦ ⟨mem_univ _, hp.2⟩)).neg

end PDE.Analysis
