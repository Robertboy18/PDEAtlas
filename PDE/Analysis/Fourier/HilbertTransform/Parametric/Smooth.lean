/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Temporal
import PDE.Analysis.Fourier.HilbertTransform.Parametric.Continuity
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.Calculus

/-!
# The Hilbert transform of smooth families

For a family `f : ℝ → ℝ → ℝ` (space, then time), `hilbertPVX f x t` is the principal-value
Hilbert transform of the slice `f (·, t)` at `x`. On smooth compactly supported functions the
Hilbert transform commutes with differentiation (`iterate_deriv_hilbertPV`), so it maps a
spatially smooth family of bounded support to a spatially smooth family
(`IsSpatiallySmooth.hilbertPVX`) and keeps the number of its time derivatives
(`IsTimeSmooth.hilbertPVX`).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ContDiff NNReal

namespace PDE.Analysis

/-- The Hilbert transform of a family in its first variable, as a principal value. -/
def hilbertPVX (f : ℝ → ℝ → ℝ) (x t : ℝ) : ℝ := hilbertPV (fun y ↦ f y t) x

/-- Iterated derivatives of the Hilbert transform of a smooth compactly supported function. -/
theorem iterate_deriv_hilbertPV {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (k : ℕ) : deriv^[k] (hilbertPV g) = hilbertPV (deriv^[k] g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      deriv_hilbertPV_of_contDiff_two_compactSupport (hg.of_le (by simp)) hc,
      ih (contDiff_infty_iff_deriv.mp hg).2 hc.deriv]

namespace IsSpatiallySmooth

variable {T : ℝ} {f : ℝ → ℝ → ℝ}

/-- The spatial Hilbert transform of a spatially smooth family of bounded support is spatially
smooth. -/
theorem hilbertPVX (hf : IsSpatiallySmooth T f) (hs : HasBoundedSupport T f) :
    IsSpatiallySmooth T (hilbertPVX f) where
  contDiff t ht :=
    contDiff_hilbertPV_of_contDiff_compactSupport (hf.contDiff t ht) (hs.hasCompactSupport ht)
  continuous k := by
    obtain ⟨L, B, K, hL, hb⟩ := hf.exists_bounds hs k
    have heq : (fun z : ℝ × Icc (0 : ℝ) T ↦
        deriv^[k] (fun y ↦ PDE.Analysis.hilbertPVX f y z.2) z.1) =
        fun z ↦ hilbertPV (deriv^[k] (fun y ↦ f y z.2)) z.1 := by
      funext z
      exact congrFun (iterate_deriv_hilbertPV (hf.contDiff z.2 z.2.property)
        (hs.hasCompactSupport z.2.property) k) z.1
    rw [heq]
    exact continuous_hilbertPV_of_uniform_bounds (q := fun t : Icc (0 : ℝ) T ↦
      deriv^[k] (fun y ↦ f y t)) hL (fun t ↦ (hb t).1) (fun t ↦ (hb t).2.1)
      (fun t ↦ (hb t).2.2) (hf.continuous k)

end IsSpatiallySmooth

namespace IsTimeSmooth

variable {T : ℝ}

/-- The spatial Hilbert transform of a family of bounded support preserves the number of time
derivatives. -/
theorem hilbertPVX (hT : 0 < T) : ∀ {n : ℕ} {f : ℝ → ℝ → ℝ}, IsTimeSmooth T n f →
    HasBoundedSupport T f → IsTimeSmooth T n (PDE.Analysis.hilbertPVX f)
  | 0, _, h, hb => IsSpatiallySmooth.hilbertPVX h hb
  | n + 1, f, h, hb => by
    obtain ⟨hs, g, hg, hd⟩ := h
    have hgs := spatial hg
    have hgb := hb.of_hasDerivWithinAt hT hd
    refine ⟨hs.hilbertPVX hb, PDE.Analysis.hilbertPVX g, hilbertPVX hT hg hgb,
      fun x ↦ hasDerivWithinAt_Icc_of_interior ((hs.hilbertPVX hb).continuousOn_time x)
        ((hgs.hilbertPVX hgb).continuousOn_time x) fun t ht ↦ ?_⟩
    obtain ⟨L, B, K, hL, hbounds⟩ := hgs.exists_bounds hgb 0
    obtain ⟨M, hM⟩ := hb
    have hIoo (s : ℝ) (hs' : s ∈ Ioo (0 : ℝ) T) : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs'
    exact hasDerivAt_hilbertPV_of_uniform_time_bounds (f := fun s y ↦ f y s)
      (q := fun s y ↦ g y s) (times := Ioo 0 T) (K := K) (B := B) (L := L)
      (Ioo_mem_nhds ht.1 ht.2) hL
      (fun s hs' ↦ (hs.contDiff s (hIoo s hs')).of_le (by simp))
      (fun s hs' ↦ HasBoundedSupport.hasCompactSupport ⟨M, hM⟩ (hIoo s hs'))
      (fun s hs' ↦ by simpa only [Function.iterate_zero, id] using (hbounds ⟨s, hIoo s hs'⟩).1)
      (fun s hs' y ↦ by simpa only [Function.iterate_zero, id] using
        (hbounds ⟨s, hIoo s hs'⟩).2.1 y)
      (fun s hs' y hy ↦ by simpa only [Function.iterate_zero, id] using
        (hbounds ⟨s, hIoo s hs'⟩).2.2 y hy)
      (fun y s hs' ↦ (hd y s (hIoo s hs')).hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)) x

end IsTimeSmooth

end PDE.Analysis
