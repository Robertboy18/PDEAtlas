/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Integer.RealPart
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder

/-!
# First-order representatives of complex Bessel functions

An H¹ distribution represented by a complex L² function has a real H¹
representative for its real part. Each first derivative is obtained from the
Bessel estimate, then its real weak identity is supplied by the
distributional real-part bridge. The complex function need not be real outside
the region where it represents given real data.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv

namespace SobolevSpace.Fractional

open GraphSpace

variable {n : ℕ}

/-- First-order Bessel regularity reconstructs the real Sobolev graph.
All derivative rows are derived; only the base L² representative is supplied. -/
theorem exists_wkpSpaceOn_one_re_of_memSobolev
    (u : Lp ℂ 2 (volume : Measure (ℝ^n)))
    (hu : MemSobolev 1 2 (u : 𝓢'(ℝ^n, ℂ))) :
    ∃ U : W^{1,2}((Set.univ : Set (ℝ^n))),
      baseRepresentative U =ᵐ[volume] fun x ↦ (u x).re := by
  classical
  have hfirst (i : Fin n) :
      ∃ g : Lp ℂ 2 (volume : Measure (ℝ^n)),
        (g : 𝓢'(ℝ^n, ℂ)) =
          ∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(ℝ^n, ℂ)) := by
    have h0 : MemSobolev 0 2
        (∂_{EuclideanSpace.single i (1 : ℝ)} (u : 𝓢'(ℝ^n, ℂ))) := by
      convert hu.lineDerivOp (m := EuclideanSpace.single i (1 : ℝ)) using 1
      norm_num
    obtain ⟨g, hg⟩ := memSobolev_zero_iff.mp h0
    exact ⟨g, hg.symm⟩
  choose g hg using hfirst
  have huR : MemLp (fun x ↦ (u x).re) 2 (domainMeasure n Set.univ) := by
    simpa [domainMeasure] using (Lp.memLp u).re
  have hgR (i : Fin n) :
      MemLp (fun x ↦ (g i x).re) 2 (domainMeasure n Set.univ) := by
    simpa [domainMeasure] using (Lp.memLp (g i)).re
  let uR := huR.toLp (fun x ↦ (u x).re)
  let gR (i : Fin n) := (hgR i).toLp (fun x ↦ (g i x).re)
  obtain ⟨U, hU, _⟩ := exists_of_weakDerivative_coordinates uR gR
    (fun i ↦ (hasWeakDerivativeOn_re_of_lineDeriv_eq i u (g i) (hg i)).congr_ae
      huR.coeFn_toLp.symm (hgR i).coeFn_toLp.symm)
  refine ⟨U, ?_⟩
  change (U.val (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[volume] _
  rw [hU]
  simpa only [domainMeasure, Measure.restrict_univ] using huR.coeFn_toLp

end SobolevSpace.Fractional
