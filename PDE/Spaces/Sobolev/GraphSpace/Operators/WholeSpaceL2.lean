/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions

/-!
# Whole-space Sobolev rows and Lebesgue L²

The whole-space graph model uses volume restricted to `univ`. Identity pullback gives
a linear isometric equivalence with ordinary Lebesgue L² and preserves representatives
almost everywhere. The equivalence lets bounded operators act on either model without
changing its canonical norm or inner product.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Identity pullback identifies the whole-space Sobolev L2 row with Lebesgue L2.
Using an isometry keeps dependent measure instances out of subsequent rewrites. -/
def wholeSpaceL2Equiv :
    DerivLp n 2 univ ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) := by
  let e : DerivLp n 2 univ →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (ℝ^n)) :=
    Lp.compMeasurePreservingₗᵢ ℝ id (by
      simpa only [domainMeasure, Measure.restrict_univ] using
        MeasurePreserving.id (volume : Measure (ℝ^n)))
  let r : Lp ℝ 2 (volume : Measure (ℝ^n)) →ₗᵢ[ℝ] DerivLp n 2 univ :=
    Lp.compMeasurePreservingₗᵢ ℝ id (by
      simpa only [domainMeasure, Measure.restrict_univ] using
        MeasurePreserving.id (volume : Measure (ℝ^n)))
  have he (u : DerivLp n 2 univ) : (e u : ℝ^n → ℝ) =ᵐ[volume] u :=
    Lp.coeFn_compMeasurePreserving u _
  have hae : ae (domainMeasure n univ) = ae (volume : Measure (ℝ^n)) := by
    rw [domainMeasure, Measure.restrict_univ]
  have hr (u : Lp ℝ 2 (volume : Measure (ℝ^n))) :
      (r u : ℝ^n → ℝ) =ᵐ[volume] u := by
    rw [← hae]
    filter_upwards [Lp.coeFn_compMeasurePreserving u
      (show MeasurePreserving (id : ℝ^n → ℝ^n) (domainMeasure n univ) volume from
        by simpa only [domainMeasure, Measure.restrict_univ] using
          MeasurePreserving.id (volume : Measure (ℝ^n)))] with x hx
    exact hx
  exact {
    e.toLinearMap with
    invFun := r
    left_inv := fun u ↦ by
      change r (e u) = u
      apply Lp.ext
      rw [hae]
      exact (hr (e u)).trans (he u)
    right_inv := fun u ↦ Lp.ext ((he (r u)).trans (hr u))
    norm_map' := e.norm_map
  }

/-- Identity pullback preserves the almost-everywhere representative. -/
theorem wholeSpaceL2Equiv_ae (u : DerivLp n 2 univ) :
    (wholeSpaceL2Equiv u : ℝ^n → ℝ) =ᵐ[volume] u := by
  unfold wholeSpaceL2Equiv
  exact Lp.coeFn_compMeasurePreserving u _

end SobolevSpace.GraphSpace
