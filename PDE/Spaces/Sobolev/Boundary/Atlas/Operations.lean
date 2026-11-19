/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions

/-!
# Enlarging an extension atlas

An additional compatible chart can be adjoined without changing the
partition of unity: its partition function is zero. This permits local
arguments in a chosen chart to use the same atlas as the original
finite boundary cover. The additional chart may lie entirely
inside the domain.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.Boundary.C1ExtensionAtlas

open Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Adjoin a compatible chart with zero partition weight. The original
interior and boundary partition functions are preserved. -/
@[instance_reducible]
def adjoinChart (hΩ : C1ExtensionAtlas n Ω)
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hflat : ∀ x ∈ E.source, x ∈ Ω ↔ E x ∈ HalfSpace.upper n)
    (hbounded : Bornology.IsBounded E.target) : C1ExtensionAtlas n Ω where
  isOpen := hΩ.isOpen
  bounded := hΩ.bounded
  N := hΩ.N + 1
  chart := Fin.lastCases E hΩ.chart
  chart_contDiff := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using hE
    | cast j => simpa only [Fin.lastCases_castSucc] using hΩ.chart_contDiff j
  chart_symm_contDiff := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using hSymm
    | cast j => simpa only [Fin.lastCases_castSucc] using hΩ.chart_symm_contDiff j
  chart_mem_iff_upper := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using hflat
    | cast j => simpa only [Fin.lastCases_castSucc] using hΩ.chart_mem_iff_upper j
  chart_target_bounded := by
    intro i
    induction i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using hbounded
    | cast j => simpa only [Fin.lastCases_castSucc] using hΩ.chart_target_bounded j
  interiorCutoff := hΩ.interiorCutoff
  interiorCutoff_support := hΩ.interiorCutoff_support
  boundaryCutoff := Fin.lastCases 0 hΩ.boundaryCutoff
  boundaryCutoff_support := by
    intro i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simpa only [Fin.lastCases_castSucc] using hΩ.boundaryCutoff_support j
  cutoff_sum_eq_one := by
    intro x hx
    simpa only [Fin.sum_univ_castSucc, Fin.lastCases_castSucc, Fin.lastCases_last,
      TestFunction.toFun_eq_coe, FunLike.coe_zero, Pi.zero_apply, add_zero] using
      hΩ.cutoff_sum_eq_one x hx

end SobolevSpace.Boundary.C1ExtensionAtlas
