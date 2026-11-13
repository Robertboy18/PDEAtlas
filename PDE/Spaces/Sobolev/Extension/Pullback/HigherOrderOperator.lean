/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.Pullback.HigherOrder
public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.BoundedOperator
public import PDE.Analysis.Normed.Operator.InjectiveLift
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Bounded higher-order pullback

The weak chain rule already constructs the Sobolev pullback through bounded charts.
The closed graph theorem upgrades this construction to a bounded linear operator.
Its base coordinate is the same bounded `L²` pullback at every Sobolev order.
-/

@[expose] public section

open scoped Sobolev

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory GraphSpace
open scoped ENNReal

variable {n m : ℕ} {E : OpenPartialHomeomorph ℝ^n ℝ^n}

/-- The weak chain rule lifts the L² pullback to a bounded map on Hᵐ. -/
theorem exists_higherOrderPullbackCLM (hm : 0 < m)
    (hE : ContDiff ℝ m E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target) :
    ∃ P : W^{m,2}(E.target) →L[ℝ] W^{m,2}(E.source),
      wkpBaseCoordinateCLM.comp P =
        (boundedPullbackCLM (hE.of_le (by exact_mod_cast hm)) hEsymm
          hTarget).comp wkpBaseCoordinateCLM := by
  apply ContinuousLinearMap.exists_lift_of_injective
    (wkpBaseCoordinateCLM (m := m) (p := 2) (Ω := E.source))
    ((boundedPullbackCLM (hE.of_le (by exact_mod_cast hm)) hEsymm
      hTarget).comp (wkpBaseCoordinateCLM (m := m) (p := 2) (Ω := E.target)))
    (wkpBaseCoordinateCLM_injective (r := m) (p := 2) E.open_source)
  intro U
  obtain ⟨P, hP⟩ := exists_WkTwo_pullback_on_bounded_chart m hm
    (Approximation.standardMollifier n) hE hEsymm hSource hTarget U
  refine ⟨P, Lp.ext (hP.trans ?_)⟩
  exact (boundedPullbackLp_apply_ae
    (hE.of_le (by exact_mod_cast hm)) hEsymm hTarget _).symm

/-- Pullback through a bounded Cᵐ chart, as a bounded map on `Hᵐ`. -/
noncomputable def higherOrderPullbackCLM (hm : 0 < m)
    (hE : ContDiff ℝ m E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target) :
    W^{m,2}(E.target) →L[ℝ] W^{m,2}(E.source) :=
  (exists_higherOrderPullbackCLM hm hE hEsymm hSource hTarget).choose

/-- Higher-order pullback and `L²` pullback have exactly the same base coordinate. -/
theorem higherOrderPullbackCLM_base (hm : 0 < m)
    (hE : ContDiff ℝ m E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target) (U : W^{m,2}(E.target)) :
    wkpBaseCoordinateCLM (higherOrderPullbackCLM hm hE hEsymm hSource hTarget U) =
      boundedPullbackCLM (hE.of_le (by exact_mod_cast hm)) hEsymm
        hTarget (wkpBaseCoordinateCLM U) := by
  exact DFunLike.congr_fun
    (exists_higherOrderPullbackCLM hm hE hEsymm hSource hTarget).choose_spec U

/-- The Sobolev pullback represents composition with the chart almost everywhere. -/
theorem higherOrderPullbackCLM_base_ae (hm : 0 < m)
    (hE : ContDiff ℝ m E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target) (U : W^{m,2}(E.target)) :
    ⇑(wkpBaseCoordinateCLM (higherOrderPullbackCLM hm hE hEsymm hSource hTarget U))
      =ᵐ[domainMeasure n E.source] fun x ↦ wkpBaseCoordinateCLM U (E x) := by
  rw [higherOrderPullbackCLM_base, boundedPullbackCLM_apply]
  exact boundedPullbackLp_apply_ae _ _ _ _

end SobolevSpace.WeakChangeOfVariables
