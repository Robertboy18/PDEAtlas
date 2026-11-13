/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Existence.Domain
public import PDE.Analysis.Evolution.GradientFlow.Semigroup.Shift

/-!
# The nonlinear subgradient semigroup on its original domain

`exists_unique_subgradientFlow` gives, from each point `x` of the subdifferential
domain `D`, a weak trajectory that stays in `D`. Its value at time `t` defines
`subgradientDomainMap t : D → D`. Uniqueness of weak flows gives the semigroup law
`S(s + t) = S(s) ∘ S(t)` by restarting at time `t`, monotonicity of `∂I` makes each
`S(t)` 1-Lipschitz, and each orbit `t ↦ S(t) x` is continuous on `ℝ≥0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Convex
open scoped NNReal

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- A weak subgradient trajectory together with invariance of the operator domain. -/
structure SubgradientDomainFlow (I : H → EReal) (x : H) where
  /-- The trajectory. Only its values at times `t ≥ 0` are constrained. -/
  curve : ℝ → H
  /-- The distributional velocity of the trajectory. -/
  velocity : ℝ → H
  /-- The prescribed initial trace. -/
  initial : curve 0 = x
  /-- The full weak evolution relation. -/
  isFlow : IsSubgradientFlow I curve velocity
  /-- The subdifferential domain is invariant for nonnegative times. -/
  mem_domain : ∀ t, 0 ≤ t → curve t ∈ subdifferentialDomain I

/-- The domain-invariant weak trajectory from `x` given by
`exists_unique_subgradientFlow`. -/
def subgradientDomainFlow (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    (x : subdifferentialDomain I) : SubgradientDomainFlow I x := by
  apply Classical.choice
  obtain ⟨_, _, _, u, g, hzero, hflow, _, _, _, _, hdomain, _⟩ :=
    exists_unique_subgradientFlow hproper hconvex hlsc x.property
  exact ⟨⟨u, g, hzero, hflow, hdomain⟩⟩

variable (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
  (hlsc : LowerSemicontinuous I)

/-- The nonlinear solution map at nonnegative time on the subdifferential domain. -/
def subgradientDomainMap (t : ℝ≥0) (x : subdifferentialDomain I) :
    subdifferentialDomain I :=
  ⟨(subgradientDomainFlow hproper hconvex hlsc x).curve t,
    (subgradientDomainFlow hproper hconvex hlsc x).mem_domain t t.property⟩

/-- The time-zero solution map is the identity. -/
@[simp]
theorem subgradientDomainMap_zero (x : subdifferentialDomain I) :
    subgradientDomainMap hproper hconvex hlsc 0 x = x :=
  Subtype.ext (subgradientDomainFlow hproper hconvex hlsc x).initial

/-- Monotonicity makes every solution map nonexpansive. -/
theorem subgradientDomainMap_lipschitz (t : ℝ≥0) :
    LipschitzWith 1 (subgradientDomainMap hproper hconvex hlsc t) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have h := (subgradientDomainFlow hproper hconvex hlsc x).isFlow.norm_sub_le_initial
    hproper (subgradientDomainFlow hproper hconvex hlsc y).isFlow t.property
  rw [(subgradientDomainFlow hproper hconvex hlsc x).initial,
    (subgradientDomainFlow hproper hconvex hlsc y).initial] at h
  rw [NNReal.coe_one, one_mul, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm,
    dist_eq_norm]
  exact h

/-- Restarting the weak trajectory proves the nonlinear semigroup law. -/
theorem subgradientDomainMap_add (s t : ℝ≥0) (x : subdifferentialDomain I) :
    subgradientDomainMap hproper hconvex hlsc (s + t) x =
      subgradientDomainMap hproper hconvex hlsc s
        (subgradientDomainMap hproper hconvex hlsc t x) := by
  let u := subgradientDomainFlow hproper hconvex hlsc x
  let v := subgradientDomainFlow hproper hconvex hlsc
    (subgradientDomainMap hproper hconvex hlsc t x)
  have hzero : (fun r ↦ u.curve ((t : ℝ) + r)) 0 = v.curve 0 := by
    rw [v.initial]
    simp only [add_zero, subgradientDomainMap, u]
  have heq := (u.isFlow.shift t.property).eqOn_of_initial_eq hproper v.isFlow hzero
  apply Subtype.ext
  change u.curve ((s : ℝ) + t) = v.curve s
  rw [add_comm]
  exact heq s.property

/-- A domain trajectory is strongly continuous, including at time zero. -/
theorem continuous_subgradientDomainMap (x : subdifferentialDomain I) :
    Continuous (fun t : ℝ≥0 ↦ subgradientDomainMap hproper hconvex hlsc t x) := by
  apply Continuous.subtype_mk
  exact (subgradientDomainFlow hproper hconvex hlsc x).isFlow.continuousOn.comp_continuous
    continuous_subtype_val (fun t ↦ t.property)

end PDE.Analysis.Evolution
