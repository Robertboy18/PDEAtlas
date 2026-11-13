/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Dynamics.Flow
public import PDE.Analysis.Evolution.GradientFlow.Semigroup.Domain

/-!
# The nonlinear subgradient semigroup on the closed domain

Each solution map `S(t)` on the subdifferential domain `D` is a contraction, so
it extends uniquely to a contraction `subgradientSemigroup t` of the closure
`C = closure D`, which is complete. By density, `S(0) = id`,
`S(s + t) = S(s) ∘ S(t)` and `‖S(t) x - S(t) y‖ ≤ ‖x - y‖` hold on `C`. Uniform
contraction in the initial point and continuity of the trajectories from `D` make
`(t, x) ↦ S(t) x` jointly continuous, including at `t = 0`. Hence
`subgradientSemiflow` is a continuous action of `ℝ≥0` on `C`, and it is the only
contraction flow on `C` that agrees with every weak subgradient trajectory from `D`.

Evans, §9.6.2, Remarks (i) and (ii) after the proof of Theorem 3, extends the contraction
semigroup from `D(∂I)` to its closure in the same way, using the contraction estimate. On `C`,
`subgradientSemigroup_zero`, `subgradientSemigroup_add`, `continuous_subgradientSemigroup_orbit`
and `subgradientSemigroup_dist_le` are the conditions (11)-(14) of his definition of a
contraction semigroup. The extension is Mathlib's `IsDenseInducing.extend`, and the flow is a
Mathlib `Flow`. Joint continuity in `(t, x)`, `continuous_subgradientSemigroup_joint`, is ours.

## Main definitions

* `subgradientSemigroup t`: the extension of the solution map at time `t` to `C`.
* `subgradientSemiflow`: the extended semigroup as a `Flow ℝ≥0 C`.

## Main results

* `subgradientSemigroup_of_mem`, `subgradientSemigroup_eq_flow`: on `D` the extension is the
  original solution map and agrees with every weak subgradient trajectory.
* `subgradientSemigroup_zero`, `subgradientSemigroup_add`, `continuous_subgradientSemigroup_orbit`,
  `subgradientSemigroup_dist_le`: the semigroup laws, continuous orbits and the contraction
  estimate on `C`.
* `continuous_subgradientSemigroup_joint`: joint continuity in time and initial point.
* `exists_unique_subgradientSemiflow`: existence and uniqueness of the contraction flow on `C`
  that agrees with the weak trajectories from `D`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, Definitions (11)-(14) and Theorem 3 (Solution of
  gradient flow), p. 566, and Remarks (i) and (ii) after its proof, p. 570.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set PDE.Analysis.Convex
open scoped NNReal

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

local notation "D" => subdifferentialDomain I
local notation "C" => closure (subdifferentialDomain I)
local notation "ι" =>
  inclusion (subset_closure (s := subdifferentialDomain I))

variable (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
  (hlsc : LowerSemicontinuous I)

/-- The nonlinear solution map on the closure of the subdifferential domain,
constructed by uniformly extending the domain solution map. -/
def subgradientSemigroup (t : ℝ≥0) : C → C :=
  ((isUniformEmbedding_set_inclusion (subset_closure : D ⊆ C)).isUniformInducing.isDenseInducing
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)).extend
      (ι ∘ subgradientDomainMap hproper hconvex hlsc t)

/-- The constructed extension agrees with the original solution on the operator domain. -/
@[simp]
theorem subgradientSemigroup_of_mem (t : ℝ≥0) (x : D) :
    subgradientSemigroup hproper hconvex hlsc t (ι x) =
      ι (subgradientDomainMap hproper hconvex hlsc t x) := by
  apply IsDenseInducing.extend_eq
  exact (continuous_inclusion subset_closure).comp
    (subgradientDomainMap_lipschitz hproper hconvex hlsc t).continuous

/-- Completeness of the closed domain gives a continuous extension at each time. -/
theorem continuous_subgradientSemigroup (t : ℝ≥0) :
    Continuous (subgradientSemigroup hproper hconvex hlsc t) := by
  let : CompleteSpace C := isClosed_closure.isComplete.completeSpace_coe
  apply UniformContinuous.continuous
  exact uniformContinuous_uniformly_extend
    (isUniformEmbedding_set_inclusion (subset_closure : D ⊆ C)).isUniformInducing
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)
    ((show Isometry ι from fun _ _ ↦ rfl).uniformContinuous.comp
      (subgradientDomainMap_lipschitz hproper hconvex hlsc t).uniformContinuous)

/-- The contraction estimate persists at all initial points in the closed domain. -/
theorem subgradientSemigroup_lipschitz (t : ℝ≥0) :
    LipschitzWith 1 (subgradientSemigroup hproper hconvex hlsc t) := by
  apply LipschitzWith.mk_one
  refine isClosed_property2
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl) ?_ ?_
  · exact isClosed_le
      (((continuous_subgradientSemigroup hproper hconvex hlsc t).comp continuous_fst).dist
        ((continuous_subgradientSemigroup hproper hconvex hlsc t).comp continuous_snd))
      (continuous_fst.dist continuous_snd)
  · intro x y
    rw [subgradientSemigroup_of_mem, subgradientSemigroup_of_mem]
    have h := (subgradientDomainMap_lipschitz hproper hconvex hlsc t).dist_le_mul x y
    rw [NNReal.coe_one, one_mul] at h
    exact h

/-- Distances between solutions cannot increase, also for initial data in the closure. -/
theorem subgradientSemigroup_dist_le (t : ℝ≥0) (x y : C) :
    dist (subgradientSemigroup hproper hconvex hlsc t x)
      (subgradientSemigroup hproper hconvex hlsc t y) ≤ dist x y := by
  simpa only [NNReal.coe_one, one_mul] using
    (subgradientSemigroup_lipschitz hproper hconvex hlsc t).dist_le_mul x y

/-- At time zero the extension is the identity on the entire closed domain. -/
@[simp]
theorem subgradientSemigroup_zero (x : C) :
    subgradientSemigroup hproper hconvex hlsc 0 x = x := by
  refine isClosed_property
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)
    (isClosed_eq (continuous_subgradientSemigroup hproper hconvex hlsc 0) continuous_id) ?_ x
  intro y
  simp only [subgradientSemigroup_of_mem, subgradientDomainMap_zero, id_eq]

/-- The restart law extends from domain trajectories to all initial points in the closure. -/
theorem subgradientSemigroup_add (s t : ℝ≥0) (x : C) :
    subgradientSemigroup hproper hconvex hlsc (s + t) x =
      subgradientSemigroup hproper hconvex hlsc s
        (subgradientSemigroup hproper hconvex hlsc t x) := by
  refine isClosed_property
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)
    (isClosed_eq (continuous_subgradientSemigroup hproper hconvex hlsc (s + t))
      ((continuous_subgradientSemigroup hproper hconvex hlsc s).comp
        (continuous_subgradientSemigroup hproper hconvex hlsc t))) ?_ x
  intro y
  simp only [Function.comp_apply, subgradientSemigroup_of_mem, subgradientDomainMap_add]

/-- Contraction makes the closure solution jointly continuous in time and initial point. -/
theorem continuous_subgradientSemigroup_joint :
    Continuous (fun tx : ℝ≥0 × C ↦ subgradientSemigroup hproper hconvex hlsc tx.1 tx.2) := by
  refine continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)
    (subgradientSemigroup_lipschitz hproper hconvex hlsc) ?_
  rintro _ ⟨x, rfl⟩
  simp only [subgradientSemigroup_of_mem]
  exact (continuous_inclusion subset_closure).comp
    (continuous_subgradientDomainMap hproper hconvex hlsc x)

/-- Every orbit from the closed domain is strongly continuous at all nonnegative times. -/
theorem continuous_subgradientSemigroup_orbit (x : C) :
    Continuous (fun t : ℝ≥0 ↦ subgradientSemigroup hproper hconvex hlsc t x) :=
  (continuous_subgradientSemigroup_joint hproper hconvex hlsc).comp
    (continuous_id.prodMk continuous_const)

/-- On the original domain the semigroup agrees with every weak subgradient
trajectory with the same initial value, independently of the existence choice. -/
theorem subgradientSemigroup_eq_flow {x : H} (hx : x ∈ D) {u g : ℝ → H}
    (hzero : u 0 = x) (hflow : IsSubgradientFlow I u g) (t : ℝ≥0) :
    (subgradientSemigroup hproper hconvex hlsc t ⟨x, subset_closure hx⟩ : H) = u t := by
  let v := subgradientDomainFlow hproper hconvex hlsc ⟨x, hx⟩
  have heq := v.isFlow.eqOn_of_initial_eq hproper hflow (v.initial.trans hzero.symm)
  exact (congrArg Subtype.val
    (subgradientSemigroup_of_mem hproper hconvex hlsc t ⟨x, hx⟩)).trans (heq t.property)

/-- The nonlinear contraction semigroup as a jointly continuous action of
nonnegative time on the closure of the subdifferential domain. -/
def subgradientSemiflow : Flow ℝ≥0 C where
  toFun := subgradientSemigroup hproper hconvex hlsc
  cont' := continuous_subgradientSemigroup_joint hproper hconvex hlsc
  map_add' := subgradientSemigroup_add hproper hconvex hlsc
  map_zero' := subgradientSemigroup_zero hproper hconvex hlsc

include hproper hconvex hlsc in
/-- A proper, convex, lower semicontinuous energy on a real Hilbert space gives a
unique strongly continuous nonlinear contraction semigroup on the closed
subdifferential domain that agrees with all original-domain weak trajectories. -/
theorem exists_unique_subgradientSemiflow :
    ∃! S : Flow ℝ≥0 C,
      (∀ t, LipschitzWith 1 (S t)) ∧
      (∀ (x : D) (u g : ℝ → H), u 0 = x → IsSubgradientFlow I u g →
        ∀ t : ℝ≥0, (S t (ι x) : H) = u t) := by
  refine ⟨subgradientSemiflow hproper hconvex hlsc, ⟨?_, ?_⟩, ?_⟩
  · exact subgradientSemigroup_lipschitz hproper hconvex hlsc
  · intro x u g hzero hflow t
    exact subgradientSemigroup_eq_flow hproper hconvex hlsc x.property hzero hflow t
  · intro S hS
    apply Flow.ext
    intro t x
    refine isClosed_property
      ((denseRange_inclusion_iff (subset_closure : D ⊆ C)).2 subset_rfl)
      (isClosed_eq (S.continuous_toFun t)
        (continuous_subgradientSemigroup hproper hconvex hlsc t)) ?_ x
    intro y
    apply Subtype.ext
    let v := subgradientDomainFlow hproper hconvex hlsc y
    exact (hS.2 y v.curve v.velocity v.initial v.isFlow t).trans
      (subgradientSemigroup_eq_flow hproper hconvex hlsc y.property
        v.initial v.isFlow t).symm

end PDE.Analysis.Evolution
