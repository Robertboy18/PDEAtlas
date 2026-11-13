/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import PDE.Analysis.WeakCompactness

/-!
# Linear constraints and weak convergence

The common kernel of an arbitrary family of continuous linear maps is weakly closed, so
weak limits satisfy every constraint that holds eventually along the approximating family.
In a real Hilbert space a bounded weakly closed set stays weakly compact after the
constraints are imposed. Divergence-free conditions, zero mean, and vanishing boundary
traces are constraints of this kind once written as continuous linear maps.

A common kernel is closed and convex, so its weak closedness is also a case of Mazur's
theorem as stated in Evans, Appendix D.4; we obtain it from the weak continuity of each map,
`WeakSpace.map`. The compactness statement combines it with
`WeakCompactness.isCompact_of_isClosed_of_isBounded`, our topological counterpart for real
Hilbert spaces of Evans's Theorem 3 in Appendix D.4.

## Main definitions

* `weakConstraintSet A`: the common kernel of the maps `A j`, as a subset of `WeakSpace ℝ E`.

## Main results

* `tendsto_weak_map`: continuous linear maps preserve weak convergence.
* `isClosed_weakConstraintSet`, `constraints_eq_zero_of_tendsto_weak`: the common kernel is
  weakly closed, and a weak limit satisfies every constraint that holds eventually along the
  approximating family.
* `WeakCompactness.isCompact_inter_weakConstraintSet`: in a real Hilbert space, a bounded
  weakly closed set meets the common kernel in a weakly compact set.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.4, Theorem 3 (Weak compactness) and Mazur's
  Theorem, p. 723. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Set

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A continuous linear map sends weakly convergent families to weakly convergent
families. -/
theorem tendsto_weak_map
    (A : E →L[ℝ] F)
    {ι : Type*} {l : Filter ι}
    {x : ι → E} {xLimit : E}
    (hx : Filter.Tendsto (fun i ↦ toWeakSpace ℝ E (x i)) l
      (nhds (toWeakSpace ℝ E xLimit))) :
    Filter.Tendsto (fun i ↦ toWeakSpace ℝ F (A (x i))) l
      (nhds (toWeakSpace ℝ F (A xLimit))) := by
  have hmap :=
    (WeakSpace.map A).continuous.continuousAt.tendsto.comp hx
  change Filter.Tendsto (fun i ↦ toWeakSpace ℝ F (A (x i))) l
    (nhds (toWeakSpace ℝ F (A xLimit))) at hmap
  exact hmap

/-- The weak-space set cut out by an arbitrary family of continuous linear
constraints. -/
def weakConstraintSet {J : Type*} (A : J → E →L[ℝ] F) :
    Set (WeakSpace ℝ E) :=
  ⋂ j, ((WeakSpace.map (A j)).ker : Set (WeakSpace ℝ E))

/-- `x` lies in the weak constraint set iff `A j x = 0` for every `j`. -/
@[simp]
theorem toWeakSpace_mem_weakConstraintSet {J : Type*}
    (A : J → E →L[ℝ] F) (x : E) :
    toWeakSpace ℝ E x ∈ weakConstraintSet A ↔
      ∀ j, A j x = 0 := by
  simp only [weakConstraintSet, mem_iInter]
  change (∀ j, A j x = 0) ↔ ∀ j, A j x = 0
  rfl

/-- An arbitrary family of continuous linear constraints cuts out a weakly
closed set. -/
theorem isClosed_weakConstraintSet {J : Type*}
    (A : J → E →L[ℝ] F) :
    IsClosed (weakConstraintSet A) := by
  unfold weakConstraintSet
  exact isClosed_iInter fun j ↦ (WeakSpace.map (A j)).isClosed_ker

/-- Simultaneous continuous linear constraints are preserved by weak limits. -/
theorem weakConstraintSet_mem_of_tendsto
    {J ι : Type*} {l : Filter ι} [l.NeBot]
    (A : J → E →L[ℝ] F)
    {x : ι → E} {xLimit : E}
    (hx : Filter.Tendsto (fun i ↦ toWeakSpace ℝ E (x i)) l
      (nhds (toWeakSpace ℝ E xLimit)))
    (hA : ∀ᶠ i in l, ∀ j, A j (x i) = 0) :
    toWeakSpace ℝ E xLimit ∈ weakConstraintSet A := by
  apply (isClosed_weakConstraintSet A).mem_of_tendsto hx
  filter_upwards [hA] with i hi
  exact (toWeakSpace_mem_weakConstraintSet A (x i)).2 hi

/-- A weak limit satisfies a family of continuous linear constraints if, eventually along
the approximating family, all constraints hold simultaneously. -/
theorem constraints_eq_zero_of_tendsto_weak
    {J ι : Type*} {l : Filter ι} [l.NeBot]
    (A : J → E →L[ℝ] F)
    {x : ι → E} {xLimit : E}
    (hx : Filter.Tendsto (fun i ↦ toWeakSpace ℝ E (x i)) l
      (nhds (toWeakSpace ℝ E xLimit)))
    (hA : ∀ᶠ i in l, ∀ j, A j (x i) = 0) :
    ∀ j, A j xLimit = 0 :=
  (toWeakSpace_mem_weakConstraintSet A xLimit).1
    (weakConstraintSet_mem_of_tendsto A hx hA)

/-- In a real Hilbert space, a norm-bounded weakly closed set remains weakly compact after
imposing an arbitrary family of continuous linear constraints. -/
theorem WeakCompactness.isCompact_inter_weakConstraintSet
    {H K J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (A : J → H →L[ℝ] K)
    {S : Set (WeakSpace ℝ H)}
    (hSclosed : IsClosed S)
    (hSbounded :
      Bornology.IsBounded ((toWeakSpace ℝ H) ⁻¹' S)) :
    IsCompact (S ∩ weakConstraintSet A) := by
  apply WeakCompactness.isCompact_of_isClosed_of_isBounded
    (hSclosed.inter (isClosed_weakConstraintSet A))
  exact Bornology.IsBounded.subset hSbounded fun _ hx ↦ hx.1

end PDE.Analysis
