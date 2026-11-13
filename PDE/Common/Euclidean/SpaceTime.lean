/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Topology.Algebra.Module.Equiv.Prod

/-!
# Product coordinates for Euclidean spacetime

LeanPDE's canonical `SpaceTime n` stores time in coordinate zero. It is continuously linearly
equivalent to the products `ℝ^n × ℝ` and `ℝ × ℝ^n`, and curried fields `ℝ^n → ℝ → E`
correspond to fields on `SpaceTime n`.

Evolution equations are most naturally stated for curried fields
`u : ℝ^n → ℝ → E`, while Mathlib's calculus on `EuclideanSpace` and the
symbolic layer work on the single space `SpaceTime n = ℝ^(n+1)`. The maps here
move between the two views without losing structure:
`spaceTimeContinuousLinearEquiv` and `timeSpaceContinuousLinearEquiv` are
continuous linear equivalences, so differentiability, measurability and
properness transfer along them.

Evans writes spacetime points as `(x, t)` with time last, as in the wave cone `K(x₀, t₀)` of
§2.4.3(b); `spaceTimeContinuousLinearEquiv` maps `SpaceTime n` to `ℝ^n × ℝ` in that order.

## Main definitions

* `splitSpaceTime`, `joinSpaceTime`: the plain functions
  `xt ↦ (spatialPart xt, time xt)` and `(x, t) ↦ timeSpaceCons t x`, inverse
  to each other (`split_joinSpaceTime`, `join_splitSpaceTime`).
* `spaceTimeContinuousLinearEquiv`, `timeSpaceContinuousLinearEquiv`: the same
  maps bundled as continuous linear equivalences, in both product orders.
* `isProperMap_timeSpaceCons`: the fixed-time slice `x ↦ (t, x)` is proper.
* `spaceTimeUncurry`, `spaceTimeCurry`: the two views of a field, with the
  round-trip lemmas `spaceTimeCurry_uncurry` and `spaceTimeUncurry_curry`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3(b), p. 83.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Common

/-- Split canonical Euclidean spacetime into spatial coordinates followed by time. -/
def splitSpaceTime {n : ℕ} (xt : SpaceTime n) : ℝ^n × ℝ :=
  (spatialPart xt, time xt)

/-- Assemble an `(x, t)` pair into canonical Euclidean spacetime. -/
def joinSpaceTime {n : ℕ} (p : ℝ^n × ℝ) : SpaceTime n :=
  timeSpaceCons p.2 p.1

/-- The first component of the split is the spatial part. -/
@[simp]
theorem splitSpaceTime_fst {n : ℕ} (xt : SpaceTime n) :
    (splitSpaceTime xt).1 = spatialPart xt :=
  rfl

/-- The second component of the split is the time coordinate. -/
@[simp]
theorem splitSpaceTime_snd {n : ℕ} (xt : SpaceTime n) :
    (splitSpaceTime xt).2 = time xt :=
  rfl

/-- Coordinate `0` of the assembled spacetime point is the time entry `p.2`. -/
@[simp]
theorem joinSpaceTime_apply_zero {n : ℕ} (p : ℝ^n × ℝ) :
    joinSpaceTime p (0 : Fin (n + 1)) = p.2 := by
  simp [joinSpaceTime]

/-- The spatial coordinates of the assembled spacetime point are those of `p.1`. -/
@[simp]
theorem joinSpaceTime_apply_succ {n : ℕ} (p : ℝ^n × ℝ) (i : Fin n) :
    joinSpaceTime p i.succ = p.1 i := by
  simp [joinSpaceTime]

/-- Splitting after joining is the identity on `ℝ^n × ℝ`. -/
@[simp]
theorem split_joinSpaceTime {n : ℕ} (p : ℝ^n × ℝ) :
    splitSpaceTime (joinSpaceTime p) = p := by
  ext <;> simp [splitSpaceTime, joinSpaceTime, time]

/-- Joining after splitting is the identity on `SpaceTime n`. -/
@[simp]
theorem join_splitSpaceTime {n : ℕ} (xt : SpaceTime n) :
    joinSpaceTime (splitSpaceTime xt) = xt := by
  simp [splitSpaceTime, joinSpaceTime, time]

/-- Canonical spacetime as a continuous linear copy of `space × time`. -/
def spaceTimeContinuousLinearEquiv (n : ℕ) :
    SpaceTime n ≃L[ℝ] ℝ^n × ℝ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)).trans
    ((Fin.consEquivL ℝ (fun _ : Fin (n + 1) ↦ ℝ)).symm.trans
      (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm).trans
          (ContinuousLinearEquiv.prodComm ℝ ℝ (ℝ^n))))

/-- The forward direction of the `space × time` equivalence is `splitSpaceTime`. -/
@[simp]
theorem spaceTimeContinuousLinearEquiv_apply (n : ℕ) (xt : SpaceTime n) :
    spaceTimeContinuousLinearEquiv n xt = splitSpaceTime xt :=
  rfl

/-- The inverse direction of the `space × time` equivalence is `joinSpaceTime`. -/
@[simp]
theorem spaceTimeContinuousLinearEquiv_symm_apply (n : ℕ) (p : ℝ^n × ℝ) :
    (spaceTimeContinuousLinearEquiv n).symm p = joinSpaceTime p :=
  rfl

/-- Canonical spacetime as a continuous linear copy of `time × space`. -/
def timeSpaceContinuousLinearEquiv (n : ℕ) :
    SpaceTime n ≃L[ℝ] ℝ × ℝ^n :=
  (spaceTimeContinuousLinearEquiv n).trans
    (ContinuousLinearEquiv.prodComm ℝ (ℝ^n) ℝ)

/-- The forward direction of the `time × space` equivalence is
`xt ↦ (time xt, spatialPart xt)`. -/
@[simp]
theorem timeSpaceContinuousLinearEquiv_apply (n : ℕ) (xt : SpaceTime n) :
    timeSpaceContinuousLinearEquiv n xt = (time xt, spatialPart xt) :=
  rfl

/-- The inverse direction of the `time × space` equivalence is `(t, x) ↦ timeSpaceCons t x`. -/
@[simp]
theorem timeSpaceContinuousLinearEquiv_symm_apply (n : ℕ) (p : ℝ × ℝ^n) :
    (timeSpaceContinuousLinearEquiv n).symm p = timeSpaceCons p.1 p.2 :=
  rfl

/-- The fixed-time embedding `x ↦ (t, x)` into canonical Euclidean spacetime is proper. -/
theorem isProperMap_timeSpaceCons (n : ℕ) (t : ℝ) :
    IsProperMap (timeSpaceCons (n := n) t) := by
  have hprod : IsProperMap (Prod.mk t : ℝ^n → ℝ × ℝ^n) := by
    refine Topology.IsClosedEmbedding.isProperMap
      ⟨isEmbedding_prodMkRight t, ?_⟩
    have hrange :
        Set.range (Prod.mk t : ℝ^n → ℝ × ℝ^n) =
          ({t} ×ˢ Set.univ) := by
      simp [Set.singleton_prod]
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  have hcomp :=
    (timeSpaceContinuousLinearEquiv n).symm.toHomeomorph.isProperMap.comp hprod
  have hfun :
      ((timeSpaceContinuousLinearEquiv n).symm.toHomeomorph ∘
        (Prod.mk t : ℝ^n → ℝ × ℝ^n)) =
        timeSpaceCons (n := n) t := by
    funext x
    rfl
  rw [hfun] at hcomp
  exact hcomp

/-- View a curried field `u x t` as a field on canonical Euclidean spacetime. -/
def spaceTimeUncurry {n : ℕ} {E : Type*} (u : ℝ^n → ℝ → E) :
    SpaceTime n → E :=
  fun xt ↦ u (spatialPart xt) (time xt)

/-- View a field on canonical Euclidean spacetime as a curried field `u x t`. -/
def spaceTimeCurry {n : ℕ} {E : Type*} (u : SpaceTime n → E) :
    ℝ^n → ℝ → E :=
  fun x t ↦ u (timeSpaceCons t x)

/-- Currying after uncurrying recovers the curried field. -/
@[simp]
theorem spaceTimeCurry_uncurry {n : ℕ} {E : Type*} (u : ℝ^n → ℝ → E) :
    spaceTimeCurry (spaceTimeUncurry u) = u := by
  funext x t
  simp [spaceTimeCurry, spaceTimeUncurry, time]

/-- Uncurrying after currying recovers the spacetime field. -/
@[simp]
theorem spaceTimeUncurry_curry {n : ℕ} {E : Type*} (u : SpaceTime n → E) :
    spaceTimeUncurry (spaceTimeCurry u) = u := by
  funext xt
  simp [spaceTimeCurry, spaceTimeUncurry, time]

end PDE.Common
