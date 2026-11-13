/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CAS.Notation

/-!
# Euclidean space and spacetime coordinates

The spacetime conventions of the library, written with the notation `ℝ^n` for
`EuclideanSpace ℝ (Fin n)` of `CAS.Notation`. Coordinate vectors use Mathlib's
`WithLp.toLp 2` constructor directly. In `SpaceTime n`, coordinate zero is time and the remaining
`n` coordinates are space.

Only Mathlib and the notation are imported, so heat equations, energy methods, Green functions,
coordinate systems, and autodiff code can all build on these definitions.

## Main definitions

* `SpaceTime n`, `time`, `positiveTimeDomain`: spacetime `ℝ^(n+1)` with time in
  coordinate `0`, and the open half-space `{t > 0}`.
* `timeSpaceCons t x`, `spatialPart`: assembling `(t, x)` and projecting back to
  `x`, with the round-trip lemmas `spatialPart_timeSpaceCons` and
  `timeSpaceCons_spatialPart`.
* `timeCLM`, `spatialPartCLM`, `embedWithTimeZeroCLM`: the same maps as
  continuous linear maps, for use in differentiation arguments.
* `initialTimeSlice`: the hyperplane `{t = 0}` of spacetime.
* `fact_pos_of_neZero`: the instance `Fact (0 < n)` for every `n` with `NeZero n`, which
  supplies the positive-dimension hypotheses of this library for numerals and successors.
-/

@[expose] public section

namespace PDE

/-- Euclidean spacetime with coordinate `0` reserved for time and the remaining
`n` coordinates reserved for space. -/
abbrev SpaceTime (n : ℕ) : Type :=
  ℝ^(n + 1)

/-- Extract the time coordinate from Euclidean spacetime.

The symbolic layer uses the same convention, with time in coordinate zero. -/
def time {n : ℕ} (p : SpaceTime n) : ℝ :=
  p 0

/-- Under the spacetime convention, the time projection is coordinate zero. -/
@[simp]
theorem time_apply {n : ℕ} (p : SpaceTime n) : time p = p 0 :=
  rfl

end PDE

namespace PDE

/-- Positive dimension as a `Fact`. Dimension hypotheses in this library are stated as
`Fact (0 < n)`; this instance derives them from `NeZero n`, so numerals such as `2`, `3`, `5` and
successors `n + 1` (in particular `SpaceTime n = ℝ^(n + 1)`) need no local instance. -/
instance fact_pos_of_neZero (n : ℕ) [NeZero n] : Fact (0 < n) :=
  ⟨Nat.pos_of_ne_zero (NeZero.ne n)⟩

end PDE

namespace PDE.Common

noncomputable section

attribute [local instance 2000] WithLp.instAddCommGroup WithLp.instModule

/-- Strictly positive spacetime `(0,∞) × ℝ^n`, with time stored in coordinate zero. -/
def positiveTimeDomain {n : ℕ} : Set (SpaceTime n) :=
  {p | 0 < time p}

/-- Membership in the positive-time domain is strict positivity of coordinate
zero. -/
@[simp]
theorem mem_positiveTimeDomain {n : ℕ} {p : SpaceTime n} :
    p ∈ positiveTimeDomain ↔ 0 < time p :=
  Iff.rfl

/-- The initial-time slice `{t = 0}` of spacetime: the hyperplane where coordinate zero
vanishes, on which initial data of evolution problems are prescribed. -/
def initialTimeSlice {n : ℕ} : Set (SpaceTime n) :=
  {p | time p = 0}

/-- Membership in the initial-time slice is vanishing of coordinate zero. -/
@[simp]
theorem mem_initialTimeSlice {n : ℕ} {p : SpaceTime n} :
    p ∈ initialTimeSlice ↔ time p = 0 :=
  Iff.rfl

/-- The last coordinate index in `Fin n`, available when `n > 0`. -/
def lastIndex {n : ℕ} [Fact (0 < n)] : Fin n :=
  ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt (Fact.out : 0 < n))⟩

/-- Form a spacetime point `(t, x)` with time in coordinate `0` and spatial coordinates shifted
by one. -/
def timeSpaceCons {n : ℕ} (t : ℝ) (x : ℝ^n) : ℝ^(n + 1) :=
  WithLp.toLp 2 (Matrix.vecCons t x)

/-- The zeroth coordinate of the spacetime point formed from `(t, x)` is `t`. -/
@[simp]
theorem timeSpaceCons_zero {n : ℕ} (t : ℝ) (x : ℝ^n) :
    timeSpaceCons t x (0 : Fin (n + 1)) = t := by
  simp [timeSpaceCons]

/-- The spatial coordinates of the spacetime point formed from `(t, x)` are those of `x`,
shifted by one index. -/
@[simp]
theorem timeSpaceCons_succ {n : ℕ} (t : ℝ) (x : ℝ^n) (i : Fin n) :
    timeSpaceCons t x i.succ = x i := by
  simp [timeSpaceCons]

/-- Extract the spatial coordinates from a spacetime point whose coordinate `0` is time.

The continuous linear map `spatialPartCLM` below is extensionally equal to
this function. -/
def spatialPart {n : ℕ} (xt : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 (Matrix.vecTail xt)

/-- The `i`th spatial coordinate is coordinate `i + 1` of the spacetime point. -/
@[simp]
theorem spatialPart_apply {n : ℕ} (xt : ℝ^(n + 1)) (i : Fin n) :
    spatialPart xt i = xt i.succ := by
  simp [spatialPart, Matrix.vecTail]

/-- Extracting the spatial part of a constructed spacetime point recovers
the original spatial point. -/
@[simp]
theorem spatialPart_timeSpaceCons {n : ℕ} (t : ℝ) (x : ℝ^n) :
    spatialPart (timeSpaceCons t x) = x := by
  ext i
  simp

/-- A spacetime point is reconstructed from its time coordinate and spatial
part. -/
@[simp]
theorem timeSpaceCons_spatialPart {n : ℕ} (xt : ℝ^(n + 1)) :
    timeSpaceCons (xt 0) (spatialPart xt) = xt := by
  ext i
  cases i using Fin.cases <;> simp

/-- The time coordinate as a continuous linear map.

It agrees with the plain function `time` by `rfl`, so statements can use
`time` while differentiation arguments use the linear structure. -/
def timeCLM (n : ℕ) :
    SpaceTime n →L[ℝ] ℝ :=
  EuclideanSpace.proj (0 : Fin (n + 1))

/-- The bundled time projection agrees with the plain function `time`. -/
@[simp]
theorem timeCLM_apply (n : ℕ) (xt : SpaceTime n) :
    timeCLM n xt = time xt :=
  rfl

/-- The strictly positive spacetime domain is open. -/
theorem isOpen_positiveTimeDomain {n : ℕ} : IsOpen (positiveTimeDomain (n := n)) := by
  change IsOpen ((timeCLM n) ⁻¹' Set.Ioi 0)
  exact isOpen_Ioi.preimage (timeCLM n).continuous

/-- The spatial projection as a continuous linear map. -/
def spatialPartCLM (n : ℕ) :
    SpaceTime n →L[ℝ] ℝ^n :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin n ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin n ↦ EuclideanSpace.proj i.succ)

/-- Coordinatewise action of the bundled spatial projection. -/
theorem spatialPartCLM_apply (n : ℕ) (i : Fin n) (xt : SpaceTime n) :
    spatialPartCLM n xt i = xt i.succ := by
  simp [spatialPartCLM]

/-- The spatial projection annihilates the time direction. -/
@[simp]
theorem spatialPartCLM_single_zero (n : ℕ) :
    spatialPartCLM n (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) = (0 : ℝ^n) := by
  ext i
  have h : (i.succ : Fin (n + 1)) ≠ 0 := Fin.succ_ne_zero i
  simp [spatialPartCLM_apply, h]

/-- The spatial projection sends the `(i + 1)`st spacetime basis vector to the `i`th spatial
basis vector. -/
@[simp]
theorem spatialPartCLM_single_succ (n : ℕ) (i : Fin n) :
    spatialPartCLM n (EuclideanSpace.single i.succ (1 : ℝ)) =
      (EuclideanSpace.single i (1 : ℝ) : ℝ^n) := by
  ext j
  simp [spatialPartCLM_apply]

/-- The bundled spatial projection agrees with the plain coordinate
function. -/
theorem spatialPartCLM_eq_spatialPart (n : ℕ) (xt : SpaceTime n) :
    spatialPartCLM n xt = spatialPart xt := by
  ext i
  simpa only [spatialPart_apply] using spatialPartCLM_apply n i xt

/-- The bundled spatial projection is a left inverse of spacetime
assembly. -/
@[simp]
theorem spatialPartCLM_timeSpaceCons {n : ℕ} (t : ℝ) (x : ℝ^n) :
    spatialPartCLM n (timeSpaceCons t x) = x := by
  rw [spatialPartCLM_eq_spatialPart, spatialPart_timeSpaceCons]

/-- Time and the bundled spatial projection reconstruct a spacetime
point. -/
@[simp]
theorem timeSpaceCons_spatialPartCLM {n : ℕ} (xt : SpaceTime n) :
    timeSpaceCons (xt 0) (spatialPartCLM n xt) = xt := by
  rw [spatialPartCLM_eq_spatialPart, timeSpaceCons_spatialPart]

/-- Continuous linear embedding `x ↦ (0,x)` into spacetime. -/
def embedWithTimeZeroCLM (n : ℕ) :
    ℝ^n →L[ℝ] ℝ^(n + 1) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.finCons 0
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap)

/-- The embedded point `(0, x)` has time coordinate `0`. -/
@[simp]
theorem embedWithTimeZeroCLM_zero {n : ℕ} (x : ℝ^n) :
    embedWithTimeZeroCLM n x (0 : Fin (n + 1)) = 0 := by
  simp [embedWithTimeZeroCLM]

/-- The embedded point `(0, x)` has spatial coordinates those of `x`. -/
@[simp]
theorem embedWithTimeZeroCLM_succ {n : ℕ} (x : ℝ^n) (i : Fin n) :
    embedWithTimeZeroCLM n x i.succ = x i := by
  simp [embedWithTimeZeroCLM]

end

end PDE.Common
