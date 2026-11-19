/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Gelfand triples

A Gelfand triple `V ↪ H ↪ V*` consists of a real inner-product (energy) space `V` and a
continuous injective linear map `ι : V → H` with dense range into a real inner-product (pivot)
space `H`. The pivot inner product embeds `H` into the strong dual `V*` by
`h ↦ (v ↦ ⟪h, ι v⟫_H)`, and composing with `ι` embeds `V` into `V*`. Both embeddings are
injective, the first because `ι` has dense range.

This is the setting of the variational theory of evolution equations: the time derivative of a
trajectory `u : [0, T] → V` is taken in `V*`, and on `H` the `V*`-`V` pairing is the pivot inner
product. The embedding data assume no completeness.

## Main definitions

* `GelfandTriple`: a continuous injective inclusion `V →L[ℝ] H` with dense
  range, and `GelfandTriple.identity` for `V = H`.
* `GelfandTriple.pivotToDual`, `GelfandTriple.energyToDual`: the canonical
  injections `H ↪ V*` and `V ↪ V*`, with `pivotToDual_injective` (from
  density of `V` in `H`) and `energyToDual_injective`.

## References

* J.-L. Lions and E. Magenes, *Non-Homogeneous Boundary Value Problems and Applications*,
  Vol. I, Springer, 1972, Chapter 3 (variational evolution equations).
  <https://doi.org/10.1007/978-3-642-65161-8>
* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 3, where `V = H¹₀`, `H = L²` and
  `V* = H⁻¹`. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## Embedding data -/

/-- A real Gelfand triple `V ↪ H ↪ V*`: a continuous injective linear map `V → H` with dense
range. Neither space is assumed complete. -/
structure GelfandTriple where
  /-- Continuous inclusion `V ↪ H`. -/
  inclusion : V →L[ℝ] H
  /-- The inclusion does not identify distinct energy-space vectors. -/
  injective : Function.Injective inclusion
  /-- The energy space is dense in the pivot space. -/
  denseRange : DenseRange inclusion

namespace GelfandTriple

/--
The trivial Gelfand triple `X ↪ X ↪ X*` given by the identity of a real inner-product space.

With this triple, theorems about Gelfand evolutions specialise to evolutions whose energy and
pivot spaces coincide, such as Hilbert-valued Sobolev trajectories.
-/
def identity
    (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] :
    GelfandTriple (V := X) (H := X) where
  inclusion := ContinuousLinearMap.id ℝ X
  injective := Function.injective_id
  denseRange := by
    simpa only [ContinuousLinearMap.coe_id'] using
      (denseRange_id : DenseRange (id : X → X))

/-- The identity Gelfand inclusion acts as the identity function. -/
@[simp]
theorem identity_inclusion_apply
    (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (x : X) :
    (identity X).inclusion x = x :=
  rfl

/-! ## Canonical dual embeddings -/

/-- The canonical injection `H ↪ V*`: a pivot vector acts on an energy-space
test function by the pivot inner product. -/
def pivotToDual (T : GelfandTriple (V := V) (H := H)) :
    H →L[ℝ] StrongDual ℝ V :=
  ContinuousLinearMap.toSesqForm T.inclusion

/-- The pivot-to-dual embedding evaluates by the pivot inner product. -/
@[simp]
theorem pivotToDual_apply (T : GelfandTriple (V := V) (H := H))
    (h : H) (v : V) :
    T.pivotToDual h v = inner ℝ h (T.inclusion v) :=
  rfl

/-- The pivot embedding is bounded by the norm of `V ↪ H`. -/
theorem norm_pivotToDual_le (T : GelfandTriple (V := V) (H := H)) (h : H) :
    ‖T.pivotToDual h‖ ≤ ‖T.inclusion‖ * ‖h‖ :=
  ContinuousLinearMap.toSesqForm_apply_norm_le

/-- Density of `V ↪ H` makes the canonical map `H → V*` injective. -/
theorem pivotToDual_injective (T : GelfandTriple (V := V) (H := H)) :
    Function.Injective T.pivotToDual := by
  intro x y hxy
  apply ext_inner_right ℝ
  intro z
  have heq : (fun z : H ↦ inner ℝ x z) = fun z : H ↦ inner ℝ y z :=
    T.denseRange.equalizer (innerSL ℝ x).continuous (innerSL ℝ y).continuous (by
      funext v
      exact DFunLike.congr_fun hxy v)
  exact congrFun heq z

/-- The canonical injection `V ↪ V*` obtained through the pivot space. -/
def energyToDual (T : GelfandTriple (V := V) (H := H)) :
    V →L[ℝ] StrongDual ℝ V :=
  T.pivotToDual.comp T.inclusion

/-- The energy-to-dual embedding pairs two energy vectors through the pivot space. -/
@[simp]
theorem energyToDual_apply (T : GelfandTriple (V := V) (H := H))
    (u v : V) :
    T.energyToDual u v = inner ℝ (T.inclusion u) (T.inclusion v) :=
  rfl

/-- The canonical energy-to-dual map is injective. -/
theorem energyToDual_injective (T : GelfandTriple (V := V) (H := H)) :
    Function.Injective T.energyToDual :=
  T.pivotToDual_injective.comp T.injective

end GelfandTriple

end PDE.Analysis.Evolution
