/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import PDE.Analysis.WeakCompactness

/-!
# Continuous trilinear forms

A continuous trilinear form models the nonlinear term of an evolution equation. The basic
example is the Navier–Stokes convection form `b(u, v, w) = ∫ (u · ∇) v · w`, which satisfies
`b(u, v, v) = 0` for divergence-free `u`. Testing the equation against `u` then removes the
nonlinear term from the energy identity `½ d/dt ‖u‖² + ν ‖∇u‖² = ⟨f, u⟩`, which is why weak
solutions satisfy the energy inequality.

Here that identity is the hypothesis `IsSkewInLastTwo`, and its consequences are proved for
any form with this property. Testing two solutions against `u - v` gives the difference
identity `B(u,u,u-v) - B(v,v,u-v) = B(u-v, v, u-v)` and the bound `C ‖u-v‖² ‖v‖` used in
uniqueness arguments. The limit theorems at the end pass to the limit when the first
arguments converge strongly and the last one converges weakly and boundedly, as in a
Galerkin argument.

## Main results

* `ContinuousTrilinearForm E F G`: the type `E →L[ℝ] F →L[ℝ] G →L[ℝ] ℝ`, with
  `restrict` and `restrictToSubmodules` for pulling back along embeddings.
* `IsBoundedBy B C`: the bound `|B u v w| ≤ C ‖u‖ ‖v‖ ‖w‖`, preserved under
  restriction, and `IsBoundedBy.norm_quadratic_dual_sub_le`: the quadratic
  map `u ↦ B u u` is Lipschitz into the dual on bounded sets.
* `IsSkewInLastTwo`, `IsSkewInLastTwoOn`: `B u v w = - B u w v`, globally or
  for `u` in a submodule; `IsSkewInLastTwo.energy_eq_zero` and
  `IsSkewInLastTwo.reduce_energy_equation` give the energy cancellation.
* `IsSkewInLastTwo.quadratic_difference`,
  `IsSkewInLastTwo.norm_quadratic_difference_le`: the difference identity used
  for uniqueness and continuous dependence.
* `tendsto_trilinear_apply_of_tendsto_strong_strong_weak`,
  `tendsto_quadratic_apply_of_tendsto_strong_weak`: passage to the limit with
  strong convergence in the first arguments and bounded weak convergence in
  the last.

## References

* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter II. <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

open Filter

namespace PDE.Analysis

/-- A real-valued continuous trilinear form, represented as nested continuous
linear maps. -/
abbrev ContinuousTrilinearForm
    (E F G : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] :=
  E →L[ℝ] F →L[ℝ] G →L[ℝ] ℝ

namespace ContinuousTrilinearForm

variable {E F G V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Restrict the three arguments of a continuous trilinear form along
continuous linear maps. -/
noncomputable def restrict
    {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (B : ContinuousTrilinearForm E F G)
    (iE : E' →L[ℝ] E) (iF : F' →L[ℝ] F) (iG : G' →L[ℝ] G) :
    ContinuousTrilinearForm E' F' G' :=
  let B12 := B.bilinearComp iE iF
  let post : (G →L[ℝ] ℝ) →L[ℝ] G' →L[ℝ] ℝ :=
    (ContinuousLinearMap.compL ℝ G' G ℝ).flip iG
  (ContinuousLinearMap.compL ℝ F' (G →L[ℝ] ℝ)
    (G' →L[ℝ] ℝ) post).comp B12

/-- Restriction evaluates the ambient form on the images of its arguments. -/
@[simp]
theorem restrict_apply
    {E' F' G' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [NormedAddCommGroup G'] [NormedSpace ℝ G']
    (B : ContinuousTrilinearForm E F G)
    (iE : E' →L[ℝ] E) (iF : F' →L[ℝ] F) (iG : G' →L[ℝ] G)
    (u : E') (v : F') (w : G') :
    restrict B iE iF iG u v w = B (iE u) (iF v) (iG w) :=
  rfl

/-- Restrict a continuous trilinear form to three linear subspaces. -/
noncomputable def restrictToSubmodules
    (B : ContinuousTrilinearForm E F G)
    (S : Submodule ℝ E) (T : Submodule ℝ F) (U : Submodule ℝ G) :
    ContinuousTrilinearForm S T U :=
  restrict B S.subtypeL T.subtypeL U.subtypeL

/-- Submodule restriction evaluates the ambient form on the underlying
vectors. -/
@[simp]
theorem restrictToSubmodules_apply
    (B : ContinuousTrilinearForm E F G)
    (S : Submodule ℝ E) (T : Submodule ℝ F) (U : Submodule ℝ G)
    (u : S) (v : T) (w : U) :
    restrictToSubmodules B S T U u v w =
      B (u : E) (v : F) (w : G) :=
  rfl

/-- The operator-norm bound in the last argument of a continuous trilinear
form. -/
theorem norm_apply_le_last (B : ContinuousTrilinearForm E F G)
    (u : E) (v : F) (w : G) :
    ‖B u v w‖ ≤ ‖B u v‖ * ‖w‖ :=
  ContinuousLinearMap.le_opNorm _ _

/-- The iterated operator-norm bound in the last two arguments of a
continuous trilinear form. -/
theorem norm_apply_le_last_two (B : ContinuousTrilinearForm E F G)
    (u : E) (v : F) (w : G) :
    ‖B u v w‖ ≤ ‖B u‖ * ‖v‖ * ‖w‖ := by
  calc
    ‖B u v w‖ ≤ ‖B u v‖ * ‖w‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B u‖ * ‖v‖) * ‖w‖ := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _

/-- A specified global product bound for a continuous trilinear form. -/
def IsBoundedBy (B : ContinuousTrilinearForm E F G) (C : ℝ) : Prop :=
  ∀ u v w, ‖B u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖

/-- A product bound is preserved when all three arguments are restricted to
submodules. -/
theorem IsBoundedBy.restrictToSubmodules
    {B : ContinuousTrilinearForm E F G} {C : ℝ}
    (hB : B.IsBoundedBy C)
    (S : Submodule ℝ E) (T : Submodule ℝ F) (U : Submodule ℝ G) :
    (B.restrictToSubmodules S T U).IsBoundedBy C := by
  intro u v w
  simpa using hB (u : E) (v : F) (w : G)

/-- The bound `‖B u v w‖ ≤ C ‖u‖ ‖v‖ ‖w‖` at given arguments. -/
theorem IsBoundedBy.norm_apply_le
    {B : ContinuousTrilinearForm E F G} {C : ℝ}
    (hB : B.IsBoundedBy C) (u : E) (v : F) (w : G) :
    ‖B u v w‖ ≤ C * ‖u‖ * ‖v‖ * ‖w‖ :=
  hB u v w

/--
For a form bounded by `C ≥ 0`, the dual-valued quadratic map `u ↦ B u u` satisfies
`‖B u u - B v v‖ ≤ C (‖u‖ + ‖v‖) ‖u - v‖`, so it is Lipschitz on bounded sets.
-/
theorem IsBoundedBy.norm_quadratic_dual_sub_le
    {B : ContinuousTrilinearForm E E G} {C : ℝ}
    (hB : B.IsBoundedBy C) (hC : 0 ≤ C) (u v : E) :
    ‖B u u - B v v‖ ≤
      C * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · positivity
  intro w
  have hsplit :
      (B u u - B v v) w =
        B (u - v) u w + B v (u - v) w := by
    simp only [sub_apply, map_sub]
    ring
  rw [hsplit]
  calc
    ‖B (u - v) u w + B v (u - v) w‖ ≤
        ‖B (u - v) u w‖ + ‖B v (u - v) w‖ :=
      norm_add_le _ _
    _ ≤ C * ‖u - v‖ * ‖u‖ * ‖w‖ +
        C * ‖v‖ * ‖u - v‖ * ‖w‖ :=
      add_le_add
        (hB.norm_apply_le (u - v) u w)
        (hB.norm_apply_le v (u - v) w)
    _ = (C * (‖u‖ + ‖v‖) * ‖u - v‖) * ‖w‖ := by ring

/-- Skew-symmetry in the last two arguments of a trilinear form. -/
def IsSkewInLastTwo (B : ContinuousTrilinearForm E V V) : Prop :=
  ∀ u v w, B u v w = -B u w v

/-- Skew-symmetry in the last two arguments when the first argument belongs
to a specified submodule. -/
def IsSkewInLastTwoOn
    (B : ContinuousTrilinearForm E V V) (S : Submodule ℝ E) : Prop :=
  ∀ u : E, u ∈ S → ∀ v w : V, B u v w = -B u w v

/-- Restriction turns skew-symmetry on the first-argument submodule into
global skew-symmetry of the restricted form. -/
theorem IsSkewInLastTwoOn.restrictToSubmodules
    {B : ContinuousTrilinearForm E V V} {S : Submodule ℝ E}
    (hB : B.IsSkewInLastTwoOn S) (T : Submodule ℝ V) :
    (B.restrictToSubmodules S T T).IsSkewInLastTwo := by
  intro u v w
  exact hB (u : E) u.property (v : V) (w : V)

/-- A form skew in its last two arguments vanishes when those arguments
coincide. -/
theorem IsSkewInLastTwo.diagonal_eq_zero
    {B : ContinuousTrilinearForm E V V}
    (hB : B.IsSkewInLastTwo) (u : E) (v : V) :
    B u v v = 0 := by
  have h := hB u v v
  linarith

/-- Skew-symmetry gives the cubic energy cancellation `B(u,u,u)=0`. -/
theorem IsSkewInLastTwo.energy_eq_zero
    {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwo) (u : V) :
    B u u u = 0 :=
  hB.diagonal_eq_zero u u

/-- The nonlinear term drops out when an evolution equation is tested against
its state and the trilinear form is skew in its last two arguments. -/
theorem IsSkewInLastTwo.reduce_energy_equation
    {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwo)
    (M A : V →L[ℝ] V →L[ℝ] ℝ)
    (ell : StrongDual ℝ V) (du u : V)
    (hEquation :
      M du u + A u u + B u u u = ell u) :
    M du u + A u u = ell u := by
  rw [hB.energy_eq_zero] at hEquation
  simpa using hEquation

/-- For a form skew in its last two arguments,
`B(u,u,u-v) - B(v,v,u-v) = B(u-v, v, u-v)`. -/
theorem IsSkewInLastTwo.quadratic_difference
    {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwo) (u v : V) :
    B u u (u - v) - B v v (u - v) =
      B (u - v) v (u - v) := by
  let d := u - v
  have hu : u = v + d := by
    simp [d]
  rw [show u - v = d from rfl, hu]
  simp only [map_add, add_apply]
  rw [hB.diagonal_eq_zero v d, hB.diagonal_eq_zero d d]
  ring

/-- For a skew form bounded by `C`,
`‖B(u,u,u-v) - B(v,v,u-v)‖ ≤ C ‖u-v‖ ‖v‖ ‖u-v‖`. -/
theorem IsSkewInLastTwo.norm_quadratic_difference_le
    {B : ContinuousTrilinearForm V V V}
    (hB : B.IsSkewInLastTwo) {C : ℝ}
    (hBound : B.IsBoundedBy C) (u v : V) :
    ‖B u u (u - v) - B v v (u - v)‖ ≤
      C * ‖u - v‖ * ‖v‖ * ‖u - v‖ := by
  rw [hB.quadratic_difference]
  exact hBound.norm_apply_le (u - v) v (u - v)

end ContinuousTrilinearForm

section WeakLimits

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Strong convergence in the first two arguments and bounded weak
convergence in the third pass through a continuous trilinear form. -/
theorem tendsto_trilinear_apply_of_tendsto_strong_strong_weak
    (B : ContinuousTrilinearForm E F G)
    {ι : Type*} {l : Filter ι}
    {u : ι → E} {uLimit : E}
    (hu : Tendsto u l (nhds uLimit))
    {v : ι → F} {vLimit : F}
    (hv : Tendsto v l (nhds vLimit))
    {w : ι → G} {wLimit : G}
    (hw : Tendsto (fun i ↦ toWeakSpace ℝ G (w i)) l
      (nhds (toWeakSpace ℝ G wLimit)))
    (R : ℝ) (hwR : ∀ i, ‖w i‖ ≤ R) :
    Tendsto (fun i ↦ B (u i) (v i) (w i)) l
      (nhds (B uLimit vLimit wLimit)) := by
  have hB :
      Tendsto (fun i ↦ B (u i) (v i)) l
        (nhds (B uLimit vLimit)) := by
    change Tendsto
      ((Function.uncurry fun x y ↦ B x y) ∘
        fun i ↦ (u i, v i)) l
      (nhds (B uLimit vLimit))
    exact B.continuous₂.continuousAt.tendsto.comp
      (hu.prodMk_nhds hv)
  exact WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak hB hw R hwR

/-- Strong convergence of a state and bounded weak convergence of a test
family pass through the associated quadratic trilinear expression. -/
theorem tendsto_quadratic_apply_of_tendsto_strong_weak
    (B : ContinuousTrilinearForm E E G)
    {ι : Type*} {l : Filter ι}
    {u : ι → E} {uLimit : E}
    (hu : Tendsto u l (nhds uLimit))
    {w : ι → G} {wLimit : G}
    (hw : Tendsto (fun i ↦ toWeakSpace ℝ G (w i)) l
      (nhds (toWeakSpace ℝ G wLimit)))
    (R : ℝ) (hwR : ∀ i, ‖w i‖ ≤ R) :
    Tendsto (fun i ↦ B (u i) (u i) (w i)) l
      (nhds (B uLimit uLimit wLimit)) :=
  tendsto_trilinear_apply_of_tendsto_strong_strong_weak
    B hu hu hw R hwR

end WeakLimits

end PDE.Analysis
