/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative -- shake: keep
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Compatibility
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Coordinates

/-!
# Higher-Order Even Reflection

Even reflection changes parity each time a normal derivative is taken.  If
every derivative coordinate with an odd number of normal derivatives has
zero trace, the reflected coordinates form the weak derivatives of a global
`H^m(ℝ^n)` field.  The resulting extension agrees with the original base
coordinate on the upper half-space.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace HigherOrderReflection

open Set MeasureTheory Function
open SobolevSpace.Extension.GraphSpace.HalfSpace
open scoped ENNReal Topology

variable (n m : ℕ) [Fact (0 < n)]

/-- Every derivative word of length at most `m` is represented by the expected
parity-reflected coordinate.  The proof composes the first-order steps without
assuming global `H^m` regularity in advance. -/
theorem evenReflectListCoordinate_hasWeakDerivative
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      ¬ Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (α : List (Fin n)) (hα : α.length ≤ m) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) α
      (evenReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m) :
        ℝ^n → ℝ)
      (evenReflectListCoordinate (n := n) (m := m) U α hα : ℝ^n → ℝ) := by
  let D : List (Fin n) → ℝ^n → ℝ := fun β ↦
    if hβ : β.length ≤ m then
      (evenReflectListCoordinate (n := n) (m := m) U β hβ : ℝ^n → ℝ)
    else 0
  have hD0 : LocallyIntegrableOn (D [])
      (Set.univ : Set (ℝ^n)) volume := by
    simpa [D] using memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        (evenReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m)))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hstep : ∀ (β : List (Fin n)) (i : Fin n), β.length < m →
      HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
        (D β) (D (β ++ [i])) := by
    intro β i hβ
    have hβLe : β.length ≤ m := Nat.le_of_lt hβ
    have hβiLe : (β ++ [i]).length ≤ m := by
      simpa [List.length_append] using hβ
    simpa [D, hβ, hβLe, hβiLe] using
      evenReflectListCoordinate_step (n := n) (m := m) U htrace β hβ i
  simpa [D, hα] using hasWeakDerivativeOn_of_append_single_chain_order
    (n := n) (Ω := (Set.univ : Set (ℝ^n))) m D hD0 hstep α hα

/-- The coordinatewise even-reflection bundle satisfies all global weak
derivative identities under exactly the zero-trace hypotheses for odd-normal
source coordinates. -/
theorem evenReflectAmbient_mem_globalHm
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      ¬ Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule) :
    evenReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n m 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n m 2 Set.univ)) := by
  classical
  change IsWkpOn (n := n) (k := m) (p := 2) (Ω := Set.univ)
    (evenReflectAmbient (n := n) (m := m)
      (U : WkpAmbientOn n m 2 ℝ^n₊))
  rw [isWkpOn_iff_hasWeakDerivativeOn_list]
  intro α hα
  simpa using evenReflectListCoordinate_hasWeakDerivative
    (n := n) (m := m) U htrace α hα

/--
Continuous even reflection from the closed trace-compatible subspace of
upper-half-space `H^m` into global `H^m(ℝ^n)`.
-/
noncomputable def evenReflection :
    EvenReflectionSpace n m →L[ℝ] W^{m,2}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((evenReflectAmbient (n := n) (m := m)).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n m 2 ℝ^n₊)).comp
        (Submodule.subtypeL (evenReflectionSubmodule n m).toSubmodule)))
    (wkpSubmoduleOn n m 2 (Set.univ : Set (ℝ^n)))
    (fun U ↦ evenReflectAmbient_mem_globalHm
      (n := n) (m := m) (U : W^{m,2}(ℝ^n₊))
      ((mem_evenReflectionSubmodule_iff (n := n) (m := m) _).1 U.property))

/-- The even-reflection operator has the coordinatewise ambient reflection as
its underlying Sobolev bundle. -/
@[simp] theorem evenReflection_apply_coe (U : EvenReflectionSpace n m) :
    ((evenReflection (n := n) (m := m) U : W^{m,2}(ℝ^n)) :
        WkpAmbientOn n m 2 Set.univ) =
      evenReflectAmbient (n := n) (m := m)
        ((U : W^{m,2}(ℝ^n₊)) :
          WkpAmbientOn n m 2 ℝ^n₊) :=
  rfl

/-- Restricting the even-reflection operator to the upper half-space is the
original Sobolev field. -/
@[simp] theorem restrict_evenReflection (U : EvenReflectionSpace n m) :
    restrictCLM
        (n := n) (k := m) (p := 2)
        (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
        (subset_univ ℝ^n₊)
        (evenReflection (n := n) (m := m) U) =
      (U : W^{m,2}(ℝ^n₊)) := by
  apply Subtype.ext
  exact restrict_evenReflectAmbient
    (n := n) (m := m)
    ((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)

/-- The even-reflection operator is injective. -/
theorem evenReflection_injective :
    Function.Injective (evenReflection (n := n) (m := m)) := by
  intro U V hUV
  apply Subtype.ext
  have hrestrict := congrArg
    (restrictCLM
      (n := n) (k := m) (p := 2)
      (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
      (subset_univ ℝ^n₊))
    hUV
  simpa using hrestrict

/-- Even reflection multiplies the squared `H^m` norm by exactly two. -/
theorem norm_evenReflection_sq (U : EvenReflectionSpace n m) :
    ‖evenReflection (n := n) (m := m) U‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  change ‖evenReflectAmbient (n := n) (m := m)
      ((U : W^{m,2}(ℝ^n₊)) :
        WkpAmbientOn n m 2 ℝ^n₊)‖ ^ 2 =
    2 * ‖((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)‖ ^ 2
  exact norm_evenReflectAmbient_sq
    (n := n) (m := m)
    ((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)

/-- Even reflection multiplies the `H^m` norm by `√2`. -/
theorem norm_evenReflection (U : EvenReflectionSpace n m) :
    ‖evenReflection (n := n) (m := m) U‖ =
      Real.sqrt 2 * ‖U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_evenReflection_sq, mul_pow, Real.sq_sqrt (by norm_num)]
  rfl

end HigherOrderReflection
end GraphSpace
end SobolevSpace
