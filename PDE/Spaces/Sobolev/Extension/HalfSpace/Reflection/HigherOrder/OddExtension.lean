/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Compatibility
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative -- shake: keep
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Coordinates

/-!
# Higher-Order Odd Reflection

Odd reflection changes parity each time a normal derivative is taken.  If
every derivative coordinate with an even number of normal derivatives has
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

/-- Every derivative word of the odd reflection has the parity prescribed by
its number of normal derivatives. -/
theorem oddReflectListCoordinate_hasWeakDerivative
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (α : List (Fin n)) (hα : α.length ≤ m) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) α
      (oddReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m) :
        ℝ^n → ℝ)
      (oddReflectListCoordinate (n := n) (m := m) U α hα : ℝ^n → ℝ) := by
  let D : List (Fin n) → ℝ^n → ℝ := fun β ↦
    if hβ : β.length ≤ m then
      (oddReflectListCoordinate (n := n) (m := m) U β hβ : ℝ^n → ℝ)
    else 0
  have hD0 : LocallyIntegrableOn (D [])
      (Set.univ : Set (ℝ^n)) volume := by
    simpa [D] using memLp_locallyIntegrableOn_domain
      (MeasureTheory.Lp.memLp
        (oddReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m)))
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hstep : ∀ (β : List (Fin n)) (i : Fin n), β.length < m →
      HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
        (D β) (D (β ++ [i])) := by
    intro β i hβ
    have hβLe : β.length ≤ m := Nat.le_of_lt hβ
    have hβiLe : (β ++ [i]).length ≤ m := by
      simpa [List.length_append] using hβ
    simpa [D, hβ, hβLe, hβiLe] using
      oddReflectListCoordinate_step (n := n) (m := m) U htrace β hβ i
  simpa [D, hα] using hasWeakDerivativeOn_of_append_single_chain_order
    (n := n) (Ω := (Set.univ : Set (ℝ^n))) m D hD0 hstep α hα

/-- The coordinatewise odd-reflection bundle satisfies all global weak
derivative identities under the even-normal zero-trace hypotheses. -/
theorem oddReflectAmbient_mem_globalHm
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule) :
    oddReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n m 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n m 2 Set.univ)) := by
  classical
  change IsWkpOn (n := n) (k := m) (p := 2) (Ω := Set.univ)
    (oddReflectAmbient (n := n) (m := m)
      (U : WkpAmbientOn n m 2 ℝ^n₊))
  rw [isWkpOn_iff_hasWeakDerivativeOn_list]
  intro α hα
  simpa using oddReflectListCoordinate_hasWeakDerivative
    (n := n) (m := m) U htrace α hα

/--
Continuous odd reflection from the closed trace-compatible subspace of
upper-half-space `H^m` into global `H^m(ℝ^n)`.
-/
noncomputable def oddReflection :
    OddReflectionSpace n m →L[ℝ] W^{m,2}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((oddReflectAmbient (n := n) (m := m)).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n m 2 ℝ^n₊)).comp
        (Submodule.subtypeL (oddReflectionSubmodule n m).toSubmodule)))
    (wkpSubmoduleOn n m 2 (Set.univ : Set (ℝ^n)))
    (fun U ↦ oddReflectAmbient_mem_globalHm
      (n := n) (m := m) (U : W^{m,2}(ℝ^n₊))
      ((mem_oddReflectionSubmodule_iff (n := n) (m := m) _).1 U.property))

/-- The odd-reflection operator has the coordinatewise ambient reflection as
its underlying Sobolev bundle. -/
@[simp] theorem oddReflection_apply_coe (U : OddReflectionSpace n m) :
    ((oddReflection (n := n) (m := m) U : W^{m,2}(ℝ^n)) :
        WkpAmbientOn n m 2 Set.univ) =
      oddReflectAmbient (n := n) (m := m)
        ((U : W^{m,2}(ℝ^n₊)) :
          WkpAmbientOn n m 2 ℝ^n₊) :=
  rfl

/-- Restricting the odd-reflection operator to the upper half-space is the
original Sobolev field. -/
@[simp] theorem restrict_oddReflection (U : OddReflectionSpace n m) :
    restrictCLM
        (n := n) (k := m) (p := 2)
        (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
        (subset_univ ℝ^n₊)
        (oddReflection (n := n) (m := m) U) =
      (U : W^{m,2}(ℝ^n₊)) := by
  apply Subtype.ext
  exact restrict_oddReflectAmbient
    (n := n) (m := m)
    ((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)

/-- The odd-reflection operator is injective. -/
theorem oddReflection_injective :
    Function.Injective (oddReflection (n := n) (m := m)) := by
  intro U V hUV
  apply Subtype.ext
  have hrestrict := congrArg
    (restrictCLM
      (n := n) (k := m) (p := 2)
      (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
      (subset_univ ℝ^n₊))
    hUV
  simpa using hrestrict

/-- Odd reflection multiplies the squared `H^m` norm by exactly two. -/
theorem norm_oddReflection_sq (U : OddReflectionSpace n m) :
    ‖oddReflection (n := n) (m := m) U‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  change ‖oddReflectAmbient (n := n) (m := m)
      ((U : W^{m,2}(ℝ^n₊)) :
        WkpAmbientOn n m 2 ℝ^n₊)‖ ^ 2 =
    2 * ‖((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)‖ ^ 2
  exact norm_oddReflectAmbient_sq
    (n := n) (m := m)
    ((U : W^{m,2}(ℝ^n₊)) :
      WkpAmbientOn n m 2 ℝ^n₊)

/-- Odd reflection multiplies the `H^m` norm by `√2`. -/
theorem norm_oddReflection (U : OddReflectionSpace n m) :
    ‖oddReflection (n := n) (m := m) U‖ =
      Real.sqrt 2 * ‖U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_oddReflection_sq, mul_pow, Real.sq_sqrt (by norm_num)]
  rfl

end HigherOrderReflection
end GraphSpace
end SobolevSpace
