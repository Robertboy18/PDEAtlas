/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.Coordinates
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.OddHalfSpaceExtension
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TangentialDerivative

/-!
# Second-Order Odd Reflection

For `u ∈ H¹₀(ℝ^n₊)` the odd reflection `ũ(x', xₙ) = -u(x', -xₙ)` lies in `H¹(ℝ^n)`: the zero
trace is exactly what prevents a jump across `{xₙ = 0}` (Brezis, *Functional Analysis, Sobolev
Spaces and PDE*, Chapter 9, reflection across a flat boundary; the zero-trace case is developed
in `Boundary.ZeroTrace.OddHalfSpaceExtension`). We push that one order further. Given
`U ∈ H²(ℝ^n₊)` whose base `H¹` slice has zero trace, the coordinatewise odd reflection of `U`
(odd for words with an even number of normal derivatives, even otherwise, see
`HigherOrder.Coordinates`) is an element of `H²(ℝ^n)`. No trace condition is needed on the
first derivatives: the tangential derivatives of `u` inherit the zero trace, and the normal
derivative is reflected evenly, which requires none.

The second-order rows are obtained from the first-order ones by one more application of the
first-order reflection lemmas: tangential-tangential words use the odd tangential result,
normal-normal words differentiate the even reflected normal derivative, and mixed words
differentiate normally first and then commute the derivative word.

## Main results

* `oddReflectListCoordinate_hasWeakDerivative_orderTwo_of_firstOrder`,
  `oddReflectAmbient_mem_globalH2_of_firstOrder`: once the first-order rows of the reflection
  are known to be weak derivatives on `ℝ^n`, all second-order rows follow.
* `oddReflectAmbient_mem_globalH2_of_contDiffOneRepresentative`: the first-order data can be
  supplied by a global `C¹` representative of the reflected base function.
* `oddReflectListCoordinate_hasWeakDerivative_orderOne_of_base_zeroTrace`,
  `oddReflectAmbient_mem_globalH2_of_base_zeroTrace`: the zero trace of the base `H¹` slice
  alone gives global `H²` membership.
* `oddReflectionH2Submodule`, `OddReflectionH2Space`: the closed subspace of `H²(ℝ^n₊)` with
  zero base trace, the natural domain of the operator.
* `oddReflectionH2`: the continuous odd reflection `OddReflectionH2Space n →L[ℝ] H²(ℝ^n)`, with
  `restrict_oddReflectionH2` (left inverse), `oddReflectionH2_injective`, and
  `norm_oddReflectionH2` (the `H²` norm is multiplied by exactly `√2`).

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace HigherOrderReflection

open Set MeasureTheory Function
open SobolevSpace.Extension.GraphSpace.HalfSpace
open scoped ENNReal Topology Sobolev

variable (n : ℕ) [Fact (0 < n)]

/-- Once the first-order odd reflection is known globally, all order-two
rows follow without further trace data.  This is the reusable weak gluing
form needed when first-order regularity is supplied by a classical `C¹`
representative rather than by `H¹₀` closure. -/
theorem oddReflectListCoordinate_hasWeakDerivative_orderTwo_of_firstOrder
    (U : W^{2,2}(ℝ^n₊))
    (hfirst : ∀ i : Fin n,
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) : ℝ^n → ℝ)
        (oddReflectListCoordinate (n := n) (m := 2) U [i] (by simp) : ℝ^n → ℝ))
    (α : List (Fin n)) (hα : α.length ≤ 2) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) α
      (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) : ℝ^n → ℝ)
      (oddReflectListCoordinate (n := n) (m := 2) U α hα : ℝ^n → ℝ) := by
  classical
  cases α with
  | nil =>
      exact hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  | cons i rest =>
      cases rest with
      | nil => simpa using hfirst i
      | cons j tail =>
          obtain rfl : tail = [] :=
            List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hα; omega)
          let ui := coordinateAtList (n := n) (m := 2) U [i] (by simp)
          let uij := coordinateAtList (n := n) (m := 2) U [i, j] (by simp)
          have hlocal : HasWeakDerivativeOn (n := n) ℝ^n₊ [j]
              (ui : ℝ^n → ℝ) (uij : ℝ^n → ℝ) := by
            simpa [ui, uij] using
              coordinateAtList_hasWeakDerivative_append_single
                (n := n) (m := 2) U [i] (by simp) j
          by_cases hi : i = PDE.Common.lastIndex (n := n)
          · subst i
            refine (hfirst _).append_single j ?_
            by_cases hj : j = PDE.Common.lastIndex (n := n)
            · subst j
              simpa [oddReflectListCoordinate, ui, uij] using
                (hasWeakDerivativeOn_univ_evenExtend_of_upper_last
                  (n := n) (p := (2 : ℝ≥0∞)) ui uij hlocal)
            · simpa [oddReflectListCoordinate, ui, uij, hj] using
                (hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last
                  (n := n) (p := (2 : ℝ≥0∞)) j hj ui uij hlocal)
          · by_cases hj : j = PDE.Common.lastIndex (n := n)
            · subst j
              let ul := coordinateAtList (n := n) (m := 2) U
                [PDE.Common.lastIndex (n := n)] (by simp)
              let uli := coordinateAtList (n := n) (m := 2) U
                [PDE.Common.lastIndex (n := n), i] (by simp)
              have hlocal' : HasWeakDerivativeOn (n := n) ℝ^n₊ [i]
                  (ul : ℝ^n → ℝ) (uli : ℝ^n → ℝ) := by
                simpa [ul, uli] using
                  coordinateAtList_hasWeakDerivative_append_single
                    (n := n) (m := 2) U
                    [PDE.Common.lastIndex (n := n)] (by simp) i
              have hstep : HasWeakDerivativeOn (n := n) Set.univ [i]
                  (oddReflectListCoordinate (n := n) (m := 2) U
                    [PDE.Common.lastIndex (n := n)] (by simp) : ℝ^n → ℝ)
                  (oddReflectListCoordinate (n := n) (m := 2) U
                    [PDE.Common.lastIndex (n := n), i] (by simp) : ℝ^n → ℝ) := by
                simpa [oddReflectListCoordinate, ul, uli, hi] using
                  (hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last
                    (n := n) (p := (2 : ℝ≥0∞)) i hi ul uli hlocal')
              have hword :=
                (hfirst (PDE.Common.lastIndex (n := n))).append_single i hstep
              have hcoord : oddReflectListCoordinate (n := n) (m := 2) U
                    [PDE.Common.lastIndex (n := n), i] (by simp) =
                  oddReflectListCoordinate (n := n) (m := 2) U
                    [i, PDE.Common.lastIndex (n := n)] (by simp) := by
                unfold oddReflectListCoordinate
                rw [show [PDE.Common.lastIndex (n := n), i].count
                    (PDE.Common.lastIndex (n := n)) = 1 by simp [hi],
                  show [i, PDE.Common.lastIndex (n := n)].count
                    (PDE.Common.lastIndex (n := n)) = 1 by simp [hi]]
                simp only [Nat.not_even_one, ite_false]
                congr 1
                exact coordinateAtList_eq_of_perm (n := n) (m := 2) U
                  (by simp) (by simp) (List.Perm.swap _ _ [])
              exact (hcoord ▸ hword).perm (List.Perm.swap _ _ [])
            · refine (hfirst i).append_single j ?_
              simpa [oddReflectListCoordinate, ui, uij, hi, hj] using
                (hasWeakDerivativeOn_univ_oddExtend_of_upper_ne_last
                  (n := n) (p := (2 : ℝ≥0∞)) j hj ui uij hlocal)



/-- The coordinatewise odd-reflection bundle is global `H²` whenever its
first-order reflected rows have already been proved to be the weak
derivatives of the reflected base row. -/
theorem oddReflectAmbient_mem_globalH2_of_firstOrder
    (U : W^{2,2}(ℝ^n₊))
    (hfirst : ∀ i : Fin n,
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) :
          ℝ^n → ℝ)
        (oddReflectListCoordinate (n := n) (m := 2) U [i] (by simp) :
          ℝ^n → ℝ)) :
    oddReflectAmbient (n := n) (m := 2)
        (U : WkpAmbientOn n 2 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n 2 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n 2 2 Set.univ)) := by
  classical
  change IsWkpOn (n := n) (k := 2) (p := 2) (Ω := Set.univ)
    (oddReflectAmbient (n := n) (m := 2)
      (U : WkpAmbientOn n 2 2 ℝ^n₊))
  rw [isWkpOn_iff_hasWeakDerivativeOn_list]
  intro α hα
  simpa using oddReflectListCoordinate_hasWeakDerivative_orderTwo_of_firstOrder
    (n := n) U hfirst α hα

/-- A global `C¹` representative of the odd reflection supplies the entire
first-order weak interface data.  Almost-everywhere identification of the
representative and its classical coordinate derivatives with the
parity-selected rows is then enough to promote the reflected bundle to
global `H²`. -/
theorem oddReflectAmbient_mem_globalH2_of_contDiffOneRepresentative
    (U : W^{2,2}(ℝ^n₊)) (g : ℝ^n → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hbase : g =ᵐ[MeasureTheory.volume]
      (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) :
        ℝ^n → ℝ))
    (hcoord : ∀ i : Fin n,
      (fun x ↦ (∂[i] g) x) =ᵐ[MeasureTheory.volume]
        (oddReflectListCoordinate (n := n) (m := 2) U [i] (by simp) :
          ℝ^n → ℝ)) :
    oddReflectAmbient (n := n) (m := 2)
        (U : WkpAmbientOn n 2 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n 2 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n 2 2 Set.univ)) := by
  have hfirst : ∀ i : Fin n,
      HasWeakDerivativeOn (n := n) Set.univ [i]
        (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) :
          ℝ^n → ℝ)
        (oddReflectListCoordinate (n := n) (m := 2) U [i] (by simp) :
          ℝ^n → ℝ) := by
    intro i
    have hclassical : HasWeakDerivativeOn (n := n) Set.univ [i] g
        (fun x ↦ (∂[i] g) x) := by
      simpa [iteratedPartialDeriv] using
        (hasWeakDerivativeOn_iteratedPartialDeriv_finite
          (n := n) (Ω := (Set.univ : Set (ℝ^n))) [i]
          (hg.of_le (by norm_num)))
    exact (hasWeakDerivativeOn_congr_ae (n := n)
      (by simpa [domainMeasure] using hbase.symm)
      (by simpa [domainMeasure] using (hcoord i).symm)).2 hclassical
  exact oddReflectAmbient_mem_globalH2_of_firstOrder (n := n) U hfirst

/-- The zero trace of the base `H¹` slice supplies every first-order weak
derivative row of the global odd reflection. -/
theorem oddReflectListCoordinate_hasWeakDerivative_orderOne_of_base_zeroTrace
    (U : W^{2,2}(ℝ^n₊))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
          (by omega) U ∈
      (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (i : Fin n) :
    HasWeakDerivativeOn (n := n) Set.univ [i]
      (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) : ℝ^n → ℝ)
      (oddReflectListCoordinate (n := n) (m := 2) U [i] (by simp) : ℝ^n → ℝ) := by
  classical
  let baseH10 : H¹₀(ℝ^n₊) :=
    ⟨lowerOrderCLM
        (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
        (by omega) U, htrace0⟩
  have hg := (ZeroTraceOdd.oddExtendH10 (n := n) baseH10).property
    (singleDerivIndex (n := n) i)
  by_cases hi : i = PDE.Common.lastIndex (n := n)
  · subst i
    simpa [baseH10, oddReflectListCoordinate, ZeroTraceOdd.oddExtendH10_apply_coe,
      ZeroTraceOdd.oddExtendAmbient_apply, ZeroTraceOdd.oddExtendLpAt,
      lowerOrderCLM_apply, coordinateAtList, derivIndexOfList_singleton] using hg
  · simpa [baseH10, oddReflectListCoordinate, ZeroTraceOdd.oddExtendH10_apply_coe,
      ZeroTraceOdd.oddExtendAmbient_apply, ZeroTraceOdd.oddExtendLpAt,
      lowerOrderCLM_apply, coordinateAtList, derivIndexOfList_singleton, hi] using hg

/-- At order two, an odd reflection requires only the base zero trace.
Tangential-tangential differentiation uses odd tangential reflection;
normal-normal differentiation proceeds through the even reflected normal
derivative; and the mixed case differentiates normal first and then commutes
the derivative word. -/
theorem oddReflectListCoordinate_hasWeakDerivative_orderTwo_of_base_zeroTrace
    (U : W^{2,2}(ℝ^n₊))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
          (by omega) U ∈
      (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (α : List (Fin n)) (hα : α.length ≤ 2) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) α
      (oddReflectListCoordinate (n := n) (m := 2) U [] (by simp) : ℝ^n → ℝ)
      (oddReflectListCoordinate (n := n) (m := 2) U α hα : ℝ^n → ℝ) := by
  exact oddReflectListCoordinate_hasWeakDerivative_orderTwo_of_firstOrder
    (n := n) U
    (fun i ↦
      oddReflectListCoordinate_hasWeakDerivative_orderOne_of_base_zeroTrace
        (n := n) U htrace0 i)
    α hα

/-- The coordinatewise odd-reflection bundle is a global `H²` element
from only the zero trace of the base `H¹` slice. -/
theorem oddReflectAmbient_mem_globalH2_of_base_zeroTrace
    (U : W^{2,2}(ℝ^n₊))
    (htrace0 :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
          (by omega) U ∈
      (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule) :
    oddReflectAmbient (n := n) (m := 2)
        (U : WkpAmbientOn n 2 2 ℝ^n₊) ∈
      (wkpSubmoduleOn n 2 2 (Set.univ : Set (ℝ^n)) :
        Submodule ℝ (WkpAmbientOn n 2 2 Set.univ)) := by
  apply oddReflectAmbient_mem_globalH2_of_firstOrder (n := n) U
  intro i
  exact oddReflectListCoordinate_hasWeakDerivative_orderOne_of_base_zeroTrace
    (n := n) U htrace0 i

/--
The closed subspace of upper-half-space `H²` data whose base `H¹` slice
belongs to `H¹₀`.  This is the natural source space for second-order odd
reflection.
-/
noncomputable def oddReflectionH2Submodule :
    ClosedSubmodule ℝ (W^{2,2}(ℝ^n₊)) :=
  (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).comap
      (lowerOrderCLM
        (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
        (by omega))

/-- The second-order odd-reflection compatibility submodule is closed in
upper-half-space `H²`. -/
instance instIsClosed_oddReflectionH2Submodule_toSubmodule :
    IsClosed ((oddReflectionH2Submodule n).toSubmodule :
      Set (W^{2,2}(ℝ^n₊))) :=
  (oddReflectionH2Submodule n).isClosed

/-- The type of upper-half-space `H²` data with zero base trace. -/
abbrev OddReflectionH2Space :=
  (oddReflectionH2Submodule n).toSubmodule

/-- Membership in the second-order odd-reflection subspace is exactly zero
trace of the base `H¹` slice. -/
@[simp] theorem mem_oddReflectionH2Submodule_iff
    (U : W^{2,2}(ℝ^n₊)) :
    U ∈ oddReflectionH2Submodule n ↔
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := ℝ^n₊)
          (by omega) U ∈
        (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule := by
  rfl

/--
Continuous odd reflection from upper-half-space `H²` with zero base trace
into global `H²(ℝ^n)`.
-/
noncomputable def oddReflectionH2 :
    OddReflectionH2Space n →L[ℝ] W^{2,2}(ℝ^n) :=
  ContinuousLinearMap.codRestrict
    ((oddReflectAmbient (n := n) (m := 2)).comp
      ((Submodule.subtypeL (wkpSubmoduleOn n 2 2 ℝ^n₊)).comp
        (Submodule.subtypeL (oddReflectionH2Submodule n).toSubmodule)))
    (wkpSubmoduleOn n 2 2 (Set.univ : Set (ℝ^n)))
    (fun U ↦ oddReflectAmbient_mem_globalH2_of_base_zeroTrace
      (n := n) (U : W^{2,2}(ℝ^n₊))
      ((mem_oddReflectionH2Submodule_iff (n := n) _).1 U.property))

/-- The second-order odd-reflection operator has the coordinatewise ambient
reflection as its underlying Sobolev bundle. -/
@[simp] theorem oddReflectionH2_apply_coe (U : OddReflectionH2Space n) :
    ((oddReflectionH2 (n := n) U : W^{2,2}(ℝ^n)) :
        WkpAmbientOn n 2 2 Set.univ) =
      oddReflectAmbient (n := n) (m := 2)
        ((U : W^{2,2}(ℝ^n₊)) :
          WkpAmbientOn n 2 2 ℝ^n₊) :=
  rfl

/-- Restricting the second-order odd-reflection operator to the upper
half-space is the original Sobolev field. -/
@[simp] theorem restrict_oddReflectionH2 (U : OddReflectionH2Space n) :
    restrictCLM
        (n := n) (k := 2) (p := 2)
        (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
        (subset_univ ℝ^n₊)
        (oddReflectionH2 (n := n) U) =
      (U : W^{2,2}(ℝ^n₊)) := by
  apply Subtype.ext
  exact restrict_oddReflectAmbient
    (n := n) (m := 2)
    ((U : W^{2,2}(ℝ^n₊)) :
      WkpAmbientOn n 2 2 ℝ^n₊)

/-- The second-order odd-reflection operator is injective. -/
theorem oddReflectionH2_injective :
    Function.Injective (oddReflectionH2 (n := n)) := by
  intro U V hUV
  apply Subtype.ext
  have hrestrict := congrArg
    (restrictCLM
      (n := n) (k := 2) (p := 2)
      (_root_.SobolevSpace.HalfSpace.measurableSet_upper (n := n))
      (subset_univ ℝ^n₊))
    hUV
  simpa using hrestrict

/-- Second-order odd reflection multiplies the squared `H²` norm by exactly
two. -/
theorem norm_oddReflectionH2_sq (U : OddReflectionH2Space n) :
    ‖oddReflectionH2 (n := n) U‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  change ‖oddReflectAmbient (n := n) (m := 2)
      ((U : W^{2,2}(ℝ^n₊)) :
        WkpAmbientOn n 2 2 ℝ^n₊)‖ ^ 2 =
    2 * ‖((U : W^{2,2}(ℝ^n₊)) :
      WkpAmbientOn n 2 2 ℝ^n₊)‖ ^ 2
  exact norm_oddReflectAmbient_sq
    (n := n) (m := 2)
    ((U : W^{2,2}(ℝ^n₊)) :
      WkpAmbientOn n 2 2 ℝ^n₊)

/-- Second-order odd reflection multiplies the `H²` norm by `√2`. -/
theorem norm_oddReflectionH2 (U : OddReflectionH2Space n) :
    ‖oddReflectionH2 (n := n) U‖ =
      Real.sqrt 2 * ‖U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_oddReflectionH2_sq, mul_pow, Real.sq_sqrt (by norm_num)]
  rfl

end HigherOrderReflection
end GraphSpace
end SobolevSpace
