/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.Lp
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.OddHalfSpaceExtension
import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.NormalDerivative
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.FirstOrder.TangentialDerivative
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Higher-Order Reflection Coordinates

Mixed derivatives are stored by `DerivIndex` as symmetric multisets.  The
reflection sign of a coordinate is determined by the multiplicity of the last
(normal) direction.  For an even reflection, coordinates with even normal
multiplicity extend evenly and coordinates with odd multiplicity extend oddly.

We define the list-indexed parity-reflection coordinates, identify
them with symmetric derivative-bundle coordinates, and prove the one-step
weak-derivative recurrences used by both even and odd reflection.

The parity rule comes from the first-order reflection lemma (Brezis, *Functional Analysis,
Sobolev Spaces and PDE*, Chapter 9): tangential derivatives commute with
reflection, while the normal derivative of an even reflection is odd and vice versa. Iterating,
`∂^α` of the even reflection of `u` is the even or odd reflection of `∂^α u` according to the
parity of the number of normal derivatives in `α`. Unlike the first-order case, however, an odd
reflection is a weak derivative on the whole space only when the reflected coordinate has zero
trace on `{xₙ = 0}`; otherwise a jump appears at the interface. This is why the step lemmas
carry an `H¹₀` hypothesis on the slices that get reflected oddly. The relevant one-step results
for a zero-trace `H¹` slice come from `Boundary.ZeroTrace.OddHalfSpaceExtension`.

## Main results

* `coordinateAtList`, `evenReflectListCoordinate`, `oddReflectListCoordinate`: the `L²`
  coordinate of `U ∈ H^m(ℝ^n₊)` indexed by a derivative word `α`, and its parity-selected
  even/odd reflection to `ℝ^n`.
* `evenReflectLpAt`, `oddReflectLpAt`, `evenReflectAmbient`, `oddReflectAmbient`: the same on
  canonical symmetric indices and on the whole order-`m` bundle, as continuous linear maps.
* `norm_evenReflectAmbient`, `norm_oddReflectAmbient`: both bundle reflections multiply the
  `H^m` norm by exactly `√2`; `restrict_*` and `*_injective`: restriction is a left inverse.
* `coordinateAtList_hasWeakDerivative_append_single`, `coordinateAtList_eq_of_perm`,
  `oddReflectListCoordinate_eq_of_perm`: appending
  a direction to the word takes the weak derivative, and permuted words give the same
  coordinate (commutativity of weak mixed derivatives, via uniqueness).
* `evenReflectListCoordinate_step`, `oddReflectListCoordinate_step`: the one-step
  weak-derivative recurrences on `ℝ^n`, under the zero-trace hypotheses described above.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for extension by reflection across a flat boundary.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace HigherOrderReflection

open Set MeasureTheory Function
open SobolevSpace.Extension.GraphSpace.HalfSpace
open scoped ENNReal Topology Sobolev

variable (n m : ℕ) [Fact (0 < n)]


/-- The `L²` coordinate represented by a concrete derivative word. -/
def coordinateAtList (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length ≤ m) : DerivLp n 2 ℝ^n₊ :=
  (U : WkpAmbientOn n m 2 ℝ^n₊)
    (derivIndexOfList (n := n) (k := m) α hα)

/-- Parity-selected scalar extension for one concrete derivative word of an
evenly reflected base function. -/
noncomputable def evenReflectListCoordinate
    (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length ≤ m) :
    DerivLp n 2 Set.univ :=
  if Even (α.count (PDE.Common.lastIndex (n := n))) then
    _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2)
      (coordinateAtList (n := n) (m := m) U α hα)
  else
    _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2)
      (coordinateAtList (n := n) (m := m) U α hα)

/-- Parity-selected scalar extension for a canonical symmetric derivative
index. -/
noncomputable def evenReflectLpAt (a : DerivIndex n m) :
    DerivLp n 2 ℝ^n₊ →L[ℝ] DerivLp n 2 Set.univ :=
  if Even (a.multiplicity (PDE.Common.lastIndex (n := n))) then
    _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2)
  else
    _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2)

/-- Parity-selected scalar extension for a concrete derivative word of an
oddly reflected base function. -/
noncomputable def oddReflectListCoordinate
    (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length ≤ m) : DerivLp n 2 Set.univ :=
  if Even (α.count (PDE.Common.lastIndex (n := n))) then
    _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2)
      (coordinateAtList (n := n) (m := m) U α hα)
  else
    _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2)
      (coordinateAtList (n := n) (m := m) U α hα)

/-- A concrete source representative transfers to the literal parity-selected
representative of an odd-reflection derivative row. -/
theorem oddReflectListCoordinate_apply_ae_of_ae_eq
    (U : W^{m,2}(ℝ^n₊)) (α : List (Fin n))
    (hα : α.length ≤ m) (f : ℝ^n → ℝ)
    (hf : (coordinateAtList (n := n) (m := m) U α hα : ℝ^n → ℝ)
      =ᵐ[domainMeasure n ℝ^n₊] f) :
    (oddReflectListCoordinate (n := n) (m := m) U α hα : ℝ^n → ℝ)
      =ᵐ[MeasureTheory.volume]
        if Even (α.count (PDE.Common.lastIndex (n := n))) then
          fun x ↦ if x (PDE.Common.lastIndex (n := n)) < 0 then
            -f (_root_.SobolevSpace.HalfSpace.reflect n x) else f x
        else
          fun x ↦ if x (PDE.Common.lastIndex (n := n)) < 0 then
            f (_root_.SobolevSpace.HalfSpace.reflect n x) else f x := by
  by_cases heven : Even
      (α.count (PDE.Common.lastIndex (n := n)))
  · simp only [oddReflectListCoordinate, heven, ite_eq_left]
    exact _root_.SobolevSpace.HalfSpace.oddExtendLp_apply_ae_piecewise_of_ae_eq
      (n := n) (p := (2 : ℝ≥0∞))
      (coordinateAtList (n := n) (m := m) U α hα) f hf
  · simp only [oddReflectListCoordinate, heven]
    exact _root_.SobolevSpace.HalfSpace.evenExtendLp_apply_ae_piecewise_of_ae_eq
      (n := n) (p := (2 : ℝ≥0∞))
      (coordinateAtList (n := n) (m := m) U α hα) f hf

/-- Parity-selected scalar extension for a symmetric derivative coordinate of
an oddly reflected base function. -/
noncomputable def oddReflectLpAt (a : DerivIndex n m) :
    DerivLp n 2 ℝ^n₊ →L[ℝ] DerivLp n 2 Set.univ :=
  if Even (a.multiplicity (PDE.Common.lastIndex (n := n))) then
    _root_.SobolevSpace.HalfSpace.oddExtendLp (n := n) (p := 2)
  else
    _root_.SobolevSpace.HalfSpace.evenExtendLp (n := n) (p := 2)

/-- Coordinatewise even reflection on the order-`m` ambient Sobolev bundle. -/
noncomputable def evenReflectAmbient :
    WkpAmbientOn n m 2 ℝ^n₊ →L[ℝ] WkpAmbientOn n m 2 Set.univ := by
  classical
  let eUpper := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n m ↦ DerivLp n 2 ℝ^n₊)
  let eUniv := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n m ↦ DerivLp n 2 Set.univ)
  exact eUniv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        (evenReflectLpAt (n := n) (m := m) a).comp
          (ContinuousLinearMap.proj a)).comp
      eUpper.toContinuousLinearMap)

/-- Coordinatewise odd reflection on the order-`m` ambient Sobolev bundle. -/
noncomputable def oddReflectAmbient :
    WkpAmbientOn n m 2 ℝ^n₊ →L[ℝ] WkpAmbientOn n m 2 Set.univ := by
  classical
  let eUpper := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n m ↦ DerivLp n 2 ℝ^n₊)
  let eUniv := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun _ : DerivIndex n m ↦ DerivLp n 2 Set.univ)
  exact eUniv.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun a ↦
        (oddReflectLpAt (n := n) (m := m) a).comp
          (ContinuousLinearMap.proj a)).comp
      eUpper.toContinuousLinearMap)

/-- Coordinatewise formula for the even bundle reflection: at the symmetric index `a` it applies
the parity-selected scalar reflection `evenReflectLpAt a`. -/
@[simp] theorem evenReflectAmbient_apply
    (U : WkpAmbientOn n m 2 ℝ^n₊) (a : DerivIndex n m) :
    evenReflectAmbient (n := n) (m := m) U a =
      evenReflectLpAt (n := n) (m := m) a (U a) := by
  classical
  simp [evenReflectAmbient]

/-- Coordinatewise formula for the odd bundle reflection: at the symmetric index `a` it applies
the parity-selected scalar reflection `oddReflectLpAt a`. -/
@[simp] theorem oddReflectAmbient_apply
    (U : WkpAmbientOn n m 2 ℝ^n₊) (a : DerivIndex n m) :
    oddReflectAmbient (n := n) (m := m) U a =
      oddReflectLpAt (n := n) (m := m) a (U a) := by
  classical
  simp [oddReflectAmbient]

/-- Every parity choice used by an even reflection has the same exact
coordinatewise `L²` norm factor. -/
theorem norm_evenReflectLpAt_sq (a : DerivIndex n m) (u : DerivLp n 2 ℝ^n₊) :
    ‖evenReflectLpAt (n := n) (m := m) a u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  by_cases hparity : Even
      (a.multiplicity (PDE.Common.lastIndex (n := n)))
  · simpa [evenReflectLpAt, hparity] using
      (_root_.SobolevSpace.HalfSpace.norm_evenExtendLp_sq (n := n) u)
  · simpa [evenReflectLpAt, hparity] using
      (_root_.SobolevSpace.HalfSpace.norm_oddExtendLp_sq (n := n) u)

/-- Every parity choice used by an odd reflection has the same exact
coordinatewise `L²` norm factor. -/
theorem norm_oddReflectLpAt_sq (a : DerivIndex n m) (u : DerivLp n 2 ℝ^n₊) :
    ‖oddReflectLpAt (n := n) (m := m) a u‖ ^ 2 = 2 * ‖u‖ ^ 2 := by
  by_cases hparity : Even
      (a.multiplicity (PDE.Common.lastIndex (n := n)))
  · simpa [oddReflectLpAt, hparity] using
      (_root_.SobolevSpace.HalfSpace.norm_oddExtendLp_sq (n := n) u)
  · simpa [oddReflectLpAt, hparity] using
      (_root_.SobolevSpace.HalfSpace.norm_evenExtendLp_sq (n := n) u)

/-- Exact intrinsic `H^m` bundle norm of the coordinatewise even reflection.
The identity sums the exact scalar reflection formula over all weak derivative
coordinates of order at most `m`. -/
theorem norm_evenReflectAmbient_sq (U : WkpAmbientOn n m 2 ℝ^n₊) :
    ‖evenReflectAmbient (n := n) (m := m) U‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp_rw [evenReflectAmbient_apply, norm_evenReflectLpAt_sq]
  rw [Finset.mul_sum]

/-- Coordinatewise even reflection multiplies the bundle norm by `√2`. -/
theorem norm_evenReflectAmbient (U : WkpAmbientOn n m 2 ℝ^n₊) :
    ‖evenReflectAmbient (n := n) (m := m) U‖ =
      Real.sqrt 2 * ‖U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_evenReflectAmbient_sq, mul_pow, Real.sq_sqrt (by norm_num)]

/-- Exact intrinsic `H^m` bundle norm of the coordinatewise odd reflection. -/
theorem norm_oddReflectAmbient_sq (U : WkpAmbientOn n m 2 ℝ^n₊) :
    ‖oddReflectAmbient (n := n) (m := m) U‖ ^ 2 = 2 * ‖U‖ ^ 2 := by
  classical
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp_rw [oddReflectAmbient_apply, norm_oddReflectLpAt_sq]
  rw [Finset.mul_sum]

/-- Coordinatewise odd reflection multiplies the bundle norm by `√2`. -/
theorem norm_oddReflectAmbient (U : WkpAmbientOn n m 2 ℝ^n₊) :
    ‖oddReflectAmbient (n := n) (m := m) U‖ =
      Real.sqrt 2 * ‖U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _))).mp
  rw [norm_oddReflectAmbient_sq, mul_pow, Real.sq_sqrt (by norm_num)]

/-- Restricting the coordinatewise even reflection to the upper half-space
recovers the original derivative bundle. -/
@[simp] theorem restrict_evenReflectAmbient (U : WkpAmbientOn n m 2 ℝ^n₊) :
    restrictAmbient
        (n := n) (k := m) (p := 2)
        (subset_univ ℝ^n₊)
        (evenReflectAmbient (n := n) (m := m) U) =
      U := by
  apply PiLp.ext
  intro a
  simp only [restrictAmbient_apply, evenReflectAmbient_apply]
  by_cases hparity : Even
      (a.multiplicity (PDE.Common.lastIndex (n := n)))
  · simp [evenReflectLpAt, hparity]
  · simp [evenReflectLpAt, hparity]

/-- Restricting the coordinatewise odd reflection to the upper half-space
recovers the original derivative bundle. -/
@[simp] theorem restrict_oddReflectAmbient (U : WkpAmbientOn n m 2 ℝ^n₊) :
    restrictAmbient
        (n := n) (k := m) (p := 2)
        (subset_univ ℝ^n₊)
        (oddReflectAmbient (n := n) (m := m) U) =
      U := by
  apply PiLp.ext
  intro a
  simp only [restrictAmbient_apply, oddReflectAmbient_apply]
  by_cases hparity : Even
      (a.multiplicity (PDE.Common.lastIndex (n := n)))
  · simp [oddReflectLpAt, hparity]
  · simp [oddReflectLpAt, hparity]

/-- Coordinatewise even reflection is injective. -/
theorem evenReflectAmbient_injective :
    Function.Injective (evenReflectAmbient (n := n) (m := m)) := by
  intro U V hUV
  have hrestrict := congrArg
    (restrictAmbient
      (n := n) (k := m) (p := 2)
      (subset_univ ℝ^n₊))
    hUV
  simpa using hrestrict

/-- Coordinatewise odd reflection is injective. -/
theorem oddReflectAmbient_injective :
    Function.Injective (oddReflectAmbient (n := n) (m := m)) := by
  intro U V hUV
  have hrestrict := congrArg
    (restrictAmbient
      (n := n) (k := m) (p := 2)
      (subset_univ ℝ^n₊))
    hUV
  simpa using hrestrict

/-- Appending one direction to a derivative word selects the corresponding
weak derivative of its list coordinate. -/
theorem coordinateAtList_hasWeakDerivative_append_single
    (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length < m) (i : Fin n) :
    HasWeakDerivativeOn (n := n) ℝ^n₊ [i]
      (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα) : ℝ^n → ℝ)
      (coordinateAtList (n := n) (m := m) U (α ++ [i]) (by
        simpa [List.length_append] using hα) : ℝ^n → ℝ) := by
  have hs := (derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U).property
    (singleDerivIndex (n := n) i)
  simpa [derivativeSlice_apply_coe, derivativeSliceAmbient_apply,
    derivativeSliceIndex, coordinateAtList] using hs

/-- List coordinates related by a permutation are equal as `L²` elements.
This is commutativity of weak mixed derivatives, obtained from uniqueness. -/
theorem coordinateAtList_eq_of_perm
    (U : W^{m,2}(ℝ^n₊))
    {α β : List (Fin n)} (hα : α.length ≤ m) (hβ : β.length ≤ m)
    (hperm : α.Perm β) :
    coordinateAtList (n := n) (m := m) U α hα =
      coordinateAtList (n := n) (m := m) U β hβ := by
  apply MeasureTheory.Lp.ext
  let aα := derivIndexOfList (n := n) (k := m) α hα
  let aβ := derivIndexOfList (n := n) (k := m) β hβ
  have hweakα : HasWeakDerivativeOn (n := n) ℝ^n₊ α
      (((U : WkpAmbientOn n m 2 ℝ^n₊) (baseIndex n m)) : ℝ^n → ℝ)
      (coordinateAtList (n := n) (m := m) U α hα : ℝ^n → ℝ) :=
    by simpa [coordinateAtList, aα] using
      U.property.hasWeakDerivativeOn_list α hα
  have hweakβ : HasWeakDerivativeOn (n := n) ℝ^n₊ α
      (((U : WkpAmbientOn n m 2 ℝ^n₊) (baseIndex n m)) : ℝ^n → ℝ)
      (coordinateAtList (n := n) (m := m) U β hβ : ℝ^n → ℝ) :=
    (by simpa [coordinateAtList, aβ] using
      (U.property.hasWeakDerivativeOn_list β hβ).perm hperm.symm)
  exact hweakα.unique_ae
    (_root_.SobolevSpace.HalfSpace.isOpen_upper (n := n)) hweakβ

/-- Permuting a derivative word does not change its stored odd-reflection coordinate: both
the multiplicity of the normal index and the weak source coordinate are permutation
invariant. -/
theorem oddReflectListCoordinate_eq_of_perm
    (U : W^{m,2}(ℝ^n₊))
    {α β : List (Fin n)} (hα : α.length ≤ m) (hβ : β.length ≤ m)
    (hperm : α.Perm β) :
    oddReflectListCoordinate (n := n) (m := m) U α hα =
      oddReflectListCoordinate (n := n) (m := m) U β hβ := by
  unfold oddReflectListCoordinate
  have hc : α.count (PDE.Common.lastIndex (n := n)) =
      β.count (PDE.Common.lastIndex (n := n)) :=
    List.Perm.count_eq (a := PDE.Common.lastIndex (n := n)) hperm
  rw [hc]
  split <;> congr 1 <;>
    exact coordinateAtList_eq_of_perm (n := n) (m := m) U hα hβ hperm

/-- The even-reflection ambient bundle agrees with the list coordinate at a
canonicalized derivative word. -/
@[simp high] theorem evenReflectAmbient_apply_derivIndexOfList
    (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length ≤ m) :
    evenReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊)
        (derivIndexOfList (n := n) (k := m) α hα) =
      evenReflectListCoordinate (n := n) (m := m) U α hα := by
  by_cases heven : Even
      (α.count (PDE.Common.lastIndex (n := n)))
  · simp [evenReflectListCoordinate, evenReflectLpAt, coordinateAtList, heven]
  · simp [evenReflectListCoordinate, evenReflectLpAt, coordinateAtList, heven]

/-- The base coordinate of the even-reflection ambient bundle is the reflected
empty derivative word. -/
@[simp high] theorem evenReflectAmbient_apply_baseIndex
    (U : W^{m,2}(ℝ^n₊)) :
    evenReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊) (baseIndex n m) =
      evenReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m) := by
  simpa only [derivIndexOfList_nil] using evenReflectAmbient_apply_derivIndexOfList
    (n := n) (m := m) U [] (Nat.zero_le m)

/-- The odd-reflection ambient bundle agrees with the list coordinate at a
canonicalized derivative word. -/
@[simp high] theorem oddReflectAmbient_apply_derivIndexOfList
    (U : W^{m,2}(ℝ^n₊))
    (α : List (Fin n)) (hα : α.length ≤ m) :
    oddReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊)
        (derivIndexOfList (n := n) (k := m) α hα) =
      oddReflectListCoordinate (n := n) (m := m) U α hα := by
  by_cases heven : Even
      (α.count (PDE.Common.lastIndex (n := n)))
  · simp [oddReflectListCoordinate, oddReflectLpAt, coordinateAtList, heven]
  · simp [oddReflectListCoordinate, oddReflectLpAt, coordinateAtList, heven]

/-- The base coordinate of the odd-reflection ambient bundle is the reflected
empty derivative word. -/
@[simp high] theorem oddReflectAmbient_apply_baseIndex
    (U : W^{m,2}(ℝ^n₊)) :
    oddReflectAmbient (n := n) (m := m)
        (U : WkpAmbientOn n m 2 ℝ^n₊) (baseIndex n m) =
      oddReflectListCoordinate (n := n) (m := m) U [] (Nat.zero_le m) := by
  simpa only [derivIndexOfList_nil] using oddReflectAmbient_apply_derivIndexOfList
    (n := n) (m := m) U [] (Nat.zero_le m)

/-- One weak derivative step for the parity-reflected coordinate family.

When the source coordinate has even normal multiplicity, ordinary even
reflection supplies the step.  When it has odd normal multiplicity, the source
is reflected oddly and its `H¹₀` slice hypothesis is exactly what excludes an
interface delta. -/
theorem evenReflectListCoordinate_step
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      ¬ Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (α : List (Fin n)) (hα : α.length < m) (i : Fin n) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      (evenReflectListCoordinate (n := n) (m := m) U α (Nat.le_of_lt hα) :
        ℝ^n → ℝ)
      (evenReflectListCoordinate (n := n) (m := m) U (α ++ [i]) (by
        simpa [List.length_append] using hα) : ℝ^n → ℝ) := by
  classical
  let hαi : (α ++ [i]).length ≤ m := by
    simpa [List.length_append] using hα
  have hlocal : HasWeakDerivativeOn (n := n) ℝ^n₊ [i]
      (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα) : ℝ^n → ℝ)
      (coordinateAtList (n := n) (m := m) U (α ++ [i]) hαi : ℝ^n → ℝ) :=
    coordinateAtList_hasWeakDerivative_append_single
      (n := n) (m := m) U α hα i
  by_cases heven : Even
      (α.count (PDE.Common.lastIndex (n := n)))
  · by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst i
      simpa [evenReflectListCoordinate, heven, Nat.even_add_one,
        List.count_append, hαi] using
        (Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_evenExtend_of_upper_last
          (n := n) (p := (2 : ℝ≥0∞))
          (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα))
          (coordinateAtList (n := n) (m := m) U
            (α ++ [PDE.Common.lastIndex (n := n)]) hαi) hlocal)
    · simpa [evenReflectListCoordinate, heven, List.count_append, hi, hαi] using
        (Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last
          (n := n) (p := (2 : ℝ≥0∞)) i hi
          (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα))
          (coordinateAtList (n := n) (m := m) U (α ++ [i]) hαi) hlocal)
  · let sliceH10 : H¹₀(ℝ^n₊) :=
      ⟨derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U, htrace α hα heven⟩
    have hglobal :=
      (ZeroTraceOdd.oddExtendH10 (n := n) sliceH10).property
        (singleDerivIndex (n := n) i)
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst i
      simpa [evenReflectListCoordinate, heven, Nat.even_add_one,
        List.count_append, hαi, sliceH10,
        ZeroTraceOdd.oddExtendH10_apply_coe, ZeroTraceOdd.oddExtendAmbient_apply,
        ZeroTraceOdd.oddExtendLpAt, derivativeSlice_apply_coe,
        derivativeSliceAmbient_apply, derivativeSliceIndex, coordinateAtList] using hglobal
    · simpa [evenReflectListCoordinate, heven, List.count_append, hαi, sliceH10,
        ZeroTraceOdd.oddExtendH10_apply_coe, ZeroTraceOdd.oddExtendAmbient_apply,
        ZeroTraceOdd.oddExtendLpAt, derivativeSlice_apply_coe,
        derivativeSliceAmbient_apply, derivativeSliceIndex, coordinateAtList, hi] using hglobal

/-- One weak derivative step for the odd base parity.  Here even-normal source
coordinates are reflected oddly, so exactly those `H¹` slices require zero
trace. -/
theorem oddReflectListCoordinate_step
    (U : W^{m,2}(ℝ^n₊))
    (htrace : ∀ (α : List (Fin n)) (hα : α.length < m),
      Even (α.count (PDE.Common.lastIndex (n := n))) →
        derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U ∈
          (h10SubmoduleOn (n := n) (Ω := ℝ^n₊)).toSubmodule)
    (α : List (Fin n)) (hα : α.length < m) (i : Fin n) :
    HasWeakDerivativeOn (n := n) (Set.univ : Set (ℝ^n)) [i]
      (oddReflectListCoordinate (n := n) (m := m) U α (Nat.le_of_lt hα) :
        ℝ^n → ℝ)
      (oddReflectListCoordinate (n := n) (m := m) U (α ++ [i]) (by
        simpa [List.length_append] using hα) : ℝ^n → ℝ) := by
  classical
  let hαi : (α ++ [i]).length ≤ m := by
    simpa [List.length_append] using hα
  have hlocal : HasWeakDerivativeOn (n := n) ℝ^n₊ [i]
      (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα) : ℝ^n → ℝ)
      (coordinateAtList (n := n) (m := m) U (α ++ [i]) hαi : ℝ^n → ℝ) :=
    coordinateAtList_hasWeakDerivative_append_single
      (n := n) (m := m) U α hα i
  by_cases heven : Even
      (α.count (PDE.Common.lastIndex (n := n)))
  · let sliceH10 : H¹₀(ℝ^n₊) :=
      ⟨derivativeSlice (n := n) (Ω := ℝ^n₊) α hα U, htrace α hα heven⟩
    have hglobal :=
      (ZeroTraceOdd.oddExtendH10 (n := n) sliceH10).property
        (singleDerivIndex (n := n) i)
    by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst i
      simpa [oddReflectListCoordinate, heven, Nat.even_add_one,
        List.count_append, hαi, sliceH10,
        ZeroTraceOdd.oddExtendH10_apply_coe, ZeroTraceOdd.oddExtendAmbient_apply,
        ZeroTraceOdd.oddExtendLpAt, derivativeSlice_apply_coe,
        derivativeSliceAmbient_apply, derivativeSliceIndex, coordinateAtList] using hglobal
    · simpa [oddReflectListCoordinate, heven, List.count_append, hαi, sliceH10,
        ZeroTraceOdd.oddExtendH10_apply_coe, ZeroTraceOdd.oddExtendAmbient_apply,
        ZeroTraceOdd.oddExtendLpAt, derivativeSlice_apply_coe,
        derivativeSliceAmbient_apply, derivativeSliceIndex, coordinateAtList, hi] using hglobal
  · by_cases hi : i = PDE.Common.lastIndex (n := n)
    · subst i
      simpa [oddReflectListCoordinate, heven, Nat.even_add_one,
        List.count_append, hαi] using
        (Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_evenExtend_of_upper_last
          (n := n) (p := (2 : ℝ≥0∞))
          (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα))
          (coordinateAtList (n := n) (m := m) U
            (α ++ [PDE.Common.lastIndex (n := n)]) hαi) hlocal)
    · simpa [oddReflectListCoordinate, heven, List.count_append, hi, hαi] using
        (Extension.GraphSpace.HalfSpace.hasWeakDerivativeOn_univ_evenExtend_of_upper_ne_last
          (n := n) (p := (2 : ℝ≥0∞)) i hi
          (coordinateAtList (n := n) (m := m) U α (Nat.le_of_lt hα))
          (coordinateAtList (n := n) (m := m) U (α ++ [i]) hαi) hlocal)

end HigherOrderReflection
end GraphSpace
end SobolevSpace
