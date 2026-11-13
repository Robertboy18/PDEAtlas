/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Higher-order supported-core Sobolev spaces

For every order `k`, we realize a compactly supported smooth function as an element of
`W^{k,2}(Ω)` and define their closure. For open `Ω`, this is the standard
`W^{k,2}_0(Ω)`. The closure remains well-defined for arbitrary sets, but may be
degenerate when the set has empty interior.

We specialize the finite-exponent construction of
`Boundary.ZeroTrace.FiniteExponent` to `p = 2` and add two things that are
specific to the Hilbert case: the interaction with first-order slicing
(`derivativeSlice`), so that lower-order derivatives of `W^{k,2}_0` functions
have zero trace in the `H¹₀` sense, and explicit formulas for the top
derivative coordinate in one dimension.

## Main results

* `testFunctionToWk`, `wk0SubmoduleOn`, `Wk0SpaceOn`: the smooth inclusion and the closed
  subspace `W^{k,2}_0(Ω)`.
* `denseRange_testFunctionToWk0Linear`, `Wk0SpaceOn.closed_property_of_testFunctions`:
  density of test functions and the resulting closure principle.
* `derivativeSlice_testFunctionToWk`, `Wk0SpaceOn.derivativeSlice_mem_H10`: every derivative
  of order below `m` of a `W^{m,2}_0(Ω)` function lies in `H¹₀(Ω)`.
* `topDerivIndexOne`, `testFunctionToWk_top_coordinate_one_ae`: the one-dimensional top
  coordinate `d^k/dx^k` and its classical representative.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, for the definition of `W^{k,p}_0(U)` as the
  closure of `C_c^∞(U)` in `W^{k,p}(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology ENNReal Sobolev

namespace GraphSpace


variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- A compactly supported smooth function on `Ω`, with all classical derivatives through order
`k`, regarded as an element of `W^{k,2}(Ω)`. -/
noncomputable def testFunctionToWk
    (φ : TestFunctionOn n Ω) : W^{k,2}(Ω) :=
  testFunctionToWkp (n := n) (k := k) (p := 2) (Ω := Ω) φ

/-- Each coordinate of `testFunctionToWk` is represented a.e. by the corresponding classical
iterated partial derivative. -/
theorem testFunctionToWk_coordinate_ae
    (φ : TestFunctionOn n Ω) (a : DerivIndex n k) :
    (((testFunctionToWk (n := n) (k := k) (Ω := Ω) φ :
        WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv (n := n) a.toList φ.1.toFun x := by
  simpa [testFunctionToWk] using
    (testFunctionToWkp_coordinate_ae
      (n := n) (k := k) (p := 2) (Ω := Ω) φ a)

/-- The norm of a smooth Sobolev coordinate is the concrete `L²` seminorm of its classical
representative. -/
theorem norm_testFunctionToWk_coordinate_eq_eLpNorm_toReal
    (φ : TestFunctionOn n Ω) (a : DerivIndex n k) :
    ‖((testFunctionToWk (n := n) (k := k) (Ω := Ω) φ :
        WkpAmbientOn n k 2 Ω) a)‖ =
      ENNReal.toReal (MeasureTheory.eLpNorm
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList φ.1.toFun x)
        2 (domainMeasure n Ω)) := by
  simpa [testFunctionToWk] using
    (norm_testFunctionToWkp_coordinate_eq_eLpNorm_toReal
      (n := n) (k := k) (p := 2) (Ω := Ω) φ a)

/-- Closure in `W^{k,2}(Ω)` of compactly supported smooth functions.

For open `Ω` this is the conventional definition of `W^{k,2}_0(Ω)`. No trace
characterization is bundled into this definition. -/
noncomputable def wk0SubmoduleOn :
    ClosedSubmodule ℝ (W^{k,2}(Ω)) :=
  wkp0SubmoduleOn (n := n) (k := k) (p := 2) (Ω := Ω)

/-- The supported-core closure as a type; on open sets this is `W^{k,2}_0(Ω)`. -/
abbrev Wk0SpaceOn (n k : ℕ) (Ω : Set (ℝ^n)) : Type :=
  Wkp0SpaceOn n k 2 Ω

/-- A test function belongs to `W^{k,2}_0(Ω)` by the defining closure. -/
theorem testFunctionToWk_mem_Wk0
    (φ : TestFunctionOn n Ω) :
    testFunctionToWk (n := n) (k := k) (Ω := Ω) φ ∈
      (wk0SubmoduleOn (n := n) (k := k) (Ω := Ω)).toSubmodule := by
  simpa [testFunctionToWk, wk0SubmoduleOn] using
    (testFunctionToWkp_mem_Wkp0
      (n := n) (k := k) (p := 2) (Ω := Ω) φ)

/-- The canonical inclusion of test functions into `W^{k,2}_0(Ω)`. -/
noncomputable def testFunctionToWk0
    (φ : TestFunctionOn n Ω) : W₀^{k,2}(Ω) :=
  testFunctionToWkp0 (n := n) (k := k) (p := 2) (Ω := Ω) φ

/-- Forgetting the zero-trace constraint gives the usual `W^{k,2}` image of a test function. -/
@[simp] theorem testFunctionToWk0_coe
    (φ : TestFunctionOn n Ω) :
    ((testFunctionToWk0 (n := n) (k := k) (Ω := Ω) φ :
      W₀^{k,2}(Ω)) : W^{k,2}(Ω)) =
      testFunctionToWk (n := n) (k := k) (Ω := Ω) φ := by
  rfl

/-- The canonical inclusion into `W^{k,2}_0(Ω)` is linear. -/
noncomputable def testFunctionToWk0Linear :
    TestFunctionOn n Ω →ₗ[ℝ] W₀^{k,2}(Ω) :=
  testFunctionToWkp0Linear (n := n) (k := k) (p := 2) (Ω := Ω)

/-- Test functions have dense image in the zero-trace completion. -/
theorem denseRange_testFunctionToWk0Linear :
    DenseRange (testFunctionToWk0Linear (n := n) (k := k) (Ω := Ω)) := by
  exact denseRange_testFunctionToWkp0Linear
    (n := n) (k := k) (p := 2) (Ω := Ω)

/-- Closed properties that hold for all test functions hold throughout `W^{k,2}_0(Ω)`. -/
theorem Wk0SpaceOn.closed_property_of_testFunctions
    {S : Set (W^{k,2}(Ω))} (hSclosed : IsClosed S)
    (hTest : ∀ φ : TestFunctionOn n Ω,
      testFunctionToWk (n := n) (k := k) (Ω := Ω) φ ∈ S)
    (u : W₀^{k,2}(Ω)) :
    (u : W^{k,2}(Ω)) ∈ S := by
  apply Wkp0SpaceOn.closed_property_of_testFunctions
    (n := n) (k := k) (p := 2) (Ω := Ω) hSclosed
  intro φ
  simpa [testFunctionToWk] using hTest φ

private theorem iteratedPartialDeriv_derivativeSliceIndex
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (α : List (Fin n)) (hα : α.length < k)
    (a : DerivIndex n 1) (x : ℝ^n) :
    iteratedPartialDeriv (n := n)
        (derivativeSliceIndex (n := n) α hα a).toList f x =
      iteratedPartialDeriv (n := n) a.toList
        (fun y ↦ iteratedPartialDeriv (n := n) α f y) x := by
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    have hperm :=
      derivIndexOfList_toList_perm (n := n) (k := k) α (Nat.le_of_lt hα)
    simpa [derivativeSliceIndex, iteratedPartialDeriv] using
      congrFun (iteratedPartialDeriv_congr_perm_smooth (n := n) hf hperm) x
  · subst a
    have hperm :=
      derivIndexOfList_toList_perm (n := n) (k := k) (α ++ [i]) (by
        simpa [List.length_append] using hα)
    have hcanonical := congrFun
      (iteratedPartialDeriv_congr_perm_smooth (n := n) hf hperm) x
    have hcomm : (α ++ [i]).Perm ([i] ++ α) := List.perm_append_comm
    have hsmooth := congrFun
      (iteratedPartialDeriv_congr_perm_smooth (n := n) hf hcomm) x
    have hcomp :=
      PDE.iteratedPartialDeriv_append (n := n) [i] α f x
    simpa [derivativeSliceIndex] using
      hcanonical.trans (hsmooth.trans hcomp)

/-- On a smooth test function, taking an order-`α` first-order slice agrees with inserting the
classical derivative `D^α φ` into `H¹(Ω)`. -/
theorem derivativeSlice_testFunctionToWk
    (φ : TestFunctionOn n Ω) (α : List (Fin n)) (hα : α.length < k) :
    derivativeSlice (n := n) (m := k) (Ω := Ω) α hα
        (testFunctionToWk (n := n) (k := k) (Ω := Ω) φ) =
      testFunctionToH1 (n := n) (Ω := Ω)
        (φ.iteratedPartialDeriv α) := by
  classical
  apply Subtype.ext
  refine PiLp.ext fun a ↦ ?_
  apply MeasureTheory.Lp.ext
  filter_upwards
    [testFunctionToWk_coordinate_ae (n := n) (k := k) (Ω := Ω) φ
      (derivativeSliceIndex (n := n) α hα a),
      mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := 1) (p := 2) (Ω := Ω)
        (φ.iteratedPartialDeriv α).1.toFun
        (φ.iteratedPartialDeriv α).1.contDiff
        (φ.iteratedPartialDeriv α).1.hasCompactSupport a]
      with x hhigh hone
  change
    (((testFunctionToWk (n := n) (k := k) (Ω := Ω) φ :
        WkpAmbientOn n k 2 Ω) (derivativeSliceIndex (n := n) α hα a) :
          ℝ^n → ℝ) x) =
      (((testFunctionToH1 (n := n) (Ω := Ω)
          (φ.iteratedPartialDeriv α) :
            WkpAmbientOn n 1 2 Ω) a : ℝ^n → ℝ) x)
  have hone' :
      (((testFunctionToH1 (n := n) (Ω := Ω)
          (φ.iteratedPartialDeriv α) :
            WkpAmbientOn n 1 2 Ω) a : ℝ^n → ℝ) x) =
        iteratedPartialDeriv (n := n) a.toList
          (φ.iteratedPartialDeriv α).1.toFun x := by
    simpa [testFunctionToH1] using hone
  rw [hhigh, hone']
  simpa using iteratedPartialDeriv_derivativeSliceIndex
    (n := n) (k := k) φ.1.contDiff α hα a x

/-- Every derivative of order strictly below `m` of an element of
`W^{m,2}_0(Ω)` belongs to `H¹₀(Ω)`, expressed using the canonical
first-order Sobolev slice. -/
theorem Wk0SpaceOn.derivativeSlice_mem_H10
    {m : ℕ} (u : W₀^{m,2}(Ω))
    (α : List (Fin n)) (hα : α.length < m) :
    derivativeSlice (n := n) (m := m) (Ω := Ω) α hα
        (u : W^{m,2}(Ω)) ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  apply Wk0SpaceOn.closed_property_of_testFunctions
    (n := n) (k := m) (Ω := Ω)
    (S := derivativeSlice (n := n) (m := m) (Ω := Ω) α hα ⁻¹'
      ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule :
        Set (H¹(Ω))))
  · exact (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.preimage
      (derivativeSlice (n := n) (m := m) (Ω := Ω) α hα).continuous
  · intro φ
    change derivativeSlice (n := n) (m := m) (Ω := Ω) α hα
        (testFunctionToWk (n := n) (k := m) (Ω := Ω) φ) ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule
    rw [derivativeSlice_testFunctionToWk
      (n := n) (k := m) (Ω := Ω) φ α hα]
    exact testFunctionToH1_mem_H10 (n := n) (Ω := Ω) _

/-! ## The top coordinate in one dimension -/

/-- The one-dimensional derivative index consisting of `k` repetitions of the sole coordinate. -/
def topDerivIndexOne (k : ℕ) : DerivIndex 1 k :=
  derivIndexOfList (n := 1) (k := k) (List.replicate k 0) (by simp)

/-- The top derivative in one dimension is encoded by `k` repetitions of the sole coordinate. -/
@[simp] theorem topDerivIndexOne_toList (k : ℕ) :
    (topDerivIndexOne k).toList = List.replicate k 0 := by
  apply List.perm_replicate.mp
  simpa [topDerivIndexOne] using
    (derivIndexOfList_toList_perm (n := 1) (k := k) (List.replicate k 0) (by simp))

/-- The top one-dimensional coordinate has the expected classical representative. -/
theorem testFunctionToWk_top_coordinate_one_ae {Ω : Set (ℝ^1)}
    (φ : TestFunctionOn 1 Ω) :
    (((testFunctionToWk (n := 1) (k := k) (Ω := Ω) φ :
        WkpAmbientOn 1 k 2 Ω) (topDerivIndexOne k) : ℝ^1 → ℝ))
      =ᵐ[domainMeasure 1 Ω]
        fun x ↦ iteratedPartialDeriv (n := 1) (List.replicate k 0) φ.1.toFun x := by
  simpa using
    (testFunctionToWk_coordinate_ae (n := 1) (k := k) (Ω := Ω) φ
      (topDerivIndexOne k))

/-- The top one-dimensional coordinate norm is the `L²` norm of the repeated partial derivative. -/
theorem norm_testFunctionToWk_top_coordinate_one_eq_eLpNorm_toReal
    {Ω : Set (ℝ^1)} (φ : TestFunctionOn 1 Ω) :
    ‖((testFunctionToWk (n := 1) (k := k) (Ω := Ω) φ :
        WkpAmbientOn 1 k 2 Ω) (topDerivIndexOne k))‖ =
      ENNReal.toReal (MeasureTheory.eLpNorm
        (fun x ↦ iteratedPartialDeriv (n := 1) (List.replicate k 0) φ.1.toFun x)
        2 (domainMeasure 1 Ω)) := by
  simpa using
    (norm_testFunctionToWk_coordinate_eq_eLpNorm_toReal
      (n := 1) (k := k) (Ω := Ω) φ (topDerivIndexOne k))

end GraphSpace

end SobolevSpace
