/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Supported-core Sobolev spaces

For `1 ≤ p`, we realize compactly supported smooth functions as elements of
`W^{k,p}(Ω)` and define their closure. On open sets and for `p < ∞` this is the standard
space `W^{k,p}_0(Ω)`. At `p = ∞` it is the `W^{k,∞}`-closure of `C_c^∞(Ω)`. The definition
involves no boundary trace.

`W^{k,p}_0(Ω)` is the closure of `C_c^∞(Ω)` in the
`W^{k,p}(Ω)` norm (Evans, PDE, §5.2.2; Brezis, Functional Analysis, Sobolev Spaces and PDE,
Chapter 9). Here the ambient space is the graph-space model `WkpSpaceOn n k p Ω`, and a
test function enters through its classical derivatives via `mkWkpSpaceOnOfContDiff`.

## Main results

* `testFunctionToWkp`, `testFunctionToWkpLinear`: the inclusion of compactly supported smooth
  functions into `W^{k,p}(Ω)`, with `testFunctionToWkp_coordinate_ae` identifying each
  coordinate with the corresponding classical derivative.
* `wkp0SubmoduleOn`, `Wkp0SpaceOn`: the closed submodule `W^{k,p}_0(Ω)` and its type.
* `wkpSpace_mem_Wkp0_univ`: for `p < ∞`, `W^{k,p}(ℝ^n) = W^{k,p}_0(ℝ^n)`, by mollification and
  cutoff (the global density theorem).
* `denseRange_testFunctionToWkp0Linear`, `Wkp0SpaceOn.closed_property_of_testFunctions`:
  test functions are dense in `W^{k,p}_0(Ω)`, so closed properties transfer from them.
* `instCompleteSpace_Wkp0SpaceOn`: `W^{k,p}_0(Ω)` is complete.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, p. 259, for the definition of `W^{k,p}_0(U)` as the
  closure of `C_c^∞(U)` in `W^{k,p}(U)`, and §5.3.1, Theorem 1, pp. 264-265, for approximation by
  mollification.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 9, for `W^{1,p}_0(Ω)` and the density of `C_c^∞(ℝ^N)` in `W^{1,p}(ℝ^N)`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology ENNReal Sobolev

namespace GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- A compactly supported smooth function on `Ω`, regarded as an element of
`W^{k,p}(Ω)` through its classical derivatives. -/
noncomputable def testFunctionToWkp
    (φ : TestFunctionOn n Ω) : W^{k,p}(Ω) :=
  mkWkpSpaceOnOfContDiff
    (n := n) (k := k) (p := p) (Ω := Ω)
    φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport

/-- Each coordinate of `testFunctionToWkp` is represented almost everywhere
by the corresponding classical iterated partial derivative. -/
theorem testFunctionToWkp_coordinate_ae
    (φ : TestFunctionOn n Ω) (a : DerivIndex n k) :
    (((testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ :
        WkpAmbientOn n k p Ω) a : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv (n := n) a.toList φ.1.toFun x := by
  simpa [testFunctionToWkp] using
    (mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := k) (p := p) (Ω := Ω)
      φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport a)

/-- The norm of a smooth Sobolev coordinate is the `Lᵖ` seminorm of its
classical representative. -/
theorem norm_testFunctionToWkp_coordinate_eq_eLpNorm_toReal
    (φ : TestFunctionOn n Ω) (a : DerivIndex n k) :
    ‖((testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ :
        WkpAmbientOn n k p Ω) a)‖ =
      ENNReal.toReal (MeasureTheory.eLpNorm
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList φ.1.toFun x)
        p (domainMeasure n Ω)) := by
  rw [MeasureTheory.Lp.norm_def]
  congr 1
  exact MeasureTheory.eLpNorm_congr_ae
    (testFunctionToWkp_coordinate_ae
      (n := n) (k := k) (p := p) (Ω := Ω) φ a)

/-- The inclusion of compactly supported smooth functions into `W^{k,p}(Ω)`
is linear. -/
noncomputable def testFunctionToWkpLinear :
    TestFunctionOn n Ω →ₗ[ℝ] W^{k,p}(Ω) where
  toFun := testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω)
  map_add' := by
    intro φ ψ
    exact (globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := p) (Ω := Ω)).map_add φ.1 ψ.1
  map_smul' := by
    intro c φ
    exact (globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := p) (Ω := Ω)).map_smul c φ.1

/-- Applying the linear test-function embedding recovers the classical
Sobolev constructor. -/
@[simp]
theorem testFunctionToWkpLinear_apply
    (φ : TestFunctionOn n Ω) :
    testFunctionToWkpLinear
        (n := n) (k := k) (p := p) (Ω := Ω) φ =
      testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ :=
  rfl

variable [Fact (1 ≤ p)]

/-- The closure in `W^{k,p}(Ω)` of compactly supported smooth functions. -/
noncomputable def wkp0SubmoduleOn :
    ClosedSubmodule ℝ (W^{k,p}(Ω)) :=
  Submodule.closure (LinearMap.range
    (testFunctionToWkpLinear (n := n) (k := k) (p := p) (Ω := Ω)))

/-- The supported-core closure as a type. On open sets and for `p < ∞` this is
`W^{k,p}_0(Ω)`; at `p = ∞` it is the `W^{k,∞}`-closure of `C_c^∞(Ω)`. -/
abbrev Wkp0SpaceOn
    (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) : Type :=
  ↥((wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω)).toSubmodule)

/-- The closure of supported smooth test functions in the scalar Sobolev space. -/
scoped[Sobolev] notation "W₀^{" k "," p "}(" Ω ")" =>
  SobolevSpace.GraphSpace.Wkp0SpaceOn _ k p Ω

/-- The scalar supported smooth closure on the underlying set of a bundled domain. -/
scoped[Sobolev] notation "W₀^{" k "," p "}(" Ω ")" =>
  SobolevSpace.GraphSpace.Wkp0SpaceOn _ k p (SetLike.coe Ω)

/-- A test function belongs to `W^{k,p}_0(Ω)` by the defining closure. -/
theorem testFunctionToWkp_mem_Wkp0
    (φ : TestFunctionOn n Ω) :
    testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ ∈
      (wkp0SubmoduleOn
        (n := n) (k := k) (p := p) (Ω := Ω)).toSubmodule := by
  apply subset_closure
  exact ⟨φ, rfl⟩

/-- Sequential closure principle for `W^{k,p}_0(Ω)`: a `W^{k,p}(Ω)` limit
of compactly supported smooth test functions belongs to the supported-core
closure. -/
theorem mem_Wkp0_of_tendsto_testFunctionToWkp
    (u : W^{k,p}(Ω)) (φ : ℕ → TestFunctionOn n Ω)
    (hφ : Filter.Tendsto
      (fun m ↦
        testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) (φ m))
      Filter.atTop (𝓝 u)) :
    u ∈ (wkp0SubmoduleOn
      (n := n) (k := k) (p := p) (Ω := Ω)).toSubmodule := by
  apply (wkp0SubmoduleOn
    (n := n) (k := k) (p := p) (Ω := Ω)).isClosed'.mem_of_tendsto hφ
  exact Filter.Eventually.of_forall fun m ↦
    testFunctionToWkp_mem_Wkp0
      (n := n) (k := k) (p := p) (Ω := Ω) (φ m)

/-- At every finite exponent, compactly supported smooth functions are dense
in the whole-space graph space. Equivalently,
`W^{k,p}(ℝ^n) = W^{k,p}_0(ℝ^n)` in the supported-core sense. -/
theorem wkpSpace_mem_Wkp0_univ
    (hp : p ≠ ∞) (U : W^{k,p}(ℝ^n)) :
    U ∈ (wkp0SubmoduleOn
      (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n)))).toSubmodule := by
  obtain ⟨f, hf, hcs, hlim⟩ :=
    globalApproximation_WkpSpace
      (n := n) (p := p) (Approximation.standardMollifier n) hp k U
  let φ : ℕ → TestFunctionOn n Set.univ := fun m ↦
    ⟨_root_.TestFunction.mk (f m) (hf m) (hcs m) (Set.subset_univ _),
      Set.subset_univ _⟩
  apply mem_Wkp0_of_tendsto_testFunctionToWkp
    (n := n) (k := k) (p := p) (Ω := (Set.univ : Set (ℝ^n))) U φ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hφ_toFun (m : ℕ) : (φ m).1.toFun = f m := by
    funext x
    rfl
  simp_rw [testFunctionToWkp, hφ_toFun]
  exact hlim

/-- The canonical inclusion of test functions into `W^{k,p}_0(Ω)`. -/
noncomputable def testFunctionToWkp0
    (φ : TestFunctionOn n Ω) : W₀^{k,p}(Ω) :=
  ⟨testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ,
    testFunctionToWkp_mem_Wkp0
      (n := n) (k := k) (p := p) (Ω := Ω) φ⟩

/-- Forgetting the zero-trace constraint gives the usual `W^{k,p}` image of a test function. -/
@[simp] theorem testFunctionToWkp0_coe
    (φ : TestFunctionOn n Ω) :
    ((testFunctionToWkp0
      (n := n) (k := k) (p := p) (Ω := Ω) φ :
        W₀^{k,p}(Ω)) : W^{k,p}(Ω)) =
      testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ := rfl

/-- The canonical inclusion into `W^{k,p}_0(Ω)` is linear. -/
noncomputable def testFunctionToWkp0Linear :
    TestFunctionOn n Ω →ₗ[ℝ] W₀^{k,p}(Ω) where
  toFun := testFunctionToWkp0 (n := n) (k := k) (p := p) (Ω := Ω)
  map_add' := by
    intro φ ψ
    apply Subtype.ext
    exact (testFunctionToWkpLinear
      (n := n) (k := k) (p := p) (Ω := Ω)).map_add φ ψ
  map_smul' := by
    intro c φ
    apply Subtype.ext
    exact (testFunctionToWkpLinear
      (n := n) (k := k) (p := p) (Ω := Ω)).map_smul c φ

/-- Test functions have dense image in the supported-core completion. -/
theorem denseRange_testFunctionToWkp0Linear :
    DenseRange
      (testFunctionToWkp0Linear (n := n) (k := k) (p := p) (Ω := Ω)) := by
  rw [DenseRange, Subtype.dense_iff]
  intro u hu
  change u ∈ closure
    (((↑) : W₀^{k,p}(Ω) → W^{k,p}(Ω)) ''
      Set.range
        (testFunctionToWkp0Linear
          (n := n) (k := k) (p := p) (Ω := Ω)))
  have himage :
      (((↑) : W₀^{k,p}(Ω) → W^{k,p}(Ω)) ''
          Set.range
            (testFunctionToWkp0Linear
              (n := n) (k := k) (p := p) (Ω := Ω))) =
        (LinearMap.range
          (testFunctionToWkpLinear
            (n := n) (k := k) (p := p) (Ω := Ω)) :
            Set (W^{k,p}(Ω))) := by
    ext v
    constructor
    · rintro ⟨w, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact
        ⟨testFunctionToWkp0
            (n := n) (k := k) (p := p) (Ω := Ω) φ,
          ⟨φ, rfl⟩, rfl⟩
  rw [himage]
  exact hu

/-- Closed properties that hold for every test function hold throughout
`W^{k,p}_0(Ω)`. -/
theorem Wkp0SpaceOn.closed_property_of_testFunctions
    {S : Set (W^{k,p}(Ω))} (hSclosed : IsClosed S)
    (hTest : ∀ φ : TestFunctionOn n Ω,
      testFunctionToWkp (n := n) (k := k) (p := p) (Ω := Ω) φ ∈ S)
    (u : W₀^{k,p}(Ω)) :
    (u : W^{k,p}(Ω)) ∈ S := by
  apply closure_minimal _ hSclosed u.property
  rintro v ⟨φ, rfl⟩
  exact hTest φ

/-- `W^{k,p}_0(Ω)` is complete: it is a closed subspace of the complete space `W^{k,p}(Ω)`. -/
instance instCompleteSpace_Wkp0SpaceOn
    (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Set (ℝ^n)) :
    CompleteSpace (W₀^{k,p}(Ω)) :=
  (wkp0SubmoduleOn
    (n := n) (k := k) (p := p) (Ω := Ω)).isClosed'.completeSpace_coe

end GraphSpace

end SobolevSpace
