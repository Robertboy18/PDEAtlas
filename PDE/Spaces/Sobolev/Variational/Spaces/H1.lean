/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# The Sobolev spaces H¹ and H¹₀

`H1SpaceOn n Ω`, written `H¹(Ω)`, is `WkpSpaceOn n 1 2 Ω`, and `H10SpaceOn n Ω`, written
`H¹₀(Ω)`, is the closure in it of the smooth test functions supported in `Ω`. For open `Ω`
these are Evans's `H¹(Ω) = W^{1,2}(Ω)` and `H¹₀(Ω) = W^{1,2}_0(Ω)` (§5.2.2), the spaces of the
weak formulation in §6.1.2. The closure needs no regularity of `Ω`; on a nonopen set the ambient
space keeps the generalized test-function meaning of `HasWeakDerivativeOn`.

## Main results

* `testFunctionToH1`, `testFunctionToH10Linear`: test functions as elements of `H¹(Ω)` and
  `H¹₀(Ω)`.
* `H10SpaceOn.closed_property_of_CcSmooth`: a closed subset of `H¹(Ω)` that contains every
  test function contains `H¹₀(Ω)`.
* `denseRange_testFunctionToH10Linear`: test functions are dense in `H¹₀(Ω)`, the hypothesis
  of `LinearMap.extendOfNorm`.
* Normed, measurable and Borel instances on `H¹₀(Ω)` and on its strong dual.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.2, definitions of `W^{k,p}(U)`, `H^k(U)` and
  `W^{k,p}_0(U)`, pp. 258-259; and §6.1.2, identity (7), p. 314.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology InnerProductSpace ENNReal


namespace GraphSpace

/-!
## `H¹` and `H¹₀` in the Sobolev graph space

`h10SubmoduleOn` is the closure of `C_c^∞(Ω)` in the order-one, exponent-two graph space.
-/

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The order-one, exponent-two weak-derivative graph space. On open `Ω`, this is the
Hilbert space `H¹(Ω) = W^{1,2}(Ω)`. -/
abbrev H1SpaceOn (n : ℕ) (Ω : Set (ℝ^n)) : Type :=
  WkpSpaceOn n 1 2 Ω

/-- The scalar first-order Hilbert Sobolev space. Use `open scoped Sobolev`
to write it as `H¹(Ω)`, with the spatial dimension inferred from `Ω`. -/
scoped[Sobolev] notation "H¹(" Ω ")" => SobolevSpace.GraphSpace.H1SpaceOn _ Ω

/-- Scalar `H¹` on a bundled domain, using its underlying set. -/
scoped[Sobolev] notation "H¹(" Ω ")" =>
  SobolevSpace.GraphSpace.H1SpaceOn _ (SetLike.coe Ω)

open scoped Sobolev

/-- The whole-space Sobolev space `H¹(ℝ^n)`. -/
abbrev H1Space (n : ℕ) : Type :=
  H1SpaceOn n Set.univ

/-- Scalar `H¹` on the whole Euclidean space. -/
scoped[Sobolev] notation "H¹(" "ℝ^" n ")" =>
  SobolevSpace.GraphSpace.H1Space n

/-- A test function with support in `Ω` gives an element of `H¹(Ω)`. -/
noncomputable def testFunctionToH1 (φΩ : TestFunctionOn n Ω) : H¹(Ω) :=
  mkWkpSpaceOnOfContDiff (n := n) (k := 1) (p := 2) (Ω := Ω)
    φΩ.1.toFun φΩ.1.contDiff φΩ.1.hasCompactSupport

/-- The linear map sending `C_c^∞(Ω)` test functions to `H¹(Ω)` by choosing classical derivatives
as weak derivatives. -/
noncomputable def testFunctionToH1Linear :
    TestFunctionOn n Ω →ₗ[ℝ] H¹(Ω) :=
  testFunctionToWkpLinear (n := n) (k := 1) (p := 2) (Ω := Ω)

/-- Applying the linear test-function inclusion agrees with the underlying
`H¹` constructor. -/
theorem testFunctionToH1Linear_apply (φΩ : TestFunctionOn n Ω) :
    testFunctionToH1Linear (n := n) (Ω := Ω) φΩ =
      testFunctionToH1 (n := n) (Ω := Ω) φΩ :=
  rfl

/--
The norm of a coordinate in the Sobolev bundle attached to a smooth test
function is exactly the `Lp` seminorm of the corresponding classical
iterated partial derivative.
-/
theorem norm_testFunctionToH1_coordinate_eq_eLpNorm_toReal
    (φΩ : TestFunctionOn n Ω) (a : DerivIndex n 1) :
    ‖((testFunctionToH1 (n := n) (Ω := Ω) φΩ :
        WkpAmbientOn n 1 2 Ω) a)‖ =
      ENNReal.toReal (MeasureTheory.eLpNorm
        (fun x ↦ iteratedPartialDeriv (n := n) a.toList φΩ.1.toFun x)
        2 (domainMeasure n Ω)) := by
  simpa [testFunctionToH1, testFunctionToWkp] using
    (norm_testFunctionToWkp_coordinate_eq_eLpNorm_toReal
      (n := n) (k := 1) (p := 2) (Ω := Ω) φΩ a)

/-- The submodule of `H¹(Ω)` consisting of the images of `C_c^∞(Ω)` test functions. -/
noncomputable def ccSmoothSubmoduleOn :
    Submodule ℝ (H¹(Ω)) :=
  LinearMap.range
    (testFunctionToWkpLinear (n := n) (k := 1) (p := 2) (Ω := Ω))

/-- The closure of `C_c^∞(Ω)` in `H¹(Ω)`. For open `Ω` this is Evans's
`H¹₀(Ω) = W^{1,2}_0(Ω)` (§5.2.2). -/
noncomputable def h10SubmoduleOn :
    ClosedSubmodule ℝ (H¹(Ω)) :=
  wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)

/-- The closed-subspace type associated to `h10SubmoduleOn`; for open `Ω`, this is
`H¹₀(Ω)`. -/
abbrev H10SpaceOn (n : ℕ) (Ω : Set (ℝ^n)) : Type :=
  Wkp0SpaceOn n 1 2 Ω

/-- The closure of compactly supported smooth functions in `H¹(Ω)`.
The notation is shared by variational PDE formulations through `open scoped Sobolev`. -/
scoped[Sobolev] notation "H¹₀(" Ω ")" => SobolevSpace.GraphSpace.H10SpaceOn _ Ω

/-- Scalar `H¹₀` on a bundled domain, using its underlying set. -/
scoped[Sobolev] notation "H¹₀(" Ω ")" =>
  SobolevSpace.GraphSpace.H10SpaceOn _ (SetLike.coe Ω)

/-- The closure of compactly supported smooth functions in whole-space `H¹`. -/
scoped[Sobolev] notation "H¹₀(" "ℝ^" n ")" =>
  SobolevSpace.GraphSpace.H10SpaceOn n Set.univ

/-- The norm on `H¹₀(Ω)` is inherited from its closed subspace of `H¹(Ω)`.
Registering this structure at the named space also makes the operator norm on its
strong dual available without unfolding both graph subspaces during instance search. -/
instance H10SpaceOn.instNormedAddCommGroup : NormedAddCommGroup (H¹₀(Ω)) :=
  (wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)).toSubmodule.normedAddCommGroup

/-- The seminormed structure used in operator-norm estimates is the one underlying
the inherited `H¹₀(Ω)` normed-group structure. -/
instance H10SpaceOn.instSeminormedAddCommGroup : SeminormedAddCommGroup (H¹₀(Ω)) :=
  H10SpaceOn.instNormedAddCommGroup.toSeminormedAddCommGroup

/-- Scalar multiplication on `H¹₀(Ω)` is inherited from the ambient Sobolev submodule,
with its canonical normed-group structure. -/
instance H10SpaceOn.instNormedSpace : NormedSpace ℝ (H¹₀(Ω)) :=
  Submodule.normedSpace (wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)).toSubmodule

/-- Measurability on `H¹₀(Ω)` uses its norm-topology Borel sigma algebra. -/
instance H10SpaceOn.instMeasurableSpace : MeasurableSpace (H¹₀(Ω)) :=
  borel _

/-- The measurable structure on `H¹₀(Ω)` is its Borel structure. -/
instance H10SpaceOn.instBorelSpace : BorelSpace (H¹₀(Ω)) :=
  ⟨rfl⟩

/-- The strong dual of `H¹₀(Ω)` carries the Borel sigma algebra of its operator-norm
topology, as used for Bochner-measurable variational source terms. -/
instance H10SpaceOn.instStrongDualMeasurableSpace :
    MeasurableSpace (StrongDual ℝ (H¹₀(Ω))) :=
  borel _

/-- The measurable structure on the strong dual of `H¹₀(Ω)` is its norm-topology
Borel structure. -/
instance H10SpaceOn.instStrongDualBorelSpace :
    BorelSpace (StrongDual ℝ (H¹₀(Ω))) :=
  ⟨rfl⟩

/-- Every compactly supported smooth test function on `Ω` belongs to `H¹₀(Ω)` by definition of
`H¹₀` as the closure of `C_c^∞(Ω)` in `H¹(Ω)`. -/
theorem testFunctionToH1_mem_H10 (φΩ : TestFunctionOn n Ω) :
    testFunctionToH1 (n := n) (Ω := Ω) φΩ ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  simpa [testFunctionToH1, testFunctionToWkp, h10SubmoduleOn] using
    (testFunctionToWkp_mem_Wkp0
      (n := n) (k := 1) (p := 2) (Ω := Ω) φΩ)

/-- Sequential closure principle for `H¹₀(Ω)`: an `H¹(Ω)` limit of compactly
supported smooth test functions belongs to `H¹₀(Ω)`.  This is the form used by
support-preserving mollification and cutoff arguments. -/
theorem mem_H10_of_tendsto_testFunctionToH1
    (u : H¹(Ω)) (φ : ℕ → TestFunctionOn n Ω)
    (hφ : Filter.Tendsto
      (fun m ↦ testFunctionToH1 (n := n) (Ω := Ω) (φ m))
      Filter.atTop (𝓝 u)) :
    u ∈ (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  apply (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.mem_of_tendsto hφ
  exact Filter.Eventually.of_forall fun m ↦
    testFunctionToH1_mem_H10 (n := n) (Ω := Ω) (φ m)

/-- Canonical map from `C_c^∞(Ω)` test functions into `H¹₀(Ω)`. -/
noncomputable def testFunctionToH10 (φΩ : TestFunctionOn n Ω) : H¹₀(Ω) :=
  testFunctionToWkp0 (n := n) (k := 1) (p := 2) (Ω := Ω) φΩ

/-- The canonical `C_c^∞(Ω) → H¹₀(Ω)` map forgets to the usual `H¹(Ω)` representative. -/
@[simp]
theorem testFunctionToH10_coe (φΩ : TestFunctionOn n Ω) :
    ((testFunctionToH10 (n := n) (Ω := Ω) φΩ : H¹₀(Ω)) :
      H¹(Ω)) =
        testFunctionToH1 (n := n) (Ω := Ω) φΩ :=
  rfl

/-- Every element of `H¹₀(Ω)`, viewed in `H¹(Ω)`, lies in the closure of the image of
`C_c^∞(Ω)`, as in Evans's definition of `W^{k,p}_0` (§5.2.2). -/
theorem H10SpaceOn.mem_closure_CcSmooth (u : H¹₀(Ω)) :
    (u : H¹(Ω)) ∈
      closure ((ccSmoothSubmoduleOn (n := n) (Ω := Ω) : Submodule ℝ (H¹(Ω))) :
        Set (H¹(Ω))) := by
  let M : Submodule ℝ (H¹(Ω)) :=
    ccSmoothSubmoduleOn (n := n) (Ω := Ω)
  have hu' : (u : H¹(Ω)) ∈ M.topologicalClosure := by
    change (u : H¹(Ω)) ∈
      ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule : Set (H¹(Ω)))
    exact u.property
  change (u : H¹(Ω)) ∈ closure (M : Set (H¹(Ω)))
  exact hu'

/-- Closure principle for `H¹₀(Ω)`: any closed subset of `H¹(Ω)` containing every compactly
supported smooth test function contains every `H¹₀(Ω)` element.

Evans uses this approximation step in §6.1.2 to extend the identity (7) from test functions
`v ∈ C_c^∞(U)` to all `v ∈ H¹₀(U)`: the statement is proved for test functions, the set where it
holds is closed in `H¹`, and density finishes the argument. -/
theorem H10SpaceOn.closed_property_of_CcSmooth
    {S : Set (H¹(Ω))} (hSclosed : IsClosed S)
    (hCc : ((ccSmoothSubmoduleOn (n := n) (Ω := Ω) : Submodule ℝ (H¹(Ω))) :
      Set (H¹(Ω))) ⊆ S)
    (u : H¹₀(Ω)) :
    (u : H¹(Ω)) ∈ S := by
  exact
    closure_minimal hCc hSclosed
      (H10SpaceOn.mem_closure_CcSmooth (n := n) (Ω := Ω) u)

/-- The canonical injection `C_c^∞(Ω) → H¹₀(Ω)` is linear. -/
noncomputable def testFunctionToH10Linear :
    TestFunctionOn n Ω →ₗ[ℝ] H¹₀(Ω) :=
  testFunctionToWkp0Linear (n := n) (k := 1) (p := 2) (Ω := Ω)

/-- Forgetting the linear map `C_c^∞(Ω) → H¹₀(Ω)` to `H¹(Ω)` gives the usual test-function
inclusion into `H¹(Ω)`. -/
@[simp]
theorem testFunctionToH10Linear_coe_apply (φΩ : TestFunctionOn n Ω) :
    ((testFunctionToH10Linear (n := n) (Ω := Ω) φΩ : H¹₀(Ω)) :
      H¹(Ω)) =
        testFunctionToH1Linear (n := n) (Ω := Ω) φΩ :=
  rfl

/--
Compactly supported smooth functions have dense image in `H¹₀(Ω)`.  This is
the map-level form of the defining closure, as needed by
`LinearMap.extendOfNorm` when a bounded estimate is first proved on test
functions.
-/
theorem denseRange_testFunctionToH10Linear :
    DenseRange (testFunctionToH10Linear (n := n) (Ω := Ω)) := by
  exact denseRange_testFunctionToWkp0Linear
    (n := n) (k := 1) (p := 2) (Ω := Ω)

/-- The underlying submodule defining `H¹₀(Ω)` is closed in `H¹(Ω)`. -/
instance instIsClosed_h10SubmoduleOn_toSubmodule :
    IsClosed ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule : Set (H¹(Ω))) := by
  exact (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'

end GraphSpace

end SobolevSpace
