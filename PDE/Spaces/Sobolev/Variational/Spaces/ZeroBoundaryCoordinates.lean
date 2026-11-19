/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.GraphSpace.Norms
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Coordinates on `H¹` and `H¹₀`

An element of `H¹(Ω)` in this library is a bundle of `n + 1` functions in `L²(Ω)`: the function
itself and its `n` weak partial derivatives. We define the continuous coordinate maps
`u ↦ u` and `u ↦ ∂_i u` from `H¹₀(Ω)` (the closure of the test functions in `H¹(Ω)`) into
`L²(Ω)`, each of operator norm at most one, and prove the decompositions

`‖u‖²_{H¹} = ‖u‖²_{L²} + ∑_i ‖∂_i u‖²_{L²}`,
`⟪u, v⟫_{H¹} = ⟪u, v⟫_{L²} + ∑_i ⟪∂_i u, ∂_i v⟫_{L²}`.

For a smooth compactly supported test function the coordinates are the function and its classical
derivatives, so inner products against test functions become explicit integrals. On an open domain
the base coordinate map is injective and has dense range in `L²(Ω)`; the density statement contains
the classical density of `C_c^∞(Ω)` in `L²(Ω)` (Brezis, Chapter 4). None of this depends on a
particular elliptic operator or variational problem.

## Main results

* `coordCLM`, `baseCoordCLM`, `derivCoordCLM`: the coordinate projections from `H¹₀(Ω)`, with
  `baseCoordCLM_norm_le` and `derivCoordCLM_norm_le`.
* `norm_sq_eq_base_sq_add_sum_deriv_sq`, `inner_eq_base_add_sum_deriv`: the norm and inner
  product decompositions.
* `gradientCLM`: the restriction to `H¹₀` of the vector-valued weak gradient `wkpGradientCLM`
  on `H¹` (from `GraphSpace.Operators.Gradient`), with the squared `L²(Ω; ℝⁿ)` norm identities
  `norm_wkpGradientCLM_sq_eq_sum_deriv_sq` and `norm_gradientCLM_sq_eq_sum_deriv_sq`.
* `baseCoordCLM_testFunction_apply_ae`, `derivCoordCLM_testFunction_apply_ae`,
  `inner_base_testFunction_eq_integral`, `inner_deriv_testFunction_eq_integral`: coordinates of
  test functions and the resulting integral formulas.
* `baseCoordCLM_injective`, `baseCoordCLM_denseRange`: injectivity and density of the base
  coordinate map on an open domain.

## How it works

Injectivity on an open domain is `WkpSpaceOn.ext_of_base_ae`: weak derivatives on an open set are
unique (Evans §5.2.1, Lemma), so the value of an element determines its whole bundle. For density we
show that the orthogonal complement of the range in `L²(Ω)` is zero. If `f` is orthogonal to the
value of every test function `g` supported in `Ω`, then `∫_Ω f g = 0`
(`inner_base_testFunction_eq_integral`), and Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `f = 0` almost everywhere on `Ω`. The
norm and inner product decompositions are the coordinate splittings of the Hilbert ambient product
(`ambient_norm_sq_eq_base_sq_add_sum_deriv_sq`, `ambient_inner_eq_base_add_sum_deriv`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, Lemma, p. 257, the uniqueness of weak derivatives up
  to a set of measure zero.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext,
  Springer, 2011, Chapter 4, for the density of `C_c^∞(Ω)` in `L^p(Ω)` for `p < ∞`.
  <https://doi.org/10.1007/978-0-387-70914-7>
-/

open PDE (iteratedPartialDeriv)
open scoped Sobolev

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}


section Coordinates

local notation "Ambient" => WkpAmbientOn n 1 2 Ω
local notation "L2" => DerivLp n 2 Ω

/-- The closure-defined `H¹₀(Ω)` space, regarded as a linear subspace of `H¹(Ω)`. -/
@[reducible]
noncomputable def h10Submodule : Submodule ℝ H¹(Ω) :=
  (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule

/-- The canonical continuous linear inclusion `H¹₀(Ω) → H¹(Ω)`. -/
@[reducible]
noncomputable def h10SubtypeL : H¹₀(Ω) →L[ℝ] H¹(Ω) :=
  (h10Submodule (n := n) (Ω := Ω)).subtypeL

/-- The canonical inclusion `H¹₀(Ω) → H¹(Ω)` agrees pointwise with the
underlying subtype coercion. -/
@[simp]
theorem h10SubtypeL_apply (u : H¹₀(Ω)) :
    h10SubtypeL (n := n) (Ω := Ω) u = (u : H¹(Ω)) :=
  rfl

/-- Project an arbitrary linear subspace of `H¹(Ω)` to one `L²` derivative coordinate. -/
noncomputable def coordCLMOf (S : Submodule ℝ H¹(Ω)) (a : DerivIndex n 1) : S →L[ℝ] L2 :=
  (wkpCoordinateCLM
    (n := n) (m := 1) (p := 2) (Ω := Ω) a).comp S.subtypeL

/-- Project `H¹₀(Ω)` continuously to the `L²` coordinate indexed by `a`. -/
noncomputable def coordCLM (a : DerivIndex n 1) : H¹₀(Ω) →L[ℝ] L2 :=
  coordCLMOf (n := n) (Ω := Ω)
    (h10Submodule (n := n) (Ω := Ω)) a

/-- The continuous `L²` projection to the zeroth-order coordinate of `H¹₀(Ω)`. -/
@[reducible]
noncomputable def baseCoordCLM : H¹₀(Ω) →L[ℝ] L2 :=
  coordCLM (n := n) (Ω := Ω) (baseIndex n 1)

/-- The continuous `L²` projection to the weak derivative in direction `i`. -/
@[reducible]
noncomputable def derivCoordCLM (i : Fin n) : H¹₀(Ω) →L[ℝ] L2 :=
  coordCLM (n := n) (Ω := Ω) (singleDerivIndex (n := n) i)

/-- Restricting a canonical `H¹` coordinate projection to `H¹₀` recovers
the corresponding zero-boundary coordinate map. -/
@[simp]
theorem wkpCoordinateCLM_h10SubtypeL (a : DerivIndex n 1) (u : H¹₀(Ω)) :
    wkpCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω) a
        (h10SubtypeL (n := n) (Ω := Ω) u) =
      coordCLM (n := n) (Ω := Ω) a u :=
  rfl

/-- Restricting the canonical `H¹` base-coordinate projection to `H¹₀`
recovers `baseCoordCLM`. -/
@[simp]
theorem wkpBaseCoordinateCLM_h10SubtypeL (u : H¹₀(Ω)) :
    wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)
        (h10SubtypeL (n := n) (Ω := Ω) u) =
      baseCoordCLM (n := n) (Ω := Ω) u :=
  rfl

/-- Evaluating a zero-boundary coordinate projection is the same as first
forgetting to `H¹(Ω)` and then evaluating the corresponding Sobolev
coordinate. -/
@[simp]
theorem coordCLM_apply (a : DerivIndex n 1) (u : H¹₀(Ω)) :
    coordCLM (n := n) (Ω := Ω) a u =
      (((u : H¹(Ω)) : Ambient) a) :=
  rfl

/-- The base-coordinate map evaluates the zeroth-order Sobolev coordinate. -/
@[simp]
theorem baseCoordCLM_apply (u : H¹₀(Ω)) :
    baseCoordCLM (n := n) (Ω := Ω) u =
      (((u : H¹(Ω)) : Ambient) (baseIndex n 1)) :=
  rfl

/-- The derivative-coordinate map evaluates the corresponding first-order
Sobolev coordinate. -/
@[simp]
theorem derivCoordCLM_apply (i : Fin n) (u : H¹₀(Ω)) :
    derivCoordCLM (n := n) (Ω := Ω) i u =
      (((u : H¹(Ω)) : Ambient) (singleDerivIndex (n := n) i)) :=
  rfl

/-- The `L²` base-coordinate projection from `H¹₀(Ω)` has operator norm at most one. -/
theorem baseCoordCLM_norm_le (u : H¹₀(Ω)) :
    ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ≤ ‖u‖ := by
  simpa using
    (wkpBaseCoordinateCLM_norm_le
      (n := n) (m := 1) (p := 2) (Ω := Ω) (u : H¹(Ω)))

/-- On an open domain, the `L²` base-coordinate map from `H¹₀(Ω)` is injective.

Equality of the underlying `L²` functions determines the full Sobolev fields because weak
derivatives are unique on open sets. -/
theorem baseCoordCLM_injective (hΩopen : IsOpen Ω) :
    Function.Injective (baseCoordCLM (n := n) (Ω := Ω)) := by
  intro u v huv
  apply Subtype.ext
  apply WkpSpaceOn.ext_of_base_ae (n := n) (k := 1) (p := (2 : ℝ≥0∞)) hΩopen
  have huvAe :
      ((baseCoordCLM (n := n) (Ω := Ω) u : L2) : ℝ^n → ℝ) =ᵐ[
        domainMeasure n Ω]
      ((baseCoordCLM (n := n) (Ω := Ω) v : L2) : ℝ^n → ℝ) := by
    rw [huv]
  simpa only [baseCoordCLM_apply] using huvAe

/-- Each first-derivative coordinate projection from `H¹₀(Ω)` has operator norm at most one. -/
theorem derivCoordCLM_norm_le (i : Fin n) (u : H¹₀(Ω)) :
    ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ≤ ‖u‖ := by
  simpa using
    (wkpCoordinateCLM_norm_le
      (n := n) (m := 1) (p := 2) (Ω := Ω)
      (singleDerivIndex (n := n) i) (u : H¹(Ω)))

end Coordinates

section Decomposition


/-- The squared `H¹₀` norm splits into its canonical base and
first-derivative coordinate maps. -/
theorem norm_sq_eq_base_sq_add_sum_deriv_sq (u : H¹₀(Ω)) :
    ‖u‖ ^ 2 =
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 +
        ∑ i : Fin n,
          ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 := by
  change
    ‖(((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω))‖ ^ 2 = _
  simpa only [baseCoordCLM_apply, derivCoordCLM_apply] using
    (ambient_norm_sq_eq_base_sq_add_sum_deriv_sq
      (n := n) (Ω := Ω)
      (((u : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)))

/-- The `H¹₀` inner product splits into its base and first-derivative coordinates. -/
theorem inner_eq_base_add_sum_deriv (u v : H¹₀(Ω)) :
    inner ℝ u v =
      inner ℝ (baseCoordCLM (n := n) (Ω := Ω) u)
        (baseCoordCLM (n := n) (Ω := Ω) v) +
      ∑ i : Fin n,
        inner ℝ (derivCoordCLM (n := n) (Ω := Ω) i u)
          (derivCoordCLM (n := n) (Ω := Ω) i v) := by
  let U : WkpAmbientOn n 1 2 Ω :=
    ((h10SubtypeL (n := n) (Ω := Ω) u : H¹(Ω)) :
      WkpAmbientOn n 1 2 Ω)
  let W : WkpAmbientOn n 1 2 Ω :=
    ((h10SubtypeL (n := n) (Ω := Ω) v : H¹(Ω)) :
      WkpAmbientOn n 1 2 Ω)
  change
    inner ℝ U W =
      inner ℝ (U (baseIndex n 1)) (W (baseIndex n 1)) +
        ∑ i : Fin n,
          inner ℝ (U (singleDerivIndex (n := n) i))
            (W (singleDerivIndex (n := n) i))
  exact ambient_inner_eq_base_add_sum_deriv (n := n) (Ω := Ω) U W

end Decomposition

section Gradient

local notation "Ambient" => WkpAmbientOn n 1 2 Ω
local notation "μ" => domainMeasure n Ω

/-- The squared `L²` norm of the vector-valued weak gradient is the sum of
the squared `L²` norms of the weak partial derivatives. This identity respects
the almost-everywhere representatives used by `Lp`. -/
theorem norm_wkpGradientCLM_sq_eq_sum_deriv_sq (u : H¹(Ω)) :
    ‖∇ u‖ ^ 2 =
      ∑ i : Fin n, ‖(u : Ambient) (singleDerivIndex (n := n) i)‖ ^ 2 := by
  let d (i : Fin n) := (u : Ambient) (singleDerivIndex (n := n) i)
  have hint (i : Fin n) :
      Integrable (fun x ↦ ‖d i x‖ ^ 2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      (L2.integrable_inner (𝕜 := ℝ) (d i) (d i))
  calc
    ‖∇ u‖ ^ 2 =
        ∫ x, ‖∇ u x‖ ^ 2 ∂μ := by
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ)
          (∇ u) (∇ u))
    _ = ∫ x, ∑ i : Fin n, ‖d i x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [wkpGradientCLM_apply_ae u] with x hx
      simp only [EuclideanSpace.norm_sq_eq, hx, d]
    _ = ∑ i : Fin n, ∫ x, ‖d i x‖ ^ 2 ∂μ :=
      integral_finsetSum _ fun i _ ↦ hint i
    _ = ∑ i : Fin n, ‖d i‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [real_inner_self_eq_norm_sq] using
        (L2.inner_def (𝕜 := ℝ) (d i) (d i)).symm

/-- The weak-gradient map has norm at most one for the full `H¹` norm. -/
theorem norm_wkpGradientCLM_apply_le (u : H¹(Ω)) :
    ‖∇ u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  calc
    ‖∇ u‖ ^ 2 =
        ∑ i : Fin n, ‖(u : Ambient) (singleDerivIndex (n := n) i)‖ ^ 2 :=
      norm_wkpGradientCLM_sq_eq_sum_deriv_sq u
    _ ≤ ‖(u : Ambient) (baseIndex n 1)‖ ^ 2 +
        ∑ i : Fin n, ‖(u : Ambient) (singleDerivIndex (n := n) i)‖ ^ 2 :=
      le_add_of_nonneg_left (sq_nonneg _)
    _ = ‖u‖ ^ 2 := (ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (u : Ambient)).symm

/-- The weak gradient on `H¹₀` is the restriction of the `H¹` gradient. -/
noncomputable def gradientCLM : H¹₀(Ω) →L[ℝ] Lp (ℝ^n) 2 μ :=
  (wkpGradientCLM (n := n) (Ω := Ω)).comp (h10SubtypeL (n := n) (Ω := Ω))

/-- Including a zero-boundary field into `H¹` preserves its weak gradient. -/
theorem wkpGradientCLM_h10SubtypeL (u : H¹₀(Ω)) :
    ∇ (h10SubtypeL (n := n) (Ω := Ω) u) =
      gradientCLM (n := n) (Ω := Ω) u :=
  rfl

/-- Each coordinate of the `H¹₀` weak gradient agrees almost everywhere with
the corresponding scalar derivative coordinate. -/
theorem gradientCLM_apply_ae (u : H¹₀(Ω)) :
    ∀ᵐ x ∂μ, ∀ i : Fin n,
      (∇ (u : H¹(Ω))) x i =
        derivCoordCLM (n := n) (Ω := Ω) i u x :=
  wkpGradientCLM_apply_ae (u : H¹(Ω))

/-- The squared gradient norm on `H¹₀` is the sum of the squared norms of its
scalar weak derivative coordinates. -/
theorem norm_gradientCLM_sq_eq_sum_deriv_sq (u : H¹₀(Ω)) :
    ‖∇ (u : H¹(Ω))‖ ^ 2 =
      ∑ i : Fin n, ‖derivCoordCLM (n := n) (Ω := Ω) i u‖ ^ 2 :=
  norm_wkpGradientCLM_sq_eq_sum_deriv_sq (u : H¹(Ω))

/-- The weak-gradient map has norm at most one for the full `H¹₀` norm. -/
theorem gradientCLM_norm_le (u : H¹₀(Ω)) :
    ‖∇ (u : H¹(Ω))‖ ≤ ‖u‖ :=
  norm_wkpGradientCLM_apply_le (u : H¹(Ω))

end Gradient

section TestFunctions

/-- The base coordinate of a canonical smooth test function is represented by the test
function itself. -/
theorem baseCoordCLM_testFunction_apply_ae
    (φ : TestFunctionOn n Ω) :
    (baseCoordCLM (n := n) (Ω := Ω)
        (testFunctionToH10 (n := n) (Ω := Ω) φ) : ℝ^n → ℝ) =ᵐ[
      domainMeasure n Ω] φ.1.toFun := by
  rw [baseCoordCLM_apply, testFunctionToH10_coe]
  simpa [testFunctionToH1,
    GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
    (mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport
      (baseIndex n 1))

/-- A derivative coordinate of a canonical smooth test function is represented by the
corresponding classical partial derivative. -/
theorem derivCoordCLM_testFunction_apply_ae
    (i : Fin n) (φ : TestFunctionOn n Ω) :
    (derivCoordCLM (n := n) (Ω := Ω) i
        (testFunctionToH10 (n := n) (Ω := Ω) φ) : ℝ^n → ℝ) =ᵐ[
      domainMeasure n Ω]
      fun x ↦ (∂[i] φ.1.toFun) x := by
  rw [derivCoordCLM_apply, testFunctionToH10_coe]
  simpa [testFunctionToH1,
    GraphSpace.singleDerivIndex_toList, iteratedPartialDeriv] using
    (mkWkpSpaceOnOfContDiff_apply_ae
      (n := n) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport
      (singleDerivIndex (n := n) i))

/-- A derivative-coordinate inner product against a smooth test function is the integral of
the weak derivative against the corresponding classical derivative. -/
theorem inner_deriv_testFunction_eq_integral
    (u : H¹₀(Ω)) (i : Fin n) (φ : TestFunctionOn n Ω) :
    ⟪derivCoordCLM (n := n) (Ω := Ω) i u,
      derivCoordCLM (n := n) (Ω := Ω) i
        (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, (derivCoordCLM (n := n) (Ω := Ω) i u :
          ℝ^n → ℝ) x * (∂[i] φ.1.toFun) x
        ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [derivCoordCLM_testFunction_apply_ae
    (n := n) (Ω := Ω) i φ] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- A base-coordinate inner product against a smooth test function is the integral
`∫ f φ`. -/
theorem inner_base_testFunction_eq_integral
    (f : DerivLp n 2 Ω) (φ : TestFunctionOn n Ω) :
    ⟪f, baseCoordCLM (n := n) (Ω := Ω)
      (testFunctionToH10 (n := n) (Ω := Ω) φ)⟫_ℝ =
      ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [baseCoordCLM_testFunction_apply_ae
    (n := n) (Ω := Ω) φ] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- On an open domain, `H¹₀(Ω)` is dense in `L²(Ω)` under the base-coordinate inclusion. -/
theorem baseCoordCLM_denseRange
    (hΩopen : IsOpen Ω) :
    DenseRange (baseCoordCLM (n := n) (Ω := Ω)) := by
  change Dense
    (((baseCoordCLM (n := n) (Ω := Ω)).range :
      Submodule ℝ (DerivLp n 2 Ω)) : Set (DerivLp n 2 Ω))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  rw [MeasureTheory.Lp.eq_zero_iff_ae_eq_zero]
  apply (MeasureTheory.ae_restrict_iff' hΩopen.measurableSet).2
  apply hΩopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
  · exact memLp_locallyIntegrableOn_domain (MeasureTheory.Lp.memLp f) (by norm_num)
  · intro g hgSmooth hgCompact hgSupport
    let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
      { toFun := g
        contDiff' := hgSmooth
        hasCompactSupport' := hgCompact
        tsupport_subset' := Set.subset_univ _ }
    let φΩ : TestFunctionOn n Ω := ⟨φ, hgSupport⟩
    have hinner :
        ⟪f, baseCoordCLM (n := n) (Ω := Ω)
          (testFunctionToH10 (n := n) (Ω := Ω) φΩ)⟫_ℝ = 0 := by
      apply Submodule.inner_left_of_mem_orthogonal
        (K := (baseCoordCLM (n := n) (Ω := Ω)).range)
        (v := f)
      · exact ⟨testFunctionToH10 (n := n) (Ω := Ω) φΩ, rfl⟩
      · exact hf
    have hrestricted :
        ∫ x, (f : ℝ^n → ℝ) x * g x ∂domainMeasure n Ω = 0 := by
      rw [inner_base_testFunction_eq_integral] at hinner
      simpa [φΩ, φ] using hinner
    have hzeroOutside :
        ∀ x : ℝ^n, x ∉ Ω → g x • (f : ℝ^n → ℝ) x = 0 := by
      intro x hx
      have hg0 : g x = 0 := by
        by_contra hne
        exact hx (hgSupport (subset_closure hne))
      simp [hg0]
    rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroOutside]
    simpa [domainMeasure, mul_comm] using hrestricted

end TestFunctions

end GraphSpace

end SobolevSpace
