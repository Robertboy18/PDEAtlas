/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.LocalMinimizer.Basic
public import PDE.FDeriv.Operators
import PDE.Analysis.Calculus.Gradient.HessianNorm
import PDE.Analysis.Calculus.Gradient.QuadraticGrowth
import PDE.Analysis.Convex.Differentiable.Supporting
import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
import PDE.FDeriv.Calculus
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Calculus.Differentiation.GradientRepresentative
import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Local minimizers of convex gradient energies

## Motivation

Is every weak solution of the Euler–Lagrange equation of `∫ F(∇u)` a local
minimizer, and are there local minimizers at all?

## The idea

For a convex density the answer to the first question is yes. A convex
differentiable `F` lies above its tangent planes: `F(p + ξ) ≥ F(p) + ⟨∇F(p), ξ⟩`. With
`p = ∇U` and `ξ = ∇W`, integration over a bounded set `V` gives
`∫_V F(∇(U + W)) ≥ ∫_V F(∇U) + ∫_V ⟨∇F(∇U), ∇W⟩`. If `U` is a weak solution the last
integral vanishes for every `W` in `H¹₀(V)`, so no such `W` lowers the energy. This also
shows that minimality against test functions, which is the definition, already gives
minimality against all of `H¹₀(V)`. A `C¹` function whose flux `∇F(∇v)` is `C¹` and
divergence-free is a weak solution by integration by parts, so it is a local minimizer.
Affine functions have a constant flux, and this gives local minimizers for every convex
density with Lipschitz gradient on every set.

## Main results

* `integral_add_integral_inner_gradient_le` (all bounded `V`, all convex differentiable `F`
  with Lipschitz gradient, all `U`, `W` in `H¹(V)`): the tangent-plane inequality for the
  energy.
* `isLocalMinimizerOn_iff_integral_inner_gradient_eq_zero` (all sets `Ω`, same `F`): `u` is
  a local minimizer on `Ω` if and only if its representatives solve the weak
  Euler–Lagrange equation on every open `V` with compact closure in `Ω`.
* `IsLocalMinimizerOn.integral_le_integral_add` (same scope): a local minimizer has no more
  energy than any perturbation by an element of `H¹₀(V)`.
* `isLocalMinimizerOn_of_divergence_eq_zero` (all open `Ω`, same `F`, all `v` in `C¹(Ω)`
  with `C¹` flux): if `div(∇F(∇v)) = 0` at every point of `Ω`, then `v` is a local
  minimizer. `isLocalMinimizerOn_of_contDiffOn_two` is the case of a convex `C²` density
  with bounded Hessian and `v` in `C²(Ω)`.
* `isLocalMinimizerOn_affine` (all sets `Ω`, same `F`, all affine functions) and
  `isLocalMinimizerOn_affine_of_quadratic_bounds` (all `C²` densities with
  `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²`, `θ > 0`): affine functions are local minimizers and
  belong to `W^{1,2}_loc(Ω)`.

## Relations

* `IsLocalMinimizerOn.integral_inner_gradient_eq_zero` is one direction of the equivalence.
  The other direction needs convexity.
* `PDE.Analysis.fderiv_apply_sub_le_sub_of_convex` is the tangent-plane inequality, and
  `hasWeakDerivativeOn_of_contDiffAt_one` is the integration by parts.
* `isLocalMinimizerOn_affine_of_quadratic_bounds` shows that the hypotheses of
  `exists_holder_gradient_of_isLocalMinimizerOn`, `exists_classical_of_isLocalMinimizerOn`
  and `exists_smooth_of_isLocalMinimizerOn` hold for every density of their class, on every
  open set.
* `isLocalMinimizerOn_of_contDiffOn_two` is the converse of
  `exists_classical_of_isLocalMinimizerOn`. It is combined with
  `exists_smooth_of_isLocalMinimizerOn` in `isLocalMinimizerOn_iff_exists_smooth` of
  `PDE.CalculusOfVariations.LocalMinimizer.Smooth`.

## What stays open

Without convexity a weak solution need not be a local minimizer, and nothing is said about
that case. The second variation is not used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, for weak solutions of the Euler–Lagrange
  equation and the role of convexity.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω V : Set (ℝ^n)} {F : ℝ^n → ℝ} {u : ℝ^n → ℝ} {C : ℝ≥0}

/-- **Tangent-plane inequality for the energy.** Let `V` be bounded and let `F` be convex
and differentiable with Lipschitz gradient. For all `U` and `W` in `H¹(V)`,
`∫_V F(∇U) + ∫_V ⟨∇F(∇U), ∇W⟩ ≤ ∫_V F(∇(U + W))`.

This is the pointwise inequality `F(p) + ⟨∇F(p), ξ⟩ ≤ F(p + ξ)` of a convex function,
integrated. All three integrands are integrable because `F` grows at most quadratically
and the flux `∇F(∇U)` is in `L²`. -/
theorem integral_add_integral_inner_gradient_le (hV : Bornology.IsBounded V)
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (U W : H¹(V)) :
    (∫ x, F (∇ U x) ∂domainMeasure n V) +
        (∫ x, ⟪∇ F (∇ U x), ∇ W x⟫ ∂domainMeasure n V) ≤
      ∫ x, F (∇ (U + W) x) ∂domainMeasure n V := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hV
  have hint₁ := integrable_gradientDensity_of_lipschitzWith hV hF hLip U
  have hint₂ := integrable_gradientDensity_of_lipschitzWith hV hF hLip (U + W)
  have hmem : MemLp (fun x ↦ ∇ F (∇ U x)) 2 (domainMeasure n V) :=
    hLip.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp (∇ U))
  have hint₃ : Integrable (fun x ↦ ⟪∇ F (∇ U x), ∇ W x⟫) (domainMeasure n V) :=
    (L2.integrable_inner (𝕜 := ℝ) (hmem.toLp _) (∇ W)).congr
      (hmem.coeFn_toLp.mono fun x hx ↦ congrArg (fun z ↦ ⟪z, ∇ W x⟫) hx)
  have hadd : (∇ (U + W) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n V] fun x ↦ ∇ U x + ∇ W x := by
    rw [map_add]
    exact Lp.coeFn_add (∇ U) (∇ W)
  rw [← integral_add hint₁ hint₃]
  refine integral_mono_ae (hint₁.add hint₃) hint₂ ?_
  filter_upwards [hadd] with x hx
  have h := fderiv_apply_sub_le_sub_of_convex hconv (hF (∇ U x)).hasFDerivAt
    (∇ U x + ∇ W x) (mem_univ _) (mem_univ _)
  rw [add_sub_cancel_left] at h
  rw [hx, inner_gradient_left]
  linarith

/-- For a convex density, a function whose representatives solve the weak Euler–Lagrange
equation against test functions is a local minimizer. Here `F` is convex and
differentiable with Lipschitz gradient, and `Ω` is any set. -/
theorem isLocalMinimizerOn_of_integral_inner_gradient_eq_zero (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (h : ∀ V : Set (ℝ^n), IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
      ∀ U : H¹(V), baseRepresentative U =ᵐ[domainMeasure n V] u →
        ∀ φ : TestFunctionOn n V,
          (∫ x, ⟪∇ F (∇ U x), ∇ (testFunctionToWkp φ : H¹(V)) x⟫ ∂domainMeasure n V) = 0) :
    IsLocalMinimizerOn F Ω u := fun V hV hVc hVΩ U hU φ ↦ by
  have hle := integral_add_integral_inner_gradient_le (hVc.isBounded.subset subset_closure)
    hconv hF hLip U (testFunctionToWkp φ)
  rwa [h V hV hVc hVΩ U hU φ, add_zero] at hle

/-- **For convex densities, local minimizers are the weak solutions.** Let `F` be convex
and differentiable with Lipschitz gradient, and let `Ω` be any set. Then `u` is a local
minimizer of `∫ F(∇u)` on `Ω` if and only if, on every open `V` with compact closure in
`Ω`, every `U` in `H¹(V)` that represents `u` satisfies `∫_V ⟨∇F(∇U), ∇w⟩ = 0` for all `w`
in `H¹₀(V)`.

The forward direction is the first variation and holds without convexity. The converse is
the tangent-plane inequality. -/
theorem isLocalMinimizerOn_iff_integral_inner_gradient_eq_zero (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F)) :
    IsLocalMinimizerOn F Ω u ↔
      ∀ V : Set (ℝ^n), IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
        ∀ U : H¹(V), baseRepresentative U =ᵐ[domainMeasure n V] u → ∀ w : H¹₀(V),
          (∫ x, ⟪∇ F (∇ U x), ∇ (w : H¹(V)) x⟫ ∂domainMeasure n V) = 0 :=
  ⟨fun h _ hV hVc hVΩ U hU w ↦ h.integral_inner_gradient_eq_zero hF hLip hV hVc hVΩ U hU w,
    fun h ↦ isLocalMinimizerOn_of_integral_inner_gradient_eq_zero hconv hF hLip
      fun V hV hVc hVΩ U hU φ ↦ h V hV hVc hVΩ U hU (testFunctionToWkp0 φ)⟩

/-- **For convex densities, all of `H¹₀(V)` may compete.** Let `F` be convex and
differentiable with Lipschitz gradient, and let `u` be a local minimizer on `Ω`. On every
open `V` with compact closure in `Ω`, a representative `U` of `u` has no more energy than
`U + w`, for every `w` in `H¹₀(V)`.

The definition only compares with smooth compactly supported perturbations. The weak
equation extends to `H¹₀(V)` by density, and the tangent-plane inequality does the rest. -/
theorem IsLocalMinimizerOn.integral_le_integral_add (hmin : IsLocalMinimizerOn F Ω u)
    (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (U : H¹(V)) (hU : baseRepresentative U =ᵐ[domainMeasure n V] u) (w : H¹₀(V)) :
    (∫ x, F (∇ U x) ∂domainMeasure n V) ≤
      ∫ x, F (∇ (U + (w : H¹(V))) x) ∂domainMeasure n V := by
  have hle := integral_add_integral_inner_gradient_le (hVc.isBounded.subset subset_closure)
    hconv hF hLip U (w : H¹(V))
  rwa [hmin.integral_inner_gradient_eq_zero hF hLip hV hVc hVΩ U hU w, add_zero] at hle

/-- **Classical solutions are local minimizers.** Let `Ω` be open and let `F` be convex and
differentiable with Lipschitz gradient. Let `v` be `C¹` on `Ω` with a flux `∇F(∇v)` that is
`C¹` on `Ω`. If `div(∇F(∇v)) = 0` at every point of `Ω`, then `v` is a local minimizer of
`∫ F(∇u)` on `Ω`.

On an open `V` inside `Ω`, each flux component has its classical derivative as weak
derivative. Summing these identities against a test function gives the weak equation, and
`isLocalMinimizerOn_of_integral_inner_gradient_eq_zero` applies. -/
theorem isLocalMinimizerOn_of_divergence_eq_zero (hΩ : IsOpen Ω) (hconv : ConvexOn ℝ univ F)
    (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F)) {v : ℝ^n → ℝ}
    (hv : ContDiffOn ℝ 1 v Ω) (hflux : ContDiffOn ℝ 1 (fun y ↦ ∇ F (∇ v y)) Ω)
    (hdiv : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0) :
    IsLocalMinimizerOn F Ω v := by
  refine isLocalMinimizerOn_of_integral_inner_gradient_eq_zero hconv hF hLip
    fun V hV hVc hVΩ U hU φ ↦ ?_
  have hVΩ' : V ⊆ Ω := subset_closure.trans hVΩ
  -- Each flux component has its classical partial derivative as weak derivative on `V`.
  have hw (i : Fin n) : HasWeakDerivativeOn V [i] (fun y ↦ ∇ F (∇ v y) i)
      (∂[i] (fun y ↦ ∇ F (∇ v y) i)) :=
    hasWeakDerivativeOn_of_contDiffAt_one hV
      (fun x hx ↦ ((contDiffOn_piLp 2).mp hflux i).contDiffAt (hΩ.mem_nhds (hVΩ' hx))) i
  -- The weak gradients are the classical ones, so the pairing is a sum over coordinates.
  have hsum : (∫ x, ⟪∇ F (∇ U x), ∇ (testFunctionToWkp φ : H¹(V)) x⟫ ∂domainMeasure n V) =
      ∑ i, ∫ x, ∇ F (∇ v x) i * (∂[i] φ.1.toFun) x ∂domainMeasure n V := by
    rw [← integral_finsetSum _ fun i _ ↦ by
      simpa only [iteratedPartialDeriv] using
        (hw i).integrable_mul_iteratedPartialDeriv φ.1 φ.2]
    refine integral_congr_ae ?_
    filter_upwards [wkpGradientCLM_ae_eq_gradient_of_contDiffOn hV U (hv.mono hVΩ') hU,
      wkpGradientCLM_testFunctionToWkp_ae (p := 2) φ] with x hx hφ
    rw [hx, hφ, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [gradient_apply_eq_partialDeriv φ.1.toFun x i]
    simp only [RCLike.inner_apply, RCLike.conj_to_real, mul_comm]
  -- Integration by parts in each coordinate.
  have hparts (i : Fin n) :
      (∫ x, ∇ F (∇ v x) i * (∂[i] φ.1.toFun) x ∂domainMeasure n V) =
        -∫ x, (∂[i] (fun y ↦ ∇ F (∇ v y) i)) x * φ.1.toFun x ∂domainMeasure n V := by
    simpa [iteratedPartialDeriv] using hw i φ.1 φ.2
  rw [hsum, Finset.sum_congr rfl fun i _ ↦ hparts i, Finset.sum_neg_distrib, neg_eq_zero,
    ← integral_finsetSum _ fun i _ ↦ (hw i).integrable_mul_testFunction φ.1 φ.2]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
  have h0 : ∑ i, (∂[i] (fun y ↦ ∇ F (∇ v y) i)) x = 0 := hdiv x (hVΩ' hx)
  rw [← Finset.sum_mul, h0, zero_mul, Pi.zero_apply]

/-- **Converse of classical regularity.** Let `Ω` be open and let `F` be convex and `C²`
with bounded Hessian. Every `v` in `C²(Ω)` that solves `div(∇F(∇v)) = 0` at every point of
`Ω` is a local minimizer of `∫ F(∇u)` on `Ω`. The flux `∇F(∇v)` is `C¹`, so this is
`isLocalMinimizerOn_of_divergence_eq_zero`. -/
theorem isLocalMinimizerOn_of_contDiffOn_two (hΩ : IsOpen Ω) (hconv : ConvexOn ℝ univ F)
    (hF : ContDiff ℝ 2 F) {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hdiv : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0) :
    IsLocalMinimizerOn F Ω v := by
  have hgrad : ContDiffOn ℝ 1 (∇ v) Ω := by
    apply contDiffOn_piLp' 2
    intro i x hx
    simpa only [gradient_apply_eq_partialDeriv, Nat.cast_one] using
      (contDiffAt_partialDeriv 1 (hv.contDiffAt (hΩ.mem_nhds hx)) i).contDiffWithinAt
  exact isLocalMinimizerOn_of_divergence_eq_zero hΩ hconv (hF.differentiable (by norm_num))
    (lipschitzWith_gradient_of_hessian_bound hF hbound) (hv.of_le (by norm_num))
    ((contDiff_gradient_of_contDiff_two hF).comp_contDiffOn hgrad) hdiv

/-- **Affine functions are local minimizers.** Let `F` be convex and differentiable with
Lipschitz gradient. For every vector `a`, every constant `c` and every set `Ω`, the function
`x ↦ ⟨a, x⟩ + c` is a local minimizer of `∫ F(∇u)` on `Ω`.

Its gradient is the constant `a`, so its flux `∇F(a)` is constant and divergence-free.
This gives a local minimizer for every density of the class and every `Ω`. -/
theorem isLocalMinimizerOn_affine (hconv : ConvexOn ℝ univ F) (hF : Differentiable ℝ F)
    (hLip : LipschitzWith C (∇ F)) (a : ℝ^n) (c : ℝ) (Ω : Set (ℝ^n)) :
    IsLocalMinimizerOn F Ω (fun x ↦ ⟪a, x⟫ + c) := by
  have hgrad (y : ℝ^n) : ∇ (fun x : ℝ^n ↦ ⟪a, x⟫ + c) y = a :=
    (hasGradientAt_iff_hasFDerivAt.mpr ((innerSL ℝ a).hasFDerivAt.add_const c)).gradient
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ^n ↦ ⟪a, x⟫ + c) :=
    (innerSL ℝ a).contDiff.add contDiff_const
  refine (isLocalMinimizerOn_of_divergence_eq_zero isOpen_univ hconv hF hLip
    hsmooth.contDiffOn ?_ fun x _ ↦ ?_).mono (subset_univ Ω)
  · simp only [hgrad]
    exact contDiffOn_const
  · simp [PDE.divergence, hgrad]

variable {θ Λ : ℝ}

/-- **The regularity theorems have instances.** Let `F` be `C²` with
`θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where `θ > 0`. For every vector `a`,
every constant `c` and every set `Ω`, the function `x ↦ ⟨a, x⟩ + c` is in `W^{1,2}_loc(Ω)`
and is a local minimizer of `∫ F(∇u)` on `Ω`.

So the hypotheses on `u` in `exists_holder_gradient_of_isLocalMinimizerOn`,
`exists_classical_of_isLocalMinimizerOn` and `exists_smooth_of_isLocalMinimizerOn` hold for
every density of their class. The density is uniformly convex with Lipschitz gradient, so
this is `isLocalMinimizerOn_affine`. -/
theorem isLocalMinimizerOn_affine_of_quadratic_bounds (hF : ContDiff ℝ 2 F) (hθ : 0 < θ)
    (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2)
    (a : ℝ^n) (c : ℝ) (Ω : Set (ℝ^n)) :
    IsLocallyWkpOn 1 2 Ω (fun x ↦ ⟪a, x⟫ + c) ∧
      IsLocalMinimizerOn F Ω (fun x ↦ ⟪a, x⟫ + c) := by
  have hsmooth : ContDiff ℝ 1 (fun x : ℝ^n ↦ ⟪a, x⟫ + c) :=
    (innerSL ℝ a).contDiff.add contDiff_const
  exact ⟨(isLocallyWkpOn_of_contDiffOn isOpen_univ hsmooth.contDiffOn 2).mono (subset_univ Ω),
    isLocalMinimizerOn_affine
      ((strongConvexOn_of_hessian_bound hF hell).strictConvexOn hθ).convexOn
      (hF.differentiable (by norm_num))
      (lipschitzWith_gradient_of_hessian_bound hF fun p ↦
        norm_hessian_le_of_quadratic_le hF.contDiffAt hθ.le (hell p) (hbound p)) a c Ω⟩

end PDE.CalculusOfVariations
