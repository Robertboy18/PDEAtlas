/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.Analysis.Calculus.Gradient.QuadraticGrowth
import PDE.Analysis.MeasureTheory.LocalRepresentative
import PDE.Analysis.MeasureTheory.Lp.IntegralMinimum
import PDE.Analysis.MeasureTheory.Lp.LipschitzSuperposition
import PDE.Analysis.MeasureTheory.Lp.Superposition

/-!
# Local minimizers of gradient energies

## Motivation

What does it mean for a function `u` in `W^{1,2}_loc(Ω)` to minimize
`∫ F(∇u)` on an arbitrary open set `Ω`, and which equation does such a minimizer solve?

## The idea

`u` is a local minimizer on `Ω` if, on every open `V` with compact closure in
`Ω`, adding a smooth function with compact support in `V` does not lower the energy over
`V`. The perturbation may be large. Among the notions that compare `u` with all perturbations
in a class, this is the weakest, since smooth functions with compact support are the smallest
class in use: no boundary values and no global integrability enter. If the gradient of `F` is
Lipschitz, the energy is finite on `W^{1,2}(V)` and can be differentiated along a test function
`φ`.
Fermat's rule gives `∫_V ⟨∇F(∇u), ∇φ⟩ = 0`. The flux `∇F(∇u)` is in `L²(V)`, so the left
side is continuous in `φ` for the `H¹` norm, and the identity extends to all of `H¹₀(V)`.
A local minimizer is therefore a weak solution of `div(∇F(∇u)) = 0` on every such `V`, and
the interior regularity theory for weak solutions on bounded open sets applies on small
balls. Continuous representatives of one function agree on overlaps, so regular
representatives on balls glue to one on all of `Ω`.

## Main results

* `IsLocalMinimizerOn F Ω u` (definition, for every dimension, every set `Ω` and every
  density `F`): local minimality of `∫ F(∇u)` against smooth compactly supported
  perturbations. `IsLocalMinimizerOn.mono` and `IsLocalMinimizerOn.congr_ae` restrict the
  set and change `u` on a null set.
* `integrable_gradientDensity_of_lipschitzWith` (all bounded sets `V`, all differentiable
  `F` with Lipschitz gradient, all `U` in `H¹(V)`): the energy density `F(∇U)` is integrable.
* `integral_inner_gradient_eq_zero_of_forall_testFunction_le` (same scope): if no test
  function on `V` lowers the energy of `U`, then `∫_V ⟨∇F(∇U), ∇w⟩ = 0` for every `w` in
  `H¹₀(V)`.
* `IsLocalMinimizerOn.integral_inner_gradient_eq_zero` (all local minimizers, same `F`):
  this weak Euler–Lagrange equation on every open `V` with compact closure in `Ω`.
* `IsLocalMinimizerOn.exists_ball_weakSolution` (all open `Ω`, all local minimizers in
  `W^{1,2}_loc(Ω)`): around every point there is a ball on which `u` is represented by a
  weak solution.
* `IsLocalMinimizerOn.exists_contDiffOn_ae_eq` (same scope, every order `k`): if weak
  solutions on balls have `C^k` representatives near the centre, then `u` has a `C^k`
  representative on `Ω`.

## Relations

* The first variation is `MeasureTheory.integral_firstVariation_eq_zero_of_affine_min`, used
  with the submodule of test functions.
  `integral_firstVariation_eq_zero_of_mixedWkpIntegral_minimizer` is the same argument for a
  minimizer in a Dirichlet class, where all of `W₀^{1,p}` competes.
* The gluing is `MeasureTheory.exists_contDiffAt_ae_eq_of_locally`.
* `PDE.CalculusOfVariations.LocalMinimizer.Smooth` and
  `PDE.CalculusOfVariations.LocalMinimizer.Holder` apply these results with the regularity
  theorems of the modules under `PDE/Elliptic/Regularity/Quasilinear/Interior/HigherOrder/`.
* `PDE.CalculusOfVariations.LocalMinimizer.Convex` proves the converse of the weak
  Euler–Lagrange equation for convex densities.
* `isLocalMinimizerOn_affine` there and `isLocalMinimizerOn_of_prescribed_boundary` in
  `PDE.CalculusOfVariations.LocalMinimizer.Dirichlet` show that the definition has
  instances: affine functions, and minimizers with prescribed boundary values.
* `IsC1LocalMinimizer` is local in another sense: it compares with the `C²` perturbations that
  vanish on the boundary and are small in `C¹` on the whole domain. Here "local" refers to the
  subdomains `V`, and the perturbations may be large.

## What stays open

The density depends on the gradient only, the unknown is scalar and the exponent is `2`.
The energy in the definition is a Bochner integral, which is `0` when `F(∇U)` is not
integrable on `V`. The definition has its intended meaning when `F` has quadratic growth,
for instance when its gradient is Lipschitz, which is the case in all theorems here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.3, Theorem 4, for the weak Euler–Lagrange
  equation of a minimizer, and §8.3 for the regularity argument that starts from it.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω Ω' V : Set (ℝ^n)} {F : ℝ^n → ℝ} {u v : ℝ^n → ℝ}

/-- `u` is a local minimizer of `∫ F(∇u)` on `Ω`: on every open `V` with compact closure
in `Ω`, every `W^{1,2}(V)` element that represents `u` has no more energy than its
perturbation by any smooth function with compact support in `V`.

The perturbations may be large, and they are the smallest class in use, so among the notions
that compare with all perturbations in a class this is the weakest. Nothing is asked of `u`
outside such sets `V`, and `Ω` need not be bounded.

The predicate does not say that `u` is in `W^{1,2}_loc(Ω)`: on a set `V` where `u` has no
representative in `W^{1,2}(V)` it asks nothing. It does not say that the energies are finite
either: the integrals are Bochner integrals, which are `0` for a density that is not
integrable. The regularity theorems assume `IsLocallyWkpOn 1 2 Ω u` and a density with
Lipschitz gradient, for which every energy is finite
(`integrable_gradientDensity_of_lipschitzWith`). -/
def IsLocalMinimizerOn (F : ℝ^n → ℝ) (Ω : Set (ℝ^n)) (u : ℝ^n → ℝ) : Prop :=
  ∀ V : Set (ℝ^n), IsOpen V → IsCompact (closure V) → closure V ⊆ Ω →
    ∀ U : W^{1,2}(V), baseRepresentative U =ᵐ[domainMeasure n V] u →
      ∀ φ : TestFunctionOn n V,
        (∫ x, F (∇ U x) ∂domainMeasure n V) ≤
          ∫ x, F (∇ (U + testFunctionToWkp φ) x) ∂domainMeasure n V

/-- A local minimizer on `Ω` is a local minimizer on every subset of `Ω`. -/
theorem IsLocalMinimizerOn.mono (h : IsLocalMinimizerOn F Ω u) (hsub : Ω' ⊆ Ω) :
    IsLocalMinimizerOn F Ω' u :=
  fun V hV hVc hVΩ ↦ h V hV hVc (hVΩ.trans hsub)

/-- Local minimality depends only on the almost-everywhere class of the function on `Ω`. -/
theorem IsLocalMinimizerOn.congr_ae (h : IsLocalMinimizerOn F Ω u)
    (huv : u =ᵐ[domainMeasure n Ω] v) : IsLocalMinimizerOn F Ω v :=
  fun V hV hVc hVΩ U hU ↦ h V hV hVc hVΩ U
    (hU.trans (ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ) huv.symm))

section FirstVariation

variable {C : ℝ≥0}

/-- **The energy is finite on `H¹`.** On a bounded set `V`, the energy density `F(∇U)` of
every `U` in `H¹(V)` is integrable when `F` is differentiable with Lipschitz gradient. Such
an `F` grows at most quadratically, and `∇U` is square integrable. No convexity is used. -/
theorem integrable_gradientDensity_of_lipschitzWith (hV : Bornology.IsBounded V)
    (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F)) (U : H¹(V)) :
    Integrable (fun x ↦ F (∇ U x)) (domainMeasure n V) := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hV
  exact (Lp.memLp (∇ U)).integrable_comp_of_norm_rpow_le two_ne_zero ENNReal.ofNat_ne_top
    (G := fun _ z ↦ F z) (hF.continuous.measurable.comp measurable_snd)
    (integrable_const (|F 0| + ‖fderiv ℝ F 0‖ ^ 2))
    (ae_of_all _ fun _ z ↦ by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two] using
        abs_le_quadratic_of_lipschitzWith_fderiv hF (lipschitzWith_fderiv_of_gradient hLip) z)

/-- **Weak Euler–Lagrange equation from minimality against test functions.** Let `V` be
bounded, let `F` be differentiable with Lipschitz gradient, and let `U` be in `H¹(V)`. If no
smooth function with compact support in `V` lowers the energy `∫_V F(∇U)`, then
`∫_V ⟨∇F(∇U), ∇w⟩ = 0` for every `w` in `H¹₀(V)`.

No convexity is used. The energy is differentiated along each test function, which gives
the identity for test functions. The flux `∇F(∇U)` is in `L²(V)`, so the identity is closed
under `H¹` limits, and test functions are dense in `H¹₀(V)`. -/
theorem integral_inner_gradient_eq_zero_of_forall_testFunction_le
    (hV : Bornology.IsBounded V) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (U : H¹(V))
    (hmin : ∀ φ : TestFunctionOn n V,
      (∫ x, F (∇ U x) ∂domainMeasure n V) ≤
        ∫ x, F (∇ (U + testFunctionToWkp φ) x) ∂domainMeasure n V)
    (w : H¹₀(V)) :
    (∫ x, ⟪∇ F (∇ U x), ∇ (w : H¹(V)) x⟫ ∂domainMeasure n V) = 0 := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hV
  -- The derivative of `F` is Lipschitz, so it grows linearly.
  have hLip' : LipschitzWith C (fderiv ℝ F) := lipschitzWith_fderiv_of_gradient hLip
  have hgrowth (z : ℝ^n) : ‖fderiv ℝ F z‖ ≤ ‖fderiv ℝ F 0‖ + C * ‖z‖ :=
    norm_le_norm_zero_add_mul_of_lipschitzWith hLip' z
  have hFm : Measurable (Function.uncurry fun (_ : ℝ^n) (z : ℝ^n) ↦ F z) :=
    hF.continuous.measurable.comp measurable_snd
  have hdFm : Measurable (fun z : (ℝ^n) × (ℝ^n) × (ℝ^n) ↦ fderiv ℝ F z.2.1 z.2.2) :=
    ((hLip'.continuous.comp (continuous_fst.comp continuous_snd)).clm_apply
      (continuous_snd.comp continuous_snd)).measurable
  -- Fermat's rule along each test function.
  have hexp : (2 : ℝ≥0∞).toReal - 1 = 1 := by
    rw [ENNReal.toReal_ofNat]
    norm_num
  have hfirst (φ : TestFunctionOn n V) :
      (∫ x, ⟪∇ F (∇ U x), ∇ (testFunctionToWkp φ : H¹(V)) x⟫ ∂domainMeasure n V) = 0 := by
    have h := (integral_firstVariation_eq_zero_of_affine_min
      (μ := domainMeasure n V) (p := 2) (q := 2)
      (wkpGradientCLM (n := n) (p := 2) (Ω := V)).toLinearMap
      (LinearMap.range (testFunctionToWkpLinear (n := n) (k := 1) (p := 2) (Ω := V)))
      ENNReal.ofNat_ne_top (F := fun _ z ↦ F z) (dF := fun _ z ↦ fderiv ℝ F z)
      (h := fun _ ↦ ‖fderiv ℝ F 0‖) (C := C) hFm hdFm
      (ae_of_all _ fun _ z ↦ (hF z).hasFDerivAt) (memLp_const _)
      (ae_of_all _ fun _ z ↦ by simpa only [hexp, Real.rpow_one] using hgrowth z)
      U U (by simp) (integrable_gradientDensity_of_lipschitzWith hV hF hLip U)
      (fun W hW ↦ by
        obtain ⟨ψ, hψ⟩ := hW
        obtain rfl : W = U + testFunctionToWkp ψ := sub_eq_iff_eq_add'.mp hψ.symm
        exact hmin ψ)
      (testFunctionToWkp φ) ⟨φ, rfl⟩).2
    calc
      (∫ x, ⟪∇ F (∇ U x), ∇ (testFunctionToWkp φ : H¹(V)) x⟫ ∂domainMeasure n V) =
          ∫ x, fderiv ℝ F (∇ U x) (∇ (testFunctionToWkp φ : H¹(V)) x) ∂domainMeasure n V := by
        simp only [inner_gradient_left]
      _ = 0 := h
  -- The flux is in `L²`, so the pairing is continuous on `H¹(V)` and passes to `H¹₀(V)`.
  obtain ⟨q, hq⟩ : ∃ q : Lp (ℝ^n) 2 (domainMeasure n V),
      q =ᵐ[domainMeasure n V] fun x ↦ ∇ F (∇ U x) :=
    ⟨_, (hLip.comp_memLp_of_memLp_const (memLp_const _) (Lp.memLp (∇ U))).coeFn_toLp⟩
  have hpair (W : H¹(V)) :
      (∫ x, ⟪∇ F (∇ U x), ∇ W x⟫ ∂domainMeasure n V) = ⟪q, ∇ W⟫ := by
    rw [L2.inner_def]
    exact integral_congr_ae (hq.mono fun x hx ↦ congrArg (fun z ↦ ⟪z, ∇ W x⟫) hx.symm)
  have hclosed : IsClosed {W : H¹(V) | ⟪q, ∇ W⟫ = 0} :=
    isClosed_eq (continuous_const.inner (wkpGradientCLM (n := n) (p := 2) (Ω := V)).continuous)
      continuous_const
  have hw : ⟪q, ∇ (w : H¹(V))⟫ = 0 :=
    Wkp0SpaceOn.closed_property_of_testFunctions hclosed
      (fun φ ↦ (hpair _).symm.trans (hfirst φ)) w
  rw [hpair, hw]

/-- **Weak Euler–Lagrange equation of a local minimizer.** Let `F` be differentiable with
Lipschitz gradient and let `u` be a local minimizer of `∫ F(∇u)` on `Ω`. On every open `V`
with compact closure in `Ω`, every `U` in `H¹(V)` that represents `u` satisfies
`∫_V ⟨∇F(∇U), ∇w⟩ = 0` for every `w` in `H¹₀(V)`.

This is the hypothesis of the interior regularity theorems for weak solutions. It is
`integral_inner_gradient_eq_zero_of_forall_testFunction_le` on the set `V`. -/
theorem IsLocalMinimizerOn.integral_inner_gradient_eq_zero (hmin : IsLocalMinimizerOn F Ω u)
    (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (U : H¹(V)) (hU : baseRepresentative U =ᵐ[domainMeasure n V] u) (w : H¹₀(V)) :
    (∫ x, ⟪∇ F (∇ U x), ∇ (w : H¹(V)) x⟫ ∂domainMeasure n V) = 0 :=
  integral_inner_gradient_eq_zero_of_forall_testFunction_le
    (hVc.isBounded.subset subset_closure) hF hLip U (hmin V hV hVc hVΩ U hU) w

/-- Around every point of an open set `Ω`, a local minimizer in `W^{1,2}_loc(Ω)` is
represented on a ball inside `Ω` by an `H¹` function that solves the weak Euler–Lagrange
equation there. The density is differentiable with Lipschitz gradient.

All local statements about minimizers start from this ball. -/
theorem IsLocalMinimizerOn.exists_ball_weakSolution (hmin : IsLocalMinimizerOn F Ω u)
    (hΩ : IsOpen Ω) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (hu : IsLocallyWkpOn 1 2 Ω u) {x : ℝ^n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧ ∃ U : H¹(ball x r),
      baseRepresentative U =ᵐ[domainMeasure n (ball x r)] u ∧
      ∀ w : H¹₀(ball x r),
        (∫ y, ⟪∇ F (∇ U y), ∇ (w : H¹(ball x r)) y⟫ ∂domainMeasure n (ball x r)) = 0 := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.mp hΩ x hx
  have hcl : closure (ball x (ε / 2)) ⊆ Ω :=
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball (by linarith))).trans hεΩ
  have hc : IsCompact (closure (ball x (ε / 2))) :=
    (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  obtain ⟨U, hU⟩ := hu _ isOpen_ball hc hcl
  exact ⟨ε / 2, by positivity, subset_closure.trans hcl, U, hU,
    hmin.integral_inner_gradient_eq_zero hF hLip isOpen_ball hc hcl U hU⟩

/-- **Local regularity glues.** Let `u` be a local minimizer in `W^{1,2}_loc(Ω)` on an open
set `Ω`, for a differentiable density with Lipschitz gradient. Suppose that every weak
solution on a ball has a `C^k` representative on a neighbourhood of the centre. Then `u`
has a representative that is `C^k` on all of `Ω`.

The hypothesis `hreg` is what an interior regularity theorem for weak solutions on bounded
open sets provides. Continuous representatives agree on overlaps of open sets, so the local
ones define one function. -/
theorem IsLocalMinimizerOn.exists_contDiffOn_ae_eq {k : WithTop ℕ∞}
    (hmin : IsLocalMinimizerOn F Ω u) (hΩ : IsOpen Ω) (hF : Differentiable ℝ F)
    (hLip : LipschitzWith C (∇ F)) (hu : IsLocallyWkpOn 1 2 Ω u)
    (hreg : ∀ (x : ℝ^n) (r : ℝ), 0 < r → ∀ U : H¹(ball x r),
      (∀ w : H¹₀(ball x r),
        (∫ y, ⟪∇ F (∇ U y), ∇ (w : H¹(ball x r)) y⟫ ∂domainMeasure n (ball x r)) = 0) →
      ∃ N : Set (ℝ^n), IsOpen N ∧ x ∈ N ∧ N ⊆ ball x r ∧ ∃ v : ℝ^n → ℝ,
        ContDiffOn ℝ k v N ∧ v =ᵐ[volume.restrict N] baseRepresentative U) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ k v Ω ∧ v =ᵐ[volume.restrict Ω] u := by
  obtain ⟨v, hv, hvu⟩ := MeasureTheory.exists_contDiffAt_ae_eq_of_locally
    (𝕜 := ℝ) (μ := volume) (Ω := Ω) (f := u) (k := k) (fun x hx ↦ by
      obtain ⟨r, hr, hrΩ, U, hU, hweak⟩ := hmin.exists_ball_weakSolution hΩ hF hLip hu hx
      obtain ⟨N, hN, hxN, hNr, w, hw, hwU⟩ := hreg x r hr U hweak
      exact ⟨N, hN, hxN, hNr.trans hrΩ, w, hw,
        hwU.trans (ae_restrict_of_ae_restrict_of_subset hNr hU)⟩)
  exact ⟨v, fun x hx ↦ (hv x hx).contDiffWithinAt, hvu⟩

end FirstVariation

end PDE.CalculusOfVariations
