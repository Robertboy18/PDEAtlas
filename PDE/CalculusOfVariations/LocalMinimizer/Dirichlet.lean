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
import PDE.CalculusOfVariations.LocalMinimizer.Smooth
import PDE.CalculusOfVariations.PrescribedBoundary
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Calculus.Differentiation.GradientRepresentative
import PDE.Spaces.Sobolev.GraphSpace.Local.Restriction

/-!
# Minimizers with prescribed boundary values are local minimizers

## Motivation

Is a minimizer of `∫_Ω F(∇w)` among the `w` in `H¹(Ω)` with `w - g` in
`H¹₀(Ω)`, as the direct method produces it, a local minimizer in the sense of
`IsLocalMinimizerOn`, so that the interior regularity theorems apply to it?

## The idea

Yes. Let `U` be the minimizer, let `V` be open with compact closure in `Ω`,
and let `φ` be a test function supported in `V`. Then `φ` is also a test function on `Ω`,
and `U + φ` has the boundary values of `U`, so `∫_Ω F(∇U) ≤ ∫_Ω F(∇(U + φ))`. Outside `V`
the gradient of `φ` vanishes, so the two integrands agree on `Ω \ V`. Both are integrable,
because `F` grows at most quadratically and `Ω` is bounded. Subtracting the integrals over
`Ω \ V` leaves the inequality on `V`. On `V` the restriction of `U` is the only `H¹(V)`
function that represents it, and restriction commutes with the weak gradient. No convexity
is used. For a uniformly convex smooth density the direct method applies, and the
regularity theorem gives a smooth representative of the minimizer inside `Ω`.

## Main results

* `isLocalMinimizerOn_of_forall_testFunction_le` (all bounded open `Ω`, all differentiable
  `F` with Lipschitz gradient, all `U` in `H¹(Ω)`): if no test function on `Ω` lowers the
  energy of `U`, then `U` is a local minimizer on `Ω`.
* `isLocalMinimizerOn_of_prescribed_boundary` (same scope, all `g` in `H¹(Ω)`): a
  minimizer among the functions with the boundary values of `g` is in `W^{1,2}_loc(Ω)` and
  is a local minimizer on `Ω`.
* `exists_smooth_minimizer_prescribed_boundary` (all dimensions, all bounded open `Ω`, all
  `C^∞` densities with `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²`, `θ > 0`, all `g` in `H¹(Ω)`): a
  minimizer with the boundary values of `g` exists, and it has a representative that is
  `C^∞` on `Ω` and solves `div(∇F(∇v)) = 0` at every point of `Ω`.

## Relations

* `exists_minimizer_wkpGradientIntegral_prescribed_boundary` gives the minimizer, and
  `exists_smooth_of_isLocalMinimizerOn` its regularity.
* `integrable_gradientDensity_of_lipschitzWith` makes the energies finite, so that the
  integral over `Ω` splits into the integrals over `V` and over `Ω \ V`.
* `wkpGradientCLM_restrictCLM_ae`, `wkpGradientCLM_testFunctionToWkp_ae` and
  `WkpSpaceOn.ext_of_base_ae` compare the two domains.
* `isLocalMinimizerOn_affine_of_quadratic_bounds` gives other local minimizers, with no
  boundedness of `Ω`.

## What stays open

Regularity up to the boundary, which needs regular boundary values and a regular boundary.
Uniqueness of the minimizer is not stated here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorem 2, for the existence of a minimizer
  with prescribed boundary values, and §8.3 for its interior regularity.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Metric SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.CalculusOfVariations

variable {n : ℕ} {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ} {C : ℝ≥0}

/-- **Minimality against test functions passes to subdomains.** Let `Ω` be bounded and
open, let `F` be differentiable with Lipschitz gradient, and let `U` be in `H¹(Ω)`. If no
smooth function with compact support in `Ω` lowers the energy `∫_Ω F(∇U)`, then `U` is a
local minimizer of `∫ F(∇u)` on `Ω`.

A test function on a subdomain `V` is a test function on `Ω`, and its gradient vanishes
outside `V`. So the two energies over `Ω` differ only by their parts over `V`. -/
theorem isLocalMinimizerOn_of_forall_testFunction_le (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (U : H¹(Ω))
    (hmin : ∀ φ : TestFunctionOn n Ω,
      (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤
        ∫ x, F (∇ (U + testFunctionToWkp φ) x) ∂domainMeasure n Ω) :
    IsLocalMinimizerOn F Ω (baseRepresentative U) := by
  intro V hV hVc hVΩ UV hUV φ
  have hsub : V ⊆ Ω := subset_closure.trans hVΩ
  have hφV : tsupport φ.1.toFun ⊆ V := φ.2
  let R := restrictCLM (n := n) (k := 1) (p := 2) hV.measurableSet hsub
  let φΩ : TestFunctionOn n Ω := ⟨φ.1, hφV.trans hsub⟩
  let W : H¹(Ω) := U + testFunctionToWkp φΩ
  -- The representative on `V` is the restriction of `U`, and likewise for the test function.
  have hUV' : UV = R U :=
    WkpSpaceOn.ext_of_base_ae hV UV (R U)
      (hUV.trans (restrictCLM_apply_ae hV.measurableSet hsub U (baseIndex n 1)).symm)
  have hφ : (testFunctionToWkp φ : H¹(V)) = R (testFunctionToWkp φΩ) :=
    WkpSpaceOn.ext_of_base_ae hV _ _
      ((testFunctionToWkp_coordinate_ae (k := 1) (p := 2) φ (baseIndex n 1)).trans
        ((restrictCLM_apply_ae hV.measurableSet hsub (testFunctionToWkp φΩ)
          (baseIndex n 1)).trans (ae_restrict_of_ae_restrict_of_subset hsub
            (testFunctionToWkp_coordinate_ae (k := 1) (p := 2) φΩ (baseIndex n 1)))).symm)
  have hsum : UV + testFunctionToWkp φ = R W := by
    rw [hUV', hφ, ← map_add]
  -- On `V` the energies are the energies of `U` and of `U + φ`.
  have hleft : (∫ x, F (∇ UV x) ∂domainMeasure n V) = ∫ x in V, F (∇ U x) := by
    rw [hUV']
    exact integral_congr_ae ((wkpGradientCLM_restrictCLM_ae hV.measurableSet hsub U).mono
      fun x hx ↦ congrArg F hx)
  have hright : (∫ x, F (∇ (UV + testFunctionToWkp φ) x) ∂domainMeasure n V) =
      ∫ x in V, F (∇ W x) := by
    rw [hsum]
    exact integral_congr_ae ((wkpGradientCLM_restrictCLM_ae hV.measurableSet hsub W).mono
      fun x hx ↦ congrArg F hx)
  -- Outside `V` the perturbation does not change the gradient.
  have hout : ∀ᵐ x ∂volume.restrict (Ω \ V), F (∇ W x) = F (∇ U x) := by
    have hadd : (∇ W : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω]
        fun x ↦ ∇ U x + ∇ (testFunctionToWkp φΩ : H¹(Ω)) x := by
      change (∇ (U + testFunctionToWkp φΩ) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] _
      rw [map_add]
      exact Lp.coeFn_add (∇ U) (∇ (testFunctionToWkp φΩ : H¹(Ω)))
    filter_upwards [ae_restrict_of_ae_restrict_of_subset sdiff_subset hadd,
      ae_restrict_of_ae_restrict_of_subset sdiff_subset
        (wkpGradientCLM_testFunctionToWkp_ae (p := 2) φΩ),
      ae_restrict_mem (hΩ.measurableSet.diff hV.measurableSet)] with x hx hφx hxV
    have hzero : fderiv ℝ φ.1.toFun x = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h ↦ hxV.2 (hφV h)
    have hgrad : ∇ φ.1.toFun x = 0 := by rw [gradient, hzero, map_zero]
    have hW : ∇ W x = ∇ U x := by
      calc
        ∇ W x = ∇ U x + ∇ (testFunctionToWkp φΩ : H¹(Ω)) x := hx
        _ = ∇ U x + ∇ φ.1.toFun x := congrArg (∇ U x + ·) hφx
        _ = ∇ U x := by rw [hgrad, add_zero]
    rw [hW]
  -- Split both energies over `Ω` into the parts over `V` and over `Ω \ V`.
  have hsplit (Z : H¹(Ω)) : (∫ x in V, F (∇ Z x)) + (∫ x in Ω \ V, F (∇ Z x)) =
      ∫ x, F (∇ Z x) ∂domainMeasure n Ω := by
    have h := integral_inter_add_sdiff (μ := volume) hV.measurableSet
      (integrable_gradientDensity_of_lipschitzWith hb hF hLip Z)
    rwa [inter_eq_right.mpr hsub] at h
  have hle : (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤ ∫ x, F (∇ W x) ∂domainMeasure n Ω :=
    hmin φΩ
  rw [← hsplit U, ← hsplit W, integral_congr_ae hout] at hle
  rw [hleft, hright]
  linarith

/-- **Minimizers with prescribed boundary values are local minimizers.** Let `Ω` be
bounded and open, let `F` be differentiable with Lipschitz gradient, and let `g` and `U`
be in `H¹(Ω)` with `U - g` in `H¹₀(Ω)`. If `U` has the least energy `∫_Ω F(∇W)` among all
`W` in `H¹(Ω)` with `W - g` in `H¹₀(Ω)`, then `U` is in `W^{1,2}_loc(Ω)` and is a local
minimizer of `∫ F(∇u)` on `Ω`.

No convexity is needed. A test function is in `H¹₀(Ω)`, so `U + φ` is a competitor, and
`isLocalMinimizerOn_of_forall_testFunction_le` applies. -/
theorem isLocalMinimizerOn_of_prescribed_boundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hF : Differentiable ℝ F) (hLip : LipschitzWith C (∇ F))
    (g U : H¹(Ω))
    (hUg : U - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω))
    (hmin : ∀ W : H¹(Ω), W - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
      (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤ ∫ x, F (∇ W x) ∂domainMeasure n Ω) :
    IsLocallyWkpOn 1 2 Ω (baseRepresentative U) ∧
      IsLocalMinimizerOn F Ω (baseRepresentative U) := by
  refine ⟨isLocallyWkpOn_baseRepresentative U,
    isLocalMinimizerOn_of_forall_testFunction_le hΩ hb hF hLip U fun φ ↦
      hmin (U + testFunctionToWkp φ) ?_⟩
  have h := (wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω)).toSubmodule.add_mem hUg
    (testFunctionToWkp_mem_Wkp0 φ)
  rwa [← add_sub_right_comm] at h

variable {θ Λ : ℝ}

/-- **The Dirichlet problem has a minimizer that is smooth inside.** Let `Ω ⊆ ℝⁿ` be
bounded and open, in any dimension, and let `F` be `C^∞` with
`θ ‖ξ‖² ≤ D²F(p)(ξ, ξ) ≤ Λ ‖ξ‖²` for all `p` and `ξ`, where `θ > 0`. For every `g` in
`H¹(Ω)` there is `U` in `H¹(Ω)` with `U - g` in `H¹₀(Ω)` that has the least energy
`∫_Ω F(∇W)` among all `W` with `W - g` in `H¹₀(Ω)`. This `U` has a representative that is
`C^∞` on `Ω` and satisfies `div(∇F(∇v)) = 0` at every point of `Ω`.

Existence is the direct method, `exists_minimizer_wkpGradientIntegral_prescribed_boundary`.
The minimizer is a local minimizer by `isLocalMinimizerOn_of_prescribed_boundary`, and
`exists_smooth_of_isLocalMinimizerOn` gives the representative. Nothing is assumed about
the boundary of `Ω`. -/
theorem exists_smooth_minimizer_prescribed_boundary (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hθ : 0 < θ)
    (hell : ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ)
    (hbound : ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2) (g : H¹(Ω)) :
    ∃ U : H¹(Ω), U - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) ∧
      (∀ W : H¹(Ω), W - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
        (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤ ∫ x, F (∇ W x) ∂domainMeasure n Ω) ∧
      ∃ v : ℝ^n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v Ω ∧
        v =ᵐ[volume.restrict Ω] baseRepresentative U ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  -- A minimizer exists: trivially in dimension zero, by the direct method otherwise.
  obtain ⟨U, hUg, hmin⟩ : ∃ U : H¹(Ω),
      U - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) ∧
      ∀ W : H¹(Ω), W - g ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := 2) (Ω := Ω) →
        (∫ x, F (∇ U x) ∂domainMeasure n Ω) ≤ ∫ x, F (∇ W x) ∂domainMeasure n Ω := by
    rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i₀⟩⟩
    · refine ⟨g, by simp, fun W _ ↦ le_of_eq (integral_congr_ae (ae_of_all _ fun x ↦ ?_))⟩
      exact congrArg F (Subsingleton.elim _ _)
    · have : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
      have := isFiniteMeasure_domainMeasure_of_isBounded hb
      exact exists_minimizer_wkpGradientIntegral_prescribed_boundary (p := 2) (by norm_num)
        i₀.pos hb (F := fun _ z ↦ F z) (a := fun _ ↦ |F 0| + ‖fderiv ℝ F 0‖ ^ 2)
        (b := fun _ ↦ |F 0| + ‖fderiv ℝ F 0‖ ^ 2 / θ) (c := θ / 4) (C := Λ.toNNReal + 1)
        (hF.continuous.measurable.comp measurable_snd)
        (ae_of_all _ fun _ ↦
          ((strongConvexOn_of_hessian_bound hF2 hell).strictConvexOn hθ).convexOn)
        (integrable_const _) (integrable_const _) (div_pos hθ (by norm_num)) (by positivity)
        (ae_of_all _ fun _ z ↦ by
          simpa only [NNReal.coe_ofNat, Real.rpow_two] using
            quadratic_lower_bound_of_hessian_bound hF2 hθ hell z)
        (ae_of_all _ fun _ z ↦ by
          simpa only [NNReal.coe_ofNat, Real.rpow_two] using
            quadratic_upper_bound_of_hessian_bound hF2 (NNReal.coe_nonneg _) hnorm z)
        g
  -- It is a local minimizer, hence smooth inside.
  obtain ⟨hloc, hlm⟩ := isLocalMinimizerOn_of_prescribed_boundary hΩ hb
    (hF2.differentiable (by norm_num)) (lipschitzWith_gradient_of_hessian_bound hF2 hnorm)
    g U hUg hmin
  exact ⟨U, hUg, hmin, exists_smooth_of_isLocalMinimizerOn hΩ hF hθ hell hbound hloc hlm⟩

end PDE.CalculusOfVariations
