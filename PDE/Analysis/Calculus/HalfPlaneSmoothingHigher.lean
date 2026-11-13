/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.HalfPlaneSmoothing
import PDE.Spaces.Sobolev.Approximation.Mollification.UniformJets

/-!
# Smoothing of `C^{k,α}` data given on the closed upper half-plane

For a datum `f` of class `C^k` within the closed upper half-plane `H̄`, `k ≥ 1`, the smoothing of
order `k`, `halfPlaneSmoothingOf k ε f`, mollifies at the scale `ε` the weighted reflection of
order `k` of the odd part `tangentialOddPart f`. It is smooth, odd in `x₀`, vanishes beyond the
support radius plus `2ε`, and converges to the odd part uniformly on `H̄` as `ε → 0`. If the
derivatives within `H̄` of order `j ≤ k` of `f` are bounded by `N` and the `k`-th is `α`-Hölder with
constant `N`, then the derivatives of order `j` of the smoothing are at most
`2ʲ reflectionBound k j N` and its `k`-th derivative is `α`-Hölder with constant
`2ᵏ (reflectionBound k (k + 1) + 1) N`, uniformly in `ε`.

## Main definitions

* `halfPlaneSmoothingOf`: the mollification at the scale `ε` of the weighted reflection of order
  `k` of the odd part.

## Main results

* `contDiff_halfPlaneSmoothingOf`: the smoothing of order `k` is smooth.
* `isOddUnderCoordinateReflection_halfPlaneSmoothingOf`: the smoothing is odd in `x₀`.
* `halfPlaneSmoothingOf_eq_zero`: the smoothing vanishes beyond the support radius plus `2ε`.
* `tendstoUniformlyOn_halfPlaneSmoothingOf`: the smoothings converge to the odd part uniformly on
  `H̄` as `ε → 0`.
* `norm_iteratedFDeriv_halfPlaneSmoothingOf_le`: the derivatives of order `j ≤ k` of the
  smoothing are at most `2ʲ reflectionBound k j N`.
* `norm_iteratedFDeriv_halfPlaneSmoothingOf_sub_le`: the `k`-th derivative of the smoothing is
  `α`-Hölder with constant `2ᵏ (reflectionBound k (k + 1) + 1) N`.
* `contDiffOn_tangentialOddPart`: the odd part keeps regularity within `H̄`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric PDE.Common SobolevSpace.Approximation
open SobolevSpace.GraphSpace.HigherOrderReflection
open scoped Topology

namespace PDE.Analysis

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

set_option quotPrecheck false in
local notation "σL" => (coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).toContinuousLinearEquiv

/-- The reflection maps the closed upper half-plane onto itself. -/
theorem preimage_coordinateReflection_zero : (σL ⁻¹' H̄ : Set (ℝ^2)) = H̄ := by
  ext y
  simp [coordinateReflectionLinearIsometryEquiv]

variable {k : ℕ} {f : ℝ^2 → ℝ}

/-- The odd part as a combination of `f` and `f ∘ σ`. -/
theorem tangentialOddPart_eq_smul (f : ℝ^2 → ℝ) :
    tangentialOddPart f = (2⁻¹ : ℝ) • (f - f ∘ σL) := by
  funext x
  simp only [tangentialOddPart, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  rw [div_eq_inv_mul]
  rfl

/-- Composition with the reflection keeps regularity within `H̄`. -/
theorem contDiffOn_comp_tangentialReflection {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f H̄) :
    ContDiffOn ℝ n (f ∘ σL) H̄ :=
  hf.comp (σL : ℝ^2 →L[ℝ] ℝ^2).contDiff.contDiffOn fun _ hy ↦ coordinateReflection_zero_mem hy

/-- The odd part keeps regularity within `H̄`. -/
theorem contDiffOn_tangentialOddPart {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f H̄) :
    ContDiffOn ℝ n (tangentialOddPart f) H̄ := by
  rw [tangentialOddPart_eq_smul]
  exact (hf.sub (contDiffOn_comp_tangentialReflection hf)).const_smul (2⁻¹ : ℝ)

/-- Derivatives within `H̄` of `f ∘ σ`. -/
theorem iteratedFDerivWithin_comp_tangentialReflection (j : ℕ) {y : ℝ^2} (hy : 0 ≤ y 1) :
    iteratedFDerivWithin ℝ j (f ∘ σL) H̄ y =
      (iteratedFDerivWithin ℝ j f H̄ (σL y)).compContinuousLinearMap
        fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2) := by
  have h := ContinuousLinearEquiv.iteratedFDerivWithin_comp_right σL f
    (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2)) (x := y) (coordinateReflection_zero_mem hy) j
  rwa [preimage_coordinateReflection_zero] at h

/-- The derivatives within `H̄` of the odd part. -/
theorem iteratedFDerivWithin_tangentialOddPart (hf : ContDiffOn ℝ k f H̄) {j : ℕ} (hj : j ≤ k)
    {y : ℝ^2} (hy : 0 ≤ y 1) :
    iteratedFDerivWithin ℝ j (tangentialOddPart f) H̄ y = (2⁻¹ : ℝ) •
      (iteratedFDerivWithin ℝ j f H̄ y - iteratedFDerivWithin ℝ j (f ∘ σL) H̄ y) := by
  have hj' : (j : WithTop ℕ∞) ≤ k := by exact_mod_cast hj
  have hd : ContDiffOn ℝ j (f - f ∘ σL) H̄ :=
    (hf.sub (contDiffOn_comp_tangentialReflection hf)).of_le hj'
  rw [tangentialOddPart_eq_smul, iteratedFDerivWithin_const_smul_apply (hd y hy)
    (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2)) hy, iteratedFDerivWithin_sub_apply
    ((hf.of_le hj') y hy) (((contDiffOn_comp_tangentialReflection hf).of_le hj') y hy)
    (uniqueDiffOn_coordinateHalfSpace (1 : Fin 2)) hy]

/-- Bounds of the derivatives within `H̄` pass to the odd part. -/
theorem norm_iteratedFDerivWithin_tangentialOddPart_le (hf : ContDiffOn ℝ k f H̄) {j : ℕ}
    (hj : j ≤ k) {N : ℝ} (hN : ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N)
    {y : ℝ^2} (hy : 0 ≤ y 1) : ‖iteratedFDerivWithin ℝ j (tangentialOddPart f) H̄ y‖ ≤ N := by
  rw [iteratedFDerivWithin_tangentialOddPart hf hj hy, norm_smul,
    iteratedFDerivWithin_comp_tangentialReflection j hy]
  have h1 := hN y hy
  have h2 : ‖(iteratedFDerivWithin ℝ j f H̄ (σL y)).compContinuousLinearMap
      fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)‖ ≤ N := by
    rw [ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _
      fun _ ↦ coordinateReflectionLinearIsometryEquiv (0 : Fin 2)]
    exact hN _ (coordinateReflection_zero_mem hy)
  have h3 := norm_sub_le (iteratedFDerivWithin ℝ j f H̄ y)
    ((iteratedFDerivWithin ℝ j f H̄ (σL y)).compContinuousLinearMap
      fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2))
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  linarith

/-- A Hölder bound of the derivative of order `k` within `H̄` passes to the odd part. -/
theorem norm_iteratedFDerivWithin_tangentialOddPart_sub_le (hf : ContDiffOn ℝ k f H̄)
    {M α : ℝ} (hH : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ M * ‖y - z‖ ^ α)
    {y z : ℝ^2} (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    ‖iteratedFDerivWithin ℝ k (tangentialOddPart f) H̄ y -
        iteratedFDerivWithin ℝ k (tangentialOddPart f) H̄ z‖ ≤ M * ‖y - z‖ ^ α := by
  rw [iteratedFDerivWithin_tangentialOddPart hf le_rfl hy,
    iteratedFDerivWithin_tangentialOddPart hf le_rfl hz,
    iteratedFDerivWithin_comp_tangentialReflection k hy,
    iteratedFDerivWithin_comp_tangentialReflection k hz, ← smul_sub]
  set A := iteratedFDerivWithin ℝ k f H̄
  have hsub : (A (σL y)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)) -
      (A (σL z)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)) =
      (A (σL y) - A (σL z)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)) := by
    ext v
    simp
  have h2 : ‖(A (σL y) - A (σL z)).compContinuousLinearMap
      (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2))‖ ≤ M * ‖y - z‖ ^ α := by
    rw [ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv _
      fun _ ↦ coordinateReflectionLinearIsometryEquiv (0 : Fin 2)]
    have := hH _ _ (coordinateReflection_zero_mem hy) (coordinateReflection_zero_mem hz)
    rwa [← coordinateReflection_sub, norm_coordinateReflection] at this
  have h1 := hH y z hy hz
  have heq : A y - (A (σL y)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)) -
      (A z - (A (σL z)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2))) =
      (A y - A z) - ((A (σL y)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)) -
      (A (σL z)).compContinuousLinearMap (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2))) := by abel
  rw [norm_smul, heq, hsub, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
  have h3 := norm_sub_le (A y - A z) ((A (σL y) - A (σL z)).compContinuousLinearMap
    (fun _ ↦ (σL : ℝ^2 →L[ℝ] ℝ^2)))
  linarith

/-! ### Smoothing of order `k` -/

/-- The smoothing of order `k` at the scale `ε`: the mollification of the weighted reflection of
order `k` of the odd part. -/
def halfPlaneSmoothingOf (k : ℕ) (ε : ℝ) (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  mollify (standardMollifier 2) ε (weightedReflectionFun 1 k (tangentialOddPart f))

variable {ε : ℝ}

/-- The weighted reflection of the odd part of a `C^k` datum, `k ≥ 1`, is `C^k`. -/
theorem contDiff_weightedReflectionFun_tangentialOddPart (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f H̄) :
    ContDiff ℝ k (weightedReflectionFun 1 k (tangentialOddPart f)) :=
  contDiff_weightedReflectionFun_of_le 1 hk le_rfl (contDiffOn_tangentialOddPart hf)

/-- The weighted reflection of the odd part of a datum vanishing beyond the radius `R` has compact
support. -/
theorem hasCompactSupport_weightedReflectionFun_tangentialOddPart {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    HasCompactSupport (weightedReflectionFun 1 k (tangentialOddPart f)) :=
  hasCompactSupport_weightedReflectionFun 1 fun _ hy hyR ↦ tangentialOddPart_eq_zero hR hy hyR

/-- The smoothing of order `k` is smooth. -/
theorem contDiff_halfPlaneSmoothingOf (hε : 0 < ε) (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f H̄) :
    ContDiff ℝ (⊤ : ℕ∞) (halfPlaneSmoothingOf k ε f) :=
  mollify_contDiff_of_pos _ hε _
    (contDiff_weightedReflectionFun_tangentialOddPart hk hf).continuous.locallyIntegrable

/-- The smoothing of order `k` is odd in `x₀`. -/
theorem isOddUnderCoordinateReflection_halfPlaneSmoothingOf (hε : 0 < ε) :
    IsOddUnderCoordinateReflection (0 : Fin 2) (halfPlaneSmoothingOf k ε f) := by
  refine mollify_odd_of_radial _
    (fun r ↦ Real.smoothTransition (2 - r) / ∫ y : ℝ^2, Real.smoothTransition (2 - ‖y‖))
    (fun x ↦ standardMollifier_eq_norm x) hε 0 fun x ↦ ?_
  rw [weightedReflectionFun_comp_coordinateReflection 1 (l := 0) (by decide) (ε := -1)
    (fun y _ ↦ by rw [isOddUnderCoordinateReflection_tangentialOddPart f y]; ring) x]
  ring

/-- The smoothing of order `k` vanishes beyond the support radius plus `2ε`. -/
theorem halfPlaneSmoothingOf_eq_zero {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : R + 2 * ε < ‖x‖) :
    halfPlaneSmoothingOf k ε f x = 0 :=
  mollify_standard_eq_zero (fun _ hz ↦ weightedReflectionFun_eq_zero_of_norm_lt 1
    (fun _ hy hyR ↦ tangentialOddPart_eq_zero hR hy hyR) hz) hx

/-- **The smoothings of order `k` converge to the odd part** uniformly on `H̄`, along scales in
`(0, 1]` tending to zero. -/
theorem tendstoUniformlyOn_halfPlaneSmoothingOf (hk : 1 ≤ k) (hf : ContDiffOn ℝ k f H̄) {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεle : ∀ j, ε j ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn (fun j ↦ halfPlaneSmoothingOf k (ε j) f) (tangentialOddPart f) atTop H̄ := by
  have hc := (contDiff_weightedReflectionFun_tangentialOddPart hk hf).continuous
  have hu := iteratedPartialDeriv_mollify_tendstoUniformly (standardMollifier 2)
    (contDiff_zero.2 hc) (hasCompactSupport_weightedReflectionFun_tangentialOddPart hR) ε hεpos
    hεle hε0 [] (by simp)
  have hu' : TendstoUniformly (fun j ↦ halfPlaneSmoothingOf k (ε j) f)
      (weightedReflectionFun 1 k (tangentialOddPart f)) atTop := hu
  exact (hu'.tendstoUniformlyOn).congr_right fun x hx ↦
    weightedReflectionFun_eq_of_nonneg 1 k _ x hx

/-- **Bounds of the derivatives.** For a `C^k` datum, `k ≥ 1`, whose derivative of order `j ≤ k`
within `H̄` is bounded by `N`, the derivative of order `j` of the smoothing of order `k` is at most
`2ʲ reflectionBound k j N` everywhere. -/
theorem norm_iteratedFDeriv_halfPlaneSmoothingOf_le (hε : 0 < ε) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f H̄) {R : ℝ} (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {j : ℕ}
    (hj : j ≤ k) {N : ℝ} (hN : ∀ y : ℝ^2, 0 ≤ y 1 → ‖iteratedFDerivWithin ℝ j f H̄ y‖ ≤ N)
    (x : ℝ^2) :
    ‖iteratedFDeriv ℝ j (halfPlaneSmoothingOf k ε f) x‖ ≤ 2 ^ j * (reflectionBound k j * N) := by
  have h := norm_iteratedFDeriv_mollify_le (standardMollifier 2) hε
    (contDiff_weightedReflectionFun_tangentialOddPart hk hf)
    (hasCompactSupport_weightedReflectionFun_tangentialOddPart hR) hj
    (norm_iteratedFDeriv_weightedReflectionFun_le 1 hk (contDiffOn_tangentialOddPart hf) hj
      fun y hy ↦ norm_iteratedFDerivWithin_tangentialOddPart_le hf hj hN hy) x
  rwa [Nat.cast_ofNat] at h

/-- **Hölder bound of the top derivative.** For a `C^k` datum, `k ≥ 1`, whose derivative of order
`k` within `H̄` is `α`-Hölder with constant `N`, `0 ≤ α ≤ 1`, the derivative of order `k` of the
smoothing of order `k` is `α`-Hölder with constant `2ᵏ (reflectionBound k (k + 1) + 1) N`. -/
theorem norm_iteratedFDeriv_halfPlaneSmoothingOf_sub_le (hε : 0 < ε) (hk : 1 ≤ k)
    (hf : ContDiffOn ℝ k f H̄) {R : ℝ} (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0)
    {N α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hN : 0 ≤ N)
    (hH : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 →
      ‖iteratedFDerivWithin ℝ k f H̄ y - iteratedFDerivWithin ℝ k f H̄ z‖ ≤ N * ‖y - z‖ ^ α)
    (x y : ℝ^2) :
    ‖iteratedFDeriv ℝ k (halfPlaneSmoothingOf k ε f) x -
        iteratedFDeriv ℝ k (halfPlaneSmoothingOf k ε f) y‖ ≤
      2 ^ k * ((reflectionBound k (k + 1) + 1) * N * ‖x - y‖ ^ α) := by
  have h := norm_iteratedFDeriv_mollify_sub_le_rpow (standardMollifier 2) hε
    (contDiff_weightedReflectionFun_tangentialOddPart hk hf)
    (hasCompactSupport_weightedReflectionFun_tangentialOddPart hR) le_rfl
    (norm_iteratedFDeriv_weightedReflectionFun_sub_rpow_le 1 hk (contDiffOn_tangentialOddPart hf)
      hα0 hα1 hN fun y z hy hz ↦ norm_iteratedFDerivWithin_tangentialOddPart_sub_le hf hH hy hz)
    x y
  rwa [Nat.cast_ofNat] at h

end PDE.Analysis
