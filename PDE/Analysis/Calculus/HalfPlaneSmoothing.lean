/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HolderBounds
public import PDE.Analysis.Calculus.HalfSpaceReflectionHigher
import PDE.Spaces.Sobolev.Approximation.Mollification.UniformJets
import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles

/-!
# Smoothing of data given on the closed upper half-plane

A datum `f` given on the closed upper half-plane `H̄ = {x₁ ≥ 0}` is approximated by smooth
functions on the plane that are odd in `x₀` and supported near the support of `f`. The odd part
`(f - f ∘ σ) / 2`, `σ` the reflection `x₀ ↦ -x₀`, equals `f` on `H̄` when `f` is odd there. The
smoothing at the scale `ε` mollifies the even reflection `g(x₀, |x₁|)` of the odd part. It is
smooth and odd, it vanishes beyond the support radius plus `2ε`, it keeps the uniform bound and
the `α`-Hölder constant of `f` on `H̄` (`0 ≤ α ≤ 1`; `α = 1` is the Lipschitz constant, and for
`C¹` data the bound of the gradient), it is linear in `f` and depends only on `f` on `H̄`, and it
converges to the odd part uniformly as `ε → 0`.

The smoothing of `C^{k,α}` data, which keeps the bounds of the derivatives, is in
`PDE.Analysis.Calculus.HalfPlaneSmoothingHigher`.

## Main definitions

* `tangentialOddPart`: the odd part `(f - f ∘ σ) / 2` of `f` in `x₀`.
* `evenReflection`: the even reflection `g(x₀, |x₁|)` across the boundary line.
* `halfPlaneSmoothing`: the mollification at the scale `ε` of the even reflection of the odd
  part.

## Main results

* `tangentialOddPart_eq_of_odd`: the odd part of a function odd on `H̄` is the function on `H̄`.
* `contDiff_halfPlaneSmoothing`: the smoothing is smooth.
* `isOddUnderCoordinateReflection_halfPlaneSmoothing`: the smoothing is odd in `x₀`.
* `halfPlaneSmoothing_eq_zero`: the smoothing vanishes beyond the support radius plus `2ε`.
* `abs_halfPlaneSmoothing_le`: the smoothing keeps the uniform bound on `H̄`.
* `abs_halfPlaneSmoothing_sub_le`: the smoothing keeps the `α`-Hölder constant on `H̄`.
* `tendstoUniformlyOn_halfPlaneSmoothing`: the smoothings converge to the odd part uniformly on
  `H̄` as `ε → 0`.
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

/-! ### The odd part -/

/-- The odd part `(f x - f (σ x)) / 2` of `f` in the coordinate `x₀`. -/
def tangentialOddPart (f : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (f x - f (coordinateReflection (0 : Fin 2) x)) / 2

/-- The reflection `x₀ ↦ -x₀` maps the closed upper half-plane into itself. -/
theorem coordinateReflection_zero_mem {x : ℝ^2} (hx : 0 ≤ x 1) :
    0 ≤ coordinateReflection (0 : Fin 2) x 1 := by
  rwa [coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide)]

/-- The odd part is odd. -/
theorem isOddUnderCoordinateReflection_tangentialOddPart (f : ℝ^2 → ℝ) :
    IsOddUnderCoordinateReflection (0 : Fin 2) (tangentialOddPart f) := by
  intro x
  simp only [tangentialOddPart]
  rw [coordinateReflection_involutive]
  ring

/-- The odd part is linear. -/
theorem tangentialOddPart_sub (f g : ℝ^2 → ℝ) :
    tangentialOddPart (f - g) = tangentialOddPart f - tangentialOddPart g := by
  funext x
  simp only [tangentialOddPart, Pi.sub_apply]
  ring

/-- The odd part on `H̄` depends only on the values on `H̄`. -/
theorem tangentialOddPart_congr {f g : ℝ^2 → ℝ} (h : ∀ y : ℝ^2, 0 ≤ y 1 → f y = g y)
    {x : ℝ^2} (hx : 0 ≤ x 1) : tangentialOddPart f x = tangentialOddPart g x := by
  simp only [tangentialOddPart, h x hx, h _ (coordinateReflection_zero_mem hx)]

/-- The odd part of a function odd on `H̄` is the function on `H̄`. -/
theorem tangentialOddPart_eq_of_odd {f : ℝ^2 → ℝ}
    (hodd : ∀ y : ℝ^2, 0 ≤ y 1 → f (coordinateReflection (0 : Fin 2) y) = -f y) {x : ℝ^2}
    (hx : 0 ≤ x 1) : tangentialOddPart f x = f x := by
  simp only [tangentialOddPart, hodd x hx]
  ring

/-- The odd part of a function continuous on `H̄` is continuous on `H̄`. -/
theorem continuousOn_tangentialOddPart {f : ℝ^2 → ℝ} (hf : ContinuousOn f H̄) :
    ContinuousOn (tangentialOddPart f) H̄ := by
  have hσ : ContinuousOn (fun x ↦ f (coordinateReflection (0 : Fin 2) x)) H̄ :=
    hf.comp (coordinateReflectionLinearIsometryEquiv (0 : Fin 2)).continuous.continuousOn
      fun x hx ↦ coordinateReflection_zero_mem hx
  exact (hf.sub hσ).div_const 2

/-- A uniform bound on `H̄` passes to the odd part. -/
theorem abs_tangentialOddPart_le {f : ℝ^2 → ℝ} {B : ℝ} (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B)
    {x : ℝ^2} (hx : 0 ≤ x 1) : |tangentialOddPart f x| ≤ B := by
  have h1 := hB x hx
  have h2 := hB _ (coordinateReflection_zero_mem hx)
  simp only [tangentialOddPart, abs_div, abs_two]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_sub (f x) (f (coordinateReflection (0 : Fin 2) x))]

/-- The support of `f` on `H̄` bounds that of the odd part. -/
theorem tangentialOddPart_eq_zero {f : ℝ^2 → ℝ} {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : 0 ≤ x 1)
    (hxR : R < ‖x‖) : tangentialOddPart f x = 0 := by
  have h2 := hR _ (coordinateReflection_zero_mem hx) (by rwa [norm_coordinateReflection])
  simp [tangentialOddPart, hR x hx hxR, h2]

/-- A Hölder bound on `H̄` passes to the odd part. -/
theorem abs_tangentialOddPart_sub_le {f : ℝ^2 → ℝ} {M α : ℝ}
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) {y z : ℝ^2}
    (hy : 0 ≤ y 1) (hz : 0 ≤ z 1) :
    |tangentialOddPart f y - tangentialOddPart f z| ≤ M * ‖y - z‖ ^ α := by
  have h1 := hM y z hy hz
  have h2 := hM _ _ (coordinateReflection_zero_mem hy) (coordinateReflection_zero_mem hz)
  rw [← coordinateReflection_sub, norm_coordinateReflection] at h2
  have heq : tangentialOddPart f y - tangentialOddPart f z =
      ((f y - f z) - (f (coordinateReflection 0 y) - f (coordinateReflection 0 z))) / 2 := by
    simp only [tangentialOddPart]
    ring
  rw [heq, abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_sub (f y - f z) (f (coordinateReflection 0 y) - f (coordinateReflection 0 z))]

/-! ### The even reflection -/

/-- The folding `(x₀, |x₁|)` of the plane onto the closed upper half-plane. -/
def halfPlaneFold (x : ℝ^2) : ℝ^2 :=
  WithLp.toLp 2 ![x 0, |x 1|]

/-- The first coordinate of the folding. -/
@[simp]
theorem halfPlaneFold_apply_zero (x : ℝ^2) : halfPlaneFold x 0 = x 0 := by
  simp [halfPlaneFold]

/-- The second coordinate of the folding. -/
@[simp]
theorem halfPlaneFold_apply_one (x : ℝ^2) : halfPlaneFold x 1 = |x 1| := by
  simp [halfPlaneFold]

/-- The folding lands in the closed upper half-plane. -/
theorem halfPlaneFold_mem (x : ℝ^2) : 0 ≤ halfPlaneFold x 1 := by
  simp

/-- The folding is the identity on the closed upper half-plane. -/
theorem halfPlaneFold_of_nonneg {x : ℝ^2} (hx : 0 ≤ x 1) : halfPlaneFold x = x := by
  ext i
  fin_cases i <;> simp [abs_of_nonneg hx]

/-- The folding preserves norms. -/
theorem norm_halfPlaneFold (x : ℝ^2) : ‖halfPlaneFold x‖ = ‖x‖ := by
  have h1 := EuclideanSpace.real_norm_sq_eq (halfPlaneFold x)
  have h2 := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_two, halfPlaneFold_apply_zero, halfPlaneFold_apply_one, sq_abs] at h1 h2
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)

/-- The folding is `1`-Lipschitz. -/
theorem norm_halfPlaneFold_sub_le (x y : ℝ^2) :
    ‖halfPlaneFold x - halfPlaneFold y‖ ≤ ‖x - y‖ := by
  have h1 := EuclideanSpace.real_norm_sq_eq (halfPlaneFold x - halfPlaneFold y)
  have h2 := EuclideanSpace.real_norm_sq_eq (x - y)
  simp only [Fin.sum_univ_two, PiLp.sub_apply, halfPlaneFold_apply_zero,
    halfPlaneFold_apply_one] at h1 h2
  have h3 : (|x 1| - |y 1|) ^ 2 ≤ (x 1 - y 1) ^ 2 :=
    sq_le_sq.2 (by simpa using abs_abs_sub_abs_le_abs_sub (x 1) (y 1))
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)

/-- For `x` in `H̄`, folding `y` does not increase its distance to `x`. -/
theorem norm_sub_halfPlaneFold_le {x : ℝ^2} (hx : 0 ≤ x 1) (y : ℝ^2) :
    ‖x - halfPlaneFold y‖ ≤ ‖x - y‖ := by
  have h := norm_halfPlaneFold_sub_le x y
  rwa [halfPlaneFold_of_nonneg hx] at h

/-- The folding is continuous. -/
theorem continuous_halfPlaneFold : Continuous halfPlaneFold :=
  (LipschitzWith.of_dist_le_mul (K := 1) fun x y ↦ by
    simpa [dist_eq_norm] using norm_halfPlaneFold_sub_le x y).continuous

/-- The folding commutes with the reflection `x₀ ↦ -x₀`. -/
theorem halfPlaneFold_coordinateReflection (x : ℝ^2) :
    halfPlaneFold (coordinateReflection (0 : Fin 2) x) =
      coordinateReflection (0 : Fin 2) (halfPlaneFold x) := by
  ext i
  fin_cases i <;> simp [coordinateReflection_apply_same]

/-- The even reflection `g (x₀, |x₁|)` of `g` across the boundary line. -/
def evenReflection (g : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  g (halfPlaneFold x)

/-- The even reflection agrees with `g` on `H̄`. -/
theorem evenReflection_of_nonneg {g : ℝ^2 → ℝ} {x : ℝ^2} (hx : 0 ≤ x 1) :
    evenReflection g x = g x := by
  rw [evenReflection, halfPlaneFold_of_nonneg hx]

/-- The even reflection is idempotent. -/
theorem evenReflection_evenReflection (g : ℝ^2 → ℝ) :
    evenReflection (evenReflection g) = evenReflection g :=
  funext fun x ↦ evenReflection_of_nonneg (g := g) (halfPlaneFold_mem x)

/-- The even reflection of a function continuous on `H̄` is continuous. -/
theorem continuous_evenReflection {g : ℝ^2 → ℝ} (hg : ContinuousOn g H̄) :
    Continuous (evenReflection g) :=
  hg.comp_continuous continuous_halfPlaneFold halfPlaneFold_mem

/-- The even reflection of an odd function is odd. -/
theorem isOddUnderCoordinateReflection_evenReflection {g : ℝ^2 → ℝ}
    (hg : IsOddUnderCoordinateReflection (0 : Fin 2) g) :
    IsOddUnderCoordinateReflection (0 : Fin 2) (evenReflection g) := by
  intro x
  rw [evenReflection, halfPlaneFold_coordinateReflection, hg]
  rfl

/-- The even reflection depends only on the values on `H̄`. -/
theorem evenReflection_congr {g g' : ℝ^2 → ℝ} (h : ∀ y : ℝ^2, 0 ≤ y 1 → g y = g' y) :
    evenReflection g = evenReflection g' :=
  funext fun x ↦ h _ (halfPlaneFold_mem x)

/-- The even reflection is linear. -/
theorem evenReflection_sub (g g' : ℝ^2 → ℝ) :
    evenReflection (g - g') = evenReflection g - evenReflection g' :=
  rfl

/-- A uniform bound on `H̄` passes to the even reflection. -/
theorem abs_evenReflection_le {g : ℝ^2 → ℝ} {B : ℝ} (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |g y| ≤ B)
    (x : ℝ^2) : |evenReflection g x| ≤ B :=
  hB _ (halfPlaneFold_mem x)

/-- The support radius on `H̄` passes to the even reflection. -/
theorem evenReflection_eq_zero {g : ℝ^2 → ℝ} {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) {x : ℝ^2} (hx : R < ‖x‖) :
    evenReflection g x = 0 :=
  hR _ (halfPlaneFold_mem x) (by rwa [norm_halfPlaneFold])

/-- The even reflection of a function vanishing on `H̄` outside the closed ball of radius `R` is
compactly supported. -/
theorem hasCompactSupport_evenReflection_of_eq_zero {g : ℝ^2 → ℝ} {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → g y = 0) : HasCompactSupport (evenReflection g) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) R) fun _ hx ↦
    evenReflection_eq_zero hR (by simpa using hx)

/-- The even reflection of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_evenReflection {g : ℝ^2 → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (evenReflection g) := by
  obtain ⟨R, hR⟩ := hg.isCompact.isBounded.subset_closedBall 0
  exact hasCompactSupport_evenReflection_of_eq_zero (R := R) fun y _ hy ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ not_lt.2 (mem_closedBall_zero_iff.1 (hR h)) hy

/-- A Hölder bound `|g y - g z| ≤ M |y - z|^α` on `H̄`, `0 ≤ α`, passes to the even reflection
on the whole plane with the same constant. -/
theorem abs_evenReflection_sub_le {g : ℝ^2 → ℝ} {M α : ℝ} (hα : 0 ≤ α)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |g y - g z| ≤ M * ‖y - z‖ ^ α) (x y : ℝ^2) :
    |evenReflection g x - evenReflection g y| ≤ M * ‖x - y‖ ^ α := by
  have hM0 : 0 ≤ M := by
    have h := hM (EuclideanSpace.single 0 1) 0 (by simp) (by simp)
    rw [sub_zero, PiLp.norm_single, norm_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  exact (hM _ _ (halfPlaneFold_mem x) (halfPlaneFold_mem y)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (norm_halfPlaneFold_sub_le x y) hα) hM0)

/-! ### Smoothing of order zero -/

/-- Mollification by the standard mollifier at the scale `ε` of a function vanishing beyond the
radius `R` vanishes beyond the radius `R + 2ε`. For `ε ≤ 0` the mollification is zero. -/
theorem mollify_standard_eq_zero {g : ℝ^2 → ℝ} {R ε : ℝ}
    (hg : ∀ x : ℝ^2, R < ‖x‖ → g x = 0) {x : ℝ^2} (hx : R + 2 * ε < ‖x‖) :
    mollify (standardMollifier 2) ε g x = 0 := by
  rcases le_or_gt ε 0 with hε | hε
  · rw [mollify, scaled, ite_eq_left hε, MeasureTheory.zero_convolution, Pi.zero_apply]
  by_contra hne
  obtain ⟨y, hy, z, hz, rfl⟩ := support_mollify_subset_closedBall_add_support _ hε
    (tsupport_standardMollifier_subset_closedBall 2) g hne
  have hy' : ‖y‖ ≤ ε * 2 := by simpa using hy
  have hz' : ‖z‖ ≤ R := by
    by_contra h
    exact hz (hg z (lt_of_not_ge h))
  have := norm_add_le y z
  linarith

/-- The smoothing of order zero at the scale `ε`: the mollification of the even reflection of
the odd part. -/
def halfPlaneSmoothing (ε : ℝ) (f : ℝ^2 → ℝ) : ℝ^2 → ℝ :=
  mollify (standardMollifier 2) ε (evenReflection (tangentialOddPart f))

variable {ε : ℝ} {f : ℝ^2 → ℝ}

/-- The even reflection of the odd part of a function continuous on `H̄` is continuous. -/
theorem continuous_evenReflection_tangentialOddPart (hf : ContinuousOn f H̄) :
    Continuous (evenReflection (tangentialOddPart f)) :=
  continuous_evenReflection (continuousOn_tangentialOddPart hf)

/-- The smoothing is smooth. -/
theorem contDiff_halfPlaneSmoothing (hε : 0 < ε) (hf : ContinuousOn f H̄) :
    ContDiff ℝ (⊤ : ℕ∞) (halfPlaneSmoothing ε f) :=
  mollify_contDiff_of_pos _ hε _ (continuous_evenReflection_tangentialOddPart hf).locallyIntegrable

/-- The smoothing is odd in `x₀`. -/
theorem isOddUnderCoordinateReflection_halfPlaneSmoothing (hε : 0 < ε) :
    IsOddUnderCoordinateReflection (0 : Fin 2) (halfPlaneSmoothing ε f) :=
  mollify_odd_of_radial _
    (fun r ↦ Real.smoothTransition (2 - r) / ∫ y : ℝ^2, Real.smoothTransition (2 - ‖y‖))
    (fun x ↦ standardMollifier_eq_norm x) hε 0
    (isOddUnderCoordinateReflection_evenReflection
      (isOddUnderCoordinateReflection_tangentialOddPart f))

/-- The smoothing vanishes beyond the support radius plus `2ε`. -/
theorem halfPlaneSmoothing_eq_zero {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {x : ℝ^2} (hx : R + 2 * ε < ‖x‖) :
    halfPlaneSmoothing ε f x = 0 :=
  mollify_standard_eq_zero (fun _ hz ↦ evenReflection_eq_zero
    (fun _ hy hyR ↦ tangentialOddPart_eq_zero hR hy hyR) hz) hx

/-- The smoothing keeps the uniform bound on `H̄`. -/
theorem abs_halfPlaneSmoothing_le (hε : 0 < ε) {B : ℝ}
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) (x : ℝ^2) : |halfPlaneSmoothing ε f x| ≤ B :=
  norm_mollify_le_of_ae_bound _ hε (Eventually.of_forall
    (abs_evenReflection_le fun _ hy ↦ abs_tangentialOddPart_le hB hy)) x

/-- The smoothing keeps the `α`-Hölder constant on `H̄`, `0 ≤ α`; for `α = 1` this is the
Lipschitz constant. -/
theorem abs_halfPlaneSmoothing_sub_le (hε : 0 < ε) (hf : ContinuousOn f H̄) {M α : ℝ} (hα : 0 ≤ α)
    (hM : ∀ y z : ℝ^2, 0 ≤ y 1 → 0 ≤ z 1 → |f y - f z| ≤ M * ‖y - z‖ ^ α) (x y : ℝ^2) :
    |halfPlaneSmoothing ε f x - halfPlaneSmoothing ε f y| ≤ M * ‖x - y‖ ^ α :=
  abs_mollify_sub_le_rpow _ hε (continuous_evenReflection_tangentialOddPart hf)
    (abs_evenReflection_sub_le hα fun _ _ hy hz ↦ abs_tangentialOddPart_sub_le hM hy hz) x y

/-- The smoothing is linear. -/
theorem halfPlaneSmoothing_sub (hε : 0 < ε) {g : ℝ^2 → ℝ} (hf : ContinuousOn f H̄)
    (hg : ContinuousOn g H̄) :
    halfPlaneSmoothing ε (f - g) = halfPlaneSmoothing ε f - halfPlaneSmoothing ε g := by
  rw [halfPlaneSmoothing, tangentialOddPart_sub, evenReflection_sub]
  exact mollify_sub_of_pos _ hε _ _
    (continuous_evenReflection_tangentialOddPart hf).locallyIntegrable
    (continuous_evenReflection_tangentialOddPart hg).locallyIntegrable

/-- The smoothing depends only on the values on `H̄`. -/
theorem halfPlaneSmoothing_congr {g : ℝ^2 → ℝ} (h : ∀ y : ℝ^2, 0 ≤ y 1 → f y = g y) :
    halfPlaneSmoothing ε f = halfPlaneSmoothing ε g := by
  rw [halfPlaneSmoothing, halfPlaneSmoothing,
    evenReflection_congr fun y hy ↦ tangentialOddPart_congr h hy]

/-- **The smoothings converge to the odd part** uniformly on `H̄`, along scales in `(0, 1]`
tending to zero. -/
theorem tendstoUniformlyOn_halfPlaneSmoothing (hf : ContinuousOn f H̄) {R : ℝ}
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hεle : ∀ j, ε j ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformlyOn (fun j ↦ halfPlaneSmoothing (ε j) f) (tangentialOddPart f) atTop H̄ := by
  have hc := continuous_evenReflection_tangentialOddPart hf
  have hcs : HasCompactSupport (evenReflection (tangentialOddPart f)) :=
    hasCompactSupport_evenReflection_of_eq_zero fun _ hy hyR ↦ tangentialOddPart_eq_zero hR hy hyR
  have hu := iteratedPartialDeriv_mollify_tendstoUniformly (standardMollifier 2)
    (contDiff_zero.2 hc) hcs ε hεpos hεle hε0 [] (by simp)
  have hu' : TendstoUniformly (fun j ↦ halfPlaneSmoothing (ε j) f)
      (evenReflection (tangentialOddPart f)) atTop := hu
  exact (hu'.tendstoUniformlyOn).congr_right fun _ hx ↦ evenReflection_of_nonneg hx

end PDE.Analysis
