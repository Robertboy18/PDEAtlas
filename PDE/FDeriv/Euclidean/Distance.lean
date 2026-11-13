/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Euclidean.Norm

/-!
# Fréchet derivatives of Euclidean distance kernels

The Poisson kernels for the ball and the half-space, and the Newtonian kernel, are built from
inverse powers `z ↦ dist(z, y)⁻ᵏ` of the Euclidean distance. We work out the
differential calculus of such kernels on a real inner product space `E`, away from the pole
`y`: explicit continuous-linear-map formulas for the first derivative, the Hessian in a fixed
direction, smoothness of every finite order, and operator-norm bounds with decay
`dist(x,y)^(-(k+1))` for the first derivative (an exact norm) and `dist(x,y)^(-(k+2))` for the
second (with constant `k (k + 3) ‖v‖`). The bounds are the dominating functions needed to
differentiate Poisson integrals under the integral sign. Statements use Mathlib's `dist`
directly.

## Main results

* `distFDerivFormula`, `hasFDerivAt_dist_left`: `D_z dist(z, y) = ⟪(z - y) / dist(z, y), ·⟫` off
  the diagonal.
* `invDistPowFDerivFormula`, `hasFDerivAt_inv_dist_pow`, `invDistPowFDerivFormula_eq_of_ne`:
  `D_z dist(z, y)⁻ᵏ = -k dist(z, y)^(-(k+2)) ⟪z - y, ·⟫`.
* `contDiffAt_inv_dist_pow`: `dist(·, y)⁻ᵏ` is `C^m` for every `m` away from `y`.
* `hasFDerivAt_invDistPowFDerivFormula_apply`: the second derivative in a fixed direction.
* `norm_distFDerivFormula_of_ne`, `norm_invDistPowFDerivFormula_of_ne`,
  `norm_invDistPowFDerivFormula_le_of_le_dist`,
  `norm_invDistPowFDerivFormula_apply_fderiv_le`: exact operator norms of the first
  derivatives, a bound for the second, and uniform bounds when the distance is bounded below by
  a positive constant.

## Implementation notes

`distFDerivFormula` and `invDistPowFDerivFormula` are total functions of `(x, y)`. On the
diagonal they are the zero map, because the vector `x - y` vanishes there; this is why
`norm_distFDerivFormula_le_one` holds everywhere while the `HasFDerivAt` statements require
`x ≠ y`.
-/

@[expose] public section

namespace EuclideanDistance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The continuous-linear-map formula for the derivative of Euclidean distance
with respect to its first argument. It represents the analytic derivative only
away from the diagonal. -/
noncomputable def distFDerivFormula (x y : E) : E →L[ℝ] ℝ :=
  innerSL ℝ ((dist x y)⁻¹ • (x - y))

/-- The distance derivative varies continuously along continuous maps that stay off the diagonal. -/
theorem continuous_distFDerivFormula
    {X : Type*} [TopologicalSpace X] {f g : X → E}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ z, f z ≠ g z) :
    Continuous fun z ↦ distFDerivFormula (f z) (g z) := by
  have hdist : Continuous fun z ↦ dist (f z) (g z) := hf.dist hg
  have hinv : Continuous fun z ↦ (dist (f z) (g z))⁻¹ :=
    hdist.inv₀ fun z ↦ dist_ne_zero.mpr (hfg z)
  have hvec : Continuous fun z ↦
      (dist (f z) (g z))⁻¹ • (f z - g z) :=
    hinv.smul (hf.sub hg)
  change Continuous fun z ↦
    innerSL ℝ ((dist (f z) (g z))⁻¹ • (f z - g z))
  exact (innerSL ℝ (E := E)).continuous.comp hvec

/-- Euclidean distance is Fréchet differentiable in its first argument away from the diagonal. -/
theorem hasFDerivAt_dist_left {x y : E} (hxy : x ≠ y) :
    HasFDerivAt (fun z : E ↦ dist z y) (distFDerivFormula x y) x := by
  have hlin :
      HasFDerivAt (fun z : E ↦ z - y) (ContinuousLinearMap.id ℝ E) x := by
    exact hasFDerivAt_sub_const y
  have hne : x - y ≠ (0 : E) := sub_ne_zero.mpr hxy
  have hnorm :
      HasFDerivAt (fun w : E ↦ ‖w‖)
        (innerSL ℝ ((‖x - y‖)⁻¹ • (x - y))) (x - y) :=
    EuclideanNorm.hasFDerivAt_norm_of_ne_zero hne
  rw [show (fun z : E ↦ dist z y) = (fun w : E ↦ ‖w‖) ∘ fun z ↦ z - y by
    funext z
    simp only [Function.comp_apply, dist_eq_norm]]
  simpa [dist_eq_norm, distFDerivFormula] using hnorm.comp x hlin

/-- The continuous-linear-map formula for the derivative of
`z ↦ (dist z y ^ k)⁻¹`. It represents the analytic derivative only away
from the pole. -/
noncomputable def invDistPowFDerivFormula (k : ℕ) (x y : E) : E →L[ℝ] ℝ :=
  (-((dist x y ^ k) ^ 2)⁻¹) •
    ((k • dist x y ^ (k - 1)) • distFDerivFormula x y)

/-- The inverse-distance-power derivative varies continuously along continuous maps that stay off
the diagonal. -/
theorem continuous_invDistPowFDerivFormula
    {X : Type*} [TopologicalSpace X] (k : ℕ) {f g : X → E}
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ z, f z ≠ g z) :
    Continuous fun z ↦ invDistPowFDerivFormula k (f z) (g z) := by
  have hdist : Continuous fun z ↦ dist (f z) (g z) := hf.dist hg
  have hdistDeriv : Continuous fun z ↦ distFDerivFormula (f z) (g z) :=
    continuous_distFDerivFormula hf hg hfg
  have hpow : Continuous fun z ↦ dist (f z) (g z) ^ k := hdist.pow k
  have hcoef₁ : Continuous fun z ↦ (-((dist (f z) (g z) ^ k) ^ 2)⁻¹ : ℝ) := by
    exact ((hpow.pow 2).inv₀ fun z ↦
      pow_ne_zero 2 (pow_ne_zero k (dist_ne_zero.mpr (hfg z)))).neg
  have hcoef₂ : Continuous fun z ↦
      (k • dist (f z) (g z) ^ (k - 1) : ℝ) := by
    simpa only [nsmul_eq_mul, Pi.mul_def, Pi.pow_def] using
      continuous_const.mul (hdist.pow (k - 1))
  change Continuous fun z ↦
    (-((dist (f z) (g z) ^ k) ^ 2)⁻¹ : ℝ) •
      ((k • dist (f z) (g z) ^ (k - 1) : ℝ) • distFDerivFormula (f z) (g z))
  exact hcoef₁.smul (hcoef₂.smul hdistDeriv)

/-- Evaluation formula for the derivative of an inverse distance power away from its pole. -/
theorem invDistPowFDerivFormula_apply_eq_of_ne
    (k : ℕ) {x y v : E} (hxy : x ≠ y) :
    invDistPowFDerivFormula k x y v =
      (-(k : ℝ) / dist x y ^ (k + 2)) * (innerSL ℝ v) (x - y) := by
  by_cases hk : k = 0
  · subst k
    simp [invDistPowFDerivFormula]
  · have hd : dist x y ≠ 0 := dist_ne_zero.mpr hxy
    simp only [invDistPowFDerivFormula, distFDerivFormula, smul_apply,
      smul_eq_mul, nsmul_eq_mul, innerSL_apply_apply]
    rw [real_inner_smul_left, real_inner_comm]
    simp only [inner_sub_right]
    field_simp [hd, pow_ne_zero]
    have hfactor :
        dist x y ^ 2 * dist x y ^ (k - 1) * dist x y ^ k =
          dist x y * dist x y ^ (k * 2) := by
      calc
        dist x y ^ 2 * dist x y ^ (k - 1) * dist x y ^ k =
            dist x y ^ (2 + (k - 1) + k) := by
              rw [← pow_add, ← pow_add]
        _ = dist x y ^ (1 + k * 2) := by
              congr 1
              omega
        _ = dist x y * dist x y ^ (k * 2) := by
              rw [pow_add]
              simp
    ring_nf
    rw [hfactor]

/-- Operator formula for the derivative of an inverse distance power away from its pole. -/
theorem invDistPowFDerivFormula_eq_of_ne
    (k : ℕ) {x y : E} (hxy : x ≠ y) :
    invDistPowFDerivFormula k x y =
      (-(k : ℝ) / dist x y ^ (k + 2)) • innerSL ℝ (x - y) := by
  ext v
  rw [invDistPowFDerivFormula_apply_eq_of_ne k hxy]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
  rw [real_inner_comm]

/-- An inverse natural power of Euclidean distance is Fréchet differentiable away from its pole. -/
theorem hasFDerivAt_inv_dist_pow {k : ℕ} {x y : E} (hxy : x ≠ y) :
    HasFDerivAt (fun z : E ↦ (dist z y ^ k)⁻¹) (invDistPowFDerivFormula k x y) x := by
  have hd : HasFDerivAt (fun z : E ↦ dist z y) (distFDerivFormula x y) x :=
    hasFDerivAt_dist_left hxy
  have hdist : dist x y ≠ 0 := dist_ne_zero.mpr hxy
  have hpow :
      HasFDerivAt (fun z : E ↦ dist z y ^ k)
        ((k • dist x y ^ (k - 1)) • distFDerivFormula x y) x :=
    hd.pow k
  have hcomp :=
    (hasFDerivAt_inv (𝕜 := ℝ) (x := dist x y ^ k) (pow_ne_zero k hdist)).comp x hpow
  have hderiv :
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (-((dist x y ^ k) ^ 2)⁻¹)).comp
          ((k • dist x y ^ (k - 1)) • distFDerivFormula x y) =
        invDistPowFDerivFormula k x y := by
    ext v
    simp [invDistPowFDerivFormula, ContinuousLinearMap.smulRight_apply,
      smul_smul, mul_assoc, mul_comm]
  exact hcomp.congr_fderiv hderiv

/-- A constant divided by a natural power of Euclidean distance is Fréchet differentiable away
from its pole. -/
theorem hasFDerivAt_const_div_dist_pow {k : ℕ} {x y : E} (hxy : x ≠ y) (c : ℝ) :
    HasFDerivAt (fun z : E ↦ c / dist z y ^ k)
      (c • invDistPowFDerivFormula k x y) x := by
  have h := (hasFDerivAt_inv_dist_pow (k := k) hxy).const_smul c
  rw [show (fun z : E ↦ c / dist z y ^ k) =
      c • fun z : E ↦ (dist z y ^ k)⁻¹ by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]]
  exact h

section InverseDistanceSmoothness

attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

/-- An inverse natural power of Euclidean distance is smooth away from its
pole. -/
theorem contDiffAt_inv_dist_pow (m : ℕ∞)
    {k : ℕ} {x y : E} (hxy : x ≠ y) :
    ContDiffAt ℝ m (fun z : E ↦ (dist z y ^ k)⁻¹) x := by
  have hsub :
      ContDiffAt ℝ m (fun z : E ↦ z - y) x :=
    contDiffAt_id.sub contDiffAt_const
  have hdist :
      ContDiffAt ℝ m (fun z : E ↦ dist z y) x := by
    simpa only [dist_eq_norm] using
      (ContDiffAt.norm (𝕜 := ℝ) (E := E)
        hsub (sub_ne_zero.mpr hxy))
  rw [show
      (fun z : E ↦ (dist z y ^ k)⁻¹) =
        (fun z : E ↦ dist z y ^ k)⁻¹ by
    funext z
    rfl]
  exact
    (hdist.pow k).inv
      (pow_ne_zero k (dist_ne_zero.mpr hxy))

end InverseDistanceSmoothness

/-- The Hessian formula for an inverse distance power, evaluated in the fixed
direction `v`. It is the derivative of `invDistPowFDerivFormula k · y v`
away from the pole. -/
noncomputable def invDistPowSecondFDerivFormula (k : ℕ) (x y v : E) : E →L[ℝ] ℝ :=
  ((-(k : ℝ)) / dist x y ^ (k + 2)) • innerSL ℝ v +
    ((innerSL ℝ v) (x - y)) •
      ((-(k : ℝ)) • invDistPowFDerivFormula (k + 2) x y)

/-- The derivative of an evaluated inverse-distance-power derivative.

This is the Hessian of `z ↦ (dist z y ^ k)⁻¹`, evaluated in the fixed
direction `v`. The ball and half-space Poisson kernels both use it. -/
theorem hasFDerivAt_invDistPowFDerivFormula_apply
    {k : ℕ} {x y v : E} (hxy : x ≠ y) :
    HasFDerivAt (fun z : E ↦ invDistPowFDerivFormula k z y v)
      (invDistPowSecondFDerivFormula k x y v) x := by
  let s : E → ℝ := fun z ↦ (-(k : ℝ)) / dist z y ^ (k + 2)
  let t : E → ℝ := fun z ↦ (innerSL ℝ v) (z - y)
  have hs :
      HasFDerivAt s
        ((-(k : ℝ)) • invDistPowFDerivFormula (k + 2) x y) x := by
    simpa [s] using
      (hasFDerivAt_const_div_dist_pow
        (k := k + 2) (x := x) (y := y) hxy (-(k : ℝ)))
  have ht := by
    have hsub :=
      (hasFDerivAt_id (𝕜 := ℝ) (x := x)).sub
        (hasFDerivAt_const (c := y) (x := x))
    have hlin :=
      ContinuousLinearMap.hasFDerivAt
        (f := (innerSL ℝ v : E →L[ℝ] ℝ)) (x := x - y)
    exact hlin.comp x hsub
  have ht_function :=
    ht.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z ↦ show
        ((innerSL ℝ v) ∘ ((id : E → E) - fun _ ↦ y)) z = t z by
          simp [t])
  have ht_deriv :
      (innerSL ℝ v).comp
          ((ContinuousLinearMap.id ℝ E) - 0) =
        innerSL ℝ v := by
    ext z
    simp
  have ht' := ht_function.congr_fderiv ht_deriv
  have hEq :
      (fun z : E ↦ invDistPowFDerivFormula k z y v) =ᶠ[nhds x]
        fun z ↦ s z * t z := by
    filter_upwards [eventually_ne_nhds hxy] with z hz
    simpa [s, t] using
      (invDistPowFDerivFormula_apply_eq_of_ne
        (k := k) (x := z) (y := y) (v := v) hz)
  simpa [s, t, invDistPowSecondFDerivFormula] using (hs.mul ht').congr_of_eventuallyEq hEq

/-- Away from the diagonal, the distance derivative has operator norm one. -/
theorem norm_distFDerivFormula_of_ne {x y : E} (hxy : x ≠ y) :
    ‖distFDerivFormula x y‖ = 1 := by
  have hdist : dist x y ≠ 0 := dist_ne_zero.mpr hxy
  calc
    ‖distFDerivFormula x y‖ = ‖(dist x y)⁻¹ • (x - y)‖ := by
      simpa [distFDerivFormula] using
        (innerSL_apply_norm (𝕜 := ℝ) (E := E) ((dist x y)⁻¹ • (x - y)))
    _ = ‖(dist x y)⁻¹‖ * ‖x - y‖ := norm_smul _ _
    _ = (dist x y)⁻¹ * dist x y := by
      simp [dist_eq_norm]
    _ = 1 := inv_mul_cancel₀ hdist

/-- The operator norm of the distance derivative is at most one, including on the diagonal where
the formula is the zero map. -/
theorem norm_distFDerivFormula_le_one (x y : E) : ‖distFDerivFormula x y‖ ≤ 1 := by
  by_cases hxy : x = y
  · subst y
    simp [distFDerivFormula]
  · exact (norm_distFDerivFormula_of_ne hxy).le

/-- Exact decay of the derivative of an inverse natural power of distance. -/
theorem norm_invDistPowFDerivFormula_of_ne
    (k : ℕ) {x y : E} (hxy : x ≠ y) :
    ‖invDistPowFDerivFormula k x y‖ =
      (k : ℝ) * (dist x y ^ (k + 1))⁻¹ := by
  rw [invDistPowFDerivFormula_eq_of_ne k hxy, norm_smul, innerSL_apply_norm]
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hdpow : 0 < dist x y ^ (k + 2) := pow_pos hd _
  rw [Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg k), abs_of_pos hdpow]
  rw [show ‖x - y‖ = dist x y by simp [dist_eq_norm]]
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  field_simp [ne_of_gt hd, pow_ne_zero]

/-- Multiplying by the distance cancels one order of inverse-distance decay. -/
theorem dist_mul_norm_invDistPowFDerivFormula_of_ne
    (k : ℕ) {x y : E} (hxy : x ≠ y) :
    dist x y * ‖invDistPowFDerivFormula k x y‖ =
      (k : ℝ) * (dist x y ^ k)⁻¹ := by
  rw [norm_invDistPowFDerivFormula_of_ne k hxy, pow_succ]
  field_simp [dist_ne_zero.mpr hxy, pow_ne_zero]

/-- The Hessian of an inverse distance power, evaluated in a direction `v`,
decays like `dist x y ^ (-(k + 2))`.

This is the dominating bound used to differentiate ball and half-space
Poisson integrals twice under the integral sign. -/
theorem norm_invDistPowFDerivFormula_apply_fderiv_le
    (k : ℕ) {x y v : E} (hxy : x ≠ y) :
    ‖invDistPowSecondFDerivFormula k x y v‖ ≤
      (k : ℝ) * ((k + 3 : ℕ) : ℝ) * ‖v‖ *
        (dist x y ^ (k + 2))⁻¹ := by
  dsimp only [invDistPowSecondFDerivFormula]
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hinner :
      |(innerSL ℝ v) (x - y)| ≤ ‖v‖ * dist x y := by
    simpa [innerSL_apply_apply, dist_eq_norm] using
      (abs_real_inner_le_norm v (x - y))
  have hfirst :
      ‖((-(k : ℝ)) / dist x y ^ (k + 2)) • innerSL ℝ v‖ =
        (k : ℝ) * ‖v‖ * (dist x y ^ (k + 2))⁻¹ := by
    rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs]
    simp only [abs_div, abs_neg, abs_of_nonneg hk,
      abs_of_pos (pow_pos hd (k + 2))]
    ring
  have hsecond :
      ‖((innerSL ℝ v) (x - y)) •
          ((-(k : ℝ)) • invDistPowFDerivFormula (k + 2) x y)‖ ≤
        ‖v‖ * (k : ℝ) * ((k + 2 : ℕ) : ℝ) *
          (dist x y ^ (k + 2))⁻¹ := by
    rw [norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg hk]
    calc
      |(innerSL ℝ v) (x - y)| *
          ((k : ℝ) * ‖invDistPowFDerivFormula (k + 2) x y‖) ≤
          (‖v‖ * dist x y) *
            ((k : ℝ) * ‖invDistPowFDerivFormula (k + 2) x y‖) := by
        exact mul_le_mul_of_nonneg_right hinner
          (mul_nonneg hk (norm_nonneg _))
      _ = ‖v‖ * (k : ℝ) *
          (dist x y * ‖invDistPowFDerivFormula (k + 2) x y‖) := by ring
      _ = ‖v‖ * (k : ℝ) * ((k + 2 : ℕ) : ℝ) *
          (dist x y ^ (k + 2))⁻¹ := by
        rw [dist_mul_norm_invDistPowFDerivFormula_of_ne (k + 2) hxy]
        ring
  calc
    ‖((-(k : ℝ)) / dist x y ^ (k + 2)) • innerSL ℝ v +
        ((innerSL ℝ v) (x - y)) •
          ((-(k : ℝ)) • invDistPowFDerivFormula (k + 2) x y)‖ ≤
        ‖((-(k : ℝ)) / dist x y ^ (k + 2)) • innerSL ℝ v‖ +
          ‖((innerSL ℝ v) (x - y)) •
            ((-(k : ℝ)) • invDistPowFDerivFormula (k + 2) x y)‖ :=
      norm_add_le _ _
    _ ≤ (k : ℝ) * ‖v‖ * (dist x y ^ (k + 2))⁻¹ +
        ‖v‖ * (k : ℝ) * ((k + 2 : ℕ) : ℝ) *
          (dist x y ^ (k + 2))⁻¹ := by
      exact add_le_add hfirst.le hsecond
    _ = (k : ℝ) * ((k + 3 : ℕ) : ℝ) * ‖v‖ *
          (dist x y ^ (k + 2))⁻¹ := by
      push_cast
      ring

/-- Sharp decay bound for the derivative of an inverse natural power of distance. -/
theorem norm_invDistPowFDerivFormula_le (k : ℕ) {x y : E} (hxy : x ≠ y) :
    ‖invDistPowFDerivFormula k x y‖ ≤
      (k : ℝ) * (dist x y ^ (k + 1))⁻¹ := by
  exact (norm_invDistPowFDerivFormula_of_ne k hxy).le

/-- Sharp uniform bound when the distance is bounded below by a positive constant. -/
theorem norm_invDistPowFDerivFormula_le_of_le_dist
    (k : ℕ) {x y : E} {δ : ℝ} (hδpos : 0 < δ) (hδ : δ ≤ dist x y) :
    ‖invDistPowFDerivFormula k x y‖ ≤
      (k : ℝ) * (δ ^ (k + 1))⁻¹ := by
  have hxy : x ≠ y := by
    apply dist_ne_zero.mp
    exact ne_of_gt (lt_of_lt_of_le hδpos hδ)
  rw [norm_invDistPowFDerivFormula_of_ne k hxy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  have hpow :
      δ ^ (k + 1) ≤ dist x y ^ (k + 1) :=
    pow_le_pow_left₀ hδpos.le hδ (k + 1)
  simpa [one_div] using
    one_div_le_one_div_of_le (pow_pos hδpos (k + 1)) hpow

/-- Sharp bound for a distance-weighted inverse-distance derivative. -/
theorem dist_mul_norm_invDistPowFDerivFormula_le_of_le_dist
    (k : ℕ) {x y : E} {δ : ℝ} (hδpos : 0 < δ) (hδ : δ ≤ dist x y) :
    dist x y * ‖invDistPowFDerivFormula k x y‖ ≤
      (k : ℝ) * (δ ^ k)⁻¹ := by
  have hxy : x ≠ y := by
    apply dist_ne_zero.mp
    exact ne_of_gt (lt_of_lt_of_le hδpos hδ)
  rw [dist_mul_norm_invDistPowFDerivFormula_of_ne k hxy]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  have hpow : δ ^ k ≤ dist x y ^ k :=
    pow_le_pow_left₀ hδpos.le hδ k
  simpa [one_div] using
    one_div_le_one_div_of_le (pow_pos hδpos k) hpow

end EuclideanDistance
