/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityComparison

/-!
# Size of the half-plane Green stream

For a vorticity `f` continuous on the closed upper half-plane `H̄`, vanishing there outside the
disc of radius `R ≥ 0` and bounded by `B`, the Green stream `φ = halfSpaceGreenPotential f` has
the derivative within `H̄` of size at most `(1 + R²) B` (it is the rotated velocity,
`fderivWithin_halfSpaceGreenPotential_eq`), so it is `(1 + R²) B`-Lipschitz on `H̄`
(`abs_halfSpaceGreenPotential_sub_le`), and since it vanishes on the boundary,
`|φ(x)| ≤ (1 + R²) B x₁` (`abs_halfSpaceGreenPotential_le`).

The velocity of a stream `ψ` is the linear image `fderivRotation (Dψ(x))` of its derivative,
with `fderivRotation ℓ = (-ℓ e₁, ℓ e₀)` (`planarStreamVelocity_eq_fderivRotation`), so the
derivatives of the velocity are those of `Dψ` composed with a fixed map of norm at most `2`.

## Main definitions

* `fderivRotation`: the velocity `(-ℓ e₁, ℓ e₀)` of a stream whose derivative at a point is `ℓ`.

## Main results

* `norm_fderivWithin_halfSpaceGreenPotential_le`: the derivative of `φ` within `H̄` is at most
  `(1 + R²) B`.
* `abs_halfSpaceGreenPotential_sub_le`: `φ` is `(1 + R²) B`-Lipschitz on `H̄`.
* `abs_halfSpaceGreenPotential_le`: `|φ(x)| ≤ (1 + R²) B x₁` on `H̄`.
* `planarStreamVelocity_eq_fderivRotation`: the velocity of a stream is the image of its
  derivative under `fderivRotation`.
* `norm_fderivRotation_le`: `fderivRotation` has norm at most `2`.
* `contDiffAt_planarStreamVelocity`: the velocity of a stream that is `C^{n+1}` at a point is
  `C^n` there.
* `norm_iteratedFDeriv_planarStreamVelocity_le`: the derivatives of order `k` of the velocity are
  at most twice the derivatives of order `k + 1` of the stream.
-/

@[expose] public section

noncomputable section

open Set GreenFunction
open PDE.Analysis (evenReflection evenReflection_of_nonneg continuous_evenReflection
  hasCompactSupport_evenReflection_of_eq_zero)

namespace IncompressibleFlow

set_option linter.missingDocs true

set_option quotPrecheck false in
local notation "H̄" => {y : ℝ^2 | 0 ≤ y 1}

/-- The rotation `streamRotation` does not increase norms. -/
theorem norm_streamRotation_le (v : ℝ^2) : ‖streamRotation v‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w ↦ ?_
  set v' : ℝ^2 := WithLp.toLp 2 ![v 1, -v 0]
  have happ : streamRotation v w = inner ℝ v' w := by
    simp [streamRotation, v', EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two,
      dotProduct]
    ring
  have hn : ‖v'‖ = ‖v‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [v', Fin.sum_univ_two, add_comm]
  rw [happ, Real.norm_eq_abs, ← hn]
  exact abs_real_inner_le_norm v' w

variable {f : ℝ^2 → ℝ} {R B : ℝ}

/-- The derivative within the closed half-plane of the Green stream is at most `(1 + R²) B`. -/
theorem norm_fderivWithin_halfSpaceGreenPotential_le (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (halfSpaceGreenPotential f) H̄ x‖ ≤ (1 + R ^ 2) * B := by
  rw [fderivWithin_halfSpaceGreenPotential_eq hf hR hx]
  exact (norm_streamRotation_le _).trans (norm_halfPlaneVelocity_le_of_abs_le hf hR hR0 hB x)

/-- The Green stream is differentiable within the closed half-plane. -/
theorem differentiableOn_halfSpaceGreenPotential (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) :
    DifferentiableOn ℝ (halfSpaceGreenPotential f) H̄ := by
  have hφ : halfSpaceGreenPotential f = halfSpaceGreenPotential (evenReflection f) :=
    halfSpaceGreenPotential_congr fun y hy ↦ (evenReflection_of_nonneg (le_of_lt hy)).symm
  rw [hφ]
  exact ((contDiff_one_halfSpaceGreenPotential
    (continuous_evenReflection hf)
    (hasCompactSupport_evenReflection_of_eq_zero hR)).differentiable
    one_ne_zero).differentiableOn

/-- **The Green stream is Lipschitz** on the closed half-plane with constant `(1 + R²) B`. -/
theorem abs_halfSpaceGreenPotential_sub_le (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) {x y : ℝ^2} (hx : 0 ≤ x 1) (hy : 0 ≤ y 1) :
    |halfSpaceGreenPotential f x - halfSpaceGreenPotential f y| ≤ (1 + R ^ 2) * B * ‖x - y‖ := by
  have hconv : Convex ℝ H̄ := convex_halfSpace_ge (EuclideanSpace.proj (1 : Fin 2)).isLinear 0
  have h := hconv.norm_image_sub_le_of_norm_fderivWithin_le
    (differentiableOn_halfSpaceGreenPotential hf hR)
    (fun z hz ↦ norm_fderivWithin_halfSpaceGreenPotential_le hf hR hR0 hB hz) hy hx
  simpa [Real.norm_eq_abs] using h

/-- **Size of the Green stream**: `|φ(x)| ≤ (1 + R²) B x₁` on the closed half-plane. -/
theorem abs_halfSpaceGreenPotential_le (hf : ContinuousOn f H̄)
    (hR : ∀ y : ℝ^2, 0 ≤ y 1 → R < ‖y‖ → f y = 0) (hR0 : 0 ≤ R)
    (hB : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ B) {x : ℝ^2} (hx : 0 ≤ x 1) :
    |halfSpaceGreenPotential f x| ≤ (1 + R ^ 2) * B * x 1 := by
  set x' : ℝ^2 := WithLp.toLp 2 ![x 0, 0]
  have hx' : 0 ≤ x' 1 := by simp [x']
  have hb : halfSpaceGreenPotential f x' = 0 :=
    halfSpaceGreenPotential_boundary f
      (by simp [x', SobolevSpace.HalfSpace.boundary, PDE.Common.lastIndex])
  have h := abs_halfSpaceGreenPotential_sub_le hf hR hR0 hB hx hx'
  have hn : ‖x - x'‖ = x 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [x', Fin.sum_univ_two, Real.sqrt_sq hx]
  rwa [hb, sub_zero, hn] at h

/-! ### The velocity as a linear image of the derivative -/

/-- The velocity `(-ℓ e₁, ℓ e₀)` of a stream whose derivative at a point is `ℓ`. -/
def fderivRotation : (ℝ^2 →L[ℝ] ℝ) →L[ℝ] ℝ^2 :=
  (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).smulRight
      (-EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) +
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))

/-- The velocity of a stream is the image of its derivative under `fderivRotation`. -/
theorem planarStreamVelocity_eq_fderivRotation (ψ : ℝ^2 → ℝ) (x : ℝ^2) :
    planarStreamVelocity ψ x = fderivRotation (fderiv ℝ ψ x) := by
  ext i
  fin_cases i <;> simp [fderivRotation, planarStreamVelocity, PDE.partialDeriv]

/-- The map `fderivRotation` has norm at most `2`. -/
theorem norm_fderivRotation_le : ‖fderivRotation‖ ≤ 2 := by
  have h : ∀ (i j : Fin 2) (s : ℝ), ‖(ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single i (1 : ℝ))).smulRight (s • EuclideanSpace.single j (1 : ℝ))‖ ≤
        |s| := by
    intro i j s
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, PiLp.norm_single, norm_one,
      mul_one, Real.norm_eq_abs]
    have : ‖ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ℓ ↦ ?_
      simpa using ℓ.le_opNorm (EuclideanSpace.single i (1 : ℝ))
    nlinarith [abs_nonneg s]
  have h1 := h 1 0 (-1)
  have h2 := h 0 1 1
  simp only [neg_smul, one_smul, abs_neg, abs_one] at h1 h2
  have h3 := norm_add_le ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))).smulRight
      (-EuclideanSpace.single (0 : Fin 2) (1 : ℝ)))
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))).smulRight
      (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
  unfold fderivRotation
  linarith

/-- `streamRotation` inverts `fderivRotation`. -/
theorem streamRotation_fderivRotation (ℓ : ℝ^2 →L[ℝ] ℝ) :
    streamRotation (fderivRotation ℓ) = ℓ := by
  ext1 v
  have hv : v = v 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) +
      v 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext j; fin_cases j <;> simp
  conv_rhs => rw [hv]
  simp [streamRotation, fderivRotation]
  ring

/-- The derivative of a stream is the rotated velocity. -/
theorem fderiv_eq_streamRotation (ψ : ℝ^2 → ℝ) (x : ℝ^2) :
    fderiv ℝ ψ x = streamRotation (planarStreamVelocity ψ x) := by
  rw [planarStreamVelocity_eq_fderivRotation, streamRotation_fderivRotation]

/-- The velocity of a stream that is `C^{n+1}` at a point is `C^n` there. -/
theorem contDiffAt_planarStreamVelocity {ψ : ℝ^2 → ℝ} {x : ℝ^2} {n : WithTop ℕ∞}
    (hψ : ContDiffAt ℝ (n + 1) ψ x) : ContDiffAt ℝ n (planarStreamVelocity ψ) x := by
  have h : planarStreamVelocity ψ = fun y ↦ fderivRotation (fderiv ℝ ψ y) :=
    funext (planarStreamVelocity_eq_fderivRotation ψ)
  rw [h]
  exact fderivRotation.contDiff.contDiffAt.comp x (hψ.fderiv_right le_rfl)

/-- The derivatives of order `k` of the velocity are at most twice the derivatives of
order `k + 1` of the stream. -/
theorem norm_iteratedFDeriv_planarStreamVelocity_le {ψ : ℝ^2 → ℝ} {x : ℝ^2} {k : ℕ}
    (hψ : ContDiffAt ℝ (k + 1) ψ x) :
    ‖iteratedFDeriv ℝ k (planarStreamVelocity ψ) x‖ ≤ 2 * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ := by
  have h : planarStreamVelocity ψ = fderivRotation ∘ fderiv ℝ ψ :=
    funext (planarStreamVelocity_eq_fderivRotation ψ)
  rw [h, ← norm_iteratedFDeriv_fderiv]
  exact (fderivRotation.norm_iteratedFDeriv_comp_left (hψ.fderiv_right le_rfl) le_rfl).trans
    (mul_le_mul_of_nonneg_right norm_fderivRotation_le (norm_nonneg _))

end IncompressibleFlow
