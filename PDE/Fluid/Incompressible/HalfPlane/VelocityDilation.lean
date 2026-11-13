/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityHolder
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.Dilation
import PDE.Spaces.Sobolev.Calculus.Product.ClassicalLeibniz

/-!
# The half-plane velocity gradient under dilations

For a continuous compactly supported vorticity `ω` and `λ > 0`, the Green potential of the dilated
vorticity `ω_λ = ω(λ ·)` is `λ⁻² φ(λ ·)` (`GreenFunction.halfSpaceGreenPotential_comp_smul`), so
the velocity is `λ⁻¹ u(λ ·)` (`halfPlaneVelocity_comp_smul`) and the velocity gradient is
dilation invariant, `∂ᵢ(u_λ)ₖ(x) = ∂ᵢuₖ(λ x)` at points of the open upper half-plane
(`partialDeriv_halfPlaneVelocity_comp_smul`).

The size bound `|∂ᵢuₖ| ≤ 50M/α + 8B + 10L` of `abs_partialDeriv_halfPlaneVelocity_le` is not
scale invariant; applied to `ω_λ` it gives, for every `λ > 0`,

`|∂ᵢuₖ(x)| ≤ 50 λ^α M/α + 8B + 10 λ⁻² ∫_{ℝ²₊} |ω|`

(`abs_partialDeriv_halfPlaneVelocity_le_of_scale`). For a vorticity supported in a disc of radius
`ρ` with Hölder constant `M` the choice `λ = ρ` gives the scale-invariant form
`|∂ᵢuₖ| ≲ ρ^α M + B`.

## Main results

* `halfPlaneVelocity_comp_smul`: `u(ω(λ ·))(x) = λ⁻¹ u(ω)(λ x)`.
* `partialDeriv_halfPlaneVelocity_comp_smul`: `∂ᵢ(u(ω(λ ·)))ₖ(x) = ∂ᵢ(u(ω))ₖ(λ x)` in the open
  upper half-plane.
* `setIntegral_upper_abs_comp_smul`: `∫_{ℝ²₊} |ω(λ y)| dy = λ⁻² ∫_{ℝ²₊} |ω|`.
* `abs_partialDeriv_halfPlaneVelocity_le_of_scale`: for every `λ > 0`,
  `|∂ᵢuₖ(x)| ≤ 50 λ^α M/α + 8B + 10 λ⁻² ∫_{ℝ²₊} |ω|` in the open upper half-plane.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Pointwise
open GreenFunction SobolevSpace

namespace IncompressibleFlow

variable {ω : ℝ^2 → ℝ} {lam : ℝ}

/-- A constant factor passes through a partial derivative, with no differentiability needed. -/
private theorem partialDeriv_mul_left (c : ℝ) (g : ℝ^2 → ℝ) (i : Fin 2) (x : ℝ^2) :
    (∂[i] (fun y ↦ c * g y)) x = c * (∂[i] g) x :=
  PDE.partialDeriv_const_smul c (f := g)

/-- The dilated vorticity is continuous. -/
theorem continuous_comp_smul (hω : Continuous ω) (lam : ℝ) :
    Continuous fun y : ℝ^2 ↦ ω (lam • y) :=
  hω.comp (continuous_const_smul lam)

/-- **The velocity of a dilated vorticity**: `u(ω(λ ·))(x) = λ⁻¹ u(ω)(λ x)`. -/
theorem halfPlaneVelocity_comp_smul (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hlam : 0 < lam) (x : ℝ^2) (k : Fin 2) :
    halfPlaneVelocity (fun y ↦ ω (lam • y)) x k = lam⁻¹ * halfPlaneVelocity ω (lam • x) k := by
  have hG : halfSpaceGreenPotential (fun y ↦ ω (lam • y)) =
      fun y ↦ (lam ^ 2)⁻¹ * halfSpaceGreenPotential ω (lam • y) :=
    funext fun y ↦ halfSpaceGreenPotential_comp_smul hlam ω y
  have hd : Differentiable ℝ (halfSpaceGreenPotential ω) :=
    (contDiff_one_halfSpaceGreenPotential hω hc).differentiable one_ne_zero
  have hpd (j : Fin 2) : (∂[j] (halfSpaceGreenPotential (fun y ↦ ω (lam • y)))) x =
      (lam ^ 2)⁻¹ * (lam * (∂[j] (halfSpaceGreenPotential ω)) (lam • x)) := by
    rw [hG, show (fun y ↦ (lam ^ 2)⁻¹ * halfSpaceGreenPotential ω (lam • y)) =
      (fun y ↦ (lam ^ 2)⁻¹ * (fun z ↦ halfSpaceGreenPotential ω (lam • z)) y) from rfl,
      partialDeriv_mul_left, partialDeriv_comp_const_smul lam (hd _)]
  have hl : lam ≠ 0 := hlam.ne'
  fin_cases k
  · change -(∂[(1 : Fin 2)] (halfSpaceGreenPotential (fun y ↦ ω (lam • y)))) x =
      lam⁻¹ * -(∂[(1 : Fin 2)] (halfSpaceGreenPotential ω)) (lam • x)
    rw [hpd]; field_simp
  · change (∂[(0 : Fin 2)] (halfSpaceGreenPotential (fun y ↦ ω (lam • y)))) x =
      lam⁻¹ * (∂[(0 : Fin 2)] (halfSpaceGreenPotential ω)) (lam • x)
    rw [hpd]; field_simp

variable {M α B : ℝ}

/-- A positive dilation maps the open upper half-plane into itself. -/
theorem smul_mem_upper (hlam : 0 < lam) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    lam • x ∈ HalfSpace.upper 2 := by
  rw [← smul_upper_two hlam]
  exact smul_mem_smul_set hx

/-- **Dilation invariance of the velocity gradient**: `∂ᵢ(u(ω(λ ·)))ₖ(x) = ∂ᵢ(u(ω))ₖ(λ x)` in the
open upper half-plane, for a continuous compactly supported vorticity Hölder on the closed upper
half-plane. -/
theorem partialDeriv_halfPlaneVelocity_comp_smul (hω : Continuous ω) (hc : HasCompactSupport ω)
    (hα : 0 < α) (hα1 : α ≤ 1) (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hlam : 0 < lam) (i k : Fin 2) {x : ℝ^2} (hx : x ∈ HalfSpace.upper 2) :
    (∂[i] (fun y ↦ halfPlaneVelocity (fun y ↦ ω (lam • y)) y k)) x =
      (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) (lam • x) := by
  have hfun : (fun y ↦ halfPlaneVelocity (fun y ↦ ω (lam • y)) y k) =
      fun y ↦ lam⁻¹ * (fun z ↦ halfPlaneVelocity ω (lam • z) k) y :=
    funext fun y ↦ halfPlaneVelocity_comp_smul hω hc hlam y k
  have hdk : DifferentiableAt ℝ (fun y ↦ halfPlaneVelocity ω y k) (lam • x) :=
    (hasFDerivAt_halfPlaneVelocity hω hc hα hα1 hM k (smul_mem_upper hlam hx)).differentiableAt
  rw [hfun, partialDeriv_mul_left, partialDeriv_comp_const_smul lam hdk, ← mul_assoc,
    inv_mul_cancel₀ hlam.ne', one_mul]

/-- The integral of the dilated vorticity: `∫_{ℝ²₊} |ω(λ y)| dy = λ⁻² ∫_{ℝ²₊} |ω|`. -/
theorem setIntegral_upper_abs_comp_smul (hlam : 0 < lam) (ω : ℝ^2 → ℝ) :
    ∫ y in HalfSpace.upper 2, |ω (lam • y)| = (lam ^ 2)⁻¹ * ∫ y in HalfSpace.upper 2, |ω y| := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := volume) (fun y ↦ |ω y|)
    (HalfSpace.upper 2) hlam
  rwa [smul_upper_two hlam, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h

/-- **The velocity gradient bound at an arbitrary scale.** For a continuous compactly supported
vorticity with `|ω(y) - ω(z)| ≤ M |y - z|^α` and `|ω| ≤ B` on the closed upper half-plane and
every `λ > 0`, `|∂ᵢuₖ(x)| ≤ 50 λ^α M/α + 8B + 10 λ⁻² ∫_{ℝ²₊} |ω|` in the open upper half-plane. -/
theorem abs_partialDeriv_halfPlaneVelocity_le_of_scale (hω : Continuous ω)
    (hc : HasCompactSupport ω) (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
    (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) (hlam : 0 < lam) (i k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    |(∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x| ≤
      50 * (lam ^ α * M) / α + 8 * B +
        10 * ((lam ^ 2)⁻¹ * ∫ y in HalfSpace.upper 2, |ω y|) := by
  have hl0 : lam ≠ 0 := hlam.ne'
  have hnn (y : ℝ^2) (hy : 0 ≤ y 1) : 0 ≤ (lam • y) 1 := by
    simp only [PiLp.smul_apply, smul_eq_mul]; positivity
  have hMl : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 →
      |ω (lam • y) - ω (lam • z)| ≤ lam ^ α * M * ‖y - z‖ ^ α := by
    intro y z hy hz
    refine (hM _ _ (hnn y hy) (hnn z hz)).trans (le_of_eq ?_)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hlam.le,
      Real.mul_rpow hlam.le (norm_nonneg _)]
    ring
  have hBl : ∀ y, 0 ≤ y 1 → |ω (lam • y)| ≤ B := fun y hy ↦ hB _ (hnn y hy)
  have hx' : lam⁻¹ • x ∈ HalfSpace.upper 2 := smul_mem_upper (inv_pos.mpr hlam) hx
  have h := abs_partialDeriv_halfPlaneVelocity_le (continuous_comp_smul hω lam)
    (hc.comp_smul hlam.ne') hα hα1 hMl hBl i k hx'
  rw [partialDeriv_halfPlaneVelocity_comp_smul hω hc hα hα1 hM hlam i k hx', smul_smul,
    mul_inv_cancel₀ hl0, one_smul, setIntegral_upper_abs_comp_smul hlam] at h
  exact h

end IncompressibleFlow
