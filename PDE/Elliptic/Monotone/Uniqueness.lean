/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.PrescribedBoundary

/-!
# Uniqueness for strictly monotone fluxes with prescribed boundary values

Two weak solutions of `-div a(x, Du) + g(x, u) = ℓ` in the same
Sobolev boundary class agree when the flux is strictly monotone and the
reaction is monotone. Strict monotonicity is pointwise almost everywhere;
no uniform positive modulus is required.

Testing the difference of the equations with `u - v` gives zero for
the sum of two nonnegative integrals. Linear growth makes these pairings
integrable. The flux integral can vanish only if
the gradients agree almost everywhere. Bounded-domain Poincaré then
gives equality of the solutions.

The uniqueness argument needs no hemicontinuity, continuity of the
reaction, or coercive growth lower bound. Those hypotheses are used
for existence in `PrescribedBoundary`. As there, the boundary condition
means membership in an affine translate of the closure-defined `H¹₀`;
no pointwise trace or boundary regularity is assumed.
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "V" => H¹₀(Ω)
local notation "μ" => domainMeasure n Ω
local notation "P" => baseCoordCLM (n := n) (Ω := Ω)
local notation "Q" => wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Ω)

/-- Strict monotonicity of the gradient flux and monotonicity of the
reaction give uniqueness in every prescribed `H¹` boundary class on a
bounded domain of positive dimension.

The strictness assumption is
`⟨a(x,p) - a(x,q), p - q⟩ > 0` for `p ≠ q`; no uniform lower
coefficient is assumed. Measurability and linear growth give integrability
of both weak pairings, while the boundary condition allows testing
the difference of the equations with `u - v ∈ H¹₀`. -/
theorem eq_of_strictMonotone_gradientFlux_reaction
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (hstrict : ∀ᵐ x ∂μ, ∀ p q, p ≠ q →
      0 < inner ℝ (a x p - a x q) (p - q))
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ 2 μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖)
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : StrongDual ℝ V) (φ u v : H¹(Ω))
    (huBoundary : u - φ ∈ h10Submodule (n := n) (Ω := Ω))
    (hvBoundary : v - φ ∈ h10Submodule (n := n) (Ω := Ω))
    (hu : ∀ z : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (z : H¹(Ω)) x) ∂μ) +
      (∫ x, g x (Q u x) * P z x ∂μ) = ℓ z)
    (hv : ∀ z : V, (∫ x, inner ℝ (a x (∇ v x)) (∇ (z : H¹(Ω)) x) ∂μ) +
      (∫ x, g x (Q v x) * P z x ∂μ) = ℓ z) :
    u = v := by
  have hq : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 :=
    ENNReal.HolderConjugate.conjExponent_eq
  have hpow : (2 : ℝ) - 1 = 1 := by norm_num
  refine eq_of_strictMonotone_wkpGradientFlux_reaction
    (p := (2 : NNReal)) (h := h) (C := C) (h₀ := h₀) (C₀ := C₀)
    (by norm_num) a hmeas
    (by simpa only [ENNReal.coe_ofNat, hq] using hh) ?_ hn hΩbounded hstrict
    g hgmeas (by simpa only [ENNReal.coe_ofNat, hq] using hh₀) ?_ hgmono
    (fun z ↦ ℓ z) u v ?_ hu hv
  · simpa only [NNReal.coe_ofNat, hpow, Real.rpow_one] using hgrowth
  · simpa only [NNReal.coe_ofNat, hpow, Real.rpow_one] using hggrowth
  · change u - v ∈ h10Submodule (n := n) (Ω := Ω)
    simpa only [sub_sub_sub_cancel_right] using
      (h10Submodule (n := n) (Ω := Ω)).sub_mem huBoundary hvBoundary

end SobolevSpace.GraphSpace
