/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Monotone.FiniteExponent.PrescribedBoundary
public import PDE.Elliptic.Monotone.Reaction

/-!
# Prescribed Sobolev boundary values for monotone elliptic equations

Given any `φ ∈ H¹(Ω)`, the weak equation
`-div a(x, DU) + g(x, U) = ℓ` is solved in the affine class `φ + H¹₀(Ω)`.
The boundary condition means `U - φ ∈ H¹₀`, not a pointwise boundary
restriction. The domain need only be bounded and have positive dimension;
on open domains this is the usual weak Dirichlet condition.

Translation by `Dφ` preserves flux monotonicity and hemicontinuity.
A positive quadratic lower bound survives, with an offset controlled by
`b`, `|h| |Dφ|`, and `|Dφ|²`. These terms are integrable because
`h, Dφ ∈ L²`.
Translation by `φ` also preserves monotonicity and continuity of the
reaction, with an `L²` growth offset.
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

/-- Linear flux growth gives integrability of the weak pairing even
when the trial function has nonzero Sobolev boundary values. -/
theorem integrable_inner_h1GradientFlux
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (u : H¹(Ω)) (v : V) :
    Integrable (fun x ↦ inner ℝ (a x (∇ u x)) (∇ (v : H¹(Ω)) x)) μ := by
  refine integrable_inner_wkpGradientFlux (p := 2) (q := 2) (C := C)
    (by simp) a hmeas hh ?_ u (v : H¹(Ω))
  simpa only [ENNReal.toReal_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hgrowth

/-- A reaction of linear growth pairs integrably with every zero-boundary
test function when the trial function belongs to the full `H¹` space. -/
theorem integrable_h1Nemytskii_test
    (g : ℝ^n → ℝ → ℝ) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry g)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h x + C * ‖s‖)
    (u : H¹(Ω)) (v : V) :
    Integrable (fun x ↦ g x (Q u x) * P v x) μ := by
  have hq : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 :=
    ENNReal.HolderConjugate.conjExponent_eq
  refine integrable_wkpNemytskii_test (p := (2 : NNReal)) (h := h) (C := C) g hmeas
    (by simpa only [ENNReal.coe_ofNat, hq] using hh) ?_ u (v : H¹(Ω))
  simpa only [NNReal.coe_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hgrowth

/-- Every prescribed `H¹` boundary class admits a weak solution for a
monotone, hemicontinuous, quadratically coercive gradient flux and a
continuous monotone reaction with linear growth.

The boundary condition is membership in `φ + H¹₀`, with no additional
trace or boundary regularity assumption. Both integral pairings are
integrable for every trial and test function by
`integrable_inner_h1GradientFlux` and `integrable_h1Nemytskii_test`.
No sign condition or normalization at zero is imposed on the reaction. -/
theorem exists_weak_solution_monotone_prescribed_boundary
    (a : ℝ^n → ℝ^n → ℝ^n) {h : ℝ^n → ℝ} {C : ℝ}
    (hmeas : Measurable (Function.uncurry a)) (hh : MemLp h 2 μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ p, ‖a x p‖ ≤ h x + C * ‖p‖)
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω)
    (hmono : ∀ᵐ x ∂μ, ∀ p q, 0 ≤ inner ℝ (a x p - a x q) (p - q))
    (hhemi : ∀ᵐ x ∂μ, ∀ p q : ℝ^n, ContinuousWithinAt
      (fun t : ℝ ↦ inner ℝ (a x (p + t • q)) q) (Ici 0) 0)
    {b : ℝ^n → ℝ} {c : ℝ} (hc : 0 < c) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ p, c * ‖p‖ ^ 2 - b x ≤ inner ℝ (a x p) p)
    (g : ℝ^n → ℝ → ℝ) {h₀ : ℝ^n → ℝ} {C₀ : ℝ}
    (hgmeas : Measurable (Function.uncurry g)) (hh₀ : MemLp h₀ 2 μ)
    (hggrowth : ∀ᵐ x ∂μ, ∀ s, ‖g x s‖ ≤ h₀ x + C₀ * ‖s‖)
    (hgcont : ∀ᵐ x ∂μ, Continuous (g x))
    (hgmono : ∀ᵐ x ∂μ, Monotone (g x))
    (ℓ : StrongDual ℝ V) (φ : H¹(Ω)) :
    ∃ u : H¹(Ω), u - φ ∈ h10Submodule (n := n) (Ω := Ω) ∧
      ∀ v : V, (∫ x, inner ℝ (a x (∇ u x)) (∇ (v : H¹(Ω)) x) ∂μ) +
        (∫ x, g x (Q u x) * P v x ∂μ) = ℓ v := by
  have hq : ENNReal.conjExponent (2 : ℝ≥0∞) = 2 :=
    ENNReal.HolderConjugate.conjExponent_eq
  have hpow : (2 : ℝ) - 1 = 1 := by norm_num
  refine exists_weak_solution_monotone_wkp_prescribed_boundary
    (p := (2 : NNReal)) (h := h) (C := C) (h₀ := h₀) (C₀ := C₀)
    (by norm_num) a hmeas
    (by simpa only [ENNReal.coe_ofNat, hq] using hh) ?_ hn hΩbounded hmono hhemi hc hb ?_
    g hgmeas (by simpa only [ENNReal.coe_ofNat, hq] using hh₀) ?_ hgcont hgmono ℓ φ
  · simpa only [NNReal.coe_ofNat, hpow, Real.rpow_one] using hgrowth
  · simpa only [NNReal.coe_ofNat, Real.rpow_two] using hlower
  · simpa only [NNReal.coe_ofNat, hpow, Real.rpow_one] using hggrowth

end SobolevSpace.GraphSpace
