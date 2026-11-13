/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.WeakEnergy
public import PDE.Hyperbolic.FirstOrder.SmoothFormulation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Transport energy from differentiated test pairings

The weak second derivative of a Picard trajectory has scalar derivatives after
pairing with smooth compact spatial tests. Integrating those derivatives against
time tests gives the Bochner transport formulation. Spatial mollification and the
transport commutator then give the exact energy identity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology Distributions ContDiff Sobolev

namespace DeGregorio.Iteration

open PDE.Analysis.Evolution PDE.Hyperbolic.FirstOrder
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "H" => PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- Smooth-test scalar evolution gives the signed Bochner transport energy
identity. The commutator theorem supplies testing by the state itself. -/
theorem energy_sub_eq_integral_of_smooth_test_derivative
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, ContinuousOn (fun t ↦
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (hab : a < b)
    (hsym : ∀ t ∈ Icc a b, ∀ j p q,
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) =
        (A t j q p : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1))
    (L : NNReal)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      (∑ l : Fin n,
        ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)‖) ≤ L)
    {U F : ℝ → H}
    (hU : ∀ ℓ : H →L[ℝ] ℝ, ContinuousOn (fun t ↦ ℓ (U t)) (Icc a b))
    (hU2 : MemLp U 2 ν) (hF : MemLp F 2 ν)
    (htest : ∀ ψ : Fin m → 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      let φ : V := WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p))
      ∀ t ∈ Icc a b, HasDerivAt (fun τ ↦ ⟪U τ, transportBaseCLM φ⟫_ℝ)
        (transportTestFunctional (A t) φ (U t) + ⟪F t, transportBaseCLM φ⟫_ℝ) t) :
    ‖U b‖ ^ 2 - ‖U a‖ ^ 2 =
      ∫ t, transportDivergencePairing (A t) (U t) + 2 * ⟪F t, U t⟫_ℝ ∂ν := by
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) (j : Fin n) (p q : Fin m) :
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L :=
    (Finset.single_le_sum (fun l _ ↦ norm_nonneg
      ((A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n l)))
      (Finset.mem_univ j)).trans (hL t ht j p q)
  apply energy_sub_eq_integral_of_weaklyContinuous_transport_weak_equation
    A hA hab hsym L hL U F hU hU2 hF
  apply transport_timeTest_identity_of_smooth_tests hab A hA L hderiv hU2 hF (U a)
  intro ψ φ ζ hζ _ hζsupp
  have hζLp : MemLp ζ 2 ν := memLp_restrict_Ioc_of_continuousOn hζ.continuous.continuousOn
  have hζ'Lp : MemLp (deriv ζ) 2 ν :=
    memLp_restrict_Ioc_of_continuousOn (hζ.continuous_deriv (by simp)).continuousOn
  have hP := hU2.inner_const (𝕜 := ℝ) (transportBaseCLM φ)
  have hB := memLp_transportTestFunctional hab.le A hA L hderiv hU2 φ
  have hG := hF.inner_const (𝕜 := ℝ) (transportBaseCLM φ)
  have hleft := hP.integrable_mul hζ'Lp
  have hright := (hB.add hG).integrable_mul hζLp
  have hint : IntervalIntegrable
      (fun t ↦ (transportTestFunctional (A t) φ (U t) +
        ⟪F t, transportBaseCLM φ⟫_ℝ) * ζ t +
          ⟪U t, transportBaseCLM φ⟫_ℝ * deriv ζ t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact hright.add hleft
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ (htest ψ t (by simpa only [uIcc_of_le hab.le] using ht)).mul
      ((hζ.differentiable (by simp)) t).hasDerivAt) hint
  have hζb : ζ b = 0 := image_eq_zero_of_notMem_tsupport fun hb ↦
    (lt_irrefl b) (hζsupp hb)
  rw [intervalIntegral.integral_of_le hab.le] at hFTC
  change (∫ t, (transportTestFunctional (A t) φ (U t) +
      ⟪F t, transportBaseCLM φ⟫_ℝ) * ζ t +
        ⟪U t, transportBaseCLM φ⟫_ℝ * deriv ζ t ∂ν) =
    ⟪U b, transportBaseCLM φ⟫_ℝ * ζ b -
      ⟪U a, transportBaseCLM φ⟫_ℝ * ζ a at hFTC
  rw [integral_add (f := fun t ↦ (transportTestFunctional (A t) φ (U t) +
      ⟪F t, transportBaseCLM φ⟫_ℝ) * ζ t)
      (g := fun t ↦ ⟪U t, transportBaseCLM φ⟫_ℝ * deriv ζ t) hright hleft,
    hζb, mul_zero, zero_sub] at hFTC
  have hsplit :
      (∫ t, (transportTestFunctional (A t) φ (U t) +
          ⟪F t, transportBaseCLM φ⟫_ℝ) * ζ t ∂ν) =
        (∫ t, transportTestFunctional (A t) φ (U t) * ζ t ∂ν) +
          ∫ t, ⟪F t, transportBaseCLM φ⟫_ℝ * ζ t ∂ν := by
    simp_rw [add_mul]
    exact integral_add (hB.integrable_mul hζLp) (hG.integrable_mul hζLp)
  rw [hsplit] at hFTC
  linarith only [hFTC]

end DeGregorio.Iteration
