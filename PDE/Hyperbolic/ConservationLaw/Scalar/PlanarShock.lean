/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Hyperbolic.ConservationLaw.AffineInterface.BoundaryIntegral
import PDE.Hyperbolic.ConservationLaw.AffineInterface.Trace

/-!
# Planar shocks for scalar conservation laws

We prove the distributional jump calculation for a scalar conservation law

`u_t + (flux u)_x = 0`.

The function `planarShock uL uR speed` equals `uL` on `x < speed * t` and `uR` on
the complementary half-space, including the interface. Its weak integral is exactly

`(flux uL - flux uR - speed * (uL - uR)) * ∫ φ(t, speed * t) dt`.

Consequently, the planar shock is a global weak solution precisely when its states and
speed satisfy the Rankine–Hugoniot jump relation. The proof uses the affine-interface integration
theorem; the flux may be arbitrary because the profile takes only two values.

The same computation with an entropy pair `(η, q)` in place of `(u, flux u)` gives the
entropy production of the shock, so the entropy inequality for one pair is likewise reduced
to a sign condition on a single coefficient.

## Main results

* `integral_weakIntegrand_planarShock`: the weak integral of the two-state profile equals
  `(flux uL - flux uR - speed (uL - uR)) ∫ φ(t, speed t) dt`.
* `isWeakSolution_planarShock_iff_rankineHugoniot`: the planar shock is a weak solution on
  all of spacetime exactly when `flux uL - flux uR = speed (uL - uR)`.
* `integral_entropyWeakIntegrand_planarShock`,
  `satisfiesEntropyInequalityFor_planarShock_iff`: the entropy inequality for a pair
  `(η, q)` holds exactly when `q(uR) - q(uL) ≤ speed (η(uR) - η(uL))`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (5)-(12).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open MeasureTheory
open PDE.Common
open PDE.Hyperbolic.ConservationLaw
open TopologicalSpace

open scoped Distributions Topology

/-- Testing one coordinate derivative against a planar shock leaves only the jump contribution
on the left half-space. -/
theorem integral_planarShock_mul_partialDeriv
    (uL uR speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (i : Fin 2) :
    (∫ p : ℝ^2, planarShock uL uR speed p * (∂[i] (φ : ℝ^2 → ℝ)) p ∂volume) =
      (uL - uR) * ∫ p in AffineInterface.leftHalfSpace speed, (∂[i] (φ : ℝ^2 → ℝ)) p ∂volume := by
  have hd := φ.integrable_partialDeriv i
  have hmeas := AffineInterface.measurableSet_leftHalfSpace speed
  have hpoint : (fun p ↦ planarShock uL uR speed p * (∂[i] (φ : ℝ^2 → ℝ)) p) = fun p ↦
      uR * (∂[i] (φ : ℝ^2 → ℝ)) p + (AffineInterface.leftHalfSpace speed).indicator
        (fun q ↦ (uL - uR) * (∂[i] (φ : ℝ^2 → ℝ)) q) p := by
    funext p
    by_cases hp : p ∈ AffineInterface.leftHalfSpace speed
    · simp only [planarShock, hp, Set.indicator_of_mem, add_sub_cancel]
      ring
    · simp [planarShock, hp]
  rw [hpoint, integral_add (hd.const_mul uR) ((hd.const_mul _).indicator hmeas), integral_const_mul,
    integral_indicator hmeas, integral_const_mul, φ.integral_partialDeriv_eq_zero i]
  ring

/-- Composing a planar shock with a scalar function changes only the jump
coefficient in its tested coordinate derivative. -/
theorem integral_comp_planarShock_mul_partialDeriv
    (g : ℝ → ℝ) (uL uR speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (i : Fin 2) :
    (∫ p : ℝ^2, g (planarShock uL uR speed p) * (∂[i] (φ : ℝ^2 → ℝ)) p ∂volume) = (g uL - g uR) *
      ∫ p in AffineInterface.leftHalfSpace speed, (∂[i] (φ : ℝ^2 → ℝ)) p ∂volume := by
  rw [← integral_planarShock_mul_partialDeriv, ← comp_planarShock g uL uR speed]

/-- A tested time-space pair of scalar planar shocks reduces to a single
trace integral on their common interface. -/
theorem integral_planarShock_linearCombination
    (timeL timeR spaceL spaceR speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p : ℝ^2, (planarShock timeL timeR speed p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
        planarShock spaceL spaceR speed p * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) =
      (spaceL - spaceR - (timeL - timeR) * speed) *
        ∫ t : ℝ, φ (AffineInterface.interface speed t) ∂volume := by
  rw [integral_add (φ.integrable_mul_partialDeriv
      ((locallyIntegrable_planarShock timeL timeR speed).locallyIntegrableOn Set.univ) 0)
    (φ.integrable_mul_partialDeriv
      ((locallyIntegrable_planarShock spaceL spaceR speed).locallyIntegrableOn Set.univ) 1),
    integral_planarShock_mul_partialDeriv, integral_planarShock_mul_partialDeriv,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((φ.integrable_partialDeriv 0).restrict.const_mul _)
      ((φ.integrable_partialDeriv 1).restrict.const_mul _)]
  exact AffineInterface.setIntegral_linearCombination_partialDeriv_leftHalfSpace φ speed _ _

/-- The weak integral of a planar shock is its Rankine–Hugoniot coefficient times the
test-function trace on the interface. -/
theorem integral_weakIntegrand_planarShock
    (flux : ℝ → ℝ) (uL uR speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p : ℝ^2, weakIntegrand flux (planarShock uL uR speed) φ p ∂volume) =
      (flux uL - flux uR - (uL - uR) * speed) *
        ∫ t : ℝ, φ (AffineInterface.interface speed t) ∂volume := by
  simp only [weakIntegrand]
  rw [← integral_planarShock_linearCombination, ← comp_planarShock flux uL uR speed]

/-- A planar shock satisfying Rankine–Hugoniot is a global scalar weak solution. -/
theorem RankineHugoniot.isWeakSolution_planarShock
    {flux : ℝ → ℝ} {uL uR speed : ℝ} (hRH : RankineHugoniot flux uL uR speed) :
    IsWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) := by
  refine ⟨(locallyIntegrable_planarShock uL uR speed).locallyIntegrableOn Set.univ,
    (locallyIntegrable_comp_planarShock flux uL uR speed).locallyIntegrableOn Set.univ, fun φ ↦ ?_⟩
  rw [integral_weakIntegrand_planarShock]
  have hRH' : flux uR - flux uL = speed * (uR - uL) := hRH
  rw [show flux uL - flux uR - (uL - uR) * speed = 0 by linarith, zero_mul]

/-- A scalar planar shock is a global weak solution exactly when its jump
satisfies the Rankine–Hugoniot relation. -/
theorem isWeakSolution_planarShock_iff_rankineHugoniot {flux : ℝ → ℝ} {uL uR speed : ℝ} :
    IsWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) ↔
      RankineHugoniot flux uL uR speed := by
  refine ⟨fun hweak ↦ ?_, RankineHugoniot.isWeakSolution_planarShock⟩
  obtain ⟨φ, _, htrace_pos⟩ :=
    AffineInterface.exists_testFunction_nonneg_integral_interface_pos speed
  have htested := hweak.weak_eq φ
  rw [integral_weakIntegrand_planarShock] at htested
  have := (mul_eq_zero.mp htested).resolve_right htrace_pos.ne'
  change flux uR - flux uL = speed * (uR - uL)
  linarith

/-- The weak entropy integral of a scalar planar shock is its entropy-production
coefficient multiplied by the test-function trace on the interface. -/
theorem integral_entropyWeakIntegrand_planarShock
    {a : ℝ → ℝ} (E : EntropyPair a) (uL uR speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p : ℝ^2, entropyWeakIntegrand (planarShock uL uR speed) E φ p ∂volume) =
      (E.q uL - E.q uR - (E.η uL - E.η uR) * speed) *
        ∫ t : ℝ, φ (AffineInterface.interface speed t) ∂volume := by
  simp only [entropyWeakIntegrand]
  rw [← integral_planarShock_linearCombination, ← comp_planarShock E.η uL uR speed,
    ← comp_planarShock E.q uL uR speed]

/-- A scalar planar shock satisfies the inequality for one entropy pair
exactly when its entropy production across the interface is nonpositive. -/
theorem satisfiesEntropyInequalityFor_planarShock_iff
    {a : ℝ → ℝ} {E : EntropyPair a} {uL uR speed : ℝ} :
    SatisfiesEntropyInequalityFor (⊤ : Opens ℝ^2) (planarShock uL uR speed) E ↔
      E.q uR - E.q uL ≤ speed * (E.η uR - E.η uL) := by
  constructor
  · intro hentropy
    obtain ⟨φ, hφ_nonneg, htrace_pos⟩ :=
      AffineInterface.exists_testFunction_nonneg_integral_interface_pos speed
    have htested := hentropy.2.2 φ hφ_nonneg
    rw [integral_entropyWeakIntegrand_planarShock] at htested
    nlinarith
  · intro hproduction
    refine ⟨?_, ?_, fun φ hφ_nonneg ↦ ?_⟩
    · rw [comp_planarShock E.η uL uR speed]
      exact (locallyIntegrable_planarShock (E.η uL) (E.η uR) speed).locallyIntegrableOn Set.univ
    · rw [comp_planarShock E.q uL uR speed]
      exact (locallyIntegrable_planarShock (E.q uL) (E.q uR) speed).locallyIntegrableOn Set.univ
    · rw [integral_entropyWeakIntegrand_planarShock]
      exact mul_nonneg (by linarith)
        (integral_nonneg fun t ↦ hφ_nonneg (AffineInterface.interface speed t))

end

end PDE.Hyperbolic.ConservationLaw.Scalar
