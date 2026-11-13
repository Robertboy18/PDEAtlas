/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
public import PDE.Hyperbolic.ConservationLaw.PlanarShock
import PDE.DistributionTheory.TestFunction
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Hyperbolic.ConservationLaw.AffineInterface.Trace
import PDE.Hyperbolic.ConservationLaw.AffineInterface.VectorBoundaryIntegral
import PDE.Hyperbolic.ConservationLaw.Scalar.PlanarShock

/-!
# Planar shocks for systems of conservation laws

We compute the distributional jump for

`u_t + (flux u)_x = 0`

when `u` is a two-state profile separated by the line `x = speed * t`. Its
vector weak integral is the interface trace multiplied by

`flux uL - flux uR - speed • (uL - uR)`.

Thus the Rankine–Hugoniot relation is sufficient for a global weak solution.
For a fixed entropy pair, the corresponding shock admissibility inequality is
equivalent to the weak entropy inequality for the same profile.

The trace factor is the left-minus-right expression of (19) in Evans, §11.1.1, so for a
straight line of discontinuity this is his derivation (16)-(20) of the Rankine–Hugoniot
condition. The weak entropy inequality is (29) of §11.4.2.

## Main results

* `integral_weakIntegrand_planarShock`: the weak integral of the two-state
  profile against a test function is the interface trace of the test function
  times `flux uL - flux uR - speed • (uL - uR)`.
* `isWeakSolution_planarShock_iff_rankineHugoniot`: the profile is a global
  weak solution exactly when `flux uR - flux uL = speed • (uR - uL)`.
* `satisfiesEntropyInequalityFor_planarShock_iff`: for an entropy pair
  `(η, q)`, the weak entropy inequality holds exactly when
  `q(uR) - q(uL) ≤ speed (η(uR) - η(uL))`.
* `isEntropyWeakSolution_planarShock_iff`: the profile is an entropy weak
  solution exactly when Rankine–Hugoniot holds and the jump inequality holds
  for every convex entropy pair.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equations (16)-(20); §11.4.2, equations
  (28)-(29).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.System

noncomputable section

open MeasureTheory
open PDE.Common
open PDE.Hyperbolic.ConservationLaw
open TopologicalSpace

open scoped Distributions Topology

variable {m n : ℕ}

/-- The vector weak integral of a planar shock is its Rankine–Hugoniot
coefficient multiplied by the test-function trace on the interface. -/
theorem integral_weakIntegrand_planarShock (flux : ℝ^m → ℝ^m) (uL uR : ℝ^m) (speed : ℝ)
    (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p : ℝ^2, weakIntegrand flux (planarShock uL uR speed) φ p ∂volume) =
      (∫ t : ℝ, φ (AffineInterface.interface speed t) ∂volume) •
      (flux uL - flux uR - speed • (uL - uR)) := by
  let left := AffineInterface.leftHalfSpace speed
  let constantPart : ℝ^2 → ℝ^m := fun p ↦ (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p • uR +
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p • flux uR
  let jumpPart : ℝ^2 → ℝ^m := fun p ↦ (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p • (uL - uR) +
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p • (flux uL - flux uR)
  have hφ0 := φ.integrable_partialDeriv (0 : Fin 2)
  have hφ1 := φ.integrable_partialDeriv (1 : Fin 2)
  have hpoint : weakIntegrand flux (planarShock uL uR speed) φ =
        fun p ↦ constantPart p + left.indicator jumpPart p := by
    funext p
    by_cases hp : p ∈ left
    · simp only [weakIntegrand, Fin.isValue, hp, planarShock_apply_of_mem, Set.indicator_of_mem,
        constantPart, left, jumpPart]
      module
    · simp [weakIntegrand, constantPart, jumpPart, left, hp]
  have hconstantIntegral : (∫ p : ℝ^2, constantPart p ∂volume) = 0 := by
    simp only [constantPart]
    rw [integral_add (hφ0.smul_const uR) (hφ1.smul_const (flux uR)), integral_smul_const,
      integral_smul_const, φ.integral_partialDeriv_eq_zero (0 : Fin 2),
      φ.integral_partialDeriv_eq_zero (1 : Fin 2)]
    simp
  rw [integral_congr_ae (.of_forall (congrFun hpoint)),
    integral_add (show Integrable constantPart volume from
        (hφ0.smul_const uR).add (hφ1.smul_const (flux uR)))
      (show Integrable (left.indicator jumpPart) volume from
        ((hφ0.smul_const (uL - uR)).add (hφ1.smul_const (flux uL - flux uR))).indicator
          (AffineInterface.measurableSet_leftHalfSpace speed)), hconstantIntegral, zero_add,
    integral_indicator (AffineInterface.measurableSet_leftHalfSpace speed)]
  exact AffineInterface.setIntegral_smul_add_smul_partialDeriv_leftHalfSpace
    φ speed (uL - uR) (flux uL - flux uR)

/-- A planar shock satisfying Rankine–Hugoniot is a global weak solution of
the system. -/
theorem RankineHugoniot.isWeakSolution_planarShock {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ}
    (hRH : RankineHugoniot flux uL uR speed) :
    IsWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) := by
  refine ⟨(locallyIntegrable_planarShock uL uR speed).locallyIntegrableOn Set.univ,
    (locallyIntegrable_comp_planarShock flux uL uR speed).locallyIntegrableOn Set.univ, fun φ ↦ ?_⟩
  rw [integral_weakIntegrand_planarShock, show flux uL - flux uR - speed • (uL - uR) = 0 by
    rw [← neg_eq_zero, ← sub_eq_zero.mpr hRH]; module, smul_zero]

/-- A system planar shock is a global weak solution exactly when its jump
satisfies the vector Rankine–Hugoniot relation. -/
theorem isWeakSolution_planarShock_iff_rankineHugoniot
    {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} :
    IsWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) ↔
      RankineHugoniot flux uL uR speed := by
  refine ⟨fun hweak ↦ ?_, RankineHugoniot.isWeakSolution_planarShock⟩
  obtain ⟨φ, _, htrace_pos⟩ :=
    AffineInterface.exists_testFunction_nonneg_integral_interface_pos speed
  have htested := hweak.weak_eq φ
  rw [integral_weakIntegrand_planarShock] at htested
  have hc := (smul_eq_zero.mp htested).resolve_left htrace_pos.ne'
  exact sub_eq_zero.mp (by rw [← neg_eq_zero, ← hc]; module)

/-- The weak entropy integral of a planar shock is the scalar entropy
production coefficient times the interface trace. -/
theorem integral_entropyWeakIntegrand_planarShock {flux : ℝ^m → ℝ^m} (E : EntropyPair flux)
    (uL uR : ℝ^m) (speed : ℝ) (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ p : ℝ^2, entropyWeakIntegrand E (planarShock uL uR speed) φ p ∂volume) =
      (E.entropyFlux uL - E.entropyFlux uR - (E.entropy uL - E.entropy uR) * speed) * ∫ t : ℝ,
      φ (AffineInterface.interface speed t) ∂volume := by
  refine (integral_congr_ae (.of_forall fun p ↦ ?_)).trans
    (PDE.Hyperbolic.ConservationLaw.Scalar.integral_planarShock_linearCombination
      (E.entropy uL) (E.entropy uR) (E.entropyFlux uL) (E.entropyFlux uR) speed φ)
  change E.entropy (planarShock uL uR speed p) * _ +
    E.entropyFlux (planarShock uL uR speed p) * _ = _
  rw [congrFun (comp_planarShock E.entropy uL uR speed) p,
    congrFun (comp_planarShock E.entropyFlux uL uR speed) p]

/-- The entropy inequality for a planar shock is equivalent to nonpositive
entropy production across its interface. -/
theorem satisfiesEntropyInequalityFor_planarShock_iff {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {uL uR : ℝ^m} {speed : ℝ} :
    SatisfiesEntropyInequalityFor (⊤ : Opens ℝ^2) (planarShock uL uR speed) E ↔
      E.entropyFlux uR - E.entropyFlux uL ≤ speed * (E.entropy uR - E.entropy uL) := by
  refine ⟨fun hentropy ↦ ?_, fun hproduction ↦ ⟨?_, ?_, fun φ hφ ↦ ?_⟩⟩
  · obtain ⟨φ, hφ_nonneg, htrace_pos⟩ :=
      AffineInterface.exists_testFunction_nonneg_integral_interface_pos speed
    have htested := hentropy.2.2 φ hφ_nonneg
    rw [integral_entropyWeakIntegrand_planarShock] at htested
    nlinarith
  · rw [comp_planarShock E.entropy uL uR speed]
    exact (locallyIntegrable_planarShock _ _ speed).locallyIntegrableOn Set.univ
  · rw [comp_planarShock E.entropyFlux uL uR speed]
    exact (locallyIntegrable_planarShock _ _ speed).locallyIntegrableOn Set.univ
  · rw [integral_entropyWeakIntegrand_planarShock]
    exact mul_nonneg (by linarith) (integral_nonneg fun t ↦ hφ (AffineInterface.interface speed t))

/-- Weak conservation together with one entropy inequality characterizes an
entropy-admissible planar shock. -/
theorem weak_and_entropy_planarShock_iff_isAdmissibleShock {flux : ℝ^m → ℝ^m} {E : EntropyPair flux}
    {uL uR : ℝ^m} {speed : ℝ} :
    (IsWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) ∧ SatisfiesEntropyInequalityFor
      (⊤ : Opens ℝ^2) (planarShock uL uR speed) E) ↔ E.IsAdmissibleShock uL uR speed := by
  rw [isWeakSolution_planarShock_iff_rankineHugoniot, satisfiesEntropyInequalityFor_planarShock_iff]
  rfl

/-- A planar shock is an entropy weak solution exactly when it satisfies
Rankine–Hugoniot and the jump inequality for every convex entropy pair. -/
theorem isEntropyWeakSolution_planarShock_iff {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ} :
    IsEntropyWeakSolution flux (⊤ : Opens ℝ^2) (planarShock uL uR speed) ↔
      RankineHugoniot flux uL uR speed ∧ ∀ E : ConvexEntropyPair flux,
      E.entropyFlux uR - E.entropyFlux uL ≤ speed * (E.entropy uR - E.entropy uL) :=
  ⟨fun ⟨hweak, hentropy⟩ ↦ ⟨isWeakSolution_planarShock_iff_rankineHugoniot.mp hweak,
      fun E ↦ satisfiesEntropyInequalityFor_planarShock_iff.mp (hentropy E)⟩,
    fun ⟨hRH, hentropy⟩ ↦ ⟨isWeakSolution_planarShock_iff_rankineHugoniot.mpr hRH,
      fun E ↦ satisfiesEntropyInequalityFor_planarShock_iff.mpr (hentropy E)⟩⟩

end

end PDE.Hyperbolic.ConservationLaw.System
