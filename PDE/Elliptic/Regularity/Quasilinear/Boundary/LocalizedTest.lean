/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialEstimate
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates

/-!
# Localized admissible tangential tests

Multiplication by a global smooth cutoff preserves the zero trace. Thus the test
`-Dₖ⁻ʰ(η² Dₖʰu)` is admissible even when the cutoff crosses the flat boundary. Its gradient
contains both the weighted quotient and the derivative-of-cutoff term. The weak identity
below retains both terms and applies to a nonlinear flux.
-/

@[expose] public noncomputable section

open scoped Sobolev

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} [Fact (0 < n)]

/-- The forward tangential quotient multiplied by the squared cutoff. -/
def localizedTangentialForward (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) : H¹₀(HalfSpace.upper n) :=
  cutoffH10 (HalfSpace.isOpen_upper n) (squaredCutoff η)
    (tangentialDifferenceQuotientH10 k hk h u)

/-- The signed backward quotient of the localized field, with its zero trace. -/
def localizedTangentialTest (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) : H¹₀(HalfSpace.upper n) :=
  -tangentialDifferenceQuotientH10 k hk (-h) (localizedTangentialForward η k hk h u)

/-- The localized field has the full weak product-rule gradient. -/
theorem derivCoord_localizedTangentialForward
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) (i : Fin n) :
    derivCoordCLM i (localizedTangentialForward η k hk h u) =
      testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) •
        tangentialDifferenceQuotientLp 2 k hk h (derivCoordCLM i u) +
      partialTestFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) i •
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u) := by
  rw [localizedTangentialForward, derivCoordCLM_cutoffH10,
    derivCoord_tangentialDifferenceQuotientH10, baseCoord_tangentialDifferenceQuotientH10]

/-- The base coordinate of the localized field is the squared-cutoff product. -/
theorem baseCoord_localizedTangentialForward
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    baseCoordCLM (localizedTangentialForward η k hk h u) =
      testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) •
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u) := by
  rw [localizedTangentialForward, baseCoordCLM_cutoffH10,
    baseCoord_tangentialDifferenceQuotientH10]

/-- The test gradient is the signed backward quotient of the localized gradient. -/
theorem derivCoord_localizedTangentialTest
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) (i : Fin n) :
    derivCoordCLM i (localizedTangentialTest η k hk h u) =
      -tangentialDifferenceQuotientLp 2 k hk (-h)
        (derivCoordCLM i (localizedTangentialForward η k hk h u)) := by
  rw [localizedTangentialTest, map_neg, derivCoord_tangentialDifferenceQuotientH10]

/-- Evaluate a flux weak equation on the localized test and move the backward
quotient to the flux. No linear coefficient representation of the flux is used. -/
theorem localizedTangential_energy_identity
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n))
    (q : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hu : (∑ i, ⟪q i, derivCoordCLM i (localizedTangentialTest η k hk h u)⟫) =
      ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫) :
    (∑ i, ⟪tangentialDifferenceQuotientLp 2 k hk h (q i),
      testFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) •
        tangentialDifferenceQuotientLp 2 k hk h (derivCoordCLM i u)⟫) +
    (∑ i, ⟪tangentialDifferenceQuotientLp 2 k hk h (q i),
      partialTestFunctionLpTop (Ω := HalfSpace.upper n) (squaredCutoff η) i •
        tangentialDifferenceQuotientLp 2 k hk h (baseCoordCLM u)⟫) =
      ⟪f, baseCoordCLM (localizedTangentialTest η k hk h u)⟫ := by
  simpa only [derivCoord_localizedTangentialTest,
    inner_neg_tangentialBackwardDifference_eq k hk hh,
    derivCoord_localizedTangentialForward, inner_add_right, Finset.sum_add_distrib] using hu

end PDE.Elliptic.Regularity.Quasilinear
