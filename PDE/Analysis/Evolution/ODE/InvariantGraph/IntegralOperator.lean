/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedGreen
public import PDE.Analysis.Normed.ContinuousMap.Bounded.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The finite diagonal Lyapunov–Perron integral operator

Each nonzero real rate uses the convergent Green integral at the appropriate
infinite endpoint. A zero rate uses the primitive based at zero. Their finite
product is a bounded linear operator on exponentially weighted paths.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {η : ℝ}

/-- Select the convergent Green operator for a real rate, using a primitive for
the center rate zero. -/
def rateGreen (hη : 0 < η) (b : ℝ) (hgap : b ≠ 0 → η < |b|) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E) :=
  if hb : b = 0 then centerGreen hη else
    if hn : b < 0 then stableGreen (a := -b) hη.le (by simpa [abs_of_neg hn] using hgap hb)
    else unstableGreen (a := b) hη.le
      (by simpa [abs_of_nonneg (le_of_not_gt hn)] using hgap hb)

/-- The selected Green operator solves the scalar-rate inhomogeneous
equation in the Banach space. -/
theorem hasDerivAt_exponentialLift_rateGreen (hη : 0 < η) (b : ℝ)
    (hgap : b ≠ 0 → η < |b|) (u : ℝ →ᵇ E) (t : ℝ) :
    HasDerivAt (exponentialLift η (rateGreen hη b hgap u))
      (b • exponentialLift η (rateGreen hη b hgap u) t + exponentialLift η u t) t := by
  by_cases hb : b = 0
  · subst b
    simp only [rateGreen, zero_smul, zero_add]
    change HasDerivAt (fun t ↦ exponentialLift η (centerGreen hη u) t)
      (exponentialLift η u t) t
    simp only [exponentialLift_centerGreen]
    exact intervalIntegral.integral_hasDerivAt_right
      ((exponentialLift η u).continuous.intervalIntegrable 0 t)
      (exponentialLift η u).continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      (exponentialLift η u).continuous.continuousAt
  · by_cases hn : b < 0
    · have ha : η < -b := by simpa [abs_of_neg hn] using hgap hb
      simp only [rateGreen, dite_eq_right hb, dite_eq_left hn]
      change HasDerivAt (fun t ↦ exponentialLift η (stableGreen hη.le ha u) t)
        (b • exponentialLift η (stableGreen hη.le ha u) t + exponentialLift η u t) t
      simp only [exponentialLift_stableGreen]
      simpa only [neg_smul, sub_neg_eq_add, add_comm] using
        hasDerivAt_pastExponentialIntegral hη.le ha (norm_nonneg u)
          (exponentialLift η u).continuous (norm_exponentialLift_le η u) t
    · have ha : η < b := by
        simpa [abs_of_nonneg (le_of_not_gt hn)] using hgap hb
      simp only [rateGreen, dite_eq_right hb, dite_eq_right hn]
      change HasDerivAt (fun t ↦ exponentialLift η (unstableGreen hη.le ha u) t)
        (b • exponentialLift η (unstableGreen hη.le ha u) t + exponentialLift η u t) t
      simp only [exponentialLift_unstableGreen]
      simpa only [add_comm] using
        hasDerivAt_futureExponentialIntegral hη.le ha (norm_nonneg u)
          (exponentialLift η u).continuous (norm_exponentialLift_le η u) t

variable {ι : Type*} [Fintype ι]

/-- The finite diagonal Green operator, in the canonical product norm. -/
def diagonalGreen (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) :
    (ℝ →ᵇ (ι → ℝ)) →L[ℝ] (ℝ →ᵇ (ι → ℝ)) :=
  let e := piLinearIsometryEquiv (α := ℝ) (𝕜 := ℝ) (E := fun _ : ι ↦ ℝ)
  (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.piMap fun i ↦ rateGreen hη (rate i) (hgap i))).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap

/-- The coordinates of the finite diagonal Green operator are exactly the
individual real-rate operators. -/
@[simp] theorem diagonalGreen_apply (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) (u : ℝ →ᵇ (ι → ℝ)) (t : ℝ) (i : ι) :
    diagonalGreen hη rate hgap u t i =
      rateGreen hη (rate i) (hgap i) (piLinearIsometryEquiv (𝕜 := ℝ) u i) t := rfl

/-- Decoding the finite diagonal Green operator gives a differentiable
solution of the full diagonal inhomogeneous equation. -/
theorem hasDerivAt_exponentialLift_diagonalGreen (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) (u : ℝ →ᵇ (ι → ℝ)) (t : ℝ) :
    HasDerivAt (exponentialLift η (diagonalGreen hη rate hgap u))
      (fun i ↦ rate i * exponentialLift η (diagonalGreen hη rate hgap u) t i +
        exponentialLift η u t i) t := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := hasDerivAt_exponentialLift_rateGreen hη (rate i) (hgap i)
    (piLinearIsometryEquiv (𝕜 := ℝ) u i) t
  simpa only [exponentialLift, ContinuousMap.coe_mk, Pi.smul_apply, smul_eq_mul,
    diagonalGreen_apply, piLinearIsometryEquiv_apply] using h

end PDE.Analysis.Evolution
