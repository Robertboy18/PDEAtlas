/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Operator
import PDE.FDeriv.Calculus

/-!
# Uniform control of the coefficient-divergence remainder

On a fixed compact spatial set, `C¹` coefficients give a uniform bound `D` on
their row divergence. Ellipticity with constant `θ` then bounds the
nondivergence energy remainder by `(1 + D² / θ)` times the energy.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open PDE.Common
open scoped InnerProductSpace

variable {n : ℕ}

/-- The row divergence of a continuously differentiable matrix field is continuous. -/
theorem continuous_coefficientDivergence {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) :
    Continuous (coefficientDivergence a) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact continuous_iff_continuousAt.mpr fun x ↦
    (PDE.contDiffAt_partialDeriv 0 (ha i j).contDiffAt j).continuousAt

/-- Compactness bounds the coefficient divergence uniformly, independently of a wave. -/
theorem exists_coefficientDivergence_bound {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (ha : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) {K : Set (ℝ^n)} (hK : IsCompact K) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ‖coefficientDivergence a x‖ ≤ D := by
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    (continuous_coefficientDivergence ha).continuousOn
  exact ⟨max 0 D, le_max_left _ _, fun x hx ↦ (hD x hx).trans (le_max_right _ _)⟩

/-- Ellipticity implies nonnegativity of the principal quadratic form. -/
theorem quadratic_nonneg_of_elliptic {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {θ : ℝ} (hθ : 0 < θ)
    (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) (x : ℝ^n) (v : ℝ^n) :
    0 ≤ ∑ i, ∑ j, a x i j * v i * v j :=
  (mul_nonneg hθ.le (sq_nonneg _)).trans (hell x v)

/-- The double-sum remainder is the Euclidean pairing with coefficient divergence. -/
theorem coefficientDivergence_inner (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) :
    ⟪coefficientDivergence a (spatialPart p), classicalWaveSpatialGradient u p⟫_ℝ = ∑ i, ∑ j,
      (∂[j] (fun x ↦ a x i j)) (spatialPart p) * (∂[i.succ] u) p := by
  simp [PiLp.inner_apply, coefficientDivergence, Finset.mul_sum, mul_comm]

/-- A uniform divergence bound controls the full nondivergence remainder. -/
theorem coefficient_remainder_le_energy {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {θ D : ℝ} (hθ : 0 < θ)
    (hell : ∀ x (v : ℝ^n), θ * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, a x i j * v i * v j) (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) (hbound : ‖coefficientDivergence a (spatialPart p)‖ ≤ D) :
    |(∂[0] u) p * (∑ i, ∑ j, (∂[j] (fun x ↦ a x i j)) (spatialPart p) * (∂[i.succ] u) p)| ≤
      (1 + D ^ 2 / θ) * energyDensity a u p := by
  let w := (∂[0] u) p
  let v := classicalWaveSpatialGradient u p
  let E := energyDensity a u p
  have hQ := hell (spatialPart p) v
  have hQ0 := quadratic_nonneg_of_elliptic hθ hell (spatialPart p) v
  simp only [v, classicalWaveSpatialGradient_apply] at hQ hQ0
  have hw : w ^ 2 ≤ 2 * E := by
    dsimp [w, E, energyDensity]
    nlinarith
  have hv : θ * ‖v‖ ^ 2 ≤ 2 * E := by
    dsimp [v, E, energyDensity]
    nlinarith [sq_nonneg ((∂[0] u) p)]
  have hscaled : D ^ 2 * ‖v‖ ^ 2 ≤ D ^ 2 / θ * (2 * E) := by
    have hh := mul_le_mul_of_nonneg_left hv (div_nonneg (sq_nonneg D) hθ.le)
    have heq : D ^ 2 / θ * (θ * ‖v‖ ^ 2) = D ^ 2 * ‖v‖ ^ 2 := by
      field_simp
    rwa [heq] at hh
  rw [← coefficientDivergence_inner, abs_mul]
  have hc : |⟪coefficientDivergence a (spatialPart p), v⟫_ℝ| ≤ D * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hc (abs_nonneg w)
  have hs := sq_nonneg (|w| - D * ‖v‖)
  have hwabs : |w| ^ 2 = w ^ 2 := sq_abs w
  change |w| * |⟪coefficientDivergence a (spatialPart p), v⟫_ℝ| ≤ (1 + D ^ 2 / θ) * E
  nlinarith

end WaveEquation.VariableCoefficient
