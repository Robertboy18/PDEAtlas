/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.FirstOrder
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The power Dirichlet energy of a system

## Motivation

Does the integral `J(u) = ∫ |Du|ᵖ dx` of a system of functions have a minimizer with given
boundary values, for every number of unknowns, every dimension and every exponent
`1 < p < ∞`, and which equation does the minimizer solve? The integral is the simplest one
with growth `p`, and it shows that the premises of the existence theorem for convex integrals
and of the weak Euler–Lagrange system are satisfiable in every case.

## The idea

The density `F(x, s, ξ) = |ξ|ᵖ` does not depend on the point or the value. It is continuous,
convex in `ξ` because `t ↦ tᵖ` is convex and increasing on `[0, ∞)`, and it lies between
`|ξ|ᵖ` and `|(s, ξ)|ᵖ`, so coercivity and growth hold with constants `1` and zero functions.
Its derivative is `(v, η) ↦ p |ξ|^{p-2} ⟪ξ, η⟫`, of norm at most `p |(s, ξ)|^{p-1}`. So a
minimizer exists in the class of every boundary datum, on every bounded measurable set, and it
solves the system `div(|Du|^{p-2} Du) = 0` weakly. For `p = 2` this is Dirichlet's integral and
the minimizer is a weakly harmonic map.

## Main results

All are for one family of densities, every number of unknowns `m`, every dimension `n` and
every real exponent `p` in the stated range.

* `measurable_density`, `convexOn_density` (`p ≥ 1`): the density is measurable and convex in
  the gradient.
* `hasFDerivAt_density`, `measurable_densityDeriv`, `norm_densityDeriv_le` (`p > 1`): the
  derivative, its measurability and its growth of order `p - 1`.

## Relations

* With these, `exists_minimizer_integral_vectorWkp_prescribed_boundary` gives a minimizer of
  `∫ |Du|ᵖ` with given boundary values on every bounded measurable set of positive dimension,
  for `1 < p < ∞`, and `integral_firstVariation_eq_zero_of_integral_vectorWkp_le` gives the
  weak equation `∫ p |Du|^{p-2} ⟪Du, Dφ⟫ = 0`. The two bounds of the existence theorem hold
  with the constants `1` and zero functions, since `|ξ|ᵖ ≤ |(s, ξ)|ᵖ`.

## What stays open

Uniqueness of the minimizer, which follows from strict convexity for `p > 1`, and its
regularity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.CalculusOfVariations.PowerDirichlet

variable {m n : ℕ} {p : ℝ}

/-- The density `|Du|ᵖ` of the power Dirichlet energy. It does not depend on the point or on
the value. -/
def density (m n : ℕ) (p : ℝ) (_x : ℝ^n) (z : ℝ^m × ℝ^(m * n)) : ℝ := ‖z.2‖ ^ p

/-- The derivative of the density at `(s, ξ)`: the functional `(v, η) ↦ p |ξ|^{p-2} ⟪ξ, η⟫`. -/
def densityDeriv (m n : ℕ) (p : ℝ) (_x : ℝ^n) (z : ℝ^m × ℝ^(m * n)) :
    (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ :=
  ((p * ‖z.2‖ ^ (p - 2)) • innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ (ℝ^m) (ℝ^(m * n)))

/-- The derivative applied to a direction. -/
theorem densityDeriv_apply (x : ℝ^n) (z w : ℝ^m × ℝ^(m * n)) :
    densityDeriv m n p x z w = p * ‖z.2‖ ^ (p - 2) * ⟪z.2, w.2⟫_ℝ := by
  simp [densityDeriv]

/-- The density is jointly measurable. -/
theorem measurable_density : Measurable (Function.uncurry (density m n p)) :=
  measurable_snd.snd.norm.pow_const p

/-- The density is convex in the gradient, for `p ≥ 1`. -/
theorem convexOn_density (hp : 1 ≤ p) (x : ℝ^n) (s : ℝ^m) :
    ConvexOn ℝ univ fun ξ : ℝ^(m * n) ↦ density m n p x (s, ξ) := by
  refine ⟨convex_univ, fun ξ _ η _ t r ht hr htr ↦ ?_⟩
  have h1 : ‖t • ξ + r • η‖ ≤ t * ‖ξ‖ + r * ‖η‖ := by
    calc ‖t • ξ + r • η‖ ≤ ‖t • ξ‖ + ‖r • η‖ := norm_add_le _ _
      _ = t * ‖ξ‖ + r * ‖η‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ht, Real.norm_of_nonneg hr]
  have h2 := (convexOn_rpow hp).2 (norm_nonneg ξ : ‖ξ‖ ∈ Ici (0 : ℝ))
    (norm_nonneg η : ‖η‖ ∈ Ici (0 : ℝ)) ht hr htr
  calc ‖t • ξ + r • η‖ ^ p ≤ (t * ‖ξ‖ + r * ‖η‖) ^ p :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (by linarith)
    _ ≤ t • ‖ξ‖ ^ p + r • ‖η‖ ^ p := by simpa only [smul_eq_mul] using h2

/-- The density is differentiable in the pair of the value and the gradient, for `p > 1`. -/
theorem hasFDerivAt_density (hp : 1 < p) (x : ℝ^n) (z : ℝ^m × ℝ^(m * n)) :
    HasFDerivAt (density m n p x) (densityDeriv m n p x z) z :=
  (hasFDerivAt_norm_rpow z.2 hp).comp z (hasFDerivAt_snd (𝕜 := ℝ) (p := z))

/-- The derivative is jointly measurable in the point, the state and the direction. -/
theorem measurable_densityDeriv :
    Measurable fun z : (ℝ^n) × (ℝ^m × ℝ^(m * n)) × (ℝ^m × ℝ^(m * n)) ↦
      densityDeriv m n p z.1 z.2.1 z.2.2 := by
  simp only [densityDeriv_apply]
  exact ((measurable_snd.fst.snd.norm.pow_const _).const_mul p).mul
    (measurable_snd.fst.snd.inner measurable_snd.snd.snd)

/-- The derivative has growth of order `p - 1`: its norm is at most `p |(s, ξ)|^{p-1}`. -/
theorem norm_densityDeriv_le (hp : 1 < p) (x : ℝ^n) (z : ℝ^m × ℝ^(m * n)) :
    ‖densityDeriv m n p x z‖ ≤ p * ‖z‖ ^ (p - 1) := by
  have hp0 : 0 ≤ p := by linarith
  have hc : 0 ≤ p * ‖z.2‖ ^ (p - 2) := mul_nonneg hp0 (Real.rpow_nonneg (norm_nonneg _) _)
  -- `|ξ|^{p-2} |ξ| ≤ |ξ|^{p-1}`, with equality unless `ξ = 0`
  have hpow : ‖z.2‖ ^ (p - 2) * ‖z.2‖ ≤ ‖z.2‖ ^ (p - 1) := by
    rcases eq_or_lt_of_le (norm_nonneg z.2) with h0 | hpos
    · rw [← h0, mul_zero]
      exact Real.rpow_nonneg le_rfl _
    · rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
  calc ‖densityDeriv m n p x z‖
      ≤ ‖(p * ‖z.2‖ ^ (p - 2)) • innerSL ℝ z.2‖ *
          ‖ContinuousLinearMap.snd ℝ (ℝ^m) (ℝ^(m * n))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (p * ‖z.2‖ ^ (p - 2) * ‖z.2‖) * 1 := by
        refine mul_le_mul ?_ (ContinuousLinearMap.norm_snd_le ..) (norm_nonneg _)
          (mul_nonneg hc (norm_nonneg _))
        rw [norm_smul, Real.norm_of_nonneg hc, innerSL_apply_norm]
    _ = p * (‖z.2‖ ^ (p - 2) * ‖z.2‖) := by ring
    _ ≤ p * ‖z.2‖ ^ (p - 1) := mul_le_mul_of_nonneg_left hpow hp0
    _ ≤ p * ‖z‖ ^ (p - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) (norm_snd_le z) (by linarith)) hp0

end PDE.CalculusOfVariations.PowerDirichlet
