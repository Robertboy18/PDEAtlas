/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.MoreauEnvelope.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Differentiability of Moreau envelopes

For a differentiable convex functional on a real Hilbert space, comparing the
Moreau envelope at two points against the opposite proximal minimizer gives a
sharp quadratic first-order remainder. It follows that the envelope is
differentiable, its gradient is the Yosida approximation, and this gradient is
globally `1 / lambda`-Lipschitz.

## Main results

* `convexGradientMoreauEnvelope_remainder_abs_le`: the first-order remainder
  bound `|M(y) - M(x) - ⟪A_lambda x, y - x⟫| ≤ ‖y - x‖²/(2 lambda)`.
* `hasGradientAt_convexGradientMoreauEnvelope`,
  `gradient_convexGradientMoreauEnvelope`: the envelope is differentiable
  with gradient the Yosida approximation `A_lambda = (x - J_lambda x)/lambda`.
* `lipschitzWith_gradient_convexGradientMoreauEnvelope`: that gradient is
  `1/lambda`-Lipschitz.

## How it works

We bound the remainder in `convexGradientMoreauEnvelope_remainder_abs_le` from above by using
the proximal point `J_lambda x` as a competitor in the minimization that defines the envelope
at `y`. Swapping `x` and `y` and using the monotonicity of `A_lambda`
(`convexGradientYosidaApproximation_monotone`) gives the bound from below. Moreau proves his
Proposition 7.d differently: the envelope lies above an affine function that touches it at each
point, which bounds the remainder below by `0`, and the nonexpansiveness of the proximal map
bounds it above by `‖y - x‖²` (his parameter is `1`). Our route gives the constant
`1 / (2 lambda)`, and differentiability follows by a squeeze in
`hasGradientAt_convexGradientMoreauEnvelope`.

## References

* J.-J. Moreau, "Proximité et dualité dans un espace hilbertien", *Bull. Soc. Math. France* 93
  (1965), 273-299, 7.d, p. 286.
  <https://doi.org/10.24033/bsmf.1625>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973.
  <https://doi.org/10.1016/S0304-0208(08)X7125-7>
-/

@[expose] public section

noncomputable section

open Filter Set

open scoped Topology Gradient

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- For `0 < lambda`, the first-order remainder `|M y - M x - ⟪A_lambda x, y - x⟫|` of the
Moreau envelope `M` at `x`, with `A_lambda` the Yosida approximation, is at most
`‖y - x‖² / (2 * lambda)`. -/
theorem convexGradientMoreauEnvelope_remainder_abs_le
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x y : H) :
    |convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y -
        convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
        inner ℝ
          (convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
          (y - x)| ≤
      ‖y - x‖ ^ 2 / (2 * lambda) := by
  let J := convexGradientResolvent Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le
  let A := convexGradientYosidaApproximation Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  let M := convexGradientMoreauEnvelope Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  have := hlambda.ne'
  have hdecomp (z : H) : z - J z = lambda • A z := (eq_sub_of_add_eq'
    (convexGradientResolvent_add_smul_yosidaApproximation Phi hPhiConvex DPhi hPhiDiff lambda
      hlambda z)).symm
  -- Using `J u` as a competitor at `v` gives a quadratic Taylor bound at `u`.
  have hcomp (u v : H) :
      M v ≤ M u + inner ℝ (A u) (v - u) + ‖v - u‖ ^ 2 / (2 * lambda) := by
    have h := convexGradientMoreauEnvelope_le Phi hPhiConvex DPhi hPhiDiff lambda hlambda v (J u)
    have hMu : M u = Phi (J u) + ‖u - J u‖ ^ 2 / (2 * lambda) := rfl
    have hv : v - J u = (v - u) + lambda • A u := by rw [← hdecomp u]; abel
    simp only [proximalEnergy] at h
    rw [hv, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda,
      real_inner_comm] at h
    rw [hMu, hdecomp u, norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
    refine h.trans_eq ?_
    field_simp
    ring
  -- Monotonicity moves the linear term of the opposite competitor from `A y` to `A x`.
  have hmono : inner ℝ (A x) (y - x) ≤ inner ℝ (A y) (y - x) := by
    have h := convexGradientYosidaApproximation_monotone Phi hPhiConvex DPhi hPhiDiff lambda
      hlambda y x
    change 0 ≤ inner ℝ (A y - A x) (y - x) at h
    rw [inner_sub_left] at h
    linarith
  have hupper := hcomp x y
  have hlower := hcomp y x
  rw [← neg_sub y x, inner_neg_right, norm_neg] at hlower
  change |M y - M x - inner ℝ (A x) (y - x)| ≤ _
  rw [abs_le]
  constructor <;> linarith

/-- The Yosida approximation is the gradient of the Moreau envelope. -/
theorem hasGradientAt_convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    HasGradientAt
      (convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda)
      (convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
      x := by
  rw [hasGradientAt_iff_tendsto]
  refine squeeze_zero (g := fun y ↦ ‖y - x‖ / (2 * lambda)) (fun y ↦ by positivity)
    (fun y ↦ ?_) ?_
  · calc _ ≤ ‖y - x‖⁻¹ * (‖y - x‖ ^ 2 / (2 * lambda)) := by
          gcongr
          simpa only [Real.norm_eq_abs] using
            convexGradientMoreauEnvelope_remainder_abs_le Phi hPhiConvex DPhi hPhiDiff lambda
              hlambda x y
      _ = ‖y - x‖ / (2 * lambda) := by
        by_cases hzero : ‖y - x‖ = 0
        · simp [hzero]
        · field_simp
  · simpa only [div_eq_mul_inv, zero_mul] using (tendsto_norm_sub_self x).mul_const (2 * lambda)⁻¹

/-- The gradient of the Moreau envelope is the Yosida approximation. -/
theorem gradient_convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ∇
        (convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda)
        x =
      convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x :=
  (hasGradientAt_convexGradientMoreauEnvelope
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda x).gradient

/-- The Moreau envelope of a differentiable convex functional is
differentiable. -/
theorem differentiable_convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    Differentiable ℝ
      (convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) :=
  fun x ↦
    (hasGradientAt_convexGradientMoreauEnvelope
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x).differentiableAt

/-- The gradient of the Moreau envelope is globally Lipschitz with constant
`1 / lambda`. -/
theorem lipschitzWith_gradient_convexGradientMoreauEnvelope
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    LipschitzWith (Real.toNNReal (1 / lambda))
      (∇
        (convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda)) := by
  rw [show
    ∇
        (convexGradientMoreauEnvelope
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda) =
      convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda by
      funext x
      exact gradient_convexGradientMoreauEnvelope
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x]
  exact
    convexGradientYosidaApproximation_lipschitzWith
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda

end PDE.Elliptic.Semilinear
