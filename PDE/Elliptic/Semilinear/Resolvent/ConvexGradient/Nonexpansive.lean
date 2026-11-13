/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Basic
import PDE.Analysis.Convex.Differentiable.Supporting

/-!
# Metric estimates for convex-gradient resolvents

We develop the metric theory of the resolvent of the gradient of a
differentiable convex functional on a real Hilbert space. Monotonicity of the
gradient gives firm nonexpansivity of both the resolvent and its residual.
Consequently, both maps are `1`-Lipschitz, and the resolvent varies
quantitatively with its parameter.

The algebraic resolvent identities and fixed-point theory are provided by
`ConvexGradient.Basic`.

## Main results

* `convexGradientResolvent_norm_sq_le_inner`,
  `convexGradientResolvent_residual_norm_sq_le_inner`: firm nonexpansivity
  `‖J x - J y‖² ≤ ⟪x - y, J x - J y⟫` of the resolvent and of the residual
  `x - J x`.
* `convexGradientResolvent_norm_sq_add_residual_norm_sq_le`: the combined
  Pythagorean estimate `‖J x - J y‖² + ‖(x - J x) - (y - J y)‖² ≤ ‖x - y‖²`.
* `convexGradientResolvent_lipschitzWith_one`,
  `convexGradientResolvent_residual_lipschitzWith_one`: both maps are
  `1`-Lipschitz.
* `convexGradientResolvent_norm_sub_le_parameter`: the parameter dependence
  `‖J_mu x - J_lambda x‖ ≤ |1 - mu/lambda| ‖x - J_lambda x‖`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, Theorem 2 (i) and step 1 of its proof, pp. 563-564.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973, Chapitre II
  (Opérateurs maximaux monotones), pp. 19-51.
  <https://doi.org/10.1016/S0304-0208(08)72383-1>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Convex-gradient resolvents are firmly nonexpansive. -/
theorem convexGradientResolvent_norm_sq_le_inner
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x y : H) :
    ‖convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y‖ ^ 2 ≤
      inner ℝ (x - y)
        (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda y) := by
  let u :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
  let w :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda y
  have hu :=
    convexGradientResolvent_weak_equation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x (u - w)
  have hw :=
    convexGradientResolvent_weak_equation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda y (u - w)
  have hmonotone :
      0 ≤ (DPhi u - DPhi w) (u - w) :=
    PDE.Analysis.sub_apply_sub_nonneg_of_convex_of_hasFDerivAt
      hPhiConvex (hPhiDiff u) (hPhiDiff w)
  have hbalance :
      inner ℝ (u - w) (u - w) +
          lambda * ((DPhi u - DPhi w) (u - w)) =
        inner ℝ (x - y) (u - w) := by
    simp only [inner_sub_left, sub_apply]
    linarith
  have hscaled :
      0 ≤ lambda * ((DPhi u - DPhi w) (u - w)) :=
    mul_nonneg hlambda hmonotone
  change ‖u - w‖ ^ 2 ≤ inner ℝ (x - y) (u - w)
  rw [real_inner_self_eq_norm_sq] at hbalance
  linarith

/-- The residual `x - J_lambda x` of a convex-gradient resolvent is firmly
nonexpansive. -/
theorem convexGradientResolvent_residual_norm_sq_le_inner
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x y : H) :
    ‖(x -
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) -
        (y -
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)‖ ^ 2 ≤
      inner ℝ (x - y)
        ((x -
            convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) -
          (y -
            convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)) := by
  let J :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  let j := J x - J y
  let r := (x - J x) - (y - J y)
  have hdecomp : x - y = j + r := by
    dsimp only [j, r]
    abel
  have hfirm : ‖j‖ ^ 2 ≤ inner ℝ (x - y) j := by
    simpa only [J, j] using
      convexGradientResolvent_norm_sq_le_inner
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  have hcross : 0 ≤ inner ℝ j r := by
    rw [hdecomp, inner_add_left, real_inner_self_eq_norm_sq] at hfirm
    have : 0 ≤ inner ℝ r j := by linarith
    simpa only [real_inner_comm r j] using this
  change ‖r‖ ^ 2 ≤ inner ℝ (x - y) r
  rw [hdecomp, inner_add_left, real_inner_self_eq_norm_sq]
  linarith

/-- A resolvent displacement and its residual satisfy the Pythagorean
nonexpansivity estimate. -/
theorem convexGradientResolvent_norm_sq_add_residual_norm_sq_le
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x y : H) :
    ‖convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y‖ ^ 2 +
        ‖(x -
              convexGradientResolvent
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) -
            (y -
              convexGradientResolvent
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)‖ ^ 2 ≤
      ‖x - y‖ ^ 2 := by
  let J :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda
  let j := J x - J y
  let r := (x - J x) - (y - J y)
  have hdecomp : x - y = j + r := by
    dsimp only [j, r]
    abel
  have hresidual :
      ‖r‖ ^ 2 ≤ inner ℝ (x - y) r := by
    simpa only [J, r] using
      convexGradientResolvent_residual_norm_sq_le_inner
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  have hcross : 0 ≤ inner ℝ j r := by
    rw [hdecomp, inner_add_left, real_inner_self_eq_norm_sq] at hresidual
    linarith
  change ‖j‖ ^ 2 + ‖r‖ ^ 2 ≤ ‖x - y‖ ^ 2
  rw [hdecomp, norm_add_sq_real]
  linarith

/-- The convex-gradient resolvent is `1`-Lipschitz. -/
theorem convexGradientResolvent_lipschitzWith_one
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    LipschitzWith 1
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  let d :=
    convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
      convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda y
  have hfirm :
      ‖d‖ ^ 2 ≤ inner ℝ (x - y) d := by
    simpa only [d] using
      convexGradientResolvent_norm_sq_le_inner
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  have hinner : inner ℝ (x - y) d ≤ ‖x - y‖ * ‖d‖ :=
    real_inner_le_norm _ _
  by_cases hd : ‖d‖ = 0
  · simpa only [d, hd] using norm_nonneg (x - y)
  · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)
    change ‖d‖ ≤ ‖x - y‖
    nlinarith

/-- The residual map `x ↦ x - J_lambda x` is `1`-Lipschitz. -/
theorem convexGradientResolvent_residual_lipschitzWith_one
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    LipschitzWith 1
      (fun x ↦
        x -
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  let r :=
    (x -
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) -
      (y -
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)
  have hfirm : ‖r‖ ^ 2 ≤ inner ℝ (x - y) r := by
    simpa only [r] using
      convexGradientResolvent_residual_norm_sq_le_inner
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  have hinner : inner ℝ (x - y) r ≤ ‖x - y‖ * ‖r‖ :=
    real_inner_le_norm _ _
  by_cases hr : ‖r‖ = 0
  · simpa only [r, hr] using norm_nonneg (x - y)
  · have hrpos : 0 < ‖r‖ := lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr)
    change ‖r‖ ≤ ‖x - y‖
    nlinarith

/-- Quantitative stability of the resolvent with respect to its parameter.

The estimate compares `J_mu x` with `J_lambda x` through the resolvent
identity. -/
theorem convexGradientResolvent_norm_sub_le_parameter
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (mu : ℝ) (hmu : 0 ≤ mu) (x : H) :
    ‖convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff mu hmu x -
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x‖ ≤
      |1 - mu / lambda| *
        ‖x -
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x‖ := by
  let u :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x
  let z := (mu / lambda) • x + (1 - mu / lambda) • u
  have hresolvent :
      convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff mu hmu z =
        u := by
    simpa only [z, u] using
      convexGradientResolvent_resolvent_identity
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda mu hmu x
  have hinput :
      x - z = (1 - mu / lambda) • (x - u) := by
    dsimp only [z]
    module
  have hlipschitz :=
    (convexGradientResolvent_lipschitzWith_one
      Phi hPhiConvex DPhi hPhiDiff mu hmu).dist_le_mul x z
  rw [hresolvent] at hlipschitz
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm, hinput,
    norm_smul, Real.norm_eq_abs, u] using hlipschitz

end PDE.Elliptic.Semilinear
