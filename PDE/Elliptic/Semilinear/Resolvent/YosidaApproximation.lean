/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Subdifferential
import PDE.Analysis.Convex.Proximal.Yosida.Approximation
import Mathlib.Tactic.Positivity.Finset

/-!
# Yosida approximations of convex gradients

For a differentiable convex functional `Phi` on a real Hilbert space, let
`J_lambda` denote the resolvent of its gradient. At a positive parameter, the
Yosida approximation is

`A_lambda x = lambda⁻¹ (x - J_lambda x)`.

It agrees with `PDE.Analysis.Convex.yosidaApproximation` for the coerced
potential, so `lambda`-cocoercivity, monotonicity, and the sharp `1 / lambda`
Lipschitz bound follow from the subdifferential theory. The resolvent equation
identifies the Riesz image of `A_lambda x` with `DPhi (J_lambda x)`. We also
prove the standard pointwise estimates

`‖A_lambda x‖ <= ‖gradient Phi x‖`

and

`‖J_lambda x - x‖ <= lambda * ‖gradient Phi x‖`.

The zeros of the approximation are exactly the critical points of `Phi`.

## Main results

* `convexGradientYosidaApproximation`, `convexGradientResolvent_add_smul_yosidaApproximation`:
  the definition and the splitting `J_lambda + lambda A_lambda = I`.
* `convexGradientYosidaApproximation_eq_gradient`: `A_lambda x = gradient Phi (J_lambda x)`.
* `convexGradientYosidaApproximation_cocoercive`,
  `convexGradientYosidaApproximation_lipschitzWith`: `lambda`-cocoercivity and the
  `1 / lambda` Lipschitz bound.
* `convexGradientYosidaApproximation_norm_le`, `convexGradientResolvent_norm_sub_self_le`:
  the pointwise estimates against `‖gradient Phi x‖`.
* `convexGradientYosidaApproximation_eq_zero_iff`: zeros are critical points.
* `tendsto_convexGradientResolvent`, `tendsto_convexGradientYosidaApproximation`: as
  `lambda → 0⁺`, `J_lambda x → x` unconditionally and `A_lambda x → gradient Phi x` where the
  gradient is continuous.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definitions of the nonlinear resolvent and of the
  Yosida approximation (7), and Theorem 2, pp. 563-564.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Chapter 7 (The Hille–Yosida Theorem), pp. 181-199, for the
  resolvent and the Yosida approximation of a linear maximal monotone operator.
  <https://doi.org/10.1007/978-0-387-70914-7_7>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973, Chapitre II
  (Opérateurs maximaux monotones), pp. 19-51.
  <https://doi.org/10.1016/S0304-0208(08)72383-1>
-/

@[expose] public section

noncomputable section

open Filter Set

open scoped Topology Gradient

open PDE.Analysis.Convex

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

variable (Phi : H → ℝ)
  (hPhiConvex : ConvexOn ℝ Set.univ Phi)
  (DPhi : H → StrongDual ℝ H)
  (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)

/-- The Yosida approximation of the gradient of a differentiable convex
functional. -/
noncomputable def convexGradientYosidaApproximation
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) : H :=
  lambda⁻¹ •
    (x -
      convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x)

/-- The general Yosida approximation of the coerced potential is the convex-gradient one. -/
theorem subdifferentialYosida_eq_convexGradientYosidaApproximation
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) :
    yosidaApproximation (fun x ↦ (Phi x : EReal)) (isProper_coeReal Phi)
        (convex_realEpigraph_coeReal hPhiConvex)
        (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) lambda hlambda w =
      convexGradientYosidaApproximation Phi hPhiConvex DPhi hPhiDiff lambda hlambda w := by
  unfold yosidaApproximation convexGradientYosidaApproximation
  rw [subdifferentialResolvent_eq_convexGradientResolvent Phi hPhiConvex DPhi hPhiDiff hlambda]

/-- The resolvent and Yosida approximation split the identity as
`J_lambda + lambda A_lambda = I`. -/
theorem convexGradientResolvent_add_smul_yosidaApproximation
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x +
        lambda •
          convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x =
      x := by
  rw [convexGradientYosidaApproximation, smul_smul,
    mul_inv_cancel₀ hlambda.ne', one_smul]
  abel

/-- Under the Riesz identification, the Yosida approximation is the gradient
evaluated at the resolvent. -/
theorem toDual_convexGradientYosidaApproximation
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    InnerProductSpace.toDual ℝ H
          (convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) =
      DPhi
        (convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) := by
  rw [convexGradientYosidaApproximation, map_smul, map_sub]
  let u :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x
  have hequation :=
    convexGradientResolvent_equation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x
  have hscaled :
      lambda • DPhi u =
        InnerProductSpace.toDual ℝ H x -
          InnerProductSpace.toDual ℝ H u := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hequation
  change
    lambda⁻¹ •
        (InnerProductSpace.toDual ℝ H x -
          InnerProductSpace.toDual ℝ H u) =
      DPhi u
  rw [← hscaled, inv_smul_smul₀ hlambda.ne']

/-- The Yosida approximation is the gradient evaluated at the resolvent:
`A_lambda x = gradient Phi (J_lambda x)`. -/
theorem convexGradientYosidaApproximation_eq_gradient
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x =
      ∇ Phi
        (convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) := by
  apply (InnerProductSpace.toDual ℝ H).injective
  rw [toDual_gradient,
    (hPhiDiff
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x)).fderiv]
  exact toDual_convexGradientYosidaApproximation
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda x

/-- Pairing the Yosida approximation with a vector agrees with pairing the
gradient at the resolvent with that vector. -/
theorem inner_convexGradientYosidaApproximation
    (lambda : ℝ) (hlambda : 0 < lambda) (x v : H) :
    inner ℝ
          (convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
          v =
      DPhi
        (convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x)
        v := by
  have h := congrArg
    (fun L : StrongDual ℝ H ↦ L v)
    (toDual_convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
  simpa only [InnerProductSpace.toDual_apply_apply] using h

/-- The Yosida approximation is `lambda`-cocoercive. -/
theorem convexGradientYosidaApproximation_cocoercive
    (lambda : ℝ) (hlambda : 0 < lambda) (x y : H) :
    lambda *
          ‖convexGradientYosidaApproximation
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
              convexGradientYosidaApproximation
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda y‖ ^ 2 ≤
      inner ℝ
        (convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
          convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)
        (x - y) := by
  rw [← subdifferentialYosida_eq_convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff hlambda x,
    ← subdifferentialYosida_eq_convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff hlambda y, real_inner_comm]
  exact yosidaApproximation_cocoercive
    (isProper_coeReal Phi) (convex_realEpigraph_coeReal hPhiConvex)
    (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda x y

/-- The Yosida approximation is monotone in the Hilbert-space pairing. -/
theorem convexGradientYosidaApproximation_monotone
    (lambda : ℝ) (hlambda : 0 < lambda) (x y : H) :
    0 ≤
      inner ℝ
        (convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
          convexGradientYosidaApproximation
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda y)
        (x - y) := by
  exact
    (mul_nonneg hlambda.le (sq_nonneg _)).trans
      (convexGradientYosidaApproximation_cocoercive
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y)

/-- The Yosida approximation cannot have larger norm than the original
gradient at the same point. -/
theorem convexGradientYosidaApproximation_norm_le
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ‖convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x‖ ≤
      ‖∇ Phi x‖ := by
  rw [← subdifferentialYosida_eq_convexGradientYosidaApproximation
    Phi hPhiConvex DPhi hPhiDiff hlambda x]
  exact norm_yosidaApproximation_le_of_mem_subdifferential
    (isProper_coeReal Phi) (convex_realEpigraph_coeReal hPhiConvex)
    (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda
    (gradient_mem_subdifferential_coe hPhiConvex (hPhiDiff x))

/-- The resolvent differs from the identity by at most
`lambda * ‖gradient Phi x‖`. -/
theorem convexGradientResolvent_norm_sub_self_le
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    ‖convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x -
        x‖ ≤
      lambda * ‖∇ Phi x‖ := by
  rw [← subdifferentialResolvent_eq_convexGradientResolvent
    Phi hPhiConvex DPhi hPhiDiff hlambda x]
  exact norm_resolvent_sub_self_le_of_mem_subdifferential
    (isProper_coeReal Phi) (convex_realEpigraph_coeReal hPhiConvex)
    (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda
    (gradient_mem_subdifferential_coe hPhiConvex (hPhiDiff x))

/-- The Yosida approximation has the sharp norm bound
`‖A_lambda x - A_lambda y‖ ≤ ‖x - y‖ / lambda`. -/
theorem convexGradientYosidaApproximation_norm_sub_le
    (lambda : ℝ) (hlambda : 0 < lambda) (x y : H) :
    ‖convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
        convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y‖ ≤
      ‖x - y‖ / lambda := by
  rw [← subdifferentialYosida_eq_convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff hlambda x,
    ← subdifferentialYosida_eq_convexGradientYosidaApproximation
      Phi hPhiConvex DPhi hPhiDiff hlambda y, div_eq_inv_mul]
  exact norm_yosidaApproximation_sub_le
    (isProper_coeReal Phi) (convex_realEpigraph_coeReal hPhiConvex)
    (lowerSemicontinuous_coe_of_hasFDerivAt Phi DPhi hPhiDiff) hlambda x y

/-- The Yosida approximation is globally Lipschitz with constant
`1 / lambda`. -/
theorem convexGradientYosidaApproximation_lipschitzWith
    (lambda : ℝ) (hlambda : 0 < lambda) :
    LipschitzWith (Real.toNNReal (1 / lambda))
      (convexGradientYosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) := by
  apply LipschitzWith.of_dist_le'
  intro x y
  have h :=
    convexGradientYosidaApproximation_norm_sub_le
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x y
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x -
        convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda y‖ ≤
        ‖x - y‖ / lambda :=
      h
    _ = (1 / lambda) * ‖x - y‖ := by ring

/-- The zeros of the Yosida approximation are exactly the critical points of
the convex functional. -/
theorem convexGradientYosidaApproximation_eq_zero_iff
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x = 0 ↔
      DPhi x = 0 := by
  constructor
  · intro hzero
    have hdecomp :=
      convexGradientResolvent_add_smul_yosidaApproximation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
    rw [hzero, smul_zero, add_zero] at hdecomp
    exact
      (convexGradientResolvent_eq_self_iff
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x).1 hdecomp
  · intro hcritical
    have hfixed :=
      (convexGradientResolvent_eq_self_iff
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x).2 hcritical
    simp only [convexGradientYosidaApproximation, hfixed, sub_self,
      smul_zero]

/-! ## Vanishing-parameter limits -/

/-- As the positive resolvent parameter tends to zero, the resolvent tends
pointwise to the identity. The estimate is quantitative and does not require
continuity of the gradient. -/
theorem tendsto_convexGradientResolvent
    {ι : Type*} {l : Filter ι}
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hlambda_zero : Tendsto lambda l (𝓝 0)) (x : H) :
    Tendsto
      (fun i ↦
        convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i).le x)
      l (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero
  · exact fun _ ↦ norm_nonneg _
  · exact fun i ↦
      convexGradientResolvent_norm_sub_self_le
        Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x
  · simpa using hlambda_zero.mul_const ‖∇ Phi x‖

/-- If the gradient is continuous at `x`, then its Yosida approximations
converge to the original gradient at `x` as the positive parameter tends to
zero. -/
theorem tendsto_convexGradientYosidaApproximation
    {ι : Type*} {l : Filter ι}
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hlambda_zero : Tendsto lambda l (𝓝 0)) (x : H)
    (hgradient : ContinuousAt (∇ Phi) x) :
    Tendsto
      (fun i ↦
        convexGradientYosidaApproximation
          Phi hPhiConvex DPhi hPhiDiff (lambda i) (hlambda i) x)
      l (𝓝 (∇ Phi x)) := by
  simpa only [convexGradientYosidaApproximation_eq_gradient,
    Function.comp_def] using
    Filter.Tendsto.comp hgradient
      (tendsto_convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda hlambda_zero x)

end PDE.Elliptic.Semilinear
