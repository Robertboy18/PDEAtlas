/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.StrongMonotonicity.Directional
public import PDE.Analysis.Normed.PiLp.CompareExp
public import PDE.Spaces.Sobolev.Calculus.Composition.Implicit.LocalizedParameters

/-!
# Recovering a normal derivative from a nonlinear flux

The normal component of a uniformly monotone vector flux is a strictly monotone scalar
function of the missing normal gradient component. Known localized Sobolev parameters
and the localized normal flux then determine that component's weak normal derivative.
The proof uses inward quotients and keeps all cutoff errors.

In applications the parameter is the tangential gradient with its normal coordinate
set to zero. It may vanish identically, as it does in dimension one.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.Composition.Implicit
open PDE.Analysis.Operator
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} [Fact (0 < n)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A localized normal flux with controlled tangential parameters determines the missing
weak normal derivative. The scalar monotonicity hypothesis is derived from the vector flux. -/
theorem exists_localized_normal_derivative_of_flux
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (A : ℝ^n → ℝ^n → ℝ^n) (K C : ℝ≥0) {m : ℝ} (hm : 0 < m)
    (hmono : ∀ x ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A x z - A x w, z - w⟫)
    (hvariation : ∀ x ∈ HalfSpace.upper n, ∀ y ∈ HalfSpace.upper n, ∀ z w : ℝ^n,
      ‖A y w - A x z‖ ≤ K * ‖y - x‖ * ‖z‖ + C * ‖w - z‖)
    (η : ℝ^n → ℝ) {D : ℝ≥0} (hη : LipschitzWith D η)
    (hηbound : ∀ x ∈ HalfSpace.upper n, |η x| ≤ 1)
    (u q U : DerivLp n p (HalfSpace.upper n))
    (P : Fin n → DerivLp n p (HalfSpace.upper n))
    (W : Fin n → W^{1,p}(HalfSpace.upper n))
    (Q : W^{1,p}(HalfSpace.upper n))
    (hW : ∀ j, ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM (W j) x = η x * P j x)
    (heq : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      A x (parameterValues P x + u x •
        EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1)
        (PDE.Common.lastIndex (n := n)) = q x)
    (hU : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n), U x = η x * u x)
    (hQ : ∀ᵐ x ∂domainMeasure n (HalfSpace.upper n),
      wkpBaseCoordinateCLM Q x = η x * q x) :
    ∃ g : DerivLp n p (HalfSpace.upper n),
      ‖g‖ ≤
        (‖wkpCoordinateCLM (singleDerivIndex n (PDE.Common.lastIndex (n := n)))
          ((SobolevSpace.Extension.GraphSpace.HalfSpace.operator n p).toContinuousLinearMap Q)‖ +
          localizedParameterBound K C D u P W + D * (‖q‖ + m * ‖u‖)) / m ∧
      HasWeakDerivativeOn (HalfSpace.upper n) [PDE.Common.lastIndex (n := n)]
        (U : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let e : ℝ^n := EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1
  have he : ‖e‖ = 1 := by simp [e]
  apply exists_localized_normal_weakDerivative_of_sobolev_parameters hp hp_top
    (fun x z t ↦ directionalFlux (A x) e z t) K C hm
    (fun x hx z s t ↦ directionalFlux_pairing_lower_bound (A x) (hmono x hx) e he z s t)
    ?_ η hη hηbound u q U P W Q hW ?_ hU hQ
  · intro x hx y hy z w t
    exact (directionalFlux_norm_sub_le A K C (hvariation x hx y hy) e he z w t).trans
      (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (PiLp.norm_le_sum_norm z))
          (by positivity))
        (mul_le_mul_of_nonneg_left (PiLp.norm_le_sum_norm (w - z)) C.coe_nonneg))
  · simpa only [directionalFlux, e, EuclideanSpace.inner_single_right,
      RCLike.conj_to_real, one_mul] using heq

end PDE.Elliptic.Regularity.Quasilinear
