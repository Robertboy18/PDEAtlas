/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.Elliptic.Semilinear.Variational

/-!
# Basic theory of convex-gradient resolvents

We connect the variational existence theory for semilinear
equations with the resolvent maps used in nonlinear evolution equations.
For a differentiable convex functional `Phi` on a real Hilbert space, the
resolvent at a nonnegative parameter `lambda` is the unique solution of

`J_lambda x + lambda * grad Phi (J_lambda x) = x`.

The equation is stated through the Riesz identification with the strong
dual. The main results prove existence and uniqueness, the defining
equations, the nonlinear resolvent identity, bijectivity, and, for positive
`lambda`, the fixed-point characterization of critical points. The inverse is

`u |-> u + lambda * gradient Phi u`.

No separate operator or problem structure is introduced. The existence
proof applies the direct method to

`u |-> (1 / 2) * ‖u‖ ^ 2 + lambda * Phi u - inner x u`.

The affine lower bound needed for coercivity follows automatically from the
supporting hyperplane of `Phi` at the origin. Firm nonexpansivity and metric
estimates are developed in `ConvexGradient.Nonexpansive`.

## Main results

* `existsUnique_convex_gradient_resolvent`, `convexGradientResolvent`: the
  resolvent `J_lambda` and its defining equation.
* `convexGradientResolvent_resolvent_identity`: for `lambda > 0` and `mu ≥ 0`,
  `J_mu ((mu/lambda) x + (1 - mu/lambda) J_lambda x) = J_lambda x`.
* `convexGradientResolvent_bijective`,
  `convexGradientResolvent_add_smul_gradient_eq_self`: `J_lambda` is a
  bijection with inverse `u ↦ u + lambda • gradient Phi u`.
* `convexGradientResolvent_eq_self_iff`: for `lambda > 0`, fixed points of
  `J_lambda` are the critical points of `Phi`. At `lambda = 0`, the resolvent
  is the identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, Theorem 1 (iv) and the definition of the nonlinear
  resolvent, pp. 561-563.
  <https://doi.org/10.1090/gsm/019>
* H. Brezis, *Opérateurs maximaux monotones et semi-groupes de contractions dans les espaces
  de Hilbert*, North-Holland Mathematics Studies, North-Holland, 1973, Chapitre II
  (Opérateurs maximaux monotones), pp. 19-51.
  <https://doi.org/10.1016/S0304-0208(08)72383-1>
-/

open scoped Gradient

@[expose] public section

noncomputable section

open Set

namespace PDE.Elliptic.Semilinear

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- A differentiable convex functional has a unique gradient resolvent at
every nonnegative parameter. -/
theorem existsUnique_convex_gradient_resolvent
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) :
    ∃! u, ∀ v,
      inner ℝ u v + lambda * DPhi u v = inner ℝ x v := by
  let scaledPhi : H → ℝ := fun u ↦ lambda * Phi u
  let scaledDPhi : H → StrongDual ℝ H := fun u ↦ lambda • DPhi u
  have hscaledConvex : ConvexOn ℝ Set.univ scaledPhi := by
    simpa only [scaledPhi, smul_eq_mul] using
      ConvexOn.smul hlambda hPhiConvex
  have hscaledDiff :
      ∀ u, HasFDerivAt scaledPhi (scaledDPhi u) u := by
    intro u
    simpa only [scaledPhi, scaledDPhi] using
      (hPhiDiff u).const_mul lambda
  have hcoercive :
      ∀ u : H, (1 : ℝ) * ‖u‖ * ‖u‖ ≤ innerSL ℝ u u := by
    intro u
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
    simp only [one_mul, pow_two]
    exact le_rfl
  have hsymm : ∀ u v : H, innerSL ℝ u v = innerSL ℝ v u := by
    intro u v
    simpa only [innerSL_apply_apply] using (real_inner_comm u v).symm
  change ∃! u, ∀ v,
    innerSL ℝ u v + lambda * DPhi u v = innerSL ℝ x v
  simpa only [scaledDPhi, smul_apply, smul_eq_mul] using
    existsUnique_variational_weak_solution
      (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) hsymm
      1 zero_lt_one hcoercive scaledPhi hscaledConvex
      scaledDPhi hscaledDiff (innerSL ℝ x)

/-- The resolvent of the gradient of a differentiable convex functional. -/
noncomputable def convexGradientResolvent
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) : H :=
  Classical.choose <|
    existsUnique_convex_gradient_resolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x

/-- The resolvent satisfies its weak Euler equation. -/
theorem convexGradientResolvent_weak_equation
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x v : H) :
    inner ℝ
          (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
          v +
        lambda *
          DPhi
            (convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)
            v =
      inner ℝ x v := by
  exact
    (Classical.choose_spec
      (existsUnique_convex_gradient_resolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)).1 v

/-- Under the Riesz identification, the defining resolvent equation is
`J_lambda x + lambda * grad Phi (J_lambda x) = x`. -/
theorem convexGradientResolvent_equation
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) :
    InnerProductSpace.toDual ℝ H
          (convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) +
        lambda •
          DPhi
            (convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) =
      InnerProductSpace.toDual ℝ H x := by
  ext v
  simpa only [add_apply, smul_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply] using
    convexGradientResolvent_weak_equation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x v

/-- In Hilbert-space coordinates, the resolvent satisfies
`J_lambda x + lambda * gradient Phi (J_lambda x) = x`. -/
theorem convexGradientResolvent_gradient_equation
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x : H) :
    convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x +
        lambda •
          ∇ Phi
            (convexGradientResolvent
              Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) =
      x := by
  apply (InnerProductSpace.toDual ℝ H).injective
  rw [map_add, map_smul, toDual_gradient,
    (hPhiDiff
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)).fderiv]
  exact convexGradientResolvent_equation
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda x

/-- A point is the resolvent value exactly when it satisfies the defining
Riesz equation. -/
theorem convexGradientResolvent_eq_iff
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (x u : H) :
    convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x = u ↔
      InnerProductSpace.toDual ℝ H u + lambda • DPhi u =
        InnerProductSpace.toDual ℝ H x := by
  constructor
  · rintro rfl
    exact convexGradientResolvent_equation
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda x
  · intro hu
    have huWeak : ∀ v,
        inner ℝ u v + lambda * DPhi u v = inner ℝ x v := by
      intro v
      have hv := congrArg (fun L : StrongDual ℝ H ↦ L v) hu
      simpa only [add_apply, smul_apply, smul_eq_mul,
        InnerProductSpace.toDual_apply_apply] using hv
    exact
      ((Classical.choose_spec
        (existsUnique_convex_gradient_resolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda x)).2 u huWeak).symm

/-- Applying the resolvent after one explicit gradient step recovers the
starting point. -/
theorem convexGradientResolvent_add_smul_gradient_eq_self
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (u : H) :
    convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda
          (u + lambda • ∇ Phi u) =
      u := by
  apply (convexGradientResolvent_eq_iff
    Phi hPhiConvex DPhi hPhiDiff lambda hlambda _ u).2
  rw [map_add, map_smul, toDual_gradient, (hPhiDiff u).fderiv]

/-- Resolvents at two parameters satisfy the nonlinear resolvent identity.

Writing `J_lambda` for the resolvent, the point fed to `J_mu` is the affine
combination

`(mu / lambda) x + (1 - mu / lambda) J_lambda x`.

The identity follows because this point is also
`J_lambda x + mu * gradient Phi (J_lambda x)`. -/
theorem convexGradientResolvent_resolvent_identity
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (mu : ℝ) (hmu : 0 ≤ mu) (x : H) :
    convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff mu hmu
          ((mu / lambda) • x +
            (1 - mu / lambda) •
              convexGradientResolvent
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x) =
      convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x := by
  let u :=
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x
  have hx : x = u + lambda • ∇ Phi u := by
    exact
      (convexGradientResolvent_gradient_equation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x).symm
  have hargument :
      (mu / lambda) • x + (1 - mu / lambda) • u =
        u + mu • ∇ Phi u := by
    rw [hx, smul_add, smul_smul,
      div_mul_cancel₀ mu hlambda.ne']
    module
  rw [show
    (mu / lambda) • x +
        (1 - mu / lambda) •
          convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x =
      u + mu • ∇ Phi u by
        simpa only [u] using hargument]
  exact convexGradientResolvent_add_smul_gradient_eq_self
    Phi hPhiConvex DPhi hPhiDiff mu hmu u

/-- The resolvent of a single-valued convex gradient is injective. -/
theorem convexGradientResolvent_injective
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Function.Injective
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) := by
  intro x y hxy
  calc
    x =
        convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda x +
          lambda •
            ∇ Phi
              (convexGradientResolvent
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda x) :=
      (convexGradientResolvent_gradient_equation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda x).symm
    _ =
        convexGradientResolvent
            Phi hPhiConvex DPhi hPhiDiff lambda hlambda y +
          lambda •
            ∇ Phi
              (convexGradientResolvent
                Phi hPhiConvex DPhi hPhiDiff lambda hlambda y) := by
      rw [hxy]
    _ = y :=
      convexGradientResolvent_gradient_equation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda y

/-- The resolvent of a convex gradient is surjective. A preimage of `u` is
`u + lambda * gradient Phi u`. -/
theorem convexGradientResolvent_surjective
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Function.Surjective
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) := by
  intro u
  exact ⟨u + lambda • ∇ Phi u,
    convexGradientResolvent_add_smul_gradient_eq_self
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda u⟩

/-- The resolvent of a single-valued convex gradient is a bijection of the
ambient Hilbert space. -/
theorem convexGradientResolvent_bijective
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Function.Bijective
      (convexGradientResolvent
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda) :=
  ⟨convexGradientResolvent_injective
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda,
    convexGradientResolvent_surjective
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda⟩

/-- At parameter zero, the resolvent is the identity. -/
theorem convexGradientResolvent_zero
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (x : H) :
    convexGradientResolvent
      Phi hPhiConvex DPhi hPhiDiff 0 le_rfl x = x := by
  apply (convexGradientResolvent_eq_iff
    Phi hPhiConvex DPhi hPhiDiff 0 le_rfl x x).2
  simp

/-- For a positive parameter, fixed points of the resolvent are precisely
critical points of the convex functional. -/
theorem convexGradientResolvent_eq_self_iff
    (Phi : H → ℝ)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (DPhi : H → StrongDual ℝ H)
    (hPhiDiff : ∀ u, HasFDerivAt Phi (DPhi u) u)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : H) :
    convexGradientResolvent
          Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x = x ↔
      DPhi x = 0 := by
  constructor
  · intro hfixed
    have heq :=
      convexGradientResolvent_equation
        Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x
    rw [hfixed] at heq
    have hscaled : lambda • DPhi x = 0 := by
      have heq' :
          InnerProductSpace.toDual ℝ H x + lambda • DPhi x =
            InnerProductSpace.toDual ℝ H x + 0 := by
        simpa using heq
      exact add_left_cancel heq'
    exact (smul_eq_zero.mp hscaled).resolve_left hlambda.ne'
  · intro hcritical
    apply (convexGradientResolvent_eq_iff
      Phi hPhiConvex DPhi hPhiDiff lambda hlambda.le x x).2
    simp only [hcritical, smul_zero, add_zero]

end PDE.Elliptic.Semilinear
