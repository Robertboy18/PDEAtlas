/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv
import PDE.FDeriv.Calculus

/-!
# Entropy pairs and shock admissibility for scalar conservation laws

For the 1D quasilinear conservation law

`u_t + a(u) u_x = 0`,

an entropy/entropy-flux pair `(η,q)` formally satisfies `q'(r) = η'(r) * a(r)`. For smooth
solutions `u`, one then has the pointwise identity

`(η(u))_t + (q(u))_x = 0`.

We prove the pointwise entropy-pair identity and define the algebraic
Rankine–Hugoniot and Lax admissibility predicates. Distributional entropy
inequalities are in `PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak`.

The Rankine–Hugoniot condition is (12) of Evans, §3.4.1, and `LaxShock` is his entropy
condition (17). The entropy-pair identity is the scalar case of the computation (27) in Evans,
§11.4.2.

## Implementation notes

Evans requires the entropy of an entropy/entropy-flux pair to be convex (§11.4.3, (36)-(37)).
`EntropyPair` only asks for the compatibility relation `q' = η' a`; convexity is assumed where it
is used, in `PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (12), (17) and (19); §11.4.2,
  equation (27); §11.4.3, equations (36)-(37).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open PDE.Common

/-- A `C¹` entropy/entropy-flux pair for the quasilinear law
`u_t + a(u)u_x = 0`. -/
structure EntropyPair (a : ℝ → ℝ) where
  /-- Entropy. -/
  η : ℝ → ℝ
  /-- Entropy flux. -/
  q : ℝ → ℝ
  /-- Regularity of the entropy. -/
  eta_contDiff : ContDiff ℝ 1 η
  /-- Regularity of the entropy flux. -/
  entropyFlux_contDiff : ContDiff ℝ 1 q
  /-- Compatibility relation `q' = η' a`. -/
  hq : ∀ r : ℝ, deriv q r = deriv η r * a r

/-- Entropy identity for a smooth solution of `u_t + a(u)u_x = 0` (pointwise). -/
theorem entropy_identity_of_pde {a : ℝ → ℝ} (E : EntropyPair a) {u : ℝ^2 → ℝ} {x : ℝ^2}
    (hu : DifferentiableAt ℝ u x)
    (hpde : (∂[(0 : Fin 2)] u) x + a (u x) * (∂[(1 : Fin 2)] u) x = 0) :
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ E.η (u y))) x +
        (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ E.q (u y))) x = 0 := by
  have hηAt : DifferentiableAt ℝ E.η (u x) :=
    E.eta_contDiff.differentiable (by norm_num) (u x)
  have hqAt : DifferentiableAt ℝ E.q (u x) :=
    E.entropyFlux_contDiff.differentiable (by norm_num) (u x)
  have ht : (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ E.η (u y))) x = (∂[(0 : Fin 2)] u) x * deriv E.η (u x) :=
    (partialDeriv_comp_real (i := (0 : Fin 2)) (g := E.η) (u := u) (x := x) hηAt hu)
  have hx : (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ E.q (u y))) x = (∂[(1 : Fin 2)] u) x * deriv E.q (u x) :=
    (partialDeriv_comp_real (i := (1 : Fin 2)) (g := E.q) (u := u) (x := x) hqAt hu)
  -- replace `deriv q` using the entropy relation
  have hderq : deriv E.q (u x) = deriv E.η (u x) * a (u x) := by
    simpa using (E.hq (u x))
  -- multiply the PDE by `η'(u)` and regroup
  calc
    (∂[(0 : Fin 2)] (fun y : ℝ^2 ↦ E.η (u y))) x + (∂[(1 : Fin 2)] (fun y : ℝ^2 ↦ E.q (u y))) x
        = ((∂[(0 : Fin 2)] u) x * deriv E.η (u x)) +
            ((∂[(1 : Fin 2)] u) x * (deriv E.η (u x) * a (u x))) := by
            simp [ht, hx, hderq, mul_assoc,  mul_comm]
    _ = deriv E.η (u x) *
        ((∂[(0 : Fin 2)] u) x + a (u x) * (∂[(1 : Fin 2)] u) x) := by
          ring
    _ = 0 := by
          simp [hpde]

/-!
## Rankine–Hugoniot and (scalar) Lax shock admissibility (definitions)

For a C¹ flux convex between the two states, `Entropy.ConvexShock` uses the
Rankine–Hugoniot condition to prove that a decreasing planar shock is an
entropy weak solution.
-/

/-- Rankine–Hugoniot shock speed for a flux `f` and left/right states `uL,uR`.

Division in `ℝ` is totalized, so this formula has its shock-speed meaning only
under `uL ≠ uR`, which the theorems that use it assume. -/
noncomputable def rankineHugoniotSpeed (flux : ℝ → ℝ) (uL uR : ℝ) : ℝ :=
  (flux uR - flux uL) / (uR - uL)

/-- Rankine–Hugoniot condition at a shock with left/right states and speed `s`.

This uses right-minus-left jumps. -/
def RankineHugoniot (flux : ℝ → ℝ) (uL uR s : ℝ) : Prop :=
  flux uR - flux uL = s * (uR - uL)

/-- The Rankine–Hugoniot speed satisfies the Rankine–Hugoniot jump condition whenever the two
states are distinct. -/
theorem rankineHugoniotSpeed_satisfies {flux : ℝ → ℝ} {uL uR : ℝ} (h : uR ≠ uL) :
    RankineHugoniot flux uL uR (rankineHugoniotSpeed flux uL uR) := by
  unfold RankineHugoniot rankineHugoniotSpeed
  have hmul : uR - uL ≠ 0 := sub_ne_zero.mpr h
  field_simp [hmul]

/-- For distinct states, Rankine–Hugoniot is equivalent to the secant-slope
formula for the shock speed. -/
theorem rankineHugoniot_iff_speed_eq {flux : ℝ → ℝ} {uL uR s : ℝ} (h : uR ≠ uL) :
    RankineHugoniot flux uL uR s ↔ s = rankineHugoniotSpeed flux uL uR := by
  unfold RankineHugoniot rankineHugoniotSpeed
  constructor
  · intro hRH
    have hmul : uR - uL ≠ 0 := sub_ne_zero.mpr h
    -- divide by `(uR-uL)`
    apply (eq_div_iff hmul).2
    simpa [mul_comm] using hRH.symm
  · intro hs
    have hmul : uR - uL ≠ 0 := sub_ne_zero.mpr h
    -- multiply back by `(uR-uL)`
    have := (eq_div_iff hmul).1 hs
    simpa [mul_comm] using this.symm

/-- For a fixed nonzero jump, the Rankine–Hugoniot speed is unique. -/
theorem RankineHugoniot.unique_speed {flux : ℝ → ℝ} {uL uR s₁ s₂ : ℝ} (h : uR ≠ uL)
    (h₁ : RankineHugoniot flux uL uR s₁) (h₂ : RankineHugoniot flux uL uR s₂) :
    s₁ = s₂ := by
  have hs₁ := (rankineHugoniot_iff_speed_eq (flux := flux) (uL := uL) (uR := uR) (s := s₁) h).1 h₁
  have hs₂ := (rankineHugoniot_iff_speed_eq (flux := flux) (uL := uL) (uR := uR) (s := s₂) h).1 h₂
  exact hs₁.trans hs₂.symm

/-- Scalar Lax shock admissibility for a quasilinear speed `a`.

For a compressive shock from `uL` to `uR`, the shock speed lies between the characteristic speeds
on the two sides: `a uR < s < a uL`. This is the entropy condition (17) of Evans, §3.4.1. -/
def LaxShock (a : ℝ → ℝ) (uL uR s : ℝ) : Prop :=
  a uR < s ∧ s < a uL

/-- Projection to the right-state characteristic inequality. -/
theorem LaxShock.right_characteristic_lt_speed {a : ℝ → ℝ} {uL uR s : ℝ} (h : LaxShock a uL uR s) :
    a uR < s :=
  h.1

/-- Projection to the left-state characteristic inequality. -/
theorem LaxShock.speed_lt_left_characteristic {a : ℝ → ℝ} {uL uR s : ℝ} (h : LaxShock a uL uR s) :
    s < a uL :=
  h.2

/-- For a strictly increasing characteristic speed, scalar Lax admissibility
forces the usual compressive ordering of states: the right state lies below
the left state, as in (19) of Evans, §3.4.1. -/
theorem LaxShock.right_state_lt_left_state {a : ℝ → ℝ} {uL uR s : ℝ}
    (ha : StrictMono a) (h : LaxShock a uL uR s) :
    uR < uL :=
  ha.lt_iff_lt.mp (h.right_characteristic_lt_speed.trans h.speed_lt_left_characteristic)

end

end PDE.Hyperbolic.ConservationLaw.Scalar
