/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.IntegralPotential.ConjugateGrowth
public import PDE.Analysis.Calculus.Gradient
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Integral potentials on a Hilbert space

A continuous linear map into `Lᵖ` pulls an integral potential back to a Hilbert
space. Its derivative is the conjugate-space pairing. Riesz representation
then expresses the gradient of the quadratic-minus-potential energy as the
identity minus a continuous nonlinear term. With `H = H¹₀(U)`, `J` the inclusion into a
Lebesgue space and `G = F`, `energy J G` is the functional (26) of Evans, §8.5.2, and
`gradient_energy` is his formula `I'[u] = u - K[f(u)]`, which combines `I₁'[u] = u` with (29).
Evans represents the functional `v ↦ ∫ f(u) v dx` by `K[f(u)]`, where `K` solves the
Dirichlet problem by the Lax–Milgram theorem, (28); `dualLift` represents it by the Riesz
representation theorem, Mathlib's `InnerProductSpace.toDual`.
`inner_eq_integral_of_gradient_eq_zero` is the weak form of (22) in step 6 of his proof.

## Main definitions

* `energy`: the energy `½ ‖u‖² - ∫ G (J u)`.
* `dualLift`: the Riesz representative of the pairing of `Lᵠ` with the image of `J`.

## Main results

* `hasFDerivAt_energy`, `contDiff_energy`, `gradient_energy`: if `G' = g`, `g` is
  continuous, and `G` and `g` grow at most like `|z|^p` and `|z|^(p-1)`, the energy is `C¹`
  and its gradient is `u` minus the `dualLift` of the superposition of `g` with `J u`.
* `inner_eq_integral_of_gradient_eq_zero`: at a critical point `u`,
  `⟪u, v⟫ = ∫ g (J u) (J v)` for every `v`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, the problem (22), Theorem 3 (Existence) and
  steps 1-3 of its proof, (26)-(30), pp. 507-509, and step 6, p. 511.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Gradient

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ENNReal

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure α} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q]

/-- The Riesz representative of the `Lᵠ`–`Lᵖ` pairing after a Hilbert-space
inclusion. The lift is continuous and linear in the conjugate-space field. -/
def dualLift (J : H →L[ℝ] Lp ℝ p μ) : Lp ℝ q μ →L[ℝ] H :=
  (toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℝ H (Lp ℝ p μ) ℝ).flip J).comp
      ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p))

/-- The lifted field pairs with a Hilbert vector by the integral. -/
theorem inner_dualLift (J : H →L[ℝ] Lp ℝ p μ) (z : Lp ℝ q μ) (v : H) :
    inner ℝ (dualLift J z) v = ∫ x, z x * J v x ∂μ := by
  change inner ℝ ((toDual ℝ H).symm
    (((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p z).comp J)) v = _
  rw [toDual_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Quadratic Hilbert energy minus an integral potential. -/
def energy (J : H →L[ℝ] Lp ℝ p μ) (G : ℝ → ℝ) (u : H) : ℝ :=
  (1 / 2 : ℝ) * ‖u‖ ^ 2 - ∫ x, G (J u x) ∂μ

variable [IsFiniteMeasure μ] {G g : ℝ → ℝ} {A B C : ℝ}

include q in
omit [CompleteSpace H] in
/-- Conjugate growth gives the Fréchet derivative of the pulled-back
energy, without requiring the nonlinear field to belong to `L²`. -/
theorem hasFDerivAt_energy
    (J : H →L[ℝ] Lp ℝ p μ) (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1))) (u : H) :
    HasFDerivAt (energy J G)
      (innerSL ℝ u -
        ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p
          (Lp.superposition (fun _ ↦ g)
            (memLp_comp_of_conjugate_growth hc hg) (J u))).comp J) u := by
  have hQ : HasFDerivAt (fun w : H ↦ (1 / 2 : ℝ) * ‖w‖ ^ 2) (innerSL ℝ u) u := by
    convert (hasStrictFDerivAt_norm_sq u).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
    ext v
    simp
  exact hQ.sub ((hasStrictFDerivAt_integral_Lp_of_deriv_growth
    hp hp_top hd hc hG hg (J u)).hasFDerivAt.comp u J.hasFDerivAt)

include q in
omit [CompleteSpace H] in
/-- The pulled-back energy is `C¹` under the scalar conjugate growth bounds. -/
theorem contDiff_energy
    (J : H →L[ℝ] Lp ℝ p μ) (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1))) :
    ContDiff ℝ 1 (energy J G) :=
  (contDiff_const.mul (contDiff_norm_sq ℝ)).sub
    ((contDiff_integral_Lp_of_deriv_growth (q := q)
      hp hp_top hd hc hG hg).comp J.contDiff)

/-- The gradient is the identity minus the Riesz lift of the
superposition field. This is the compact-perturbation formula used in
Palais–Smale arguments. -/
theorem gradient_energy
    (J : H →L[ℝ] Lp ℝ p μ) (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1))) (u : H) :
    ∇ (energy J G) u = u - dualLift (q := q) J
      (Lp.superposition (fun _ ↦ g)
        (memLp_comp_of_conjugate_growth hc hg) (J u)) := by
  rw [gradient, (hasFDerivAt_energy (q := q) J hp hp_top hd hc hG hg u).fderiv,
    map_sub]
  change (toDual ℝ H).symm ((toDual ℝ H) u) - _ = _
  rw [(toDual ℝ H).symm_apply_apply]
  rfl

include q in
/-- A critical point satisfies the integral equation against every
Hilbert-space vector. -/
theorem inner_eq_integral_of_gradient_eq_zero
    (J : H →L[ℝ] Lp ℝ p μ) (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ z, HasDerivAt G (g z) z) (hc : Continuous g)
    (hG : ∀ z, |G z| ≤ A + B * |z| ^ p.toReal)
    (hg : ∀ z, |g z| ≤ C * (1 + |z| ^ (p.toReal - 1)))
    {u : H} (hu : ∇ (energy J G) u = 0) (v : H) :
    inner ℝ u v = ∫ x, g (J u x) * J v x ∂μ := by
  have h := congrArg (fun w ↦ inner ℝ w v) hu
  rw [gradient_energy (q := q) J hp hp_top hd hc hG hg,
    inner_sub_left, inner_zero_left, inner_dualLift, sub_eq_zero] at h
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [Lp.coeFn_superposition (fun _ : α ↦ g)
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg) (J u)] with x hx
  rw [hx]

end PDE.Analysis.Variational.IntegralPotential
