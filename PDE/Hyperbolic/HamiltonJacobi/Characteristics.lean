/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.Characteristics.Transport
import PDE.FDeriv.Operators

/-!
# Hamilton–Jacobi characteristic equations

The Hamilton–Jacobi equation `u_t + H(D_x u, t, x) = 0` on `ℝ × ℝ^n` is the
fully nonlinear first-order equation `F(Du, u, (t, x)) = 0` with

`F(p, z, (t, x)) = p₀ + H(pₓ, t, x)`,

where `p₀` is the time component of the spacetime gradient and `pₓ` its
spatial part; the value `z` does not enter. We specialize the general
characteristic system of `NonlinearFirstOrder.Characteristics.Transport` to
this `F` and read off Hamilton's equations. Along a characteristic the time
component advances at unit speed, so the parameter may be identified with
`t`, and

`ẋ = D_pH`, `ṗₓ = -D_xH`, `ṗ₀ = -H_t`, `ż = ⟪D_pH, pₓ⟫ - H`.

The last equation is the classical `ż = p · ẋ - H`: the general rule
`ż = ⟪D_pF, p⟫` gives `p₀ + ⟪D_pH, pₓ⟫`, and `p₀ = -H` on a solution.

This is Example 6 of Evans, §3.2.5(c), equations (62)-(65), for a time-dependent
Hamiltonian. Evans takes `H = H(p, x)`, so that `ṗ₀ = 0` there. The general system is (11) of
§3.2.1, and the main result specializes his Theorem 1 (Structure of characteristic ODE).

## Main results

* `hjF`: the operator `F` above; `hamiltonianTimeDerivative`: the partial derivative `H_t`.
  The partial gradients `D_pH` and `D_xH` are `momentumGradient H` and `positionGradient H`,
  the general momentum and position gradients applied to `H(p, t, x)`.
* `hamiltonJacobi_characteristic_equations_at`: for a `C²` solution `u` on
  an open set and a curve with `ẋ = D_pF`, Hamilton's equations hold at every
  parameter value at which the curve lies in the domain. Differentiability of
  `H` in its momentum argument and in its `(t, x)` arguments enter as separate
  hypotheses because the two partial gradients are taken separately.

`hamiltonJacobi_characteristic_equations_at` is pointwise at one parameter `s`, the
characteristic relation `hx_char` is also assumed only at `s`, and `H` enters through
`hF : ContDiff ℝ 1` of the phase function plus the two pointwise hypotheses `hHp` and
`hHtx`. The proof projects the spacetime gradient onto its time and space components
to identify Hamilton's equations.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.1, equation (11) and Theorem 1; §3.2.5(c), Example
  6, equations (62)-(65).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv)

namespace NonlinearFirstOrder

open PDE.Common
open scoped RealInnerProductSpace
open Finset

variable {n : ℕ}

section HamiltonJacobiCharacteristics

variable
    (H : ℝ^n → ℝ → ℝ^n → ℝ)

/-- Nonlinearity for Hamilton–Jacobi in the `F(Du, u, x) = 0` form:
`F(p, z, (t, x)) = p₀ + H(pₓ, t, x)` (the value argument `z` is unused). -/
noncomputable def hjF : ℝ^(n + 1) → ℝ → ℝ^(n + 1) → ℝ :=
  fun p _z xt ↦ p 0 + H (spatialPartCLM n p) (xt 0) (spatialPartCLM n xt)

/-- `∂H/∂t` as a 1D derivative. -/
noncomputable def hamiltonianTimeDerivative (p : ℝ^n) (t : ℝ) (x : ℝ^n) : ℝ :=
  deriv (fun τ : ℝ ↦ H p τ x) t

private theorem fderiv_Htx_apply_inr (p : ℝ^n) (t : ℝ) (x : ℝ^n) (dx : ℝ^n)
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H p tx.1 tx.2) (t, x)) :
    fderiv ℝ (fun tx : ℝ × ℝ^n ↦ H p tx.1 tx.2) (t, x) (0, dx) =
      fderiv ℝ (fun y : ℝ^n ↦ H p t y) x dx :=
  (congrArg (· dx) (hHtx.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv).symm

private theorem fderiv_Htx_apply_inl (p : ℝ^n) (t : ℝ) (x : ℝ^n)
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H p tx.1 tx.2) (t, x)) :
    fderiv ℝ (fun tx : ℝ × ℝ^n ↦ H p tx.1 tx.2) (t, x) (1, 0) =
      hamiltonianTimeDerivative H p t x := by
  rw [hamiltonianTimeDerivative, ← fderiv_apply_one_eq_deriv]
  exact (congrArg (· 1)
    (hHtx.hasFDerivAt.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t x)).fderiv).symm

/-- A spacetime coordinate derivative of `q ↦ q₀ + H(qₓ, t, x)` is the time coordinate of the
direction plus the momentum derivative of `H` in its spatial part. -/
private theorem partialDeriv_hjF_momentum (p xt : ℝ^(n + 1)) (j : Fin (n + 1))
    (hHp :
      DifferentiableAt ℝ (fun q : ℝ^n ↦ H q (xt 0) (spatialPartCLM n xt)) (spatialPartCLM n p)) :
    (∂[j] fun q : ℝ^(n + 1) ↦ q 0 + H (spatialPartCLM n q) (xt 0) (spatialPartCLM n xt)) p =
      EuclideanSpace.single j 1 0 +
        fderiv ℝ (fun q : ℝ^n ↦ H q (xt 0) (spatialPartCLM n xt)) (spatialPartCLM n p)
          (spatialPartCLM n (EuclideanSpace.single j 1)) :=
  congrArg (· (EuclideanSpace.single j 1)) ((EuclideanSpace.proj 0).hasFDerivAt.add
    (hHp.hasFDerivAt.comp p (spatialPartCLM n).hasFDerivAt)).fderiv

private theorem momentumGradient_hjF_time (p : ℝ^(n + 1)) (z : ℝ) (xt : ℝ^(n + 1))
    (hHp :
      DifferentiableAt ℝ (fun q : ℝ^n ↦ H q (xt 0) (spatialPartCLM n xt)) (spatialPartCLM n p)) :
    (momentumGradient (n := n + 1) (F := hjF H) p z xt) 0 = (1 : ℝ) := by
  simp only [momentumGradient, hjF, PDE.gradient_apply_eq_partialDeriv]
  rw [partialDeriv_hjF_momentum H p xt 0 hHp, spatialPartCLM_single_zero n]
  simp

private theorem momentumGradient_hjF_spatial (p : ℝ^(n + 1)) (z : ℝ) (xt : ℝ^(n + 1)) (i : Fin n)
    (hHp :
      DifferentiableAt ℝ (fun q : ℝ^n ↦ H q (xt 0) (spatialPartCLM n xt)) (spatialPartCLM n p)) :
    (momentumGradient (n := n + 1) (F := hjF H) p z xt) i.succ =
      momentumGradient H (spatialPartCLM n p) (xt 0) (spatialPartCLM n xt) i := by
  simp only [momentumGradient, hjF, PDE.gradient_apply_eq_partialDeriv]
  rw [partialDeriv_hjF_momentum H p xt i.succ hHp, spatialPartCLM_single_succ n]
  simp [partialDeriv, Fin.succ_ne_zero]

private theorem valueDerivative_hjF (p : ℝ^(n + 1)) (z : ℝ) (xt : ℝ^(n + 1)) :
    valueDerivative (n := n + 1) (F := hjF H) p z xt = 0 := by
  simp [valueDerivative, hjF]

/-- A spacetime coordinate derivative of `p₀ + H(pₓ, t, x)` is the derivative of
`(t, x) ↦ H(pₓ, t, x)` in the corresponding time-space direction. -/
private theorem partialDeriv_hjF_position (p xt : ℝ^(n + 1)) (j : Fin (n + 1))
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H (spatialPartCLM n p) tx.1 tx.2)
      (xt 0, spatialPartCLM n xt)) :
    (∂[j] fun y : ℝ^(n + 1) ↦ p 0 + H (spatialPartCLM n p) (y 0) (spatialPartCLM n y)) xt =
      fderiv ℝ (fun tx : ℝ × ℝ^n ↦ H (spatialPartCLM n p) tx.1 tx.2) (xt 0, spatialPartCLM n xt)
        (EuclideanSpace.single j 1 0, spatialPartCLM n (EuclideanSpace.single j 1)) := by
  let gCLM : ℝ^(n + 1) →L[ℝ] ℝ × ℝ^n := (EuclideanSpace.proj 0).prod (spatialPartCLM n)
  have hcomp := (hHtx.hasFDerivAt.comp xt gCLM.hasFDerivAt).fderiv
  rw [partialDeriv, fderiv_const_add]
  exact congrArg (· (EuclideanSpace.single j 1)) hcomp

private theorem positionGradient_hjF_time (p : ℝ^(n + 1)) (z : ℝ) (xt : ℝ^(n + 1))
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H (spatialPartCLM n p) tx.1 tx.2)
      (xt 0, spatialPartCLM n xt)) :
    (positionGradient (n := n + 1) (F := hjF H) p z xt) 0 =
      hamiltonianTimeDerivative H (spatialPartCLM n p) (xt 0) (spatialPartCLM n xt) := by
  simp only [positionGradient, hjF, PDE.gradient_apply_eq_partialDeriv]
  rw [partialDeriv_hjF_position H p xt 0 hHtx, spatialPartCLM_single_zero n]
  simpa using fderiv_Htx_apply_inl H _ _ _ hHtx

private theorem positionGradient_hjF_spatial (p : ℝ^(n + 1)) (z : ℝ) (xt : ℝ^(n + 1)) (i : Fin n)
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H (spatialPartCLM n p) tx.1 tx.2)
      (xt 0, spatialPartCLM n xt)) :
    (positionGradient (n := n + 1) (F := hjF H) p z xt) i.succ =
      positionGradient H (spatialPartCLM n p) (xt 0) (spatialPartCLM n xt) i := by
  simp only [positionGradient, hjF, PDE.gradient_apply_eq_partialDeriv]
  rw [partialDeriv_hjF_position H p xt i.succ hHtx, spatialPartCLM_single_succ n]
  simpa [partialDeriv] using fderiv_Htx_apply_inr H _ _ _ _ hHtx

/-!
### Hamilton's equations (specialization of characteristics)
-/

/-- If `u ∈ C²(U)` solves the Hamilton–Jacobi PDE
`u_t + H(Dₓu, t, x) = 0` on an open set `U` and `xcurve s ∈ U`, then at `s`
the characteristic satisfies Hamilton's equations for `(t, x, p)`, where
`p = Du` is the full spacetime gradient and `pₓ` is its spatial part. -/
theorem hamiltonJacobi_characteristic_equations_at {U : Set (ℝ^(n + 1))} (u : ℝ^(n + 1) → ℝ)
    (xcurve : ℝ → ℝ^(n + 1)) (s : ℝ) (hU : IsOpen U) (hxs : xcurve s ∈ U)
    (hF : ContDiff ℝ 1 (phaseFunction (n := n + 1) (hjF H))) (hu : ContDiffOn ℝ 2 u U)
    (hpde : ∀ xt ∈ U, hjF H (∇ u xt) (u xt) xt = 0) (hx : DifferentiableAt ℝ xcurve s)
    (hx_char : deriv xcurve s =
      momentumGradient (n := n + 1) (F := hjF H) (∇ u (xcurve s)) (u (xcurve s)) (xcurve s))
    (hHp : DifferentiableAt ℝ (fun q : ℝ^n ↦ H q ((xcurve s) 0) (spatialPartCLM n (xcurve s)))
      (spatialPartCLM n (∇ u (xcurve s))))
    (hHtx : DifferentiableAt ℝ (fun tx : ℝ × ℝ^n ↦ H (spatialPartCLM n (∇ u (xcurve s))) tx.1 tx.2)
      ((xcurve s) 0, spatialPartCLM n (xcurve s))) :
    let p : ℝ → ℝ^(n + 1) := fun t ↦ ∇ u (xcurve t)
    let z : ℝ → ℝ := fun t ↦ u (xcurve t)
    (deriv (fun t ↦ (xcurve t) 0) s = 1) ∧
      (deriv (fun t ↦ spatialPartCLM n (xcurve t)) s =
        momentumGradient H (spatialPartCLM n (p s)) ((xcurve s) 0)
          (spatialPartCLM n (xcurve s))) ∧
      (deriv (fun t ↦ (p t) 0) s =
        -hamiltonianTimeDerivative H (spatialPartCLM n (p s)) ((xcurve s) 0)
          (spatialPartCLM n (xcurve s))) ∧
      (deriv (fun t ↦ spatialPartCLM n (p t)) s =
        -positionGradient H (spatialPartCLM n (p s)) ((xcurve s) 0)
          (spatialPartCLM n (xcurve s))) ∧
      (deriv z s =
        ⟪momentumGradient H (spatialPartCLM n (p s)) ((xcurve s) 0)
          (spatialPartCLM n (xcurve s)),
          spatialPartCLM n (p s)⟫ -
          H (spatialPartCLM n (p s)) ((xcurve s) 0) (spatialPartCLM n (xcurve s))) := by
  classical
  intro p z
  obtain ⟨hz, hp, hpde_s⟩ := characteristic_equations_at (n := n + 1) (F := hjF H) (u := u)
    (xcurve := xcurve) (s := s) hU hxs hF hu hpde hx hx_char
  have hderivCLM {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : ℝ^(n + 1) →L[ℝ] F)
      {c : ℝ → ℝ^(n + 1)} (hc : DifferentiableAt ℝ c s) :
      deriv (fun t ↦ L (c t)) s = L (deriv c s) :=
    (L.hasFDerivAt.comp_hasDerivAt s hc.hasDerivAt).deriv
  have hderiv0 {c : ℝ → ℝ^(n + 1)} (hc : DifferentiableAt ℝ c s) :
      deriv (fun t ↦ c t 0) s = deriv c s 0 := by
    simpa using hderivCLM (EuclideanSpace.proj (0 : Fin (n + 1))) hc
  have hp_diff : DifferentiableAt ℝ p s := (differentiableAt_gradient (n := n + 1) u (xcurve s)
    (hu.contDiffAt (hU.mem_nhds hxs))).comp s hx
  have hp' : deriv p s = -positionGradient (n := n + 1) (F := hjF H) (p s) (z s) (xcurve s) := by
    simpa [sub_eq_add_neg, valueDerivative_hjF] using hp
  have hDp0 := momentumGradient_hjF_time H (p s) (z s) (xcurve s) hHp
  refine ⟨(hderiv0 hx).trans ((congrArg (· 0) hx_char).trans hDp0), ?_, ?_, ?_, ?_⟩
  · rw [hderivCLM _ hx]
    ext i
    simpa [spatialPartCLM_apply] using
      (congrArg (· i.succ) hx_char).trans (momentumGradient_hjF_spatial H (p s) (z s) _ i hHp)
  · rw [hderiv0 hp_diff, hp']
    simpa using congrArg Neg.neg (positionGradient_hjF_time H (p s) (z s) (xcurve s) hHtx)
  · rw [hderivCLM _ hp_diff, hp']
    ext i
    simpa [spatialPartCLM_apply] using
      congrArg Neg.neg (positionGradient_hjF_spatial H (p s) (z s) (xcurve s) i hHtx)
  · have hpde0 :
        p s 0 = -H (spatialPartCLM n (p s)) (xcurve s 0) (spatialPartCLM n (xcurve s)) := by
      simpa [p, hjF, add_eq_zero_iff_eq_neg] using hpde_s
    have hsum := Fin.sum_univ_succ fun j : Fin (n + 1) ↦
      p s j * momentumGradient (n := n + 1) (F := hjF H) (p s) (z s) (xcurve s) j
    simp only [hDp0, mul_one, momentumGradient_hjF_spatial H (p s) (z s) (xcurve s) _ hHp] at hsum
    rw [show deriv z s = _ from hz]
    simp only [PiLp.inner_apply, spatialPartCLM_apply, RCLike.inner_apply, conj_trivial] at hsum ⊢
    linarith

end HamiltonJacobiCharacteristics

end NonlinearFirstOrder
