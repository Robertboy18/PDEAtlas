/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SymbolDecay
public import PDE.Fluid.NavierStokes.Stationary.Linearization
import PDE.FDeriv.Laplacian.Congruence
import PDE.Analysis.Calculus.Homogeneous

/-!
# The stationary operator of a field with a homogeneous far field

The stationary self-similar operator `-½ (U + ξ·∇U) + (U·∇)U - ΔU` depends only on the germ of
`U`, and it is smooth when `U` is. If `U` differs from a far field `‖x‖⁻¹ A(x)`, with `A`
homogeneous of degree zero, by a function with symbol decay of order `-3`, then the operator
has symbol decay of order `-3`: Euler's identity makes `U + ξ·∇U` vanish on the far field, and
the transport and diffusion terms gain two derivatives' worth of decay. Hou, Wang and Yang use
the same cancellation for the forcing of their near field (Section 2.1).

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.1, (2.4), (2.5) and the
  decay of `F` in the sketch of proof of Proposition 3, p. 9.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public section

open Set Filter
open scoped ContDiff Topology

namespace NavierStokes

variable {n : ℕ}

/-- The stationary operator of two fields agreeing on an open set agrees on that set. -/
theorem stationaryVelocityOperator_eqOn {U V : ℝ^n → ℝ^n} {s : Set (ℝ^n)} (hs : IsOpen s)
    (h : EqOn U V s) : EqOn (stationaryVelocityOperator U) (stationaryVelocityOperator V) s := by
  intro x hx
  have hD : EqOn (fderiv ℝ U) (fderiv ℝ V) s := fun y hy ↦
    (eventuallyEq_of_mem (hs.mem_nhds hy) h).fderiv_eq
  simp only [stationaryVelocityOperator, PDE.advectiveDerivative, h hx, hD hx,
    EuclideanLaplacian.laplacian_congr_nhds (eventuallyEq_of_mem (hs.mem_nhds hx) h)]

/-- The stationary operator of a smooth field is smooth. -/
theorem contDiff_stationaryVelocityOperator {U : ℝ^n → ℝ^n} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ ∞ (stationaryVelocityOperator U) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ U) := hU.fderiv_right (by simp)
  have h₁ : ContDiff ℝ ∞ (fun x ↦ U x + fderiv ℝ U x x) := hU.add (hD.clm_apply contDiff_id)
  have h₂ : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ U x (U x)) := hD.clm_apply hU
  have hP (i : Fin n) : ContDiff ℝ ∞ (PDE.partialDeriv i U) := ContDiff.partialDeriv (k := ∞) hU i
  have hPP (i : Fin n) : ContDiff ℝ ∞ (PDE.partialDeriv i (PDE.partialDeriv i U)) :=
    ContDiff.partialDeriv (k := ∞) (hP i) i
  have hΔ : ContDiff ℝ ∞ (fun x ↦ ∑ i : Fin n,
      PDE.partialDeriv i (fun y ↦ PDE.partialDeriv i U y) x) :=
    ContDiff.sum fun i _ ↦ hPP i
  unfold stationaryVelocityOperator PDE.advectiveDerivative PDE.laplacian
  exact (((contDiff_const (c := (-(1 / 2) : ℝ))).smul h₁).add h₂).sub hΔ

open PDE.Analysis in
/-- A field whose difference from a far field `‖x‖⁻¹ A(x)`, with `A` homogeneous of degree zero
and of symbol decay of order zero, has symbol decay of order `-3` has a stationary operator of
symbol decay of order `-3`. -/
theorem hasSymbolDecay_stationaryVelocityOperator {U A : ℝ^n → ℝ^n}
    (hA : ∀ x (c : ℝ), 0 < c → A (c • x) = A x) (hAs : HasSymbolDecay 0 A)
    (he : HasSymbolDecay (-3) (fun x ↦ U x - ‖x‖⁻¹ • A x)) :
    HasSymbolDecay (-3) (stationaryVelocityOperator U) := by
  set u : ℝ^n → ℝ^n := fun x ↦ ‖x‖⁻¹ • A x with hu
  set e : ℝ^n → ℝ^n := fun x ↦ U x - ‖x‖⁻¹ • A x with he'
  have huS : HasSymbolDecay (-1) u :=
    (hasSymbolDecay_inv_norm.smul hAs).mono (by norm_num)
  have hUS : HasSymbolDecay (-1) U :=
    (huS.add (he.mono (by norm_num))).congr fun x _ ↦ by simp only [u, e, add_sub_cancel]
  have hUeq : U = fun x ↦ u x + e x := funext fun x ↦ by simp only [u, e, add_sub_cancel]
  have hhom : ∀ x (c : ℝ), 0 < c → u (c • x) = c ^ (-1 : ℤ) • u x := fun x c hc ↦ by
    rw [zpow_neg_one]
    exact PDE.inv_norm_smul_apply_smul_of_homogeneous hA x hc
  have hT : HasSymbolDecay (-3) (fun x ↦ (-(1 / 2) : ℝ) • (e x + fderiv ℝ e x x) +
      fderiv ℝ U x (U x) - PDE.laplacian U x) := by
    have h₁ : HasSymbolDecay (-3) (fun x ↦ fderiv ℝ e x x) :=
      (he.fderiv.clm_apply hasSymbolDecay_id).mono (by norm_num)
    have h₂ : HasSymbolDecay (-3) (fun x ↦ fderiv ℝ U x (U x)) :=
      (hUS.fderiv.clm_apply hUS).mono (by norm_num)
    have h₃ : HasSymbolDecay (-3) (PDE.laplacian U) := hUS.laplacian.mono (by norm_num)
    exact (((he.add h₁).const_smul _).add h₂).sub h₃
  refine hT.congr fun x hx ↦ ?_
  have hud : DifferentiableAt ℝ u x := (huS.contDiffAt hx).differentiableAt (by simp)
  have hed : DifferentiableAt ℝ e x := (he.contDiffAt hx).differentiableAt (by simp)
  have heuler : fderiv ℝ u x x = -u x := by
    rw [fderiv_apply_self_of_homogeneous hhom hud]
    simp
  have hDU : fderiv ℝ U x = fderiv ℝ u x + fderiv ℝ e x := by
    rw [hUeq]
    exact fderiv_add hud hed
  have hsum : U x + fderiv ℝ U x x = e x + fderiv ℝ e x x := by
    rw [hDU, add_apply, heuler]
    simp only [hUeq]
    abel
  simp only [stationaryVelocityOperator, PDE.advectiveDerivative, hsum]

end NavierStokes
