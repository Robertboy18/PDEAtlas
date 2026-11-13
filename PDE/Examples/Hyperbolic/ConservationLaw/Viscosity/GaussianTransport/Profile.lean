/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
public import PDE.Parabolic.Heat.Kernel.Basic
import CAS.ExactTactic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Viscous transport of one common Gaussian datum

The Gaussian is the one-dimensional heat kernel at time `1/4 + εt`,
multiplied by `√π` and translated by `ct` (`scalar_eq_heatKernel`). It solves
`∂ₜu + c ∂ₓu = ε ∂ₓ²u` (`scalar_equation`), equals `exp(-x²)` at `t = 0` for every `ε`,
is bounded by one for `t ≥ 0`, and converges pointwise to the transported Gaussian as
`ε → 0⁺` (`tendsto_scalar`).
-/

@[expose] public noncomputable section

open Filter Set PDE.Common
open scoped Topology

namespace PDE.Examples.ConservationLaw.GaussianTransport

/-- The normalized, advected Gaussian heat kernel. -/
def scalar (c ε : ℝ) (p : ℝ^2) : ℝ :=
  (1 + 4 * ε * p 0) ^ (-(1 : ℝ) / 2) *
    Real.exp (-((p 1 - c * p 0) ^ 2 / (1 + 4 * ε * p 0)))

/-- `scalar c ε` is `√π` times the heat kernel at `x - ct` and time `(1 + 4εt)/4`. -/
theorem scalar_eq_heatKernel (c ε : ℝ) (p : ℝ^2)
    (hs : 0 < 1 + 4 * ε * p 0) :
    scalar c ε p = Real.pi ^ ((1 : ℝ) / 2) *
      HeatEquation.fundamentalSolutionHeat
        (EuclideanSpace.single 0 (p 1 - c * p 0) : ℝ^1)
        ((1 + 4 * ε * p 0) / 4) := by
  have ht : ¬ (1 + 4 * ε * p 0) / 4 ≤ 0 := by linarith
  have hb : 4 * Real.pi * ((1 + 4 * ε * p 0) / 4) =
      Real.pi * (1 + 4 * ε * p 0) := by ring
  rw [HeatEquation.fundamentalSolutionHeat, ite_eq_right ht, hb]
  simp only [Nat.cast_one, PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  rw [Real.mul_rpow Real.pi_pos.le hs.le]
  have hc : Real.pi ^ ((1 : ℝ) / 2) * Real.pi ^ (-(1 : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add Real.pi_pos]
    norm_num
  unfold scalar
  rw [← mul_assoc, ← mul_assoc, hc, one_mul]
  congr 2
  ring

/-- The denominator is positive on closed forward time for every nonnegative viscosity. -/
theorem denominator_pos {ε : ℝ} (hε : 0 ≤ ε) {p : ℝ^2} (hp : 0 ≤ p 0) :
    0 < 1 + 4 * ε * p 0 := by positivity

/-- `scalar c ε` is smooth where `1 + 4εt > 0`. -/
theorem contDiffAt_scalar (c ε : ℝ) (p : ℝ^2)
    (hs : 0 < 1 + 4 * ε * p 0) : ContDiffAt ℝ (⊤ : ℕ∞) (scalar c ε) p := by
  unfold scalar
  cas using hs

/-- `|scalar c ε| ≤ 1` for `t ≥ 0` and `ε ≥ 0`. -/
theorem norm_scalar_le {ε : ℝ} (hε : 0 ≤ ε) (c : ℝ) {p : ℝ^2} (hp : 0 ≤ p 0) :
    ‖scalar c ε p‖ ≤ 1 := by
  have hs := denominator_pos hε hp
  have hS : 1 ≤ 1 + 4 * ε * p 0 := by nlinarith [mul_nonneg hε hp]
  have he : Real.exp (-((p 1 - c * p 0) ^ 2 / (1 + 4 * ε * p 0))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (sq_nonneg _) hs.le))
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold scalar; positivity)]
  exact (mul_le_mul_of_nonneg_right
    (Real.rpow_le_one_of_one_le_of_nonpos hS (by norm_num)) (Real.exp_pos _).le).trans
    (by simpa using he)

private theorem partialDeriv_scalar (c ε : ℝ) (p : ℝ^2) (i : Fin 2)
    (hs : 0 < 1 + 4 * ε * p 0) :
    (∂[i] (scalar c ε)) p =
      (-(4 * ε * (EuclideanSpace.single i 1 : ℝ^2) 0) / (2 * (1 + 4 * ε * p 0)) +
        (p 1 - c * p 0) ^ 2 * (4 * ε * (EuclideanSpace.single i 1 : ℝ^2) 0) /
          (1 + 4 * ε * p 0) ^ 2 -
        2 * (p 1 - c * p 0) *
          ((EuclideanSpace.single i 1 : ℝ^2) 1 -
            c * (EuclideanSpace.single i 1 : ℝ^2) 0) / (1 + 4 * ε * p 0)) *
      scalar c ε p := by
  have h₀ := (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h₁ := (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hS := (h₀.const_mul (4 * ε)).const_add 1
  have hY := h₁.sub (h₀.const_mul c)
  have hI := (hasDerivAt_inv hs.ne').comp_hasFDerivAt p hS
  have hr := hS.rpow_const (p := -(1 : ℝ) / 2) (Or.inl hs.ne')
  have he := (((hY.pow 2).mul hI).neg).exp
  have hu := hr.mul he
  change HasFDerivAt (scalar c ε) _ p at hu
  rw [partialDeriv, hu.fderiv]
  simp only [add_apply, smul_apply, sub_apply, neg_apply, Pi.neg_apply,
    Pi.mul_apply, Pi.sub_apply, Function.comp_apply, EuclideanSpace.coe_proj,
    smul_eq_mul, nsmul_eq_mul, Nat.reduceSub, pow_one]
  rw [Real.rpow_sub hs, Real.rpow_one]
  unfold scalar
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The time derivative of `scalar c ε`. -/
theorem partialDeriv_time_scalar (c ε : ℝ) (p : ℝ^2)
    (hs : 0 < 1 + 4 * ε * p 0) :
    (∂[0] (scalar c ε)) p =
      (-2 * ε / (1 + 4 * ε * p 0) +
        4 * ε * (p 1 - c * p 0) ^ 2 / (1 + 4 * ε * p 0) ^ 2 +
        2 * c * (p 1 - c * p 0) / (1 + 4 * ε * p 0)) * scalar c ε p := by
  rw [partialDeriv_scalar c ε p 0 hs]
  apply congrArg (· * scalar c ε p)
  simp only [PiLp.single_apply]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The first spatial derivative. -/
theorem partialDeriv_space_scalar (c ε : ℝ) (p : ℝ^2)
    (hs : 0 < 1 + 4 * ε * p 0) :
    (∂[1] (scalar c ε)) p =
      (-2 * (p 1 - c * p 0) / (1 + 4 * ε * p 0)) * scalar c ε p := by
  rw [partialDeriv_scalar c ε p 1 hs]
  simp
  ring

/-- The second spatial derivative. -/
theorem secondPartialDeriv_space_scalar (c ε : ℝ) (p : ℝ^2)
    (hs : 0 < 1 + 4 * ε * p 0) :
    (∂[1] (∂[1] (scalar c ε))) p =
      (4 * (p 1 - c * p 0) ^ 2 / (1 + 4 * ε * p 0) ^ 2 -
        2 / (1 + 4 * ε * p 0)) * scalar c ε p := by
  have h₀ := (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have h₁ := (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hS := (h₀.const_mul (4 * ε)).const_add 1
  have hY := h₁.sub (h₀.const_mul c)
  have hI := (hasDerivAt_inv hs.ne').comp_hasFDerivAt p hS
  have hK := (hY.const_mul (-2)).mul hI
  have heq : ∂[1] (scalar c ε) =ᶠ[𝓝 p]
      fun q ↦ (-2 * (q 1 - c * q 0) / (1 + 4 * ε * q 0)) * scalar c ε q := by
    filter_upwards [hS.continuousAt.eventually (lt_mem_nhds hs)] with q hq
    exact partialDeriv_space_scalar c ε q hq
  change HasFDerivAt (fun q ↦ -2 * (q 1 - c * q 0) / (1 + 4 * ε * q 0)) _ p at hK
  rw [partialDeriv_congr_nhds 1 heq, partialDeriv_mul hK.differentiableAt
    ((contDiffAt_scalar c ε p hs).differentiableAt (by simp)),
    partialDeriv_space_scalar c ε p hs]
  rw [partialDeriv, hK.fderiv]
  simp [EuclideanSpace.coe_proj]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- The classical viscous transport equation holds pointwise. -/
theorem scalar_equation (c ε : ℝ) (p : ℝ^2) (hs : 0 < 1 + 4 * ε * p 0) :
    (∂[0] (scalar c ε)) p + c * (∂[1] (scalar c ε)) p =
      ε * (∂[1] (∂[1] (scalar c ε))) p := by
  rw [partialDeriv_time_scalar c ε p hs, partialDeriv_space_scalar c ε p hs,
    secondPartialDeriv_space_scalar c ε p hs]
  ring

/-- At `t = 0`, `scalar c ε` is `exp(-x²)` for every `ε`. -/
theorem scalar_initial (c ε x : ℝ) :
    scalar c ε !₂[0, x] = Real.exp (-x ^ 2) := by
  simp [scalar]

/-- At every fixed spacetime point the family converges to the transported Gaussian. -/
theorem tendsto_scalar (c : ℝ) (p : ℝ^2) :
    Tendsto (fun ε : ℝ ↦ scalar c ε p) (𝓝[>] 0)
      (𝓝 (Real.exp (-((p 1 - c * p 0) ^ 2)))) := by
  have hS : Tendsto (fun ε : ℝ ↦ 1 + 4 * ε * p 0) (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hi : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (hi.const_mul 4 |>.mul_const (p 0) |>.const_add 1)
  have hr := hS.rpow_const (p := -(1 : ℝ) / 2) (by norm_num)
  have harg := ((tendsto_const_nhds (x := (p 1 - c * p 0) ^ 2)).div hS
    (by norm_num)).neg
  have he := Real.continuous_exp.continuousAt.tendsto.comp harg
  simpa [scalar] using hr.mul he

end PDE.Examples.ConservationLaw.GaussianTransport
