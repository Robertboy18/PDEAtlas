/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.EnergyIdentity
public import PDE.FDeriv.SpaceTime
import PDE.FDeriv.Calculus

/-!
# Classical waves with a variable principal matrix

The wave operator is in nondivergence form: `uₜₜ - ∑ aⁱʲ uᵢⱼ`.
Its energy uses the same matrix. The flux convention places the outward
direction in the second matrix index, so its divergence differentiates that index.

The coefficients depend on space only, as for the operator (71) and the equation (72) of Evans,
§7.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.4, equations (71)-(72).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open PDE.Common

variable {n : ℕ}

/-- The nondivergence wave operator with a spatially varying principal matrix. -/
def waveOperator (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] (∂[0] u)) p -
    ∑ i, ∑ j, a (spatialPart p) i j *
      (∂[i.succ] (∂[j.succ] u)) p

/-- The kinetic plus principal quadratic energy density. -/
def energyDensity (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  (1 / 2 : ℝ) * (((∂[0] u) p) ^ 2 +
    ∑ i, ∑ j, a (spatialPart p) i j *
      (∂[i.succ] u) p * (∂[j.succ] u) p)

/-- The energy flux in spatial direction `j`. -/
def energyFlux (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (u : ℝ^(n + 1) → ℝ) (j : Fin n) (p : ℝ^(n + 1)) : ℝ :=
  (∂[0] u) p *
    ∑ i, a (spatialPart p) i j * (∂[i.succ] u) p

/-- Divergence of each row of the principal matrix. -/
def coefficientDivergence (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦ ∑ j, (∂[j] (fun y ↦ a y i j)) x

/-- The nondivergence wave operator is linear on classical germs. -/
theorem waveOperator_sub (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) {u v : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u p) (hv : ContDiffAt ℝ 2 v p) :
    waveOperator a (u - v) p = waveOperator a u p - waveOperator a v p := by
  have hsecond (i j : Fin (n + 1)) : (∂[i] (∂[j] (u - v))) p = (∂[i] (∂[j] u)) p -
          (∂[i] (∂[j] v)) p := by
    have hgerm : (∂[j] (u - v)) =ᶠ[nhds p]
        fun y ↦ (∂[j] u) y - (∂[j] v) y := by
      filter_upwards [hu.eventually (by norm_num), hv.eventually (by norm_num)] with y huy hvy
      exact PDE.partialDeriv_sub (huy.differentiableAt (by norm_num))
        (hvy.differentiableAt (by norm_num))
    rw [PDE.partialDeriv_congr_nhds i hgerm]
    exact PDE.partialDeriv_sub ((PDE.contDiffAt_partialDeriv 1 hu j).differentiableAt (by norm_num))
      ((PDE.contDiffAt_partialDeriv 1 hv j).differentiableAt (by norm_num))
  simp only [waveOperator, hsecond, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Forming the matrix energy costs one derivative of the field. -/
theorem contDiffAt_energyDensity {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (ha : ∀ i j, ContDiffAt ℝ 1 (fun x ↦ a x i j) (spatialPart p))
    (hu : ContDiffAt ℝ 2 u p) :
    ContDiffAt ℝ 1 (energyDensity a u) p := by
  have hd (i : Fin (n + 1)) := PDE.contDiffAt_partialDeriv 1 hu i
  exact contDiffAt_const.mul ((hd 0).pow 2 |>.add (ContDiffAt.sum fun i _ ↦ ContDiffAt.sum fun j _ ↦
      ((ha i j).comp p (spatialPartCLM n).contDiff.contDiffAt |>.mul (hd i.succ)).mul (hd j.succ)))

/-- Each flux component is continuously differentiable for classical data. -/
theorem contDiffAt_energyFlux {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (ha : ∀ i j, ContDiffAt ℝ 1 (fun x ↦ a x i j) (spatialPart p))
    (hu : ContDiffAt ℝ 2 u p) (j : Fin n) :
    ContDiffAt ℝ 1 (energyFlux a u j) p := by
  have hd (i : Fin (n + 1)) := PDE.contDiffAt_partialDeriv 1 hu i
  exact (hd 0).mul (ContDiffAt.sum fun i _ ↦
    ((ha i j).comp p (spatialPartCLM n).contDiff.contDiffAt).mul (hd i.succ))

/-- Nonnegativity of the principal quadratic form gives nonnegative wave energy. -/
theorem energyDensity_nonneg {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (hpos : ∀ x (v : ℝ^n), 0 ≤ ∑ i, ∑ j, a x i j * v i * v j) (u : ℝ^(n + 1) → ℝ) (p : ℝ^(n + 1)) :
    0 ≤ energyDensity a u p := by
  have h := hpos (spatialPart p) (classicalWaveSpatialGradient u p)
  simpa only [energyDensity, classicalWaveSpatialGradient_apply] using
    mul_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (add_nonneg (sq_nonneg _) h)

/-- Vanishing nonnegative energy forces the time derivative to vanish. -/
theorem time_derivative_eq_zero_of_energyDensity_eq_zero {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ}
    (hpos : ∀ x (v : ℝ^n), 0 ≤ ∑ i, ∑ j, a x i j * v i * v j) {u : ℝ^(n + 1) → ℝ} {p : ℝ^(n + 1)}
    (hzero : energyDensity a u p = 0) :
    (∂[0] u) p = 0 := by
  have h := hpos (spatialPart p) (classicalWaveSpatialGradient u p)
  simp only [classicalWaveSpatialGradient_apply] at h
  unfold energyDensity at hzero
  nlinarith [sq_nonneg ((∂[0] u) p)]

end WaveEquation.VariableCoefficient
