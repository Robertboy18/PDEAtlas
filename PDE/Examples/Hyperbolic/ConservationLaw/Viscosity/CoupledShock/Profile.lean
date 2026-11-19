/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Viscosity.StationaryProfile
public import PDE.Hyperbolic.ConservationLaw.System.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# A coupled stationary viscous shock family

The shear `(a,b) ↦ (a+b,b)` couples two scalar Burgers equations. Two translated
logistic profiles give a smooth stationary solution of the viscous system
`∂ₜu + ∂ₓ flux(u) = ε ∂ₓ²u` for every `ε ≠ 0` (`viscous_equation`), bounded by `6`
uniformly in `ε`. Its initial data depend on `ε`.
-/

@[expose] public noncomputable section

open PDE.Common BurgersEquation.Viscosity

namespace PDE.Examples.ConservationLaw.CoupledShock

/-- The invertible shear used to couple the two Burgers components. -/
def mix (a b : ℝ) : ℝ^2 :=
  a • EuclideanSpace.single 0 1 +
    b • (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1)

@[simp] theorem mix_zero (a b : ℝ) : mix a b 0 = a + b := by simp [mix]
@[simp] theorem mix_one (a b : ℝ) : mix a b 1 = b := by simp [mix]

/-- `‖mix a b‖ ≤ ‖a‖ + 2‖b‖`. -/
theorem norm_mix_le (a b : ℝ) : ‖mix a b‖ ≤ ‖a‖ + 2 * ‖b‖ := by
  calc
    ‖mix a b‖ ≤ ‖a • (EuclideanSpace.single 0 1 : ℝ^2)‖ +
        ‖b • (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : ℝ^2)‖ :=
      norm_add_le _ _
    _ ≤ ‖a‖ + ‖b‖ * (1 + 1) := by
      simp only [norm_smul, PiLp.norm_single, norm_one, mul_one]
      gcongr
      simpa using norm_add_le (EuclideanSpace.single 0 1 : ℝ^2)
        (EuclideanSpace.single 1 1)
    _ = ‖a‖ + 2 * ‖b‖ := by ring

private theorem hasDerivAt_mix {a b : ℝ → ℝ} {a' b' x : ℝ}
    (ha : HasDerivAt a a' x) (hb : HasDerivAt b b' x) :
    HasDerivAt (fun y ↦ mix (a y) (b y)) (mix a' b') x :=
  HasDerivAt.add (ha.smul_const (EuclideanSpace.single 0 1 : ℝ^2))
    (hb.smul_const (EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1 : ℝ^2))

/-- The nonlinear flux in the sheared coordinates. -/
def flux (z : ℝ^2) : ℝ^2 := mix ((z 0 - z 1) ^ 2 / 2) (z 1 ^ 2 / 2)

/-- The flux is smooth. -/
theorem contDiff_flux : ContDiff ℝ (⊤ : ℕ∞) flux := by
  have h₀ : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ^2 ↦ z 0) :=
    (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).contDiff
  have h₁ : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ^2 ↦ z 1) :=
    (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).contDiff
  exact (((h₀.sub h₁).pow 2).div_const 2 |>.smul contDiff_const).add
    ((h₁.pow 2).div_const 2 |>.smul contDiff_const)

/-- The profile curve with shocks centred at `-1` and `1`. -/
def curve (ε x : ℝ) : ℝ^2 :=
  mix (stationaryProfile ε (-1) x) (stationaryProfile ε 1 x)

/-- Every fixed curve is smooth in space. -/
theorem contDiff_curve (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (curve ε) := by
  unfold curve mix
  exact ((contDiff_stationaryProfile ε (-1)).smul contDiff_const).add
    ((contDiff_stationaryProfile ε 1).smul contDiff_const)

/-- The family is stationary in time. -/
def viscous (ε : ℝ) (p : ℝ^2) : ℝ^2 := curve ε (p 1)

/-- The viscous family is smooth in space and time. -/
theorem contDiff_viscous (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (viscous ε) :=
  (contDiff_curve ε).comp (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).contDiff

/-- The viscous family is bounded by `6`, uniformly in `ε`. -/
theorem norm_viscous_le (ε : ℝ) (p : ℝ^2) : ‖viscous ε p‖ ≤ 6 := by
  have h := norm_mix_le (stationaryProfile ε (-1) (p 1)) (stationaryProfile ε 1 (p 1))
  have h₁ := norm_stationaryProfile_le ε (-1) (p 1)
  have h₂ := norm_stationaryProfile_le ε 1 (p 1)
  exact h.trans (by linarith)

private theorem deriv_curve (ε x : ℝ) :
    deriv (curve ε) x =
      mix (deriv (stationaryProfile ε (-1)) x) (deriv (stationaryProfile ε 1) x) :=
  (hasDerivAt_mix
    (((contDiff_stationaryProfile ε (-1)).differentiable (by simp) x).hasDerivAt)
    (((contDiff_stationaryProfile ε 1).differentiable (by simp) x).hasDerivAt)).deriv

private theorem deriv_deriv_curve (ε x : ℝ) :
    deriv (deriv (curve ε)) x =
      mix (deriv (deriv (stationaryProfile ε (-1))) x)
        (deriv (deriv (stationaryProfile ε 1)) x) := by
  rw [show deriv (curve ε) = _ from funext (deriv_curve ε)]
  exact (hasDerivAt_mix
    (((contDiff_infty_iff_deriv.mp (contDiff_stationaryProfile ε (-1))).2.differentiable
      (by simp) x).hasDerivAt)
    (((contDiff_infty_iff_deriv.mp (contDiff_stationaryProfile ε 1)).2.differentiable
      (by simp) x).hasDerivAt)).deriv

/-- Each profile curve solves the stationary viscous equation `(flux ∘ u)' = ε u''`. -/
theorem deriv_flux_curve {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    deriv (flux ∘ curve ε) x = ε • deriv (deriv (curve ε)) x := by
  have hcomp : flux ∘ curve ε = fun y ↦
      mix (stationaryProfile ε (-1) y ^ 2 / 2) (stationaryProfile ε 1 y ^ 2 / 2) := by
    funext y
    simp [flux, curve]
  have h₁ := ((contDiff_stationaryProfile ε (-1)).differentiable (by simp) x).hasDerivAt
  have h₂ := ((contDiff_stationaryProfile ε 1).differentiable (by simp) x).hasDerivAt
  have hd := hasDerivAt_mix ((h₁.pow 2).div_const 2) ((h₂.pow 2).div_const 2)
  change HasDerivAt (fun y ↦
    mix (stationaryProfile ε (-1) y ^ 2 / 2) (stationaryProfile ε 1 y ^ 2 / 2)) _ x at hd
  rw [hcomp, hd.deriv, deriv_deriv_curve]
  have he₁ := stationaryProfile_equation hε (-1) x
  have he₂ := stationaryProfile_equation hε 1 x
  ext i
  fin_cases i <;> simp [mix] <;> nlinarith

/-- The viscous family solves `∂ₜu + ∂ₓ flux(u) = ε ∂ₓ²u`. -/
theorem viscous_equation {ε : ℝ} (hε : ε ≠ 0) (p : ℝ^2) :
    PDE.Hyperbolic.ConservationLaw.System.fluxResidual flux (viscous ε) p =
      ε • (∂[1] (∂[1] (viscous ε))) p := by
  have hc := (contDiff_curve ε).differentiable (by simp)
  have hf := (contDiff_flux.comp (contDiff_curve ε)).differentiable (by simp)
  have hfirst : ∂[1] (viscous ε) = fun q ↦ deriv (curve ε) (q 1) := by
    funext q
    change (∂[1] (fun y : ℝ^2 ↦ curve ε (y 1))) q = _
    simpa using partialDeriv_comp_coord 1 1 (hc (q 1))
  rw [PDE.Hyperbolic.ConservationLaw.System.fluxResidual, hfirst]
  change (∂[0] (fun q : ℝ^2 ↦ curve ε (q 1))) p +
    (∂[1] (fun q : ℝ^2 ↦ (flux ∘ curve ε) (q 1))) p = _
  rw [partialDeriv_comp_coord 0 1 (hc (p 1)),
    partialDeriv_comp_coord 1 1 (hf (p 1)),
    partialDeriv_comp_coord 1 1
      ((contDiff_infty_iff_deriv.mp (contDiff_curve ε)).2.differentiable
        (by simp) (p 1))]
  simpa using deriv_flux_curve hε (p 1)

end PDE.Examples.ConservationLaw.CoupledShock
