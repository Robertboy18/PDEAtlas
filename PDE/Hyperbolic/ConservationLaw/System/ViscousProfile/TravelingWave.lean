/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.FDeriv.Calculus
public import PDE.Hyperbolic.ConservationLaw.PlanarShock
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Traveling profiles and the viscous residual

The spacetime coordinates are `(t,x)`. Substituting a profile at
`(x - speed * t) / ε` gives the conservative viscous equation, with
ordinary coordinate derivatives. The vector chain rule keeps the state dimension
arbitrary, including zero.

In the notation of Evans, §11.4.1, `travelingWave v speed ε` is the traveling wave
`u^ε(x, t) = v((x - σt)/ε)` of (3) with `σ = speed`.
`IsViscousProfile.fluxResidual_travelingWave` shows that a profile with (4)-(5) gives a
solution of the viscous system (2), and `IsViscousProfile.tendsto_travelingWave` gives the
limit (6) as `ε → 0` at every point off the line `x = σt`, the shock joining `u_l` to `u_r`
with speed `σ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4, equation (2); §11.4.1, equations (3)-(6).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}

/-- The stretched coordinate of a traveling layer in spacetime `(t,x)`. -/
def profileCoordinate (speed ε : ℝ) (p : ℝ^2) : ℝ :=
  (p 1 - speed * p 0) / ε

/-- The spacetime field obtained by inserting a traveling layer profile. -/
def travelingWave (v : ℝ → ℝ^m) (speed ε : ℝ) (p : ℝ^2) : ℝ^m :=
  v (profileCoordinate speed ε p)

/-- The stretched coordinate is smooth for every fixed scale; at scale zero
the totalized expression is the constant zero coordinate. -/
theorem contDiff_profileCoordinate (speed ε : ℝ) :
    ContDiff ℝ ω (profileCoordinate speed ε) := by
  unfold profileCoordinate
  fun_prop

/-- Composition with the stretched coordinate preserves every finite or infinite
order of differentiability of the profile. -/
theorem contDiff_travelingWave {v : ℝ → ℝ^m} {k : ℕ∞ω} (hv : ContDiff ℝ k v) (speed ε : ℝ) :
    ContDiff ℝ k (travelingWave v speed ε) :=
  hv.comp ((contDiff_profileCoordinate speed ε).of_le le_top)

/-- Time differentiation of the stretched coordinate. -/
theorem partialDeriv_time_profileCoordinate (speed : ℝ) {ε : ℝ} (hε : ε ≠ 0) (p : ℝ^2) :
    (∂[0] (profileCoordinate speed ε)) p = -speed / ε := by
  unfold profileCoordinate
  cas using hε

/-- Space differentiation of the stretched coordinate. -/
theorem partialDeriv_space_profileCoordinate (speed : ℝ) {ε : ℝ} (hε : ε ≠ 0) (p : ℝ^2) :
    (∂[1] (profileCoordinate speed ε)) p = ε⁻¹ := by
  unfold profileCoordinate
  cas using hε

/-- The vector chain rule for a differentiable profile. -/
theorem partialDeriv_travelingWave {v : ℝ → ℝ^m} (hv : Differentiable ℝ v) (speed ε : ℝ) (i : Fin 2)
    (p : ℝ^2) :
    (∂[i] (travelingWave v speed ε)) p =
      (∂[i] (profileCoordinate speed ε)) p • deriv v (profileCoordinate speed ε p) := by
  change (∂[i] (v ∘ profileCoordinate speed ε)) p = _
  unfold partialDeriv
  rw [fderiv_comp p (hv _) ((contDiff_profileCoordinate speed ε).differentiable (by simp) p),
    ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv]

/-- The second spatial derivative is the rescaled second ordinary derivative
of the profile. -/
theorem partialDeriv_space_twice_travelingWave {v : ℝ → ℝ^m} (hv : ContDiff ℝ 2 v) (speed : ℝ)
    {ε : ℝ} (hε : ε ≠ 0) (p : ℝ^2) :
    (∂[1] (∂[1] (travelingWave v speed ε))) p =
      ε⁻¹ • (ε⁻¹ • deriv (deriv v) (profileCoordinate speed ε p)) := by
  have heq : (∂[1] (travelingWave v speed ε)) =
      fun q ↦ ε⁻¹ • travelingWave (deriv v) speed ε q := by
    funext q
    rw [partialDeriv_travelingWave (hv.differentiable (by norm_num)),
      partialDeriv_space_profileCoordinate speed hε]
    rfl
  rw [heq, partialDeriv_const_smul, partialDeriv_travelingWave hv.differentiable_deriv_two,
    partialDeriv_space_profileCoordinate speed hε]

/-- A profile solves the conservative viscous PDE after stretching. -/
theorem IsViscousProfile.fluxResidual_travelingWave {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ}
    {v : ℝ → ℝ^m} (hv : IsViscousProfile flux uL uR speed v) (hflux : Differentiable ℝ flux) {ε : ℝ}
    (hε : ε ≠ 0) (p : ℝ^2) :
    fluxResidual flux (travelingWave v speed ε) p =
      ε • (∂[1] (∂[1] (travelingWave v speed ε))) p := by
  have hdiff := (contDiff_travelingWave hv.contDiff speed ε).differentiable
    (by norm_num)
  rw [fluxResidual_eq_quasilinearResidual (hflux _) (hdiff p), quasilinearResidual,
    partialDeriv_travelingWave (hv.contDiff.differentiable (by norm_num)),
    partialDeriv_time_profileCoordinate speed hε,
    partialDeriv_travelingWave (hv.contDiff.differentiable (by norm_num)),
    partialDeriv_space_profileCoordinate speed hε, map_smul,
    partialDeriv_space_twice_travelingWave hv.contDiff speed hε,
    hv.equation, ← smul_assoc, smul_eq_mul, mul_inv_cancel₀ hε, one_smul,
    smul_sub, ← smul_assoc, smul_eq_mul]
  rw [neg_div, div_eq_mul_inv, neg_smul, mul_comm speed ε⁻¹]
  abel

/-- Away from the moving interface the viscous family converges to the
planar shock. This includes time zero away from the spatial origin. -/
theorem IsViscousProfile.tendsto_travelingWave {flux : ℝ^m → ℝ^m} {uL uR : ℝ^m} {speed : ℝ}
    {v : ℝ → ℝ^m} (hv : IsViscousProfile flux uL uR speed v) {p : ℝ^2} (hp : p 1 ≠ speed * p 0) :
    Tendsto (fun ε : ℝ ↦ travelingWave v speed ε p) (𝓝[>] 0) (𝓝 (planarShock uL uR speed p)) := by
  rcases lt_or_gt_of_ne hp with hleft | hright
  · rw [planarShock_apply_of_mem hleft]
    apply hv.tendsto_atBot.comp
    simpa only [profileCoordinate, div_eq_mul_inv] using
      tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (sub_neg.mpr hleft)
  · rw [planarShock_apply_of_not_mem (not_lt_of_ge hright.le)]
    apply hv.tendsto_atTop.comp
    simpa only [profileCoordinate, div_eq_mul_inv] using
      tendsto_inv_nhdsGT_zero.const_mul_atTop (sub_pos.mpr hright)

end PDE.Hyperbolic.ConservationLaw.System
