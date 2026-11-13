/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Local.Existence
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Regularity
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.TravelingWave
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.Shock
import PDE.Hyperbolic.ConservationLaw.System.PSystem.WaveGeometry
import CAS.ExactTactic

/-!
# Exponential elasticity profiles

The stress law `p(v) = exp v` gives the globally strictly hyperbolic,
genuinely nonlinear system with flux `(-w,-exp v)`. The left state `(0,1)`
is nonzero. Every sufficiently small positive strain jump on its negative
Hugoniot branch has a complete viscous profile
(`exists_viscousProfile_positive_strain`, from `exists_small_viscousProfile_iff_lax`).
Stretching that profile solves the conservative viscous PDE at every
positive viscosity.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology
open PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.System

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.ViscousProfile.ExponentialPSystem

private theorem positive_stress_derivative (x : ℝ) : 0 < deriv Real.exp x := by
  simpa only [Real.deriv_exp] using Real.exp_pos x

private theorem positive_stress_second_derivative (x : ℝ) :
    0 < deriv (deriv Real.exp) x := by
  simpa only [Real.deriv_exp] using Real.exp_pos x

private theorem hyperbolic (q : ℝ^2) :
    IsStrictlyHyperbolicAt (PSystem.flux Real.exp) q :=
  PSystem.isStrictlyHyperbolicAt Real.differentiableAt_exp
    (positive_stress_derivative (q 0))

private theorem canonical_speed (k : Fin 2) :
    (PSystem.characteristicField Real.exp Real.differentiable_exp
      positive_stress_derivative k).speed =
      characteristicSpeed (PSystem.flux Real.exp) k := by
  funext q
  let c := √(deriv Real.exp (q 0))
  have hc : 0 < c := Real.sqrt_pos.mpr (positive_stress_derivative (q 0))
  have horder : StrictMono (PSystem.characteristicSpeed c) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [PSystem.characteristicSpeed] at hij ⊢
    linarith
  symm
  exact congrFun (characteristicSpeed_eq_of_eigenbasis
    (PSystem.eigenbasis c hc) horder
    (fun i ↦ by
      rw [PSystem.eigenbasis_apply]
      exact (PSystem.hasEigenvector_fderiv_flux Real.differentiableAt_exp
        (positive_stress_derivative (q 0)).le i).apply_eq_smul)) k

private theorem genuinely_nonlinear (k : Fin 2) :
    IsGenuinelyNonlinearFamily (PSystem.flux Real.exp) k :=
  (isGenuinelyNonlinearFamily_iff hyperbolic k
    (PSystem.characteristicField Real.exp Real.differentiable_exp
      positive_stress_derivative k) (canonical_speed k)).mpr
    (PSystem.isGenuinelyNonlinear_characteristicField Real.contDiff_exp
      positive_stress_derivative
      (fun x ↦ (positive_stress_second_derivative x).ne') k)

/-- The flux at the left state `(0, 1)` is `(-1, -1)`. -/
theorem flux_at_left :
    PSystem.flux Real.exp (!₂[0, 1] : ℝ^2) = !₂[-1, -1] := by
  ext i
  fin_cases i <;> norm_num [PSystem.flux]

/-- The right state on the Hugoniot branch with strain increment `d` is `(d, 1 - σ d)`,
with `σ` the shock speed. -/
theorem shockState_formula (d : ℝ) :
    PSystem.shockState Real.exp 0 (!₂[0, 1] : ℝ^2) d =
      !₂[d, 1 - PSystem.shockSpeed Real.exp 0 0 d * d] := by
  ext i
  fin_cases i
  · rfl
  · change 1 - PSystem.shockSpeed Real.exp 0 0 d * (d - 0) =
      1 - PSystem.shockSpeed Real.exp 0 0 d * d
    cas

/-- For small strain increments `d > 0`, the shock from `(0, 1)` on the Hugoniot branch
has a smooth viscous profile. Its traveling waves solve the viscous system for every
`ε > 0` and converge to the shock as `ε → 0⁺`. -/
theorem exists_viscousProfile_positive_strain :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d ∈ Ioo 0 d₀,
      ∃ v : ℝ → ℝ^2,
        IsViscousProfile (PSystem.flux Real.exp) (!₂[0, 1])
          (PSystem.shockState Real.exp 0 (!₂[0, 1]) d)
          (PSystem.shockSpeed Real.exp 0 0 d) v ∧
        ContDiff ℝ ∞ v ∧
        (∀ ε : ℝ, 0 < ε → ∀ p : ℝ^2,
          fluxResidual (PSystem.flux Real.exp)
              (travelingWave v (PSystem.shockSpeed Real.exp 0 0 d) ε) p =
            ε • (∂[1]
              (∂[1]
                (travelingWave v (PSystem.shockSpeed Real.exp 0 0 d) ε))) p) ∧
        ∀ p : ℝ^2, p 1 ≠ PSystem.shockSpeed Real.exp 0 0 d * p 0 →
          Tendsto (fun ε : ℝ ↦ travelingWave v (PSystem.shockSpeed Real.exp 0 0 d) ε p)
            (𝓝[>] 0) (𝓝 (planarShock (!₂[0, 1])
              (PSystem.shockState Real.exp 0 (!₂[0, 1]) d)
              (PSystem.shockSpeed Real.exp 0 0 d) p)) := by
  let q : ℝ^2 := !₂[0, 1]
  have hf : ContDiff ℝ ∞ (PSystem.flux Real.exp) :=
    PSystem.contDiff_flux Real.contDiff_exp
  obtain ⟨δ, ρ, hδ, _hδρ, hprofile⟩ :=
    exists_small_viscousProfile_iff_lax hf hyperbolic genuinely_nonlinear q
  have hstate : ContinuousAt (PSystem.shockState Real.exp 0 q) 0 := by
    have h : ContDiff ℝ 1 (PSystem.shockState Real.exp 0 q) := by
      simpa only [show q 0 = 0 from rfl, zero_add, Function.comp_def, id_eq] using
        (PSystem.contDiff_shockState_strength Real.contDiff_exp
          positive_stress_derivative 0).comp
          (contDiff_id.prodMk contDiff_const : ContDiff ℝ 1 (fun d : ℝ ↦ (d, q)))
    exact h.continuous.continuousAt
  have hq : PSystem.shockState Real.exp 0 q 0 = q := by
    exact PSystem.shockState_left_strain Real.exp 0 q
  have hnear : ∀ᶠ d in 𝓝 0, PSystem.shockState Real.exp 0 q d ∈ ball q δ :=
    hstate (hq.symm ▸ isOpen_ball.mem_nhds (mem_ball_self hδ))
  obtain ⟨d₀, hd₀, hsmall⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨d₀, hd₀, ?_⟩
  intro d hd
  have hdmem : d ∈ ball (0 : ℝ) d₀ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hd.1] using hd.2
  have hne : PSystem.shockState Real.exp 0 q d ≠ q := by
    intro heq
    have hzero := congrArg (fun u : ℝ^2 ↦ u 0) heq
    change d = 0 at hzero
    exact hd.1.ne' hzero
  have hLax := PSystem.laxShock_shockState_zero_of_left_lt_right Real.contDiff_exp
    positive_stress_derivative positive_stress_second_derivative q
    (show q 0 < d from hd.1)
  have hcanonical := congrFun (canonical_speed 0)
  obtain ⟨v, hv, _hvrange⟩ :=
    (hprofile _ (hsmall hdmem) hne (PSystem.shockSpeed Real.exp 0 0 d)).mpr
      ⟨hLax.1, 0, by
        rw [← hcanonical _]
        exact hLax.2.1, by
        rw [← hcanonical q]
        exact hLax.2.2.1⟩
  exact ⟨v, hv, hv.contDiff_infty hf, (fun ε hε p ↦
    hv.fluxResidual_travelingWave (hf.differentiable (by simp)) hε.ne' p),
    fun _ hp ↦ hv.tendsto_travelingWave hp⟩

end PDE.Examples.Hyperbolic.ConservationLaw.System.ViscousProfile.ExponentialPSystem
