/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Middle
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Gated.Spectrum
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Cutoff

import Mathlib.Analysis.Calculus.FDeriv.WithLp
import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval
import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Clock.Passage.Integrals
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.State
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Tangent components on the zero-delta upward gate

The trajectory uses the supplied middle and fast clocks and the scalar
solution with zero initial value. Its signed forcing is the same gate that has
terminal scalar value one. The upward equation, passage coverage, early support
margin, and fast-clock margins are conclusions supplied by the clock theorems.

If its first tangent coefficient vanished throughout the passage, scalar linear
uniqueness would force the scalar derivative, scalar solution, and gate to vanish.
The matched terminal value excludes this. The conclusion gives an open interval
with three nonzero coefficients in the normalized right eigenvectors.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Evolution PDE.Analysis.NormalizedPulse
open scoped BigOperators ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open MiddleClock

/-- A matched signed gate has an open upward interval where all three tangent
coefficients in the normalized right eigenvectors are nonzero.

`X` and `Z` are the supplied reference slices, and `tPlus` is their upward
passage map. In particular, the early hypothesis is a position bound, not a zero
scalar datum: the scalar datum at the passage is proved from support and its
initial value at time zero. The same `b`, `X`, and scalar solution occur in the
terminal match and in every component of the conclusion. -/
theorem exists_prescribed_clock_gate_tangent_components_ne_zero {X Z b tPlus : ℝ → ℝ} {T τ0 A B : ℝ}
    (hX : Continuous X) (hb : ContDiff ℝ ∞ b)
    (hbsupp : tsupport b ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hup : ∀ t ∈ Icc 1 T, HasDerivAt X (g (X t) + 1) t)
    (hgate : ∀ y ∈ Icc (205 : ℝ) (2051 / 10), tPlus y ∈ Ioo 1 T ∧ X (tPlus y) = y)
    (hearly : ∀ t ∈ Icc 0 (tPlus (41001 / 200)), X t < 20501 / 100)
    (hZ : ∀ t ∈ Icc 1 T, HasDerivAt Z (2 * Z t) t) (hZlower : ∀ t ∈ Icc 1 T, 1 + t ≤ Z t)
    (hZsq : ∀ t ∈ Ioo 1 T, Z t ^ 2 < A ^ 2) (hab : A ^ 2 < B ^ 2)
    (hmatch : scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0 τ0 = 1) :
    let ρ := scalarLinearSolution (fun _ : ℝ ↦ 4) (fun s ↦ b (X s)) 0 0
    let γ : ℝ → ℝ^3 := fun t ↦ !₂[Z t * ρ t, X t, Z t]
    let a : ℝ → Fin 3 → ℝ := fun t ↦
      ![Z t * ((b (X t) - 4 * ρ t) / 2 -
          deriv b (X t) * (g (X t) + 1) / (deriv g (X t) + 2)),
        g (X t) + 1, 2 * Z t]
    ∃ l u : ℝ, l < u ∧
      Ioo l u ⊆ Ioo (tPlus (41001 / 200)) (tPlus (2051 / 10)) ∧
      ∀ t ∈ Ioo l u,
        X t ∈ Ioo (205 : ℝ) (2051 / 10) ∧ 0 < Z t ∧
        a t 0 / Z t = deriv ρ t / 2 -
          deriv (fun s ↦ b (X s)) t / (deriv g (X t) + 2) ∧
        (∀ i : Fin 3, a t i ≠ 0) ∧
        HasDerivAt γ
          (GatedFlux.flux (fun s ↦ 2 * s) g cutoff (clockFeedback A B) b (γ t)) t ∧
        GatedFlux.flux (fun s ↦ 2 * s) g cutoff (clockFeedback A B) b (γ t) =
          ∑ i : Fin 3, a t i •
            GatedFlux.rightEigenvector (fun s ↦ 2 * s) g cutoff (clockFeedback A B) b
              (γ t) i := by
  classical
  intro ρ γ a
  let w : ℝ → ℝ := fun t ↦ b (X t) - 4 * ρ t
  let r : ℝ := tPlus (41001 / 200)
  let e : ℝ := tPlus (2051 / 10)
  have hρ (t : ℝ) : HasDerivAt ρ (w t) t :=
    hasDerivAt_scalarLinearSolution continuous_const (hb.continuous.comp hX) 0 0 t
  have hρcont : Continuous ρ := continuous_iff_continuousAt.mpr fun t ↦ (hρ t).continuousAt
  have hwcont : Continuous w := (hb.continuous.comp hX).sub (continuous_const.mul hρcont)
  have hgder : Continuous (deriv g) := contDiff_g.continuous_deriv (by simp)
  have hden (y : ℝ) : 0 < deriv g y + 2 := by linarith [(abs_le.mp (abs_deriv_g_le y)).1]
  have hmono := ClockSwitch.strictMonoOn_clock_upward hup
  obtain ⟨hrI, hrX⟩ := hgate (41001 / 200) (by constructor <;> norm_num)
  obtain ⟨heI, heX⟩ := hgate (2051 / 10) (by constructor <;> norm_num)
  have hrC : r ∈ Icc 1 T := ⟨hrI.1.le, hrI.2.le⟩
  have heC : e ∈ Icc 1 T := ⟨heI.1.le, heI.2.le⟩
  have hre : r < e := (hmono.lt_iff_lt hrC heC).mp (by rw [hrX, heX]; norm_num)
  have hr0 : 0 < r := zero_lt_one.trans hrI.1
  have hsub (t : ℝ) (ht : t ∈ Icc r e) : t ∈ Icc 1 T := ⟨hrC.1.trans ht.1, ht.2.trans heC.2⟩
  have hsubOpen (t : ℝ) (ht : t ∈ Ioo r e) : t ∈ Ioo 1 T := ⟨hrI.1.trans ht.1, ht.2.trans heI.2⟩
  have hZtwo (t : ℝ) (ht : t ∈ Ioo r e) : 2 < Z t := by
    linarith [hZlower t (hsub t ⟨ht.1.le, ht.2.le⟩), (hsubOpen t ht).1]
  have hbchain (t : ℝ) (ht : t ∈ Icc 1 T) :
      HasDerivAt (fun s ↦ b (X s)) (deriv b (X t) * (g (X t) + 1)) t :=
    ((hb.differentiable (by simp) (X t)).hasDerivAt).comp t (hup t ht)
  -- Zero data and the equation `ρ' = -κ ρ` keep the scalar solution at zero.
  have hstay {κ s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) (hs₀ : ρ s₀ = 0)
      (hd : ∀ s ∈ Ioo s₀ s₁, HasDerivAt ρ (-κ * ρ s + 0) s) : ρ s₁ = 0 := by
    simpa only [hs₀, scalarLinearSolution, mul_zero, intervalIntegral.integral_zero, add_zero]
      using eq_scalarLinearSolution_const_of_hasDerivAt (f := fun _ ↦ 0) hs hρcont.continuousOn
        continuousOn_const hd
  -- The scalar formula starts at zero. Before r, its signed forcing vanishes.
  have hbearly (t : ℝ) (ht : t ∈ Icc 0 r) : b (X t) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ lt_asymm (hearly t ht) (hbsupp h).1
  have hρr : ρ r = 0 := hstay (κ := 4) hr0.le (scalarLinearSolution_initial _ _ _ _)
    fun t ht ↦ by
      simpa only [w, hbearly t ⟨ht.1.le, ht.2.le⟩, zero_sub, add_zero, neg_mul] using hρ t
  have hwr : w r = 0 := by simp only [w, hbearly r ⟨hr0.le, le_rfl⟩, hρr, mul_zero, sub_zero]
  have hex : ∃ t ∈ Ioo r e, a t 0 ≠ 0 := by
    by_contra! ha0
    have hwode (t : ℝ) (ht : t ∈ Ioo r e) :
        HasDerivAt w ((deriv g (X t) / 2 - 3) * w t) t := by
      have hnorm : w t / 2 * (deriv g (X t) + 2) = deriv b (X t) * (g (X t) + 1) := by
        have := (mul_eq_zero.mp (ha0 t ht : Z t * _ = 0)).resolve_left
          (zero_lt_two.trans (hZtwo t ht)).ne'
        rwa [sub_eq_zero, eq_div_iff (hden (X t)).ne'] at this
      refine ((hbchain t (hsub t ⟨ht.1.le, ht.2.le⟩)).sub ((hρ t).const_mul 4)).congr_deriv ?_
      linear_combination -hnorm
    -- Apply the production linear uniqueness theorem with state space ℝ.
    let K : ℝ → ℝ →L[ℝ] ℝ := fun t ↦ (deriv g (X t) / 2 - 3) • (1 : ℝ →L[ℝ] ℝ)
    have hK : ContinuousOn K (Icc r e) :=
      ((((hgder.comp hX).div_const 2).sub continuous_const).smul continuous_const).continuousOn
    have hwzero : EqOn w (fun _ ↦ 0) (Icc r e) :=
      (fundamentalSolutionIcc hK ⟨r, ⟨le_rfl, hre.le⟩⟩).eqOn_of_hasDerivWithinAt
        (f := fun _ ↦ 0) hwcont.continuousOn continuousOn_const continuousOn_const
        (fun t ht ↦ by simpa only [K, smul_apply, one_apply_eq_self, smul_eq_mul, add_zero] using
          (hwode t ht).hasDerivWithinAt)
        (fun t _ ↦ by simpa only [map_zero, add_zero] using
          (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt) hwr
    have hρzero (t : ℝ) (ht : t ∈ Icc r e) : ρ t = 0 := hstay (κ := 0) ht.1 hρr fun s hs ↦ by
      simpa only [neg_zero, zero_mul, zero_add] using
        (hρ s).congr_deriv (hwzero ⟨hs.1.le, hs.2.le.trans ht.2⟩)
    have hballzero (y : ℝ) : b y = 0 := by
      by_contra hn
      have hy := hbsupp (subset_tsupport b hn)
      obtain ⟨htI, htX⟩ := hgate y ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have htC : tPlus y ∈ Icc 1 T := ⟨htI.1.le, htI.2.le⟩
      have hyre : tPlus y ∈ Icc r e :=
        ⟨(hmono.le_iff_le hrC htC).mp (by rw [hrX, htX]; linarith [hy.1]),
          (hmono.le_iff_le htC heC).mp (by rw [htX, heX]; linarith [hy.2])⟩
      have hw : b (X (tPlus y)) - 4 * ρ (tPlus y) = 0 := hwzero hyre
      rw [htX, hρzero _ hyre, mul_zero, sub_zero] at hw
      exact hn hw
    simp only [scalarLinearSolution, hballzero, mul_zero, intervalIntegral.integral_zero,
      add_zero, zero_ne_one] at hmatch
  obtain ⟨t0, ht0, ha0⟩ := hex
  have haCont : ContinuousAt (fun t ↦ a t 0) t0 := by
    have hZc := (hZ t0 (hsub t0 ⟨ht0.1.le, ht0.2.le⟩)).continuousAt
    have hbd : Continuous (deriv b) := hb.continuous_deriv (by simp)
    have := hb.continuous
    have := contDiff_g.continuous
    simp only [a, Matrix.cons_val_zero]
    fun_prop (disch := exact (hden _).ne')
  obtain ⟨l, u, ht0lu, hlu⟩ := (Filter.Eventually.and (Ioo_mem_nhds ht0.1 ht0.2)
    (haCont.eventually_ne ha0)).exists_Ioo_subset
  refine ⟨l, u, ht0lu.1.trans ht0lu.2, fun t ht ↦ (hlu ht).1, fun t htlu ↦ ?_⟩
  obtain ⟨ht, ha0t⟩ := hlu htlu
  have htC := hsub t ⟨ht.1.le, ht.2.le⟩
  have hztwo := hZtwo t ht
  have hzt : 0 < Z t := zero_lt_two.trans hztwo
  have hXt : X t ∈ Ioo (205 : ℝ) (2051 / 10) :=
    ⟨(by norm_num : (205 : ℝ) < 41001 / 200).trans (hrX ▸ hmono hrC htC ht.1),
      heX ▸ hmono htC heC ht.2⟩
  obtain ⟨hflux, hv0, hv1, hv2, -⟩ := concreteGatedFlux_upward_gate_state
    (q := γ t) hab (hb.differentiable (by simp) (X t))
    (hbsupp.trans (Ioo_subset_Ioo (by norm_num) (by norm_num))) hXt.1 hztwo (hZsq t (hsubOpen t ht))
  have hfast : PDE.Analysis.fastLogCosh 0 = (fun s : ℝ ↦ 2 * s) := funext fun s ↦ by
    simp only [PDE.Analysis.fastLogCosh, zero_mul, add_zero]
  simp only [concreteGatedFlux, hfast] at hflux hv0 hv1 hv2
  dsimp only [γ] at hflux hv0 hv1 hv2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at hflux hv1 hv2
  have hcoordinates : HasDerivAt (fun s ↦ ![Z s * ρ s, X s, Z s])
      ![2 * Z t * ρ t + Z t * w t, g (X t) + 1, 2 * Z t] t := hasDerivAt_pi.mpr fun i ↦ by
    fin_cases i
    exacts [(hZ t htC).fun_mul (hρ t), hup t htC, hZ t htC]
  have hγ : HasDerivAt γ (!₂[2 * Z t * ρ t + Z t * w t, g (X t) + 1, 2 * Z t] : ℝ^3) t :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hcoordinates
  refine ⟨hXt, hzt, ?_, fun i ↦ ?_, hγ.congr_deriv ?_, ?_⟩
  · rw [(hρ t).deriv, (hbchain t htC).deriv]
    change Z t * _ / Z t = _
    exact mul_div_cancel_left₀ _ hzt.ne'
  · fin_cases i
    exacts [ha0t, (by linarith [g_nonneg (X t)] : (0 : ℝ) < g (X t) + 1).ne',
      (mul_pos two_pos hzt).ne']
  · rw [hflux]
    ext i
    fin_cases i
    · simp only [w, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, neg_mul]
      ring
    all_goals rfl
  · rw [hflux, Fin.sum_univ_three, hv0, hv1, hv2]
    ext i
    fin_cases i
    · simp only [a, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul, mul_one]
      ring
    all_goals simp [a]

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
