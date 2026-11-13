/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.DifferenceEnergy
public import Mathlib.Analysis.ODE.Gronwall
import PDE.Analysis.ODE.SmoothDependence
import CAS.ExactTactic

/-!
# Short-time contraction estimate for frozen De Gregorio transport

Two frozen transport outputs with the same initial trace satisfy a Grönwall
estimate in terms of the input L² difference. The coefficient tends to zero
with the length of the time interval. The differential inequality is
`norm_deriv_frozen_differenceEnergy_le`, obtained from the PDEs and concrete Hilbert
pairs.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- The squared L² output difference is bounded by a time-dependent multiple
of a uniform squared L² input difference bound. The output velocities are the
Biot–Savart velocities of the inputs `f` and `g`. -/
theorem differenceEnergy_le_gronwallBound_of_frozen_transport
    {fields other : Fields} {f g : ℝ → ℝ → ℝ} {L C M t₀ T : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hpde : SatisfiesTransportEquationOn 1 fields (Icc t₀ T))
    (hother : SatisfiesTransportEquationOn 1 other (Icc t₀ T))
    (hpair : ∀ t ∈ Icc t₀ T, IsHilbertPair (fun x ↦ f x t)
      (deriv (fun x ↦ fields.velocity x t)))
    (hpairOther : ∀ t ∈ Icc t₀ T, IsHilbertPair (fun x ↦ g x t)
      (deriv (fun x ↦ other.velocity x t)))
    (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hboundary : ∀ t ∈ Icc t₀ T,
      fields.vorticity (-L) t = other.vorticity (-L) t ∧
        fields.vorticity L t = other.vorticity L t)
    (hzero : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ t ∈ Icc t₀ T, ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀)
    (hinput : ∀ t ∈ Icc t₀ T, (∫ x, (f x t - g x t) ^ 2) ≤ M) :
    ∀ t ∈ Icc t₀ T, differenceEnergy fields other L t ≤
      M * gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) (t - t₀) := by
  have hdiff : Differentiable ℝ (differenceEnergy fields other L) :=
    fun t ↦ (hasDerivAt_differenceEnergy hf hg L t).differentiableAt
  have hinitialEnergy : differenceEnergy fields other L t₀ = 0 := by
    simp only [differenceEnergy, hinitial, sub_self, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
  have hestimate := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := differenceEnergy fields other L) (f' := deriv (differenceEnergy fields other L))
    (δ := 0) (K := 5 * C) (ε := C * (1 + 2 * L ^ 2) * M)
    (a := t₀) (b := T)
    hdiff.continuous.continuousOn
    (fun t _ ↦ (hdiff t).hasDerivAt.hasDerivWithinAt)
    (by simp only [hinitialEnergy, norm_zero, le_refl])
    (by
      intro t ht
      have htc : t ∈ Icc t₀ T := ⟨ht.1, ht.2.le⟩
      rw [Real.norm_eq_abs (differenceEnergy fields other L t),
        abs_of_nonneg (differenceEnergy_nonneg fields other L t)]
      calc
        _ ≤ C * (5 * differenceEnergy fields other L t +
            (1 + 2 * L ^ 2) * ∫ x, (f x t - g x t) ^ 2) :=
          norm_deriv_frozen_differenceEnergy_le hf hg hu hv hpde hother htc
            (hpair t htc) (hpairOther t htc) hL hC
            (hboundary t htc).1 (hboundary t htc).2 (hzero t htc) (hbound t htc)
        _ ≤ C * (5 * differenceEnergy fields other L t + (1 + 2 * L ^ 2) * M) := by
          gcongr
          exact hinput t htc
        _ = _ := by cas)
  intro t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (differenceEnergy_nonneg fields other L t),
    ODE.gronwallBound_zero_mul] using hestimate t ht

/-- For fixed coefficient and support bounds, the frozen-transport energy
factor is at most one half on a positive time interval. The interval depends
only on these two bounds, not on the input difference. -/
theorem exists_pos_frozen_transport_factor_le_half (L C : ℝ) :
    ∃ δ > 0, ∀ t ∈ Icc 0 δ,
      gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) t ≤ 1 / 2 := by
  let q := gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2))
  have hq : ContinuousAt q 0 :=
    (hasDerivAt_gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) 0).continuousAt
  have hzero : q 0 = 0 := gronwallBound_x0 _ _ _
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), q t < 1 / 2 :=
    hq.eventually (Iio_mem_nhds (by rw [hzero]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ε / 2, by positivity, ?_⟩
  intro t ht
  apply (hball ?_).le
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact ht.2.trans_lt (by cas using hε)

/-- Once the explicit time factor is at most one half at the right endpoint,
the frozen transport outputs contract throughout the closed interval. -/
theorem differenceEnergy_le_half_of_frozen_transport
    {fields other : Fields} {f g : ℝ → ℝ → ℝ} {L C M t₀ T : ℝ}
    (hf : ContDiff ℝ 1 (Function.uncurry fields.vorticity))
    (hg : ContDiff ℝ 1 (Function.uncurry other.vorticity))
    (hu : ContDiff ℝ 1 (Function.uncurry fields.velocity))
    (hv : ContDiff ℝ 1 (Function.uncurry other.velocity))
    (hpde : SatisfiesTransportEquationOn 1 fields (Icc t₀ T))
    (hother : SatisfiesTransportEquationOn 1 other (Icc t₀ T))
    (hpair : ∀ t ∈ Icc t₀ T, IsHilbertPair (fun x ↦ f x t)
      (deriv (fun x ↦ fields.velocity x t)))
    (hpairOther : ∀ t ∈ Icc t₀ T, IsHilbertPair (fun x ↦ g x t)
      (deriv (fun x ↦ other.velocity x t)))
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hboundary : ∀ t ∈ Icc t₀ T,
      fields.vorticity (-L) t = other.vorticity (-L) t ∧
        fields.vorticity L t = other.vorticity L t)
    (hzero : ∀ t ∈ Icc t₀ T, fields.velocity 0 t = other.velocity 0 t)
    (hbound : ∀ t ∈ Icc t₀ T, ∀ x ∈ Icc (-L) L,
      |deriv (fun y ↦ fields.velocity y t) x| ≤ C ∧
        |other.vorticity x t| ≤ C ∧
          |deriv (fun y ↦ other.vorticity y t) x| ≤ C)
    (hinitial : ∀ x, fields.vorticity x t₀ = other.vorticity x t₀)
    (hinput : ∀ t ∈ Icc t₀ T, (∫ x, (f x t - g x t) ^ 2) ≤ M)
    (hsmall : gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) (T - t₀) ≤ 1 / 2) :
    ∀ t ∈ Icc t₀ T, differenceEnergy fields other L t ≤ M / 2 := by
  intro t ht
  calc
    _ ≤ M * gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) (t - t₀) :=
      differenceEnergy_le_gronwallBound_of_frozen_transport hf hg hu hv hpde hother
        hpair hpairOther hL hC hboundary hzero hbound hinitial hinput t ht
    _ ≤ M * gronwallBound 0 (5 * C) (C * (1 + 2 * L ^ 2)) (T - t₀) :=
      mul_le_mul_of_nonneg_left
        (gronwallBound_mono (by norm_num) (by positivity) (by positivity)
          (sub_le_sub_right ht.2 t₀)) hM
    _ ≤ M * (1 / 2) := mul_le_mul_of_nonneg_left hsmall hM
    _ = _ := by cas

end DeGregorio
