/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Layercake
public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import CAS.ExactTactic

/-!
# Integral bounds from inverse-square envelopes

Layer cake converts linear sublevel growth into an integral estimate. A separate
ceiling or square-energy estimate controls the singular part of the envelope.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- A square-root tail bound and a finite ceiling control a nonnegative integral. -/
theorem integral_le_of_sqrt_distribution_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {B K : ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) (hB : 0 ≤ B)
    (hbound : f ≤ᵐ[μ] fun _ ↦ B)
    (htail : ∀ s ∈ Ioc 0 B, μ.real {x | s ≤ f x} ≤ K * s ^ (-(1 / 2 : ℝ))) :
    (∫ x, f x ∂μ) ≤ 2 * K * Real.sqrt B := by
  rw [hf.integral_eq_integral_Ioc_meas_le hpos hbound]
  have hi : IntegrableOn (fun s : ℝ ↦ K * s ^ (-(1 / 2 : ℝ))) (Ioc 0 B) :=
    ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := B)
      (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul K).1
  calc
    (∫ s in Ioc 0 B, μ.real {x | s ≤ f x}) ≤
        ∫ s in Ioc 0 B, K * s ^ (-(1 / 2 : ℝ)) := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ measureReal_nonneg) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact htail s hs
    _ = 2 * K * Real.sqrt B := by
      rw [← intervalIntegral.integral_of_le hB, intervalIntegral.integral_const_mul]
      have hpow : (∫ s in (0 : ℝ)..B, s ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt B := by
        -- The integrable singularity at zero uses Mathlib's improper power integral.
        rw [integral_rpow (Or.inl (by norm_num)), Real.sqrt_eq_rpow]
        norm_num
        cas
      rw [hpow]
      cas

/-- A function bounded by an inverse-square profile has a square-root
integral bound when the profile's sublevel sets have linear measure growth. -/
theorem integral_le_of_inverse_sq_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f ρ : α → ℝ} {A B D : ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) (hB : 0 ≤ B)
    (hbound : f ≤ᵐ[μ] fun _ ↦ B) (hD : 0 < D)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ᵐ x ∂μ, f x ≤ D / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r) :
    (∫ x, f x ∂μ) ≤ 2 * A * Real.sqrt D * Real.sqrt B := by
  have htail (s : ℝ) (hs : s ∈ Ioc 0 B) :
      μ.real {x | s ≤ f x} ≤ (A * Real.sqrt D) * s ^ (-(1 / 2 : ℝ)) := by
    have hsub : ∀ᵐ x ∂μ, x ∈ {x | s ≤ f x} →
        x ∈ {x | ρ x ≤ Real.sqrt (D / s)} := by
      filter_upwards [hρ, henv] with x hx he hxlev
      apply Real.le_sqrt_of_sq_le
      apply (le_div_iff₀ hs.1).mpr
      have h := (le_div_iff₀ (sq_pos_of_pos hx)).mp (hxlev.trans he)
      simpa only [mul_comm] using h
    calc
      μ.real {x | s ≤ f x} ≤ μ.real {x | ρ x ≤ Real.sqrt (D / s)} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
      _ ≤ A * Real.sqrt (D / s) :=
        hlayer _ (Real.sqrt_pos.mpr (div_pos hD hs.1))
      _ = (A * Real.sqrt D) * s ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_div hD.le, Real.rpow_neg hs.1.le, ← Real.sqrt_eq_rpow]
        simp only [div_eq_mul_inv, mul_assoc]
  simpa only [mul_assoc] using integral_le_of_sqrt_distribution_bound
    hf hpos hB hbound htail

/-- The inverse-square profile controls the integral outside a sublevel set. -/
theorem setIntegral_le_of_inverse_sq_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f ρ : α → ℝ} {A D R : ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) (hD : 0 < D) (hR : 0 < R)
    (hρmeas : Measurable ρ) (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ᵐ x ∂μ, f x ≤ D / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r) :
    (∫ x in {x | R ≤ ρ x}, f x ∂μ) ≤ 2 * A * D / R := by
  have hs : MeasurableSet {x | R ≤ ρ x} := measurableSet_le measurable_const hρmeas
  have hbound : ∀ᵐ x ∂μ.restrict {x | R ≤ ρ x}, f x ≤ D / R ^ 2 := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae henv] with x hx he
    exact he.trans (div_le_div_of_nonneg_left hD.le (sq_pos_of_pos hR)
      ((sq_le_sq₀ hR.le (hR.le.trans hx)).mpr hx))
  have hgrowth (r : ℝ) (hr : 0 < r) :
      (μ.restrict {x | R ≤ ρ x}).real {x | ρ x ≤ r} ≤ A * r :=
    (ENNReal.toReal_mono (measure_ne_top _ _)
      (Measure.restrict_apply_le _ _)).trans (hlayer r hr)
  have h := integral_le_of_inverse_sq_bound hf.integrableOn
    (ae_restrict_of_ae hpos) (div_nonneg hD.le (sq_nonneg R)) hbound hD
    (ae_restrict_of_ae hρ) (ae_restrict_of_ae henv) hgrowth
  calc
    (∫ x in {x | R ≤ ρ x}, f x ∂μ) ≤ 2 * A * Real.sqrt D * Real.sqrt (D / R ^ 2) := h
    _ = 2 * A * D / R := by
      rw [Real.sqrt_div hD.le, Real.sqrt_sq hR.le]
      cas using [hD, hR]

/-- Splitting into a sublevel set and its complement combines the square
energy near the boundary with the inverse-square tail away from it. -/
theorem integral_le_sqrt_energy_add_inverse_sq_tail
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f ρ : α → ℝ} {A D R : ℝ}
    (hf : MemLp f 2 μ) (hpos : 0 ≤ᵐ[μ] f) (hD : 0 < D) (hR : 0 < R)
    (hρmeas : Measurable ρ) (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ᵐ x ∂μ, f x ≤ D / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r) :
    (∫ x, f x ∂μ) ≤ Real.sqrt (A * R) * Real.sqrt (∫ x, f x ^ 2 ∂μ) +
      2 * A * D / R := by
  let s : Set α := {x | R ≤ ρ x}
  have hs : MeasurableSet s := measurableSet_le measurable_const hρmeas
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have htail := setIntegral_le_of_inverse_sq_bound hi hpos hD hR hρmeas hρ henv hlayer
  have hmeasure : μ.real sᶜ ≤ A * R := by
    have hsub : sᶜ ⊆ {x | ρ x ≤ R} := by
      intro x hx
      change ¬ R ≤ ρ x at hx
      exact (lt_of_not_ge hx).le
    exact (measureReal_mono (μ := μ) hsub).trans (hlayer R hR)
  have hsq : (∫ x in sᶜ, f x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ :=
    setIntegral_le_integral hf.integrable_sq (Eventually.of_forall fun x ↦ sq_nonneg (f x))
  have hcauchy := integral_abs_mul_le_sqrt_integral_sq
    (memLp_const (1 : ℝ) : MemLp (fun _ : α ↦ (1 : ℝ)) 2 (μ.restrict sᶜ))
    (hf.restrict sᶜ)
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one,
    measureReal_restrict_apply_univ] at hcauchy
  have hcore : (∫ x in sᶜ, f x ∂μ) ≤
      Real.sqrt (A * R) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    calc
      (∫ x in sᶜ, f x ∂μ) ≤ ∫ x in sᶜ, |f x| ∂μ :=
        (le_abs_self _).trans abs_integral_le_integral_abs
      _ ≤ Real.sqrt (μ.real sᶜ) * Real.sqrt (∫ x in sᶜ, f x ^ 2 ∂μ) := hcauchy
      _ ≤ Real.sqrt (A * R) * Real.sqrt (∫ x, f x ^ 2 ∂μ) :=
        mul_le_mul (Real.sqrt_le_sqrt hmeasure) (Real.sqrt_le_sqrt hsq)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← integral_add_compl hs hi]
  change (∫ x in s, f x ∂μ) + (∫ x in sᶜ, f x ∂μ) ≤ _
  linarith only [htail, hcore]

/-- An inverse-square envelope whose coefficient is proportional to time gives
vanishing mass whenever time times the square energy tends to zero. -/
theorem tendsto_integral_zero_of_inverse_sq_bound
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {l : Filter ι} {f : ι → α → ℝ} {τ : ι → ℝ} {ρ : α → ℝ} {A C : ℝ}
    (hA : 0 ≤ A) (hC : 0 < C) (hτ : ∀ i, 0 < τ i)
    (hf : ∀ i, MemLp (f i) 2 μ) (hpos : ∀ i, 0 ≤ᵐ[μ] f i)
    (hρmeas : Measurable ρ) (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ i, ∀ᵐ x ∂μ, f i x ≤ C * τ i / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r)
    (henergy : Tendsto (fun i ↦ τ i * ∫ x, f i x ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, f i x ∂μ) l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall fun i ↦ hb.trans_le (integral_nonneg_of_ae (hpos i))
  · intro b hb
    have htail : Tendsto (fun h : ℝ ↦ 2 * A * C / h) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    obtain ⟨h, hh, hsmall⟩ :=
      ((eventually_gt_atTop (0 : ℝ)).and (htail.eventually (gt_mem_nhds hb))).exists
    have hbound (i : ι) : (∫ x, f i x ∂μ) ≤
        Real.sqrt (A * h) * Real.sqrt (τ i * ∫ x, f i x ^ 2 ∂μ) +
          2 * A * C / h := by
      have hi := integral_le_sqrt_energy_add_inverse_sq_tail (hf i) (hpos i)
        (mul_pos hC (hτ i)) (mul_pos hh (hτ i)) hρmeas hρ (henv i) hlayer
      have hcore : Real.sqrt (A * (h * τ i)) * Real.sqrt (∫ x, f i x ^ 2 ∂μ) =
          Real.sqrt (A * h) * Real.sqrt (τ i * ∫ x, f i x ^ 2 ∂μ) := by
        rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hA hh.le),
          Real.sqrt_mul (hτ i).le, mul_assoc]
      have htail' : 2 * A * (C * τ i) / (h * τ i) = 2 * A * C / h := by
        cas using [hh, hτ i]
      rwa [hcore, htail'] at hi
    have hlim : Tendsto (fun i ↦
        Real.sqrt (A * h) * Real.sqrt (τ i * ∫ x, f i x ^ 2 ∂μ) +
          2 * A * C / h) l (𝓝 (2 * A * C / h)) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).comp henergy).const_mul
        (Real.sqrt (A * h)) |>.add_const (2 * A * C / h)
    filter_upwards [hlim.eventually (gt_mem_nhds hsmall)] with i hi
    exact (hbound i).trans_lt hi

/-- Combining a reciprocal-time ceiling and a time-scaled inverse-square
profile gives a bound independent of time. -/
theorem integral_le_of_time_inverse_sq_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f ρ : α → ℝ} {A C t : ℝ}
    (hf : Integrable f μ) (hpos : 0 ≤ᵐ[μ] f) (hC : 0 < C) (ht : 0 < t)
    (hbound : f ≤ᵐ[μ] fun _ ↦ 1 / t)
    (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ᵐ x ∂μ, f x ≤ C * t / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r) :
    (∫ x, f x ∂μ) ≤ 2 * A * Real.sqrt C := by
  have h := integral_le_of_inverse_sq_bound hf hpos (by positivity) hbound
    (mul_pos hC ht) hρ henv hlayer
  calc
    (∫ x, f x ∂μ) ≤ 2 * A * Real.sqrt (C * t) * Real.sqrt (1 / t) := h
    _ = 2 * A * Real.sqrt C := by
      rw [Real.sqrt_mul hC.le, Real.sqrt_div zero_le_one, Real.sqrt_one]
      cas using [Real.sqrt_pos.mpr ht]

end MeasureTheory
