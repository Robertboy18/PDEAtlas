/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.InverseSquareBounds
public import PDE.Analysis.MeasureTheory.Integral.NonnegativeLimit
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Signed initial integral bounds along good times

Time integrability gives a sequence approaching zero along which time times
the energy vanishes. An inverse-square envelope then removes the negative part,
and Fatou proves integrability of the nonnegative limit with the same bound.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace MeasureTheory

/-- Integrability near zero gives arbitrarily small times with small
`t * ‖f t‖`. No pointwise boundedness of the integrable function is assumed. -/
theorem exists_pos_mul_norm_lt_of_integrableOn_Ioo
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T ε δ : ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) (hT : 0 < T) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ t ∈ Ioo 0 (min δ T), t * ‖f t‖ < ε := by
  by_contra! h
  have hr : 0 < min δ T := lt_min hδ hT
  have hf' : IntegrableOn (fun t ↦ ε⁻¹ * ‖f t‖) (Ioo 0 (min δ T)) :=
    IntegrableOn.mono_set (hf.norm.const_mul ε⁻¹)
      (Ioo_subset_Ioo le_rfl (min_le_right _ _))
  have hi : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Ioo 0 (min δ T)) := by
    apply hf'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht.1)]
    have htbound : ε / t ≤ ‖f t‖ := (div_le_iff₀ ht.1).mpr (by
      simpa only [mul_comm] using h t ht)
    have hm := mul_le_mul_of_nonneg_left htbound (inv_pos.mpr hε).le
    simpa only [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] using hm
  have hi' : IntegrableOn (fun t : ℝ ↦ t ^ (-1 : ℝ)) (Ioo 0 (min δ T)) := by
    simpa only [Real.rpow_neg_one] using hi
  exact (lt_irrefl (-1 : ℝ)) ((intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp hi')

/-- Along a sequence approaching an integrable endpoint, the product of time
and the norm of the integrand tends to zero. -/
theorem exists_seq_tendsto_zero_mul_norm_of_integrableOn_Ioo
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {T : ℝ}
    (hf : IntegrableOn f (Ioo 0 T)) (hT : 0 < T) :
    ∃ t : ℕ → ℝ, (∀ k, t k ∈ Ioo 0 T) ∧ Tendsto t atTop (𝓝 0) ∧
      Tendsto (fun k ↦ t k * ‖f (t k)‖) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have halim : Tendsto a atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht (k : ℕ) : ∃ t ∈ Ioo 0 (min (a k) T), t * ‖f t‖ < a k :=
    exists_pos_mul_norm_lt_of_integrableOn_Ioo hf hT (ha k) (ha k)
  choose t ht hsmall using ht
  refine ⟨t, fun k ↦ ⟨(ht k).1, (ht k).2.trans_le (min_le_right _ _)⟩, ?_, ?_⟩
  · exact squeeze_zero (fun k ↦ (ht k).1.le)
      (fun k ↦ (ht k).2.le.trans (min_le_left _ _)) halim
  · exact squeeze_zero (fun k ↦ mul_nonneg (ht k).1.le (norm_nonneg _))
      (fun k ↦ (hsmall k).le) halim

/-- Vanishing negative mass lets an eventual signed integral bound pass to a
nonnegative almost-everywhere limit, and proves that limit integrable. -/
theorem integrable_and_integral_le_of_tendsto_neg_part_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {G : α → ℝ} {C : ℝ}
    (hF : ∀ i, Integrable (F i) μ)
    (hG : ∀ᵐ x ∂μ, 0 ≤ G x)
    (hb : ∀ᶠ i in atTop, (∫ x, F i x ∂μ) ≤ C)
    (hneg : Tendsto (fun i ↦ ∫ x, max (-F i x) 0 ∂μ) atTop (𝓝 0))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop (𝓝 (G x))) :
    Integrable G μ ∧ (∫ x, G x ∂μ) ≤ C := by
  have hid (i : ℕ) : (fun x ↦ max (F i x) 0) =
      fun x ↦ F i x + max (-F i x) 0 := by
    funext x
    by_cases hx : 0 ≤ F i x
    · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero]
    · have hx' : F i x ≤ 0 := (lt_of_not_ge hx).le
      simp only [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), add_neg_cancel]
  have hi (i : ℕ) : (∫ x, max (F i x) 0 ∂μ) =
      (∫ x, F i x ∂μ) + ∫ x, max (-F i x) 0 ∂μ := by
    rw [hid, integral_add (hF i) (hF i).neg_part]
  have hε (ε : ℝ) (hε : 0 < ε) :
      Integrable G μ ∧ (∫ x, G x ∂μ) ≤ C + ε := by
    apply integrable_and_integral_le_of_nonnegative_limit
      (fun i ↦ (hF i).pos_part) (fun _ ↦ Eventually.of_forall fun x ↦ le_max_right _ _)
    · filter_upwards [hb, hneg.eventually (gt_mem_nhds hε)] with i hbi hni
      rw [hi]
      exact add_le_add hbi hni.le
    · filter_upwards [hG, hlim] with x hx hxl
      simpa only [max_eq_left hx] using hxl.max (tendsto_const_nhds (x := (0 : ℝ)))
  refine ⟨(hε 1 zero_lt_one).1, ?_⟩
  by_contra h
  have hlt : C < ∫ x, G x ∂μ := lt_of_not_ge h
  obtain ⟨D, hCD, hD⟩ := exists_between hlt
  have hbound := (hε (D - C) (sub_pos.mpr hCD)).2
  linarith

/-- A time-integrable square energy and an inverse-square bound on the negative
part remove a signed defect in a nonnegative initial trace. The initial datum
is proved integrable. The sublevel estimate is an explicit geometric input. -/
theorem integrable_and_integral_le_of_inverse_sq_neg_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : ℝ → α → ℝ} {g ρ : α → ℝ} {A C M T : ℝ}
    (hA : 0 ≤ A) (hC : 0 < C) (hT : 0 < T)
    (hu : ∀ t ∈ Ioo 0 T, MemLp (u t) 2 μ)
    (hρmeas : Measurable ρ) (hρ : ∀ᵐ x ∂μ, 0 < ρ x)
    (henv : ∀ t ∈ Ioo 0 T, ∀ᵐ x ∂μ, -u t x ≤ C * t / ρ x ^ 2)
    (hlayer : ∀ r > 0, μ.real {x | ρ x ≤ r} ≤ A * r)
    (henergy : IntegrableOn (fun t ↦ ∫ x, u t x ^ 2 ∂μ) (Ioo 0 T))
    (hmoment : ∀ t ∈ Ioo 0 T, (∫ x, u t x ∂μ) ≤ M)
    (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (htrace : ∀ᵐ x ∂μ, Tendsto (fun t ↦ u t x) (𝓝[>] 0) (𝓝 (g x))) :
    Integrable g μ ∧ (∫ x, g x ∂μ) ≤ M := by
  obtain ⟨t, ht, hlim, hsmall⟩ :=
    exists_seq_tendsto_zero_mul_norm_of_integrableOn_Ioo henergy hT
  have htlim : Tendsto t atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun k ↦ (ht k).1⟩
  have hnegLp (k : ℕ) : MemLp (fun x ↦ max (-u (t k) x) 0) 2 μ :=
    (hu (t k) (ht k)).neg_part
  have hnegenergy : Tendsto
      (fun k ↦ t k * ∫ x, (max (-u (t k) x) 0) ^ 2 ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun k ↦ mul_nonneg (ht k).1.le (integral_nonneg fun x ↦ sq_nonneg _))
      (fun k ↦ ?_) hsmall
    apply mul_le_mul_of_nonneg_left _ (ht k).1.le
    apply (integral_mono_ae (hnegLp k).integrable_sq
      (hu (t k) (ht k)).integrable_sq ?_).trans (le_abs_self _)
    filter_upwards [] with x
    by_cases hx : 0 ≤ u (t k) x
    · simp only [max_eq_right (neg_nonpos.mpr hx), zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg _
    · rw [max_eq_left (neg_nonneg.mpr (lt_of_not_ge hx).le), neg_sq]
  have hneg : Tendsto (fun k ↦ ∫ x, max (-u (t k) x) 0 ∂μ) atTop (𝓝 0) := by
    apply tendsto_integral_zero_of_inverse_sq_bound hA hC (fun k ↦ (ht k).1)
      hnegLp (fun k ↦ Eventually.of_forall fun x ↦ le_max_right _ _) hρmeas hρ
      (fun k ↦ ?_) hlayer hnegenergy
    filter_upwards [henv (t k) (ht k)] with x hx
    exact max_le hx (div_nonneg (mul_nonneg hC.le (ht k).1.le) (sq_nonneg _))
  apply integrable_and_integral_le_of_tendsto_neg_part_zero
    (fun k ↦ (hu (t k) (ht k)).integrable (by norm_num)) hg
    (Eventually.of_forall fun k ↦ hmoment (t k) (ht k)) hneg
  filter_upwards [htrace] with x hx
  exact hx.comp htlim

end MeasureTheory
