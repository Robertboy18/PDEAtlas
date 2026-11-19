/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative
public import PDE.Analysis.Integration.FiniteMeasureLp

/-!
# Quantitative representatives of square-integrable Sobolev curves

The fundamental theorem includes both endpoints and bounds the same representative
uniformly by the sum of the two Bochner norms. No value of an `Lp` representative at
an endpoint is treated as a trace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A curve and its weak derivative in `L²` have a continuous representative with
an interval-dependent uniform bound, including the initial trace. -/
theorem exists_continuous_L2_representative_norm_le
    {a b : ℝ} (hab : a < b)
    {u g : Lp X 2 (volume.restrict (Ioc a b))}
    (hweak : HasWeakTimeDerivativeOn (Ioo a b) u g) :
    ∃ v : ℝ → X, Continuous v ∧
      (u : ℝ → X) =ᵐ[volume.restrict (Ioc a b)] v ∧
      (∀ s ∈ Icc a b, ∀ t ∈ Icc a b, v t = v s + ∫ r in s..t, g r) ∧
      ∀ t ∈ Icc a b, ‖v t‖ ≤
        (((b - a)⁻¹ + 1) * max 1 (b - a)) * (‖u‖ + ‖g‖) := by
  have hmeasure : volume.restrict (Ioo a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  have hu : IntegrableOn (fun t ↦ u t) (Ioo a b) := by
    rw [IntegrableOn, hmeasure]
    exact (Lp.memLp u).integrable (by norm_num)
  have hg : IntegrableOn (fun t ↦ g t) (Ioo a b) := by
    rw [IntegrableOn, hmeasure]
    exact (Lp.memLp g).integrable (by norm_num)
  obtain ⟨v, hv, huv, hFTC⟩ := hweak.exists_continuous_representative_Icc hab hg
  refine ⟨v, hv, by simpa only [hmeasure] using huv, ?_, ?_⟩
  · intro s hs t ht
    exact (sub_eq_iff_eq_add.mp (hFTC s hs t ht)).trans (add_comm _ _)
  · intro t ht
    have hU := (Lp.memLp u).integral_norm_le_max_measure_mul_lpNorm (by norm_num)
    have hG := (Lp.memLp g).integral_norm_le_max_measure_mul_lpNorm (by norm_num)
    simp only [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hab.le,
      ← toReal_eLpNorm, ← Lp.norm_def] at hU hG
    have h := norm_le_average_add_integral_of_intervalIntegral hab hu hg huv hFTC ht
    rw [hmeasure] at h
    have hi : 0 ≤ (b - a)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hab.le)
    have hc : 0 ≤ max 1 (b - a) := zero_le_one.trans (le_max_left _ _)
    calc
      ‖v t‖ ≤ _ := h
      _ ≤ (b - a)⁻¹ * (max 1 (b - a) * ‖u‖) + max 1 (b - a) * ‖g‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hU hi) hG
      _ ≤ _ := by nlinarith [mul_nonneg hc (norm_nonneg u),
        mul_nonneg hi (mul_nonneg hc (norm_nonneg g))]

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
