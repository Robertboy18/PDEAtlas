/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.PositiveQuadraticIntegral
public import PDE.Hyperbolic.NonlinearWave.Cauchy.IntegrableForcing

/-!
# Duhamel estimates for localized quadratic energies

A semigroup bound in a nonnegative quadratic energy passes to integrable
forcing. The retarded exponential factor is retained for later Gronwall
estimates with spatially localized energies.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Square-root energy growth follows from the corresponding quadratic bound. -/
theorem sqrt_bilinear_semigroup_le (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ x, 0 ≤ B x x)
    (S : StronglyContinuousSemigroup E) {ω : ℝ}
    (hbound : ∀ (r : NNReal) x, B (S r x) (S r x) ≤ B x x * Real.exp (ω * r)) (r : NNReal) (x : E) :
    Real.sqrt (B (S r x) (S r x)) ≤ Real.exp (ω * r / 2) * Real.sqrt (B x x) := by
  calc
    _ ≤ Real.sqrt (B x x * Real.exp (ω * r)) := Real.sqrt_le_sqrt (hbound r x)
    _ = _ := by rw [Real.sqrt_mul (hpos x), ← Real.exp_half, mul_comm]

/-- The retarded integral obeys the weighted variation-of-constants bound
for every interval-integrable force, even when the energy form degenerates. -/
theorem sqrt_bilinear_duhamel_le (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ x, 0 ≤ B x x) (S : StronglyContinuousSemigroup E) {ω : ℝ}
    (hbound : ∀ (r : NNReal) x, B (S r x) (S r x) ≤ B x x * Real.exp (ω * r)) {f : ℝ → E} {t : ℝ}
    (ht : 0 ≤ t) (hf : IntervalIntegrable f volume 0 t) :
    Real.sqrt (B (S.duhamel f t) (S.duhamel f t)) ≤
      ∫ s in (0 : ℝ)..t, Real.exp (ω * (t - s) / 2) * Real.sqrt (B (f s) (f s)) := by
  have hi : IntervalIntegrable (fun s ↦ S (t - s).toNNReal (f s)) volume 0 t := by
    obtain ⟨C, -, hC⟩ := S.exists_norm_le_on_Icc t.toNNReal
    apply (hf.norm.const_mul C).mono_fun'
    · exact S.continuous_apply.comp_aestronglyMeasurable
        ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
          |>.prodMk hf.def'.aestronglyMeasurable)
    · rw [uIoc_of_le ht]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (S _).le_of_opNorm_le
        (hC _ ⟨zero_le, Real.toNNReal_le_toNNReal (by linarith [hs.1])⟩) (f s)
  have hq : IntervalIntegrable (fun s ↦ Real.sqrt (B (f s) (f s))) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact integrable_sqrt_bilinear_self B hf.def'
  have hk : IntervalIntegrable (fun s ↦ Real.sqrt (B (S (t - s).toNNReal (f s))
        (S (t - s).toNNReal (f s)))) volume 0 t := by
    rw [intervalIntegrable_iff]
    exact integrable_sqrt_bilinear_self B hi.def'
  have he : Continuous (fun s : ℝ ↦ Real.exp (ω * (t - s) / 2)) := by fun_prop
  calc
    _ ≤ ∫ s in (0 : ℝ)..t,
        Real.sqrt (B (S (t - s).toNNReal (f s)) (S (t - s).toNNReal (f s))) := by
      simp only [StronglyContinuousSemigroup.duhamel, intervalIntegral.integral_of_le ht]
      exact sqrt_bilinear_integral_le B hpos (hi.1)
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on ht hk (hq.continuousOn_mul he.continuousOn)
      intro s hs
      have h := sqrt_bilinear_semigroup_le B hpos S hbound (t - s).toNNReal (f s)
      simpa only [Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)] using h

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
