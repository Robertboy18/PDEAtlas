/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.EnergyIdentity
public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.DerivativeEstimate
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import PDE.Analysis.MeasureTheory.Lp.VanishingMeasure
import PDE.Hyperbolic.NonlinearWave.Critical.Cone.Bootstrap

/-!
# Physical energy decay on a critical cone

The quintic equation and two linear prefix estimates imply that kinetic and spatial-gradient energy
vanish on shrinking balls. Critical membership and derivative L⁶ control are derived on a late cone;
shrinking volume then gives L² decay. Only C² regularity on the open band is assumed.

This is the limit (19) in step 4 of the proof of Evans, §12.4, Theorem 3, with the linear estimates
as hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 4 of its proof, equations (18)-(20).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- The quintic equation and the two linear prefix estimates force the
L² energy of each first derivative to vanish on shrinking balls. -/
theorem tendsto_integral_sq_partialDeriv_of_wave_strichartz {u : ℝ^4 → ℝ} {T C K L : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (i : Fin 4)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T, lpNorm (fun r ↦
      lpNorm (fun x ↦ u (timeSpaceCons r x)) 12 (volume.restrict (Metric.ball c (T - r)))) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm
      (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r))))
    (hderivative : ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T, lpNorm
      (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q)))) :
    Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t), ((∂[i] u) (timeSpaceCons t x)) ^ 2) (𝓝[<] T)
      (𝓝 0) := by
  obtain ⟨b, hb, hboot⟩ := exists_cone_tail_bootstrap_of_wave hT hu c hwave hC hK
  have hcritical := hboot b ⟨le_rfl, hb.2⟩ (hlinear b hb)
  obtain ⟨s, hs, hbound⟩ := exists_cone_tail_partialDeriv_bound hu c i hb.1 hb.2 hL hcritical
  obtain ⟨A, hA⟩ := hderivative s ⟨hb.1.trans hs.1, hs.2⟩
  have hbound' := hbound A hA
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContinuousOn (∂[i] u) {p | 0 < p 0 ∧ p 0 < T} :=
    (hu.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const
  have hmem (t : ℝ) (ht : t ∈ Ioo 0 T) : MemLp (fun x ↦ (∂[i] u) (timeSpaceCons t x)) 6
        (volume.restrict (Metric.ball c (T - t))) := by
    have hm := memLp_movingConeField hv c ht 6
    rwa [movingConeField_section ht,
      memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet] at hm
  have hvol : Tendsto (fun t : ℝ ↦
      (volume.restrict (Metric.ball c (T - t))) Set.univ) (𝓝[<] T) (𝓝 0) := by
    have hr : Tendsto (fun t : ℝ ↦ T - t) (𝓝[<] T) (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := T)).sub
        (show Tendsto (fun t : ℝ ↦ t) (𝓝[<] T) (𝓝 T) from nhdsWithin_le_nhds)
    have hp := ENNReal.Tendsto.pow (n := 3) (ENNReal.tendsto_ofReal hr)
    have hm := ENNReal.Tendsto.mul_const hp
      (b := ENNReal.ofReal (Real.sqrt Real.pi ^ 3 / Real.Gamma ((3 : ℝ) / 2 + 1)))
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [Measure.restrict_apply_univ, EuclideanSpace.volume_ball,
      Fintype.card_fin, Nat.cast_ofNat, ENNReal.ofReal_zero,
      zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_mul] using hm
  have hnorm : Tendsto (fun t ↦ lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons t x)) 2
      (volume.restrict (Metric.ball c (T - t)))) (𝓝[<] T) (𝓝 0) := by
    apply MeasureTheory.tendsto_lpNorm_of_measure_univ_tendsto_zero
      (q := 6) (C := ENNReal.ofReal (2 * A)) (by norm_num) (by norm_num)
      (by norm_num) ENNReal.ofReal_ne_top ?_ ?_ hvol
    · filter_upwards [Ioo_mem_nhdsLT hT] with t ht
      exact (hmem t ht).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
      rw [← ofReal_lpNorm (hmem t ⟨(hb.1.trans hs.1).trans ht.1, ht.2⟩)]
      exact ENNReal.ofReal_le_ofReal (hbound' t ⟨ht.1.le, ht.2⟩)
  have hsq := hnorm.pow 2
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
  apply hsq.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  have hi := integral_norm_pow_eq_lpNorm_pow (hmem t ht).aestronglyMeasurable
    (by norm_num : (0 : ℕ) < 2)
  simpa only [Real.norm_eq_abs, sq_abs, Nat.cast_ofNat] using hi.symm

/-- Vanishing coordinate derivative energies give the kinetic and
spatial-gradient energy limit. Local classical regularity supplies integrability. -/
theorem tendsto_integral_kinetic_gradient_of_partialDeriv {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hlim : ∀ i : Fin 4, Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t),
      ((∂[i] u) (timeSpaceCons t x)) ^ 2) (𝓝[<] T) (𝓝 0)) :
    Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t), ((∂[0] u) (timeSpaceCons t x)) ^ 2 +
      ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2) (𝓝[<] T) (𝓝 0) := by
  have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hlim i)
  simp only [Finset.sum_const_zero] at hsum
  apply hsum.congr'
  filter_upwards [Ioo_mem_nhdsLT hT] with t ht
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hi (i : Fin 4) : IntegrableOn (fun x ↦ ((∂[i] u) (timeSpaceCons t x)) ^ 2)
      (Metric.ball c (T - t)) := by
    have hv : ContinuousOn (∂[i] u) {p | 0 < p 0 ∧ p 0 < T} :=
      (hu.continuousOn_fderiv_of_isOpen hopen (by norm_num)).clm_apply continuousOn_const
    have hm := memLp_movingConeField hv c ht 2
    rw [movingConeField_section ht,
      memLp_indicator_iff_restrict measurableSet_ball.nullMeasurableSet] at hm
    simpa only [Real.norm_eq_abs, sq_abs, IntegrableOn, Nat.cast_ofNat] using
      hm.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [← integral_finsetSum Finset.univ (fun i _ ↦ hi i)]
  refine setIntegral_congr_fun measurableSet_ball fun x _ ↦ ?_
  simp only [Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply]

/-- Quintic-wave nonconcentration and the two linear prefix estimates
imply vanishing kinetic and gradient energy at the cone tip. The solution is
only C² on the open forward band, with no terminal or support assumption. -/
theorem tendsto_integral_kinetic_gradient_of_wave_strichartz {u : ℝ^4 → ℝ} {T C K L : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0)
    (hC : 0 < C) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T, lpNorm (fun r ↦
      lpNorm (fun x ↦ u (timeSpaceCons r x)) 12 (volume.restrict (Metric.ball c (T - r)))) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm
      (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (T - r))))
    (hderivative : ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q)))) :
    Tendsto (fun t ↦ ∫ x in Metric.ball c (T - t), ((∂[0] u) (timeSpaceCons t x)) ^ 2 +
      ‖classicalWaveSpatialGradient u (timeSpaceCons t x)‖ ^ 2) (𝓝[<] T) (𝓝 0) := by
  refine tendsto_integral_kinetic_gradient_of_partialDeriv hT hu c fun i ↦ ?_
  exact tendsto_integral_sq_partialDeriv_of_wave_strichartz hT hu c i hwave
    hC hK hL hlinear (hderivative i)

end WaveEquation.Critical
