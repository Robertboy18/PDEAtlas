/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.Approximation
public import PDE.Parabolic.Heat.Spectral.L2Evolution
public import PDE.Parabolic.Heat.Spectral.Maximum

/-!
# Supremum stability for continuous interval heat data

At each positive time a summable heat majorant controls the change in the series
under uniform approximation of the initial data. The maximum principle for the
smooth approximants then passes to arbitrary continuous zero-boundary data.
Applying this bound to the difference gives a contraction estimate independent of time.
-/

@[expose] public section

namespace HeatEquation

open Set PDE.Analysis.Fourier.SineSeries

/-- The convergent heat series respects subtraction of continuous interval data. -/
theorem intervalHeatSeries_sub {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1))
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    intervalHeatSeries (intervalCoefficient (fun y ↦ g y - h y)) t x =
      intervalHeatSeries (intervalCoefficient g) t x -
        intervalHeatSeries (intervalCoefficient h) t x := by
  have hs {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :=
    summable_intervalHeatSeries
      (norm_intervalCoefficient_le (memLp_interval_of_continuousOn hf 2)) ht x
  unfold intervalHeatSeries
  simp_rw [intervalCoefficient_sub hg hh, sub_mul]
  exact (hs hg).tsum_sub (hs hh)

/-- A summable majorant bounds the series at each fixed positive time in terms of
a uniform bound for the initial data. This estimate need not be uniform near time zero. -/
theorem norm_intervalHeatSeries_le_majorant {g : ℝ → ℝ} {M t : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ y ∈ Icc 0 1, ‖g y‖ ≤ M) (ht : 0 < t) (x : ℝ) :
    ‖intervalHeatSeries (intervalCoefficient g) t x‖ ≤
      2 * M * ∑' n, intervalHeatMajorant 0 t n := by
  have hb := norm_intervalCoefficient_le_of_bound hbound
  have hs := (summable_intervalHeatMajorant 0 ht).mul_left (2 * M)
  have hterm (n : ℕ) :
      ‖intervalCoefficient g n * intervalHeatMode n t x‖ ≤
        2 * M * intervalHeatMajorant 0 t n := by
    rw [norm_mul]
    exact mul_le_mul (hb n) (norm_intervalHeatMode_le n le_rfl x)
      (norm_nonneg _) (mul_nonneg (by norm_num) hM)
  unfold intervalHeatSeries
  calc
    _ ≤ ∑' n, ‖intervalCoefficient g n * intervalHeatMode n t x‖ :=
      norm_tsum_le_tsum_norm (hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm)
    _ ≤ ∑' n, 2 * M * intervalHeatMajorant 0 t n :=
      (hs.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm).tsum_le_tsum hterm hs
    _ = _ := tsum_mul_left

/-- The heat series of continuous Dirichlet data is bounded by any uniform bound
for the initial data. The estimate follows by smooth approximation and the maximum principle. -/
theorem norm_intervalHeatSeries_le_of_continuousOn {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hzero : g 0 = 0) (hone : g 1 = 0)
    {M t x : ℝ} (hbound : ∀ y ∈ Icc 0 1, ‖g y‖ ≤ M)
    (ht : 0 < t) (hx : x ∈ Icc 0 1) :
    ‖intervalHeatSeries (intervalCoefficient g) t x‖ ≤ M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, zero_le_one⟩)
  let K : ℝ := 2 * ∑' n, intervalHeatMajorant 0 t n
  have hK : 0 ≤ K := by
    apply mul_nonneg (by norm_num)
    apply tsum_nonneg
    intro n
    unfold intervalHeatMajorant
    exact mul_nonneg (by positivity) (intervalHeatTimeMode_pos n t).le
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ : ℝ := ε / (K + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨q, hq, hq0, hq1, hnear⟩ := exists_contDiffOn_zero_boundary_near hg hzero hone hδ
  have hdiff : ∀ y ∈ Icc 0 1, ‖g y - q y‖ ≤ δ :=
    fun y hy ↦ by simpa only [norm_sub_rev] using (hnear y hy).le
  have hqbound (y : ℝ) (hy : y ∈ Icc 0 1) : ‖q y‖ ≤ M + δ :=
    (norm_le_norm_add_norm_sub' (q y) (g y)).trans
      (by linarith [hnear y hy, hbound y hy])
  have hqheat := norm_intervalHeatSeries_le_of_contDiffOn hq hq0 hq1
    (add_nonneg hM hδ.le) hqbound ht hx
  have herr := norm_intervalHeatSeries_le_majorant hδ.le hdiff ht x
  rw [intervalHeatSeries_sub hg hq.continuousOn ht x] at herr
  have he : 2 * δ * (∑' n, intervalHeatMajorant 0 t n) + (M + δ) = M + ε := by
    have hd : δ * (K + 1) = ε := div_mul_cancel₀ ε (by linarith : K + 1 ≠ 0)
    dsimp only [K] at hd
    nlinarith [hd]
  calc
    _ ≤ ‖intervalHeatSeries (intervalCoefficient g) t x -
        intervalHeatSeries (intervalCoefficient q) t x‖ +
          ‖intervalHeatSeries (intervalCoefficient q) t x‖ :=
      by simpa only [add_comm] using norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := (add_le_add herr hqheat).trans_eq he

/-- Uniform perturbations of continuous zero-boundary data cause no larger
perturbation of the positive-time interval heat solution. -/
theorem norm_intervalHeatSeries_sub_le {g h : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (hh : ContinuousOn h (Icc 0 1))
    (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hh0 : h 0 = 0) (hh1 : h 1 = 0)
    {M t x : ℝ} (hbound : ∀ y ∈ Icc 0 1, ‖g y - h y‖ ≤ M)
    (ht : 0 < t) (hx : x ∈ Icc 0 1) :
    ‖intervalHeatSeries (intervalCoefficient g) t x -
      intervalHeatSeries (intervalCoefficient h) t x‖ ≤ M := by
  rw [← intervalHeatSeries_sub hg hh ht x]
  exact norm_intervalHeatSeries_le_of_continuousOn (hg.fun_sub hh)
    (by simp only [hg0, hh0, sub_self]) (by simp only [hg1, hh1, sub_self])
    hbound ht hx

end HeatEquation
