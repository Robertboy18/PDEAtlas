/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.ForwardFinitePropagation
public import PDE.Hyperbolic.NonlinearWave.DomainOfDependence
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Vanishing
import PDE.FDeriv.Calculus

/-!
# Quadratic cone energy from right initial traces

A positive time slice can be treated by the smooth cone estimate. To reach the
initial slice we use forward `C¹` regularity: zero displacement and right
velocity make the quadratic energy tend to zero. This proves vanishing without
extending the equation to negative times or imposing a global spatial norm.

These estimates are shared by classical uniqueness, defocusing waves and the
negative-energy blowup argument.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

private theorem quadraticConeEnergy_eq_of_eqOn_forward {u v : ℝ^(n + 1) → ℝ} {a : ℝ}
    (h : EqOn u v {p | a ≤ p 0}) (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : a < t) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) u c T t =
      semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) v c T t := by
  unfold semilinearBackwardConeEnergy
  rw [backwardConeEnergy_eq_of_eqOn_forward h c T ht]
  congr 1
  unfold ballIntegral
  apply setIntegral_congr_fun measurableSet_ball
  intro x _
  dsimp only
  rw [h (show a ≤ (timeSpaceCons t x) 0 by simpa using ht.le)]

/-- The residual estimate gives exponential energy control between positive time slices.
Only forward regularity is needed. -/
theorem quadraticConeEnergy_le_exp_forward [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (c : ℝ^n) {a T C : ℝ} (ha : 0 < a)
    (hbound : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveEnergyBalanceResidual
      (fun z : ℝ ↦ z ^ 2 / 2) u (timeSpaceCons t x) ≤ C * semilinearWaveEnergyDensity
      (fun z : ℝ ↦ z ^ 2 / 2) u (timeSpaceCons t x))
    {t : ℝ} (ht : t ∈ Ico a T) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) u c T t ≤
      semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) u c T a * Real.exp (C * (t - a)) := by
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_eqOn_forward hu (half_pos ha)
  have he := quadraticConeEnergy_le_exp hU c (C := C) (fun s hs x hx ↦ ?_) ht
  · rw [quadraticConeEnergy_eq_of_eqOn_forward hUeq c T (by linarith [ht.1]),
      quadraticConeEnergy_eq_of_eqOn_forward hUeq c T (by linarith)] at he
    exact he
  · have hpoint : a / 2 < (timeSpaceCons s x) 0 := by simpa using
      (show a / 2 < s by linarith [hs.1])
    have hlocal := eventuallyEq_of_eqOn_forward hUeq hpoint
    have hsmooth : ContDiffAt ℝ 2 u (timeSpaceCons s x) :=
      hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
        (show (0 : ℝ) < (timeSpaceCons s x) 0 by simpa using ha.trans_le hs.1))
    have hV : ContDiff ℝ 1 (fun z : ℝ ↦ z ^ 2 / 2) := by fun_prop
    have hb := hbound s hs x hx
    rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hV hU.contDiffAt]
    rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hV hsmooth] at hb
    simp only [semilinearWaveOperator, semilinearWaveEnergyDensity,
      PDE.partialDeriv_congr_nhds 0 hlocal, waveOperator_congr_nhds hlocal,
      classicalWaveEnergyDensity_congr_nhds hlocal, hlocal.eq_of_nhds]
    exact hb

/-- Zero displacement and right velocity give zero initial quadratic cone energy. -/
theorem tendsto_quadraticConeEnergy_zero_forward {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ} (hT : 0 < T)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    Tendsto (semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) u c T) (𝓝[>] 0) (𝓝 0) := by
  let P : ℝ × ℝ^n → ℝ := fun p ↦ u (timeSpaceCons (max p.1 0) p.2) ^ 2 / 2
  have hP : Continuous P := by
    apply Continuous.div_const
    apply Continuous.pow
    apply hu.continuousOn.comp_continuous
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        ((continuous_fst.max continuous_const).prodMk continuous_snd))
    intro p
    exact le_max_right p.1 0
  let F : ℝ → ℝ := fun t ↦ ∫ x in Metric.closedBall c T, P (t, x)
  have hF : Continuous F := continuous_parametric_integral_of_continuous hP
    (isCompact_closedBall c T)
  have hzero : F 0 = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    have hbase : EqOn (fun x ↦ P (0, x)) 0 (Metric.ball c T) := by
      intro x hx
      simp [P, hpos x hx]
    have he := hbase.closure (hP.comp (continuous_const.prodMk continuous_id)) continuous_const
    intro x hx
    exact he (by rwa [closure_ball _ hT.ne'])
  have hpot : Tendsto (fun t ↦ ballIntegral n
      (fun x ↦ u (timeSpaceCons t x) ^ 2 / 2) c (T - t)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun t ↦
      setIntegral_nonneg measurableSet_ball (fun x _ ↦ by positivity))
      ?_ (hzero ▸ hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have he : ballIntegral n (fun x ↦ u (timeSpaceCons t x) ^ 2 / 2) c (T - t) =
        ∫ x in Metric.ball c (T - t), P (t, x) := by
      simp only [P, max_eq_left (show (0 : ℝ) ≤ t from le_of_lt ht), ballIntegral]
    change ballIntegral n _ c (T - t) ≤ F t
    rw [he]
    apply setIntegral_mono_set
      ((hP.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
        (isCompact_closedBall c T))
      (Eventually.of_forall fun x ↦ by dsimp [P]; positivity)
    exact Eventually.of_forall fun x hx ↦ Metric.mem_closedBall.mpr
      ((Metric.mem_ball.mp hx).le.trans (sub_le_self T ht.le))
  unfold semilinearBackwardConeEnergy
  simpa only [add_zero] using (tendsto_backwardConeEnergy_zero_forward hu c hT hpos hvel).add hpot

/-- A residual-controlled wave with zero right Cauchy data has zero quadratic cone energy. -/
theorem quadraticConeEnergy_eq_zero_forward [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T C : ℝ}
    (hT : 0 < T)
    (hbound : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveEnergyBalanceResidual
      (fun z : ℝ ↦ z ^ 2 / 2) u (timeSpaceCons t x) ≤ C * semilinearWaveEnergyDensity
      (fun z : ℝ ↦ z ^ 2 / 2) u (timeSpaceCons t x))
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) u c T t = 0 := by
  have hlim := tendsto_quadraticConeEnergy_zero_forward hu₀ c hT hpos hvel
  have hexp : Continuous (fun s : ℝ ↦ Real.exp (C * (t - s))) := by fun_prop
  apply le_antisymm ?_ (semilinearBackwardConeEnergy_nonneg
    (fun z : ℝ ↦ z ^ 2 / 2) (fun z ↦ by positivity) u c T t)
  have hlimit := hlim.mul (hexp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hlimit
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hs hst
  exact quadraticConeEnergy_le_exp_forward hu c hs
    (fun r hr ↦ hbound r ⟨hs.trans_le hr.1, hr.2⟩) ⟨hst.le, ht.2⟩

/-- The difference energy of two forward semilinear waves grows at most exponentially. -/
theorem quadraticConeEnergy_sub_le_exp_forward [Fact (0 < n)] {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hv : ContDiffOn ℝ 2 v {p | 0 < p 0}) (c : ℝ^n) {a T : ℝ} (ha : 0 < a)
    (huwave : ∀ s ∈ Ico a T, ∀ x ∈ Metric.ball c (T - s), waveOperator u (timeSpaceCons s x) +
      f (u (timeSpaceCons s x)) = 0)
    (hvwave : ∀ s ∈ Ico a T, ∀ x ∈ Metric.ball c (T - s), waveOperator v (timeSpaceCons s x) +
      f (v (timeSpaceCons s x)) = 0)
    {t : ℝ} (ht : t ∈ Ico a T) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) (u - v) c T t ≤
      semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) (u - v) c T a *
      Real.exp ((1 + (K : ℝ)) * (t - a)) := by
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_eqOn_forward hu (half_pos ha)
  obtain ⟨V, hV, hVeq⟩ := exists_contDiff_eqOn_forward hv (half_pos ha)
  have hdiff : EqOn (U - V) (u - v) {p | a / 2 ≤ p 0} :=
    fun p hp ↦ congrArg₂ (· - ·) (hUeq hp) (hVeq hp)
  have he := semilinearBackwardConeEnergy_sub_le_exp hf hU hV c
    (fun s hs x hx ↦ ?_) (fun s hs x hx ↦ ?_) ht
  · change semilinearBackwardConeEnergy _ (U - V) c T t ≤
      semilinearBackwardConeEnergy _ (U - V) c T a * _ at he
    rw [quadraticConeEnergy_eq_of_eqOn_forward hdiff c T (by linarith [ht.1]),
      quadraticConeEnergy_eq_of_eqOn_forward hdiff c T (by linarith)] at he
    exact he
  · have hpoint : a / 2 < (timeSpaceCons s x) 0 := by simpa using
      (show a / 2 < s by linarith [hs.1])
    dsimp only
    rw [waveOperator_congr_nhds (eventuallyEq_of_eqOn_forward hUeq hpoint), hUeq hpoint.le]
    exact huwave s hs x hx
  · have hpoint : a / 2 < (timeSpaceCons s x) 0 := by simpa using
      (show a / 2 < s by linarith [hs.1])
    dsimp only
    rw [waveOperator_congr_nhds (eventuallyEq_of_eqOn_forward hVeq hpoint), hVeq hpoint.le]
    exact hvwave s hs x hx

/-- Equal right Cauchy data force zero difference energy for a Lipschitz scalar reaction. -/
theorem quadraticConeEnergy_sub_eq_zero_forward [Fact (0 < n)] {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0})
    (hv : ContDiffOn ℝ 2 v {p | 0 < p 0}) (hw₀ : ContDiffOn ℝ 1 (u - v) {p | 0 ≤ p 0}) (c : ℝ^n)
    {T : ℝ} (hT : 0 < T)
    (huwave : ∀ s ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - s), waveOperator u (timeSpaceCons s x) +
      f (u (timeSpaceCons s x)) = 0)
    (hvwave : ∀ s ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - s), waveOperator v (timeSpaceCons s x) +
      f (v (timeSpaceCons s x)) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, (u - v) (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ (u - v) (timeSpaceCons t x)) (Ici 0) 0 = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    semilinearBackwardConeEnergy (fun z : ℝ ↦ z ^ 2 / 2) (u - v) c T t = 0 := by
  have hlim := tendsto_quadraticConeEnergy_zero_forward hw₀ c hT hpos hvel
  have hexp : Continuous (fun s : ℝ ↦ Real.exp ((1 + (K : ℝ)) * (t - s))) := by
    fun_prop
  apply le_antisymm ?_ (semilinearBackwardConeEnergy_nonneg
    (fun z : ℝ ↦ z ^ 2 / 2) (fun z ↦ by positivity) (u - v) c T t)
  have hlimit := hlim.mul (hexp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hlimit
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hs hst
  exact quadraticConeEnergy_sub_le_exp_forward hf hu hv c hs
    (fun r hr ↦ huwave r ⟨hs.trans_le hr.1, hr.2⟩)
    (fun r hr ↦ hvwave r ⟨hs.trans_le hr.1, hr.2⟩) ⟨hst.le, ht.2⟩

end WaveEquation
