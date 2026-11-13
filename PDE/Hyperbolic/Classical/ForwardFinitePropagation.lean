/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.ForwardInitialEnergy
import PDE.FDeriv.SpaceTime

/-!
# Finite propagation for forward classical waves

The energy argument uses `C²` regularity at positive times and `C¹`
regularity up to the initial slice. Zero displacement and right velocity on the
open base ball force vanishing on the closed backward cone, including its lateral
boundary and vertex.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.3, Theorem 6.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis PDE.Common Set
open scoped Topology

variable {n : ℕ}

/-- Zero initial data force zero energy on every positive-time slice below the vertex. -/
theorem backwardConeEnergy_eq_zero_forward [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    backwardConeEnergy u c T t = 0 := by
  apply le_antisymm ?_ (backwardConeEnergy_nonneg u c T t)
  apply ge_of_tendsto (tendsto_backwardConeEnergy_zero_forward hu₀ c hT hpos hvel)
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.1)] with s hs hst
  have hanti : AntitoneOn (backwardConeEnergy u c T) (Ico s T) := by
    apply backwardConeEnergy_antitone
    intro r hr
    exact hasDerivAt_backwardConeEnergy_forward hu c T (hs.trans_le hr.1) hr.2
      (hwave r ⟨hs.trans_le hr.1, hr.2⟩)
  exact hanti ⟨le_rfl, hst.trans ht.2⟩ ⟨hst.le, ht.2⟩ hst.le

/-- Vanishing cone energy and zero initial displacement force the field to vanish
on the closed cone, including its lateral boundary and vertex. -/
theorem eq_zero_on_closed_backwardCone_of_energy_eq_zero_forward {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hT : 0 < T) (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (henergy : ∀ s ∈ Ioo 0 T, backwardConeEnergy u c T s = 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  have hbase : ∀ x ∈ Metric.closedBall c T, u (timeSpaceCons 0 x) = 0 := by
    have hc : Continuous (fun x : ℝ^n ↦ u (timeSpaceCons 0 x)) := hu₀.continuousOn.comp_continuous
        (contDiff_timeSpaceCons_spatial n 0 (m := 1)).continuous (fun _ ↦ by simp)
    have he := (show EqOn (fun x ↦ u (timeSpaceCons 0 x)) 0 (Metric.ball c T)
      from hpos).closure hc continuous_const
    intro x hx
    exact he (by rwa [closure_ball _ hT.ne'])
  intro t ht x hx
  have hxInitial : x ∈ Metric.closedBall c T := Metric.mem_closedBall.mpr
    ((Metric.mem_closedBall.mp hx).trans (sub_le_self T ht.1))
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact hbase x hxInitial
  let path : ℝ → ℝ := fun s ↦ u (timeSpaceCons s x)
  have hline : Continuous (fun s ↦ timeSpaceCons (n := n) s x) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)
  have hpath : ContinuousOn path (Icc 0 t) :=
    hu₀.continuousOn.comp hline.continuousOn (fun _ hs ↦ by simpa using hs.1)
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt path 0 s := by
    intro s hs
    have hxBall : x ∈ Metric.ball c (T - s) := Metric.mem_ball.mpr
      ((Metric.mem_closedBall.mp hx).trans_lt (sub_lt_sub_left hs.2 T))
    have hzero := classicalWaveEnergyDensity_eq_zero_on_ball_forward hu c hs.1
      (by simpa only [backwardConeEnergy] using henergy s ⟨hs.1, hs.2.trans_le ht.2⟩) x hxBall
    have hut : (∂[0] u) (timeSpaceCons s x) = 0 := by
      unfold classicalWaveEnergyDensity at hzero
      nlinarith [sq_nonneg ((∂[0] u) (timeSpaceCons s x)),
        sq_nonneg ‖classicalWaveSpatialGradient u (timeSpaceCons s x)‖]
    have hr : ContDiffAt ℝ 2 u (timeSpaceCons s x) :=
      hu.contDiffAt ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds
        (by simpa using hs.1))
    exact (PDE.hasDerivAt_timeSpaceCons u s x
      (hr.differentiableAt (by norm_num))).congr_deriv hut
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htpos.le hpath hd
    (IntervalIntegrable.zero : IntervalIntegrable (0 : ℝ → ℝ) volume 0 t)
  have he : path t = path 0 := sub_eq_zero.mp (by simpa using hFTC.symm)
  exact he.trans (hbase x hxInitial)

/-- Finite propagation speed on the forward half-space, as in Evans, §2.4.3, Theorem 6.

The initial velocity is the right derivative at time zero. The wave equation
is needed only in the interior of the cone, and the initial data only on its open base.
The conclusion includes time zero, the lateral boundary and the vertex. -/
theorem eq_zero_on_closed_backwardCone_forward [Fact (0 < n)] {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0}) (hu₀ : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (c : ℝ^n) {T : ℝ}
    (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t), waveOperator u (timeSpaceCons t x) = 0)
    (hpos : ∀ x ∈ Metric.ball c T, u (timeSpaceCons 0 x) = 0)
    (hvel : ∀ x ∈ Metric.ball c T, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = 0) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ Metric.closedBall c (T - t), u (timeSpaceCons t x) = 0 := by
  apply eq_zero_on_closed_backwardCone_of_energy_eq_zero_forward hu hu₀ c hT hpos
  intro t ht
  exact backwardConeEnergy_eq_zero_forward hu hu₀ c hT hwave hpos hvel ht

end WaveEquation
