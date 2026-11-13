/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Topology.Order.FirstZero
public import PDE.Hyperbolic.Models.Wave.Duhamel.CauchyTrace
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave
import CAS.ExactTactic

/-!
# Short-time amplitude bounds in three space dimensions

Kirchhoff's kernel is positive, so the retarded term at `(t, x)` is bounded by the
source on the backward cone with apex `(t, x)`. A first-contact argument on a compact
parametrization of that cone then bounds a semilinear wave on a short time interval in
terms of bounds on the initial displacement, its gradient and the initial velocity.
The reaction need only be continuous: the Kirchhoff and Duhamel representation of a
`C⁴` field on a time band takes the wave operator of the field itself as its source.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common
open scoped Topology Pointwise

namespace WaveEquation

/-- If `‖g‖ ≤ G`, `‖Dg‖ ≤ K` and `‖h‖ ≤ B` everywhere, the free wave with Cauchy data
`(g, h)` is bounded by `G + t (K + B)` at time `t ≥ 0`. -/
theorem norm_kirchhoffFormula_le_initial_bounds {g h : ℝ^3 → ℝ} {G K B t : ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (hG : ∀ y, ‖g y‖ ≤ G) (hK : ∀ y, ‖fderiv ℝ g y‖ ≤ K) (hB : ∀ y, ‖h y‖ ≤ B)
    (ht : 0 ≤ t) (x : ℝ^3) :
    ‖kirchhoffFormula g h x t‖ ≤ G + t * (K + B) := by
  have hmean : ‖unitSphereAverage 3 g x t‖ ≤ G := by
    unfold unitSphereAverage
    rw [norm_div, Real.norm_of_nonneg (unitSphereArea_pos (n := 3)).le]
    apply (div_le_iff₀ (unitSphereArea_pos (n := 3))).mpr
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun ω ↦ hG (x + t • (ω : ℝ^3)))
  have htrace : ‖sphericalCauchyTrace g h x t‖ ≤ K + B := by
    unfold sphericalCauchyTrace
    rw [norm_div, Real.norm_of_nonneg (unitSphereArea_pos (n := 3)).le]
    apply (div_le_iff₀ (unitSphereArea_pos (n := 3))).mpr
    apply norm_integral_le_of_norm_le_const
    apply Filter.Eventually.of_forall
    intro ω
    have hω : ‖(ω : ℝ^3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    have hd : ‖fderiv ℝ g (x + t • (ω : ℝ^3)) (ω : ℝ^3)‖ ≤ K := by
      calc
        _ ≤ ‖fderiv ℝ g (x + t • (ω : ℝ^3))‖ * ‖(ω : ℝ^3)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K := by rw [hω, mul_one]; exact hK _
    exact (norm_add_le _ _).trans (by linarith [hB (x + t • (ω : ℝ^3))])
  rw [kirchhoffFormula_eq_mean_add_sphericalCauchyTrace hg hh]
  calc
    _ ≤ ‖unitSphereAverage 3 g x t‖ + ‖t * sphericalCauchyTrace g h x t‖ := norm_add_le _ _
    _ ≤ G + t * (K + B) := by
      rw [norm_mul, Real.norm_of_nonneg ht]
      exact add_le_add hmean (mul_le_mul_of_nonneg_left htrace ht)

/-- If `G + d (K + B) + d² A / 2 < M` and `‖f‖ ≤ A` on `[-M, M]`, then `‖u‖ < M` on
`[0, d]`. The proof looks at the first time the field reaches `M` on a compact backward
cone, so no a priori bound on the field is needed. -/
theorem norm_lt_of_short_time_semilinearWave_three {u : ℝ^4 → ℝ} {f : ℝ → ℝ} {g h : ℝ^3 → ℝ}
    {a b d G K B A M : ℝ} (hu : ContDiffOn ℝ 4 u {p | a < p 0 ∧ p 0 < b}) (ha : a < 0) (hdb : d < b)
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x) (hG : ∀ x, ‖g x‖ ≤ G)
    (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K) (hB : ∀ x, ‖h x‖ ≤ B) (hA : 0 ≤ A) (hGM : G < M)
    (hsmall : G + d * (K + B) + d ^ 2 * A / 2 < M) (hf : ∀ z, ‖z‖ ≤ M → ‖f z‖ ≤ A)
    (hwave : ∀ t ∈ Ioc 0 d, ∀ x,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) :
    ∀ t ∈ Icc 0 d, ∀ x, ‖u (timeSpaceCons t x)‖ < M := by
  intro t ht x
  by_contra hnot
  let Ψ : ℝ^3 × ℝ → ℝ^4 := fun z ↦ timeSpaceCons z.2 (x + (d - z.2) • z.1)
  have hΨ : Continuous Ψ := by
    exact (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous.comp (continuous_snd.prodMk
        (continuous_const.add ((continuous_const.sub continuous_snd).smul continuous_fst)))
  have hcont : ContinuousOn (fun z ↦ M - ‖u (Ψ z)‖)
      (Metric.closedBall (0 : ℝ^3) 1 ×ˢ Icc 0 d) := by
    apply continuousOn_const.sub
    apply (hu.continuousOn.comp hΨ.continuousOn ?_).norm
    intro z hz
    exact ⟨ha.trans_le hz.2.1, hz.2.2.trans_lt hdb⟩
  have htest : ∃ z ∈ Metric.closedBall (0 : ℝ^3) 1 ×ˢ Icc 0 d,
      M - ‖u (Ψ z)‖ ≤ 0 := by
    refine ⟨(0, t), ⟨by simp, ht⟩, ?_⟩
    simpa only [Ψ, smul_zero, add_zero, sub_nonpos] using le_of_not_gt hnot
  obtain ⟨z, hz, hzero, hpast⟩ := exists_first_zero_with_nonneg_past
    (isCompact_closedBall (0 : ℝ^3) 1) hcont
    (fun y _ ↦ by
      change 0 < M - ‖u (timeSpaceCons 0 (x + (d - 0) • y))‖
      rw [hposition]
      exact sub_pos.mpr ((hG _).trans_lt hGM)) htest
  let y := x + (d - z.2) • z.1
  have hzbound : ‖z.1‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  have hpastcone (s : ℝ) (hs : s ∈ Ioc 0 z.2) (w : ℝ^3)
      (hw : ‖w - y‖ ≤ z.2 - s) : ‖u (timeSpaceCons s w)‖ ≤ M := by
    have hws : ‖w - x‖ ≤ d - s := by
      calc
        _ = ‖(w - y) + (d - z.2) • z.1‖ := by congr 1; dsimp [y]; abel
        _ ≤ ‖w - y‖ + ‖(d - z.2) • z.1‖ := norm_add_le _ _
        _ ≤ (z.2 - s) + (d - z.2) := by
          rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr hz.2.2)]
          exact add_le_add hw (by nlinarith [hz.2.2])
        _ = d - s := by cas
    have hmem : w - x ∈ (d - s) • Metric.closedBall (0 : ℝ^3) 1 := by
      rw [smul_unitClosedBall_of_nonneg (by linarith [hs.2, hz.2.2])]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hws
    obtain ⟨v, hv, he⟩ := hmem
    change (d - s) • v = w - x at he
    have hp := hpast (v, s) ⟨hv, hs.1.le, hs.2⟩
    have heq : Ψ (v, s) = timeSpaceCons s w := by
      dsimp [Ψ]
      rw [he, add_sub_cancel]
    rw [heq] at hp
    exact sub_nonneg.mp hp
  have hforce : ∀ s ∈ Ioc 0 z.2, ∀ w : ℝ^3, ‖w - y‖ ≤ z.2 - s →
      ‖waveOperator u (timeSpaceCons s w)‖ ≤ A := by
    intro s hs w hw
    rw [eq_neg_of_add_eq_zero_left (hwave s ⟨hs.1, hs.2.trans hz.2.2⟩ w), norm_neg]
    exact hf _ (hpastcone s hs w hw)
  have he := eq_kirchhoffFormula_add_duhamel_on_band
    (F := waveOperator u) hu ha (fun _ _ _ ↦ rfl)
    hposition hinitial hz.2.1.le (hz.2.2.trans_lt hdb) y
  have hD := norm_oddDuhamelSolution_zero_le_quadratic_on_cone hz.2.1.le y hforce
  have hfree := norm_kirchhoffFormula_le_initial_bounds
    (hg.of_le (by norm_num)) hh.continuous hG hK hB hz.2.1.le y
  have hnorm := norm_add_le (spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons z.2 y))
    (oddDuhamelSolution 0 (waveOperator u) (timeSpaceCons z.2 y))
  rw [← he] at hnorm
  have hlevel : ‖u (timeSpaceCons z.2 y)‖ = M := sub_eq_zero.mp hzero |>.symm
  rw [hlevel] at hnorm
  have hKB : 0 ≤ K + B := add_nonneg ((norm_nonneg _).trans (hK 0)) ((norm_nonneg _).trans (hB 0))
  have hlin : z.2 * (K + B) ≤ d * (K + B) := mul_le_mul_of_nonneg_right hz.2.2 hKB
  have hquad : z.2 ^ 2 * A ≤ d ^ 2 * A :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz.2.1.le hz.2.2 2) hA
  change ‖kirchhoffFormula g h y z.2‖ ≤ _ at hfree
  change M ≤ ‖kirchhoffFormula g h y z.2‖ + _ at hnorm
  linarith

/-- A continuous reaction and bounded Cauchy jets give a uniform initial
amplitude bound and a quadratic error from the free wave on the same window. -/
theorem exists_pos_amplitude_and_retarded_bound_three {u : ℝ^4 → ℝ} {f : ℝ → ℝ} {g h : ℝ^3 → ℝ}
    {a b G K B : ℝ} (hu : ContDiffOn ℝ 4 u {p | a < p 0 ∧ p 0 < b}) (ha : a < 0) (hb : 0 < b)
    (hf : Continuous f) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x) (hG : ∀ x, ‖g x‖ ≤ G)
    (hK : ∀ x, ‖fderiv ℝ g x‖ ≤ K) (hB : ∀ x, ‖h x‖ ≤ B)
    (hwave : ∀ t ∈ Ioo 0 b, ∀ x,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) :
    ∃ δ ∈ Ioo 0 b, ∃ A ≥ 0, (∀ t ∈ Icc 0 δ, ∀ x, ‖u (timeSpaceCons t x)‖ < G + 1) ∧ ∀ t ∈ Icc 0 δ,
      ∀ x, ‖u (timeSpaceCons t x) - kirchhoffFormula g h x t‖ ≤ t ^ 2 * A / 2 := by
  obtain ⟨A₀, hA₀⟩ := (isCompact_Icc.image hf).isBounded.exists_norm_le
    (s := f '' Icc (-(G + 1)) (G + 1))
  let A := max A₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  have hfA (z : ℝ) (hz : ‖z‖ ≤ G + 1) : ‖f z‖ ≤ A :=
    (hA₀ _ ⟨z, abs_le.mp (by simpa only [Real.norm_eq_abs] using hz), rfl⟩).trans (le_max_left _ _)
  have hnear : ∀ᶠ d : ℝ in 𝓝 0, G + d * (K + B) + d ^ 2 * A / 2 < G + 1 := by
    have hc : Continuous (fun d : ℝ ↦ G + d * (K + B) + d ^ 2 * A / 2) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simp))
  have hright : ∀ᶠ d : ℝ in 𝓝[>] 0,
      G + d * (K + B) + d ^ 2 * A / 2 < G + 1 := nhdsWithin_le_nhds hnear
  have htime : ∀ᶠ d : ℝ in 𝓝[>] 0, d < b := nhdsWithin_le_nhds (gt_mem_nhds hb)
  obtain ⟨δ, ⟨hδsmall, hδb⟩, hδ⟩ := ((hright.and htime).and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := hδ
  have hamp := norm_lt_of_short_time_semilinearWave_three hu ha hδb hg hh
    hposition hinitial hG hK hB hA (by linarith : G < G + 1) hδsmall hfA
    (fun t ht x ↦ hwave t ⟨ht.1, ht.2.trans_lt hδb⟩ x)
  refine ⟨δ, ⟨hδpos, hδb⟩, A, hA, hamp, ?_⟩
  intro t ht x
  have he := eq_kirchhoffFormula_add_duhamel_on_band
    (F := waveOperator u) hu ha (fun _ _ _ ↦ rfl)
    hposition hinitial ht.1 (ht.2.trans_lt hδb) x
  have hforce (s : ℝ) (hs : s ∈ Ioc 0 t) (y : ℝ^3) :
      ‖waveOperator u (timeSpaceCons s y)‖ ≤ A := by
    rw [eq_neg_of_add_eq_zero_left (hwave s ⟨hs.1, (hs.2.trans ht.2).trans_lt hδb⟩ y), norm_neg]
    exact hfA _ (hamp s ⟨hs.1.le, hs.2.trans ht.2⟩ y).le
  have hD := norm_oddDuhamelSolution_zero_le_quadratic_on_cone ht.1 x (fun s hs y _ ↦ hforce s hs y)
  change u (timeSpaceCons t x) = kirchhoffFormula g h x t + _ at he
  rw [he, add_sub_cancel_left]
  exact hD

/-- Compactly supported Cauchy data give arbitrarily small spatial tails on a short
initial time interval. -/
theorem exists_pos_uniform_tail_of_compact_cauchy_three {u : ℝ^4 → ℝ} {f : ℝ → ℝ} {g h : ℝ^3 → ℝ}
    {a b : ℝ} (hu : ContDiffOn ℝ 4 u {p | a < p 0 ∧ p 0 < b}) (ha : a < 0) (hb : 0 < b)
    (hf : Continuous f) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x)
    (hwave : ∀ t ∈ Ioo 0 b, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 δ, ∀ x : ℝ^3, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  obtain ⟨G, hG⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨K, hK⟩ := (hg.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hgc.fderiv ℝ)
  obtain ⟨B, hB⟩ := hh.continuous.bounded_above_of_compact_support hhc
  obtain ⟨d, hd, A, hA, _, herr⟩ := exists_pos_amplitude_and_retarded_bound_three
    hu ha hb hf hg hh hposition hinitial hG hK hB hwave
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 * A / 2 < ε := by
    have hc : Continuous (fun r : ℝ ↦ r ^ 2 * A / 2) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hright : ∀ᶠ r : ℝ in 𝓝[>] 0, r ^ 2 * A / 2 < ε := nhdsWithin_le_nhds hnear
  have htime : ∀ᶠ r : ℝ in 𝓝[>] 0, r < d := nhdsWithin_le_nhds (gt_mem_nhds hd.1)
  obtain ⟨δ, ⟨hδsmall, hδd⟩, hδ⟩ := ((hright.and htime).and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := hδ
  obtain ⟨Rg, _, hgR⟩ := hgc.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhc.exists_pos_le_norm
  let R := max Rg Rh
  refine ⟨δ, hδpos, R + δ, ?_⟩
  intro t ht x hx
  have hzero := SmallData.kirchhoffFormula_hasForwardSupport
    (hg.of_le (by norm_num)) hh.continuous
    (fun y hy ↦ hgR y (le_of_lt ((le_max_left Rg Rh).trans_lt hy)))
    (fun y hy ↦ hhR y (le_of_lt ((le_max_right Rg Rh).trans_lt hy))) t ht.1 x
    (by linarith [ht.2] : R + t < ‖x‖)
  have he := herr t ⟨ht.1, ht.2.trans hδd.le⟩ x
  change kirchhoffFormula g h x t = 0 at hzero
  rw [hzero, sub_zero] at he
  exact he.trans_lt ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1 ht.2 2) hA)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hδsmall)

end WaveEquation
