/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialCompactness
import PDE.FDeriv.PartialDeriv.Transforms
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.SupportPropagation
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Propagating short-time spatial tails to finite forward bands

A solution with compact Cauchy data has small spatial tails on a short initial time
interval. This short-time estimate is the hypothesis `hshort`, the only input that
depends on the space dimension. Translation and reflection in time give tail
estimates on two-sided neighborhoods of positive times, and a finite subcover of
`[0, T]` makes them uniform. A smooth extension handles fields given only on the
closed forward half-space.
-/

@[expose] public noncomputable section

open Set Filter PDE PDE.Common
open scoped Topology

namespace WaveEquation

section Propagation

variable {n : ℕ} [Fact (0 < n)] {f : ℝ → ℝ}
  (hshort : ∀ {v : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ} {b : ℝ},
    ContDiff ℝ 4 v → 0 < b → Continuous f →
    ContDiff ℝ 3 g → ContDiff ℝ 2 h → HasCompactSupport g → HasCompactSupport h →
    (∀ x, v (timeSpaceCons 0 x) = g x) →
    (∀ x, (∂[0] v) (timeSpaceCons 0 x) = h x) →
    (∀ t ∈ Ioo 0 b, ∀ x,
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0) →
    ∀ {ε : ℝ}, 0 < ε → ∃ δ > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 δ, ∀ x : ℝ^n,
      R < ‖x‖ → ‖v (timeSpaceCons t x)‖ < ε)

include hshort

/-- If every displacement slice at a nonnegative time has compact support, the spatial
tails are uniformly small on a neighborhood of each time `a ≥ 0`. The time-reflected
solution is used only at positive times, where the equation holds. -/
theorem exists_uniform_tail_near_of_compact_slices_of_short_time {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 4 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {a ε : ℝ}
    (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, ∀ t ∈ Icc (max 0 (a - δ)) (a + δ), ∀ x : ℝ^n, R < ‖x‖ →
      ‖u (timeSpaceCons t x)‖ < ε := by
  let v : ℝ^(n + 1) → ℝ := fun p ↦ u (p + a • EuclideanSpace.single 0 1)
  have hv : ContDiff ℝ 4 v := hu.comp (contDiff_id.add contDiff_const)
  have hshift (t : ℝ) (x : ℝ^n) :
      timeSpaceCons t x + a • EuclideanSpace.single 0 1 = timeSpaceCons (t + a) x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hw (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0 := by
    simpa only [v, waveOperator, partialDeriv_comp_add_right, hshift] using
      hwave (t + a) (add_pos_of_pos_of_nonneg ht ha) x
  have hc (t : ℝ) (ht : 0 ≤ t) :
      HasCompactSupport (fun x : ℝ^n ↦ v (timeSpaceCons t x)) := by
    simpa only [v, hshift] using hs (t + a) (add_nonneg ht ha)
  let g : ℝ^n → ℝ := fun x ↦ v (timeSpaceCons 0 x)
  let h : ℝ^n → ℝ := fun x ↦ (∂[0] v) (timeSpaceCons 0 x)
  have hg : ContDiff ℝ 3 g :=
    (hv.of_le (by norm_num)).comp (contDiff_timeSpaceCons_spatial n 0)
  have hh : ContDiff ℝ 2 h :=
    (hv.partialDeriv 0 (k := 2) (by norm_num)).comp (contDiff_timeSpaceCons_spatial n 0)
  have hgc : HasCompactSupport g := hc 0 le_rfl
  have hhc : HasCompactSupport h := hasCompactSupport_initial_velocity_of_compact_slices
    hf (hv.of_le (by norm_num)) hw hc
  obtain ⟨δf, hδf, Rf, htf⟩ := hshort
    (b := 1) hv (by norm_num) hf hg hh hgc hhc (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun t ht x ↦ hw t ht.1 x) hε
  have hforward (t : ℝ) (ht : t ∈ Icc a (a + δf)) (x : ℝ^n) (hx : Rf < ‖x‖) :
      ‖u (timeSpaceCons t x)‖ < ε := by
    have he := htf (t - a) (by constructor <;> linarith [ht.1, ht.2]) x hx
    simpa only [v, hshift, sub_add_cancel] using he
  by_cases hazero : a = 0
  · subst a
    refine ⟨δf, hδf, Rf, ?_⟩
    intro t ht x hx
    exact hforward t ⟨(le_max_left _ _).trans ht.1, ht.2⟩ x hx
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hazero)
  let w : ℝ^(n + 1) → ℝ := fun p ↦ v (coordinateReflection 0 p)
  have hwreg : ContDiff ℝ 4 w := hv.comp
    (coordinateReflectionLinearIsometryEquiv 0).toContinuousLinearEquiv.contDiff
  have hreflect (t : ℝ) (x : ℝ^n) :
      coordinateReflection 0 (timeSpaceCons t x) = timeSpaceCons (-t) x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hweq (t : ℝ) (ht : t ∈ Ioo 0 a) (x : ℝ^n) :
      waveOperator w (timeSpaceCons t x) + f (w (timeSpaceCons t x)) = 0 := by
    rw [show waveOperator w (timeSpaceCons t x) =
      waveOperator v (coordinateReflection 0 (timeSpaceCons t x)) from
        waveOperator_comp_timeReflection (hv.of_le (by norm_num)) _]
    simpa only [w, v, hreflect, waveOperator, partialDeriv_comp_add_right, hshift] using
      hwave (-t + a) (by linarith [ht.2]) x
  have hwpos (x : ℝ^n) : w (timeSpaceCons 0 x) = g x := by
    simp only [w, hreflect, neg_zero, g]
  have hwvel (x : ℝ^n) : (∂[0] w) (timeSpaceCons 0 x) = -h x := by
    rw [show (∂[0] w) (timeSpaceCons 0 x) =
      -(∂[0] v) (coordinateReflection 0 (timeSpaceCons 0 x)) from
        partialDeriv_comp_coordinateReflection_same 0 v _
          (hv.differentiable (by norm_num)).differentiableAt, hreflect, neg_zero]
  obtain ⟨δb, hδb, Rb, htb⟩ := hshort (b := a) hwreg hapos
    hf hg hh.neg hgc (hhc.comp_left (g := fun z : ℝ ↦ -z) (by simp)) hwpos hwvel hweq hε
  refine ⟨min δf δb, lt_min hδf hδb, max Rf Rb, ?_⟩
  intro t ht x hx
  by_cases hat : a ≤ t
  · exact hforward t ⟨hat, by linarith [ht.2, min_le_left δf δb]⟩ x
      ((le_max_left Rf Rb).trans_lt hx)
  · have htime : a - t ∈ Icc 0 δb := by
      have hlo := (le_max_right 0 (a - min δf δb)).trans ht.1
      constructor <;> linarith [min_le_right δf δb]
    have he := htb (a - t) htime x ((le_max_right Rf Rb).trans_lt hx)
    have heq : -(a - t) + a = t := by abel
    simpa only [w, hreflect, v, hshift, heq] using he

/-- The radius for a small spatial tail is uniform on every finite forward
band, although each displacement slice has its own compact support. -/
theorem exists_uniform_tail_on_Icc_of_compact_slices_of_short_time {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 4 u) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  classical
  choose δ hδ R hR using fun a : Icc (0 : ℝ) T ↦
    exists_uniform_tail_near_of_compact_slices_of_short_time hshort hu hf hwave hs a.property.1 hε
  obtain ⟨S, hS⟩ := isCompact_Icc.elim_finite_subcover
    (fun a : Icc (0 : ℝ) T ↦ Ioo ((a : ℝ) - δ a) ((a : ℝ) + δ a)) (fun _ ↦ isOpen_Ioo) (fun t ht ↦
      mem_iUnion.mpr ⟨⟨t, ht⟩, by constructor <;> linarith [hδ ⟨t, ht⟩]⟩)
  refine ⟨∑ a ∈ S, max (R a) 0, ?_⟩
  intro t ht x hx
  obtain ⟨a, haS, hta⟩ := mem_iUnion₂.mp (hS ht)
  have hRa : R a ≤ ∑ b ∈ S, max (R b) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (fun b _ ↦ le_max_right (R b) 0) haS)
  apply hR a t ⟨max_le ht.1 hta.1.le, hta.2.le⟩ x
  exact hRa.trans_lt hx

/-- Uniform spatial tails on `[0, T]` for a field that is `C⁴` on the closed forward
half-space and satisfies the equation at positive times. -/
theorem exists_uniform_tail_on_Icc_of_forward_compact_slices_of_short_time {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0}) (hf : Continuous f)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^n, waveOperator u (timeSpaceCons t x) +
      f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 4 hu
  have hw (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
      waveOperator U (timeSpaceCons t x) + f (U (timeSpaceCons t x)) = 0 := by
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons t x) 0 by simpa only [timeSpaceCons_zero] using ht)
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave t ht x
  have hc (t : ℝ) (ht : 0 ≤ t) :
      HasCompactSupport (fun x : ℝ^n ↦ U (timeSpaceCons t x)) := by
    have hslice : (fun x : ℝ^n ↦ U (timeSpaceCons t x)) = fun x : ℝ^n ↦ u (timeSpaceCons t x) :=
      funext fun x ↦ heq (show 0 ≤ (timeSpaceCons t x) 0 by
        simpa only [timeSpaceCons_zero] using ht)
    rw [hslice]
    exact hs t ht
  obtain ⟨R, hR⟩ := exists_uniform_tail_on_Icc_of_compact_slices_of_short_time
    hshort hU hf hw hc T hε
  refine ⟨R, fun t ht x hx ↦ ?_⟩
  have he := heq (show 0 ≤ (timeSpaceCons t x) 0 by
    simpa only [timeSpaceCons_zero] using ht.1)
  simpa only [he] using hR t ht x hx

end Propagation

/-- Uniform spatial tails and continuity bound the amplitude on a finite
forward band, by compactness of the remaining cylinder. -/
theorem exists_uniform_amplitude_on_Icc_of_uniform_tails {n : ℕ} {u : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hu : ContinuousOn u {p | 0 ≤ p 0})
    (htail : ∀ ε > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε) :
    ∃ M ≥ 0, ∀ t ∈ Icc 0 T, ∀ x : ℝ^n, ‖u (timeSpaceCons t x)‖ ≤ M := by
  obtain ⟨R, hR⟩ := htail 1 (by norm_num)
  have hcompact : IsCompact (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : ℝ^n) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : ℝ^n) R)
  have hc : ContinuousOn (fun p : ℝ × ℝ^n ↦ u (timeSpaceCons p.1 p.2))
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : ℝ^n) R) :=
    hu.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousOn (fun p hp ↦ hp.1.1)
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hc
  refine ⟨max B 1, (by positivity), ?_⟩
  intro t ht x
  by_cases hx : ‖x‖ ≤ R
  · exact (hB (t, x)
      ⟨ht, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx⟩).trans (le_max_left _ _)
  · exact (hR t ht x (lt_of_not_ge hx)).le.trans (le_max_right _ _)

/-- A potential continuous at zero and vanishing there inherits uniform spatial tails.
The conclusion uses the non-strict threshold `B ≤ ‖x‖`, as needed on closed annuli. -/
theorem exists_uniform_potential_tail_on_Icc_of_uniform_tails {n : ℕ} {u : ℝ^(n + 1) → ℝ}
    {V : ℝ → ℝ} {s t ε : ℝ}
    (htail : ∀ η > 0, ∃ R : ℝ, ∀ r ∈ Icc 0 t, ∀ x : ℝ^n, R < ‖x‖ → ‖u (timeSpaceCons r x)‖ < η)
    (hV : ContinuousAt V 0) (hV0 : V 0 = 0) (hs0 : 0 ≤ s) (hε : 0 < ε) :
    ∃ B : ℝ, ∀ r ∈ Icc s t, ∀ x : ℝ^n, B ≤ ‖x‖ → |V (u (timeSpaceCons r x))| ≤ ε := by
  obtain ⟨η, hη, hsmall⟩ := Metric.continuousAt_iff.mp hV ε hε
  obtain ⟨R, hR⟩ := htail η hη
  refine ⟨R + 1, ?_⟩
  intro r hr x hx
  have ht := hR r ⟨hs0.trans hr.1, hr.2⟩ x (by linarith)
  have he := hsmall (by simpa only [dist_zero_right] using ht)
  have hv : |V (u (timeSpaceCons r x))| < ε := by
    simpa only [hV0, dist_zero_right, Real.norm_eq_abs] using he
  exact hv.le

end WaveEquation
