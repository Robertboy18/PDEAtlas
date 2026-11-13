/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialGrowth
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialSupport
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.IntegrableSlices
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialData
import PDE.Hyperbolic.NonlinearWave.PositivePart
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Compact initial velocity from separate compact displacement slices

For a continuous reaction, a C3 forward solution with compact displacement at
each time has compact right velocity at time zero. If the reaction is
differentiable at zero, linear-growth propagation applies. Otherwise,
the PDE forces full zero first jets at positive-time zeros. A sign with no
right-sided growth bound cannot have a positive initial velocity off the initial
displacement support. A sign with such a bound has a C2 positive-part wave;
propagation from time one bounds its support down to every positive time.
Applying the argument to both signs gives compact initial velocity.

The compact-data theorem then gives integrable initial physical energy
for a normalized C1 potential. Neither energy continuity nor vanishing flux at
infinity is asserted.
-/

@[expose] public noncomputable section

open Filter Set PDE PDE.Common
open scoped Topology

namespace WaveEquation

/-- A nonpositive right germ at zero has nonpositive initial time derivative. -/
theorem initial_velocity_nonpos_of_right_germ {n : ℕ} {u : ℝ^(n + 1) → ℝ} {x : ℝ^n}
    (hu : DifferentiableAt ℝ u (timeSpaceCons 0 x)) (hzero : u (timeSpaceCons 0 x) = 0)
    (hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), u (timeSpaceCons t x) ≤ 0) :
    (∂[0] u) (timeSpaceCons 0 x) ≤ 0 := by
  have hd := (hasDerivAt_timeSpaceCons u 0 x hu).tendsto_slope_zero_right
  apply le_of_tendsto hd
  filter_upwards [hneg, eventually_mem_nhdsWithin] with t ht htpos
  simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htpos.le) ht

/-- The zero first jet at positive times gives an upper bound of zero for the
initial velocity outside a ball, using a positive-part wave when needed. -/
theorem exists_initial_velocity_nonpos_of_zero_jet {n : ℕ} [Fact (0 < n)] {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : Continuous f) (hfzero : f 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 ≤ t → ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs0 : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons 0 x)))
    (hs1 : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons 1 x)))
    (hz : ∀ p, 0 < p 0 → u p = 0 → fderiv ℝ u p = 0) :
    ∃ R : ℝ, ∀ x : ℝ^n, R < ‖x‖ → (∂[0] u) (timeSpaceCons 0 x) ≤ 0 := by
  obtain ⟨R, hR⟩ := hs0.isCompact.isBounded.subset_closedBall (0 : ℝ^n)
  have hzero (x : ℝ^n) (hx : R < ‖x‖) : u (timeSpaceCons 0 x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := fun y : ℝ^n ↦ u (timeSpaceCons 0 y))
    intro hxmem
    have hn : ‖x‖ ≤ R := by simpa using hR hxmem
    exact hx.not_ge hn
  by_cases hright : f =O[𝓝[≥] 0] (fun z : ℝ ↦ z)
  · have hopen : IsOpen {p : ℝ^(n + 1) | 0 < p 0} :=
      isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
    have hlocal (p : ℝ^(n + 1)) (hp : 0 < p 0) :
        ∀ᶠ q in 𝓝 p, u q = 0 → fderiv ℝ u q = 0 := by
      have ht : ∀ᶠ q in 𝓝 p, 0 < q 0 := hopen.mem_nhds hp
      exact ht.mono fun q hq ↦ hz q hq
    have hplus : ContDiffOn ℝ 2 (fun p ↦ max (u p) 0) {p | 0 < p 0} :=
      PDE.Analysis.contDiffOn_two_max_zero_of_zero_jet hopen
        (hu.of_le (by norm_num)).contDiffOn hz
    have hpde (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
        waveOperator (fun p ↦ max (u p) 0) (timeSpaceCons t x) =
          -f (max (max (u (timeSpaceCons t x)) 0) 0) := by
      apply add_eq_zero_iff_eq_neg.mp
      exact semilinearWave_max_zero_of_zero_jet
        (hu.of_le (by norm_num)).contDiffAt
        (hlocal _ (by simpa only [timeSpaceCons_zero] using ht)) hfzero (hwave t ht.le x)
    obtain ⟨S, hS⟩ := exists_uniform_support_near_initial_of_nonneg
      (hf.comp (continuous_id.max continuous_const))
      (PDE.Analysis.isBigO_max_zero_of_isBigO_right hright) hplus
      (fun p _ ↦ le_max_right (u p) 0) hpde
      (hs1.comp_left (g := fun z : ℝ ↦ max z 0) (by simp))
    refine ⟨max R S, fun x hx ↦ ?_⟩
    apply initial_velocity_nonpos_of_right_germ
      (hu.differentiable (by norm_num)).differentiableAt (hzero x ((le_max_left R S).trans_lt hx))
    have ht1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [eventually_mem_nhdsWithin, ht1] with t ht ht1
    have he := hS t ⟨ht, ht1.le⟩ x ((le_max_right R S).trans_lt hx)
    exact (le_max_left _ _).trans he.le
  · refine ⟨R, fun x hx ↦ le_of_not_gt fun hv ↦ hright ?_⟩
    apply isBigO_reaction_right_of_pos_initial_velocity hfzero hu.contDiffAt
      (eventually_mem_nhdsWithin.mono fun t ht ↦ hwave t ht x) (hzero x hx) hv


/-- Separate compact displacement slices force compact initial velocity for a
C3 solution with continuous reaction. -/
theorem hasCompactSupport_initial_velocity_of_compact_slices {n : ℕ} [Fact (0 < n)] {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : Continuous f) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    HasCompactSupport (fun x : ℝ^n ↦ (∂[0] u) (timeSpaceCons 0 x)) := by
  have hfzero : f 0 = 0 := reaction_zero_of_compact_slices
    isOpen_Ioi (show (Ioi (0 : ℝ)).Nonempty from ⟨1, by norm_num⟩) (fun x ↦ hu.continuous.comp
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_subtype_val.prodMk continuous_const))) (fun s ↦ hs s s.property.le) hwave
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hpde (t : ℝ) (ht : 0 ≤ t) (x : ℝ^n) := waveOperator_add_eq_zero_of_nonneg hf hu2 hwave ht x
  by_cases hdiff : DifferentiableAt ℝ f 0
  · have hlinear : f =O[𝓝 0] (fun z : ℝ ↦ z) := by
      simpa only [hfzero, sub_zero] using hdiff.isBigO_sub
    obtain ⟨R, _, hR⟩ := exists_uniform_support_on_Icc_of_compact_slices_of_isBigO
      hf hlinear hu2 (fun t ht x ↦ add_eq_zero_iff_eq_neg.mp (hpde t ht x)) hs
      (show (0 : ℝ) ≤ 1 by norm_num)
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) R)
    intro x hx
    have hxR : R < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hz := hR 0 ⟨le_rfl, by norm_num⟩ x hxR
    have hgerm : ∀ᶠ t in 𝓝[>] (0 : ℝ), u (timeSpaceCons t x) = 0 := by
      have ht1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      filter_upwards [eventually_mem_nhdsWithin, ht1] with t ht ht1
      exact hR t ⟨ht.le, ht1.le⟩ x hxR
    apply le_antisymm
    · exact initial_velocity_nonpos_of_right_germ
        (hu.differentiable (by norm_num)).differentiableAt hz (hgerm.mono fun _ he ↦ he.le)
    · have hn := initial_velocity_nonpos_of_right_germ
        (u := -u) (x := x) (hu.neg.differentiable (by norm_num)).differentiableAt
        (by simp only [Pi.neg_apply, hz, neg_zero])
        (hgerm.mono fun _ he ↦ by simp only [Pi.neg_apply, he, neg_zero, le_refl])
      simpa only [partialDeriv_neg, neg_nonpos] using hn
  · have hjet (p : ℝ^(n + 1)) (hp : 0 < p 0) (hz : u p = 0) :
        fderiv ℝ u p = 0 := by
      apply fderiv_eq_zero_of_not_differentiable_reaction hdiff hu.contDiffAt _ hz
      have ht : ∀ᶠ q : ℝ^(n + 1) in 𝓝 p, 0 < q 0 :=
        (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds hp
      filter_upwards [ht] with q hq
      simpa only [timeSpaceCons_spatialPart] using hwave (q 0) hq (spatialPart q)
    obtain ⟨R, hR⟩ := exists_initial_velocity_nonpos_of_zero_jet hf hfzero hu hpde
      (hs 0 le_rfl) (hs 1 (by norm_num)) hjet
    have hpdeneg (t : ℝ) (ht : 0 ≤ t) (x : ℝ^n) : waveOperator (-u) (timeSpaceCons t x) +
          (fun z ↦ -f (-z)) ((-u) (timeSpaceCons t x)) = 0 := by
      have he := waveOperator_const_mul (-1) u (timeSpaceCons t x)
      simp only [neg_one_mul] at he
      change waveOperator (fun p ↦ -u p) (timeSpaceCons t x) + -f (-(-u (timeSpaceCons t x))) = 0
      rw [he]
      simpa only [Pi.neg_apply, neg_neg, ← neg_add, neg_eq_zero] using hpde t ht x
    obtain ⟨S, hS⟩ := exists_initial_velocity_nonpos_of_zero_jet (u := -u) (f := fun z ↦ -f (-z))
      (hf.comp continuous_neg).neg (by simp only [neg_zero, hfzero]) hu.neg hpdeneg
      ((hs 0 le_rfl).comp_left (g := fun z : ℝ ↦ -z) (by simp))
      ((hs 1 (by norm_num)).comp_left (g := fun z : ℝ ↦ -z) (by simp))
      (fun p hp hz ↦ by
        rw [fderiv_neg, hjet p hp (neg_eq_zero.mp hz), neg_zero])
    apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) (max R S))
    intro x hx
    have hxRS : max R S < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    apply le_antisymm (hR x ((le_max_left R S).trans_lt hxRS))
    have hn := hS x ((le_max_right R S).trans_lt hxRS)
    simpa only [partialDeriv_neg, neg_nonpos] using hn


/-- The right velocity is the velocity of any smooth forward extension. -/
private theorem initial_right_velocity_eq_of_extension {n : ℕ} {u U : ℝ^(n + 1) → ℝ}
    (hU : ContDiff ℝ 1 U) (heq : EqOn U u {p | 0 ≤ p 0}) (x : ℝ^n) :
    derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = (∂[0] U) (timeSpaceCons 0 x) := by
  have hd := (hasDerivAt_timeSpaceCons U 0 x
    (hU.differentiable one_ne_zero).differentiableAt).hasDerivWithinAt (s := Ici 0)
  have he : EqOn (fun t ↦ u (timeSpaceCons t x))
      (fun t ↦ U (timeSpaceCons t x)) (Ici 0) := by
    intro t ht
    exact (heq (show 0 ≤ (timeSpaceCons t x) 0 by simpa using ht)).symm
  exact (hd.congr_of_mem he (by simp)).derivWithin (uniqueDiffWithinAt_Ici 0)

/-- Closed-forward C3 regularity and separate compact displacement slices imply
compact support of the right velocity. -/
theorem hasCompactSupport_initial_right_velocity_of_compact_slices {n : ℕ} [Fact (0 < n)]
    {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hf : Continuous f) (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    HasCompactSupport (fun x : ℝ^n ↦ derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0) := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 3 hu
  have hcompact : HasCompactSupport (fun x : ℝ^n ↦ (∂[0] U) (timeSpaceCons 0 x)) := by
    apply hasCompactSupport_initial_velocity_of_compact_slices hf hU
    · intro t ht x
      have hgerm := eventuallyEq_of_eqOn_forward heq
        (show 0 < (timeSpaceCons t x) 0 by simpa using ht)
      rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
      exact hwave t ht x
    · intro t ht
      have hslice : (fun x : ℝ^n ↦ U (timeSpaceCons t x)) =
          (fun x : ℝ^n ↦ u (timeSpaceCons t x)) := by
        funext x
        exact heq (show 0 ≤ (timeSpaceCons t x) 0 by simpa using ht)
      rw [hslice]
      exact hs t ht
  have he : (fun x : ℝ^n ↦ derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0) =
      (fun x : ℝ^n ↦ (∂[0] U) (timeSpaceCons 0 x)) :=
    funext fun x ↦ initial_right_velocity_eq_of_extension (hU.of_le (by norm_num)) heq x
  rw [he]
  exact hcompact

/-- A normalized C1 potential and the separate compact-slice hypotheses
imply integrable initial physical energy. -/
theorem integrable_forwardSemilinearWaveEnergyDensity_initial_of_compact_slices {n : ℕ}
    [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    MeasureTheory.Integrable (forwardSemilinearWaveEnergyDensity V u 0) := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 3 hu
  have hvel (x : ℝ^n) :=
    initial_right_velocity_eq_of_extension (hU.of_le (by norm_num)) heq x
  have hhc : HasCompactSupport (fun x : ℝ^n ↦ (∂[0] U) (timeSpaceCons 0 x)) := by
    have hc := hasCompactSupport_initial_right_velocity_of_compact_slices
      hV.continuous_deriv_one hu hwave hs
    have he : (fun x : ℝ^n ↦ derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0) =
        (fun x : ℝ^n ↦ (∂[0] U) (timeSpaceCons 0 x)) := funext hvel
    rwa [he] at hc
  have hslice : (fun x : ℝ^n ↦ u (timeSpaceCons 0 x)) =
      (fun x : ℝ^n ↦ U (timeSpaceCons 0 x)) := by
    funext x
    exact (heq (show 0 ≤ (timeSpaceCons 0 x) 0 by simp)).symm
  apply integrable_forwardSemilinearWaveEnergyDensity_initial_of_compact_data
    (T := 1) (g := fun x ↦ U (timeSpaceCons 0 x)) (h := fun x ↦ (∂[0] U) (timeSpaceCons 0 x))
    (by norm_num) hV.continuous hVzero
    ((hu.of_le (by norm_num)).mono fun _ hp ↦ hp.1)
    ((hU.of_le (by norm_num)).comp (contDiff_timeSpaceCons_spatial n 0))
    (((hU.of_le (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)).partialDeriv 0).continuous.comp
      (contDiff_timeSpaceCons_spatial n 0 (m := 1)).continuous)
    (by rw [← hslice]; exact hs 0 le_rfl) hhc (congrFun hslice) hvel

end WaveEquation
