/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ZeroJet
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.LinearGrowth
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Integrable energy slices for continuous reactions

Separate compact displacement slices force the reaction to vanish at zero.
The differentiable-at-zero branch has linear growth; the other branch has a
zero time jet wherever the field vanishes. Together these give integrable
energy at every positive time, without assuming common support. Conservation
and the initial-time passage are not conclusions of these slice results.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation

/-- Compact slices on a nonempty open time interval force the reaction to
vanish at zero. Continuity in time suffices for the Baire support argument. -/
theorem reaction_zero_of_compact_slices {n : ℕ} [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {I : Set ℝ} (hI : IsOpen I) (hIn : I.Nonempty)
    (hu : ∀ x : ℝ^n, Continuous (fun t : I ↦ u (timeSpaceCons t x)))
    (hs : ∀ t : I, HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)))
    (hwave : ∀ t ∈ I, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0) :
    f 0 = 0 := by
  let : BaireSpace I := hI.baireSpace
  let : Nonempty I := hIn.to_subtype
  obtain ⟨a, R, hR⟩ := (dense_locally_uniform_spatial_support hu hs).nonempty
  have hR' := (eventually_nhds_subtype_iff I a
    (fun s ↦ ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0)).mp hR
  rw [hI.nhdsWithin_eq a.property] at hR'
  change ∀ᶠ s : ℝ in 𝓝 (a : ℝ), ∀ x : ℝ^n, (R : ℝ) < ‖x‖ → u (timeSpaceCons s x) = 0 at hR'
  have hgerm (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) :
      u =ᶠ[𝓝 (timeSpaceCons a x)] fun _ ↦ 0 := by
    have hproj : Tendsto (fun p : ℝ^(n + 1) ↦ p 0) (𝓝 (timeSpaceCons (a : ℝ) x)) (𝓝 (a : ℝ)) :=
      (show Continuous (fun p : ℝ^(n + 1) ↦ p 0) from
        (EuclideanSpace.proj 0).continuous).continuousAt
    have ht : ∀ᶠ p : ℝ^(n + 1) in 𝓝 (timeSpaceCons a x),
        ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons (p 0) y) = 0 :=
      hproj.eventually (p := fun s ↦ ∀ y : ℝ^n, (R : ℝ) < ‖y‖ → u (timeSpaceCons s y) = 0) hR'
    have hx' : ∀ᶠ p in 𝓝 (timeSpaceCons a x), (R : ℝ) < ‖spatialPart p‖ :=
      ((spatialPartCLM n).continuous.norm.continuousAt).eventually (lt_mem_nhds hx)
    filter_upwards [ht, hx'] with p hp hpx
    simpa only [timeSpaceCons_spatialPart] using hp (spatialPart p) hpx
  have hpos (x : ℝ^n) (hx : (R : ℝ) < ‖x‖) : u (timeSpaceCons a x) = 0 := (hgerm x hx).eq_of_nhds
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
  obtain ⟨x, hx⟩ := NormedSpace.exists_lt_norm ℝ (ℝ^n) (R : ℝ)
  have he := hwave a a.property x
  rwa [waveOperator_congr_nhds (hgerm x hx), waveOperator_const, hpos x hx, zero_add] at he

/-- Every positive-time energy slice is integrable for a normalized C¹ potential
and a C³ solution with separate compact displacement slices. -/
theorem integrable_semilinearWaveSpatialEnergyDensity_of_compact_slices
    {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)))
    {t : ℝ} (ht : 0 < t) : Integrable (semilinearWaveSpatialEnergyDensity V u t) := by
  -- In dimension zero the slice is a continuous function on a point.
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply Continuous.integrable_of_hasCompactSupport
    · exact (contDiff_semilinearWaveEnergyDensity hV (hu.of_le (by norm_num))).continuous.comp
        (contDiff_timeSpaceCons_spatial 0 t (m := 1)).continuous
    · exact isCompact_singleton.of_isClosed_subset (isClosed_tsupport _)
        fun x _ ↦ Set.mem_singleton_iff.mpr (Subsingleton.elim x (0 : ℝ^0))
  have : Fact (0 < n) := ⟨hn⟩
  by_cases hdiff : DifferentiableAt ℝ (deriv V) 0
  · have hfzero : deriv V 0 = 0 := reaction_zero_of_compact_slices
      isOpen_Ioi (show (Ioi (0 : ℝ)).Nonempty from ⟨1, by norm_num⟩) (fun x ↦ hu.continuous.comp
        ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
          (continuous_subtype_val.prodMk continuous_const)))
      (fun s ↦ hs s s.property.le) (fun s hsI x ↦ hwave s hsI x)
    have hlinear : deriv V =O[𝓝 0] (fun z : ℝ ↦ z) := by
      simpa only [hfzero, sub_zero] using hdiff.isBigO_sub
    have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
    have hf : Continuous (deriv V) := hV.continuous_deriv_one
    have hpde (s : ℝ) (hs' : 0 ≤ s) (x : ℝ^n) :=
      semilinearWaveOperator_eq_zero_of_nonneg hf hu2 hwave hs' x
    obtain ⟨R, _, hR⟩ := exists_uniform_support_on_Icc_of_compact_slices_of_isBigO
      hf hlinear hu2 (fun s hs' x ↦ add_eq_zero_iff_eq_neg.mp (hpde s hs' x)) hs
      (show 0 ≤ t + 1 by linarith)
    apply Continuous.integrable_of_hasCompactSupport
    · exact (contDiff_semilinearWaveEnergyDensity hV hu2).continuous.comp
        (contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
    · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) R) fun x hx ↦ ?_
      exact semilinearWaveSpatialEnergyDensity_eq_zero_off_support hVzero isOpen_Ioo
        Metric.isClosed_closedBall (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
        (fun s hsI y hy ↦ hR s ⟨hsI.1.le, hsI.2.le⟩ y
          (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy))
        (show t ∈ Ioo 0 (t + 1) by constructor <;> linarith) hx
  · apply integrable_semilinearWaveSpatialEnergyDensity_of_not_differentiable_reaction
      hdiff hV.continuous hVzero t (fun _ ↦ hu.contDiffAt) _ (hs t ht.le)
    intro x
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hsI using hwave s hsI x

/-- The positive-time energy slice is integrable using only closed-forward
C³ regularity and separately compact displacement. -/
theorem integrable_forwardSemilinearWaveEnergyDensity_of_compact_slices
    {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)))
    {t : ℝ} (ht : 0 < t) : Integrable (forwardSemilinearWaveEnergyDensity V u t) := by
  obtain ⟨U, hU, heq⟩ := PDE.Analysis.exists_contDiff_extension_halfSpace 0 3 hu
  have hi : Integrable (semilinearWaveSpatialEnergyDensity V U t) := by
    apply integrable_semilinearWaveSpatialEnergyDensity_of_compact_slices hV hVzero hU _ _ ht
    · intro s hs' x
      have hgerm := eventuallyEq_of_eqOn_forward heq
        (show 0 < (timeSpaceCons s x) 0 by simpa only [timeSpaceCons_zero] using hs')
      unfold semilinearWaveOperator
      rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
      exact hwave s hs' x
    · intro s hs'
      have he : (fun x : ℝ^n ↦ U (timeSpaceCons s x)) =
          (fun x : ℝ^n ↦ u (timeSpaceCons s x)) := by
        funext x
        exact heq (by change 0 ≤ s; exact hs')
      rw [he]
      exact hs s hs'
  apply hi.congr
  exact Eventually.of_forall fun x ↦ (forwardSemilinearWaveEnergyDensity_eq_of_extension V
      (hU.of_le (by norm_num)) heq ht.le x).symm

end WaveEquation
