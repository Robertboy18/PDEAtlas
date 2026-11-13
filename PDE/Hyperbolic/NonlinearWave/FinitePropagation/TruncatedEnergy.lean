/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.LocalDivergence
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeFlux
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Physical energy conservation on truncated cones

The local energy current is integrated only between interior times of an open
band. Its nonnegative null flux controls the remaining energy without requiring
regularity at the vertex or any global support hypothesis.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped RealInnerProductSpace Topology ENNReal

namespace WaveEquation

variable {n : ℕ}

/-- The null energy density is nonnegative for a nonnegative potential. -/
theorem semilinearWaveConeDissipation_nonneg {V : ℝ → ℝ} (hV : ∀ z, 0 ≤ V z) (u : ℝ^(n + 1) → ℝ)
    (c : ℝ^n) (p : ℝ^(n + 1)) :
    0 ≤ semilinearWaveConeDissipation V u c p :=
  add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hV _)

/-- The cap energies and lateral flux balance the work of the wave-equation
residual. This form also applies to smooth approximations of a solution. -/
theorem ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual [Fact (0 < n)] {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) {u : ℝ^(n + 1) → ℝ} {s₀ s τ T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s) (hsτ : s ≤ τ)
    (hτ : τ < T) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) +
        ∫ t in s..τ, ballIntegral n
          (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x))
          c (T - t) := by
  let P := semilinearWaveEnergyDensity V u
  let Q (p : ℝ^(n + 1)) : ℝ^n := WithLp.toLp 2 (fun i ↦ classicalWaveEnergyFlux u i p)
  have hopen : IsOpen {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hP : ContDiffOn ℝ 1 P {p | s₀ < p 0 ∧ p 0 < T} := by
    intro p hp
    exact (contDiffAt_semilinearWaveEnergyDensity hV.contDiffAt
      (hu.contDiffAt (hopen.mem_nhds hp))).contDiffWithinAt
  have hQ : ContDiffOn ℝ 1 Q {p | s₀ < p 0 ∧ p 0 < T} := by
    intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_piLp 2).mpr
    exact fun i ↦ contDiffAt_classicalWaveEnergyFlux (hu.contDiffAt (hopen.mem_nhds hp)) i
  have hres : (∫ t in s..τ, ∫ x in Metric.ball c (T - t),
      (∂[0] P) (timeSpaceCons t x) - ∇· (fun y ↦ Q (timeSpaceCons t y)) x) =
      ∫ t in s..τ, ballIntegral n
        (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x))
        c (T - t) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hsτ] at ht
    refine setIntegral_congr_fun measurableSet_ball fun x _ ↦ ?_
    have hup := hu.contDiffAt (hopen.mem_nhds
      (show s₀ < (timeSpaceCons t x) 0 ∧ (timeSpaceCons t x) 0 < T by
        simpa only [timeSpaceCons_zero] using And.intro (hs.trans_le ht.1) (ht.2.trans_lt hτ)))
    have hdiv : ∇· (fun y ↦ Q (timeSpaceCons t y)) x =
        ∑ i : Fin n, (∂[i.succ] (classicalWaveEnergyFlux u i)) (timeSpaceCons t x) := by
      unfold divergence
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact partialDeriv_timeSpaceCons_spatial i _ t x
        ((contDiffAt_classicalWaveEnergyFlux hup i).differentiableAt one_ne_zero)
    rw [hdiv]
    exact (semilinearWaveEnergyBalanceResidual_eq_partialDeriv_sub_sum hV hup).symm
  have hsurface : (∫ p in truncatedConeLateralSurface c T s τ,
      (P p - ⟪Q p, NormedSpace.normalize (spatialPart p - c)⟫)
        ∂Measure.euclideanHausdorffMeasure n) = ∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n := by
    apply setIntegral_congr_fun (isCompact_truncatedConeLateralSurface c T s τ).measurableSet
    intro p hp
    have hx : spatialPart p ≠ c := by
      intro hx
      have hz : ‖spatialPart p - c‖ = 0 := by rw [hx, sub_self, norm_zero]
      have hpos : 0 < T - p 0 := sub_pos.mpr (hp.2.1.trans_lt hτ)
      rw [hp.2.2] at hz
      exact hpos.ne' hz
    have h := semilinearWaveConeBoundaryFlux_eq_neg_dissipation V u c (spatialPart p) (p 0) hx
    have hQeq : Q p = (∂[0] u) p • classicalWaveSpatialGradient u p := by
      ext i
      rfl
    dsimp only
    rw [hQeq, real_inner_smul_left]
    simp only [semilinearWaveConeBoundaryFlux, classicalWaveConeBoundaryFlux,
      timeSpaceCons_spatialPart] at h
    dsimp only [P, semilinearWaveEnergyDensity]
    linarith
  have h := integral_divergence_truncatedCone_of_contDiffOn_band hP hQ c hs hsτ hτ
  rw [hres, hsurface] at h
  change _ + _ = _
  dsimp only [P] at h
  unfold ballIntegral at h ⊢
  linarith

/-- Physical energy at the top plus normalized lateral null flux equals energy
at the bottom. The field is smooth only on an open time band around the caps. -/
theorem ballIntegral_energy_add_truncatedCone_flux [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    {u : ℝ^(n + 1) → ℝ} {s₀ s τ T : ℝ} (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n)
    (hs : s₀ < s) (hsτ : s ≤ τ) (hτ : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  have hopen : IsOpen {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hzero : (∫ t in s..τ, ballIntegral n
      (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x)) c (T - t)) = 0 := by
    rw [intervalIntegral.integral_of_le hsτ]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ ?_
    have ht : t ∈ Icc s τ := ⟨ht.1.le, ht.2⟩
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    have hup := hu.contDiffAt (hopen.mem_nhds
      (show s₀ < (timeSpaceCons t x) 0 ∧ (timeSpaceCons t x) 0 < T by
        simpa only [timeSpaceCons_zero] using And.intro (hs.trans_le ht.1) (ht.2.trans_lt hτ)))
    exact semilinearWaveEnergyBalanceResidual_eq_zero hV hup (hwave t ht x hx)
  simpa only [hzero, add_zero] using
    ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual hV hu c hs hsτ hτ

/-- On a defocusing wave, energy in later shrinking balls is no larger. -/
theorem ballIntegral_energy_le_of_le [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {s₀ s τ T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s) (hsτ : s ≤ τ)
    (hτ : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) ≤
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  have h := ballIntegral_energy_add_truncatedCone_flux hV hu c hs hsτ hτ hwave
  have hflux : 0 ≤ (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) :=
    mul_nonneg (by positivity) (integral_nonneg fun p ↦
      semilinearWaveConeDissipation_nonneg hVnonneg u c p)
  linarith

/-- The normalized lateral energy flux is bounded by the bottom cap energy. -/
theorem integral_truncatedCone_flux_le_energy [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {s₀ s τ T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s) (hsτ : s ≤ τ)
    (hτ : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
      semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) ≤
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  have h := ballIntegral_energy_add_truncatedCone_flux hV hu c hs hsτ hτ hwave
  have henergy : 0 ≤ ballIntegral n
      (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) :=
    integral_nonneg fun x ↦ semilinearWaveEnergyDensity_nonneg V hVnonneg u _
  linarith

/-- The null flux is integrable on each closed truncated lateral cone.
The upper cap stays strictly below the vertex, where the radial normal is smooth. -/
theorem integrableOn_truncatedCone_dissipation {V : ℝ → ℝ} (hV : Continuous V) {u : ℝ^(n + 1) → ℝ}
    {s₀ s τ T : ℝ} (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s)
    (hτ : τ < T) :
    IntegrableOn (semilinearWaveConeDissipation V u c) (truncatedConeLateralSurface c T s τ)
      (Measure.euclideanHausdorffMeasure n) := by
  let Γ := truncatedConeLateralSurface c T s τ
  have hΓ : IsCompact Γ := isCompact_truncatedConeLateralSurface c T s τ
  have hopen : IsOpen {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hc : ContinuousOn (semilinearWaveConeDissipation V u c) Γ := by
    intro p hp
    have hup := hu.contDiffAt (hopen.mem_nhds ⟨hs.trans_le hp.1, hp.2.1.trans_lt hτ⟩)
    have hx : ContinuousAt (fun q : ℝ^(n + 1) ↦ spatialPart q - c) p :=
      ((spatialPartCLM n).continuous.sub continuous_const).continuousAt
    have hn : ‖spatialPart p - c‖ ≠ 0 := by
      rw [hp.2.2]
      exact (sub_pos.mpr (hp.2.1.trans_lt hτ)).ne'
    have hν := (hx.norm.inv₀ hn).smul hx
    exact ((continuousAt_const.mul ((((contDiffAt_partialDeriv 1 hup 0).continuousAt.smul hν).sub
        ((contDiffAt_piLp 2).mpr (fun i : Fin n ↦
          contDiffAt_partialDeriv 1 hup i.succ)).continuousAt).norm.pow 2)).add
          (hV.continuousAt.comp hup.continuousAt)).continuousWithinAt
  have hfinite : Measure.euclideanHausdorffMeasure n Γ ≠ ∞ := by
    obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
    have hbound := hK.lipschitzOnWith.euclideanHausdorffMeasure_image_le
      (s := Metric.closedBall c (T - s)) n
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hbound
    have hsub : Γ ⊆ backwardConeGraph c T '' Metric.closedBall c (T - s) := by
      rw [show Γ = _ from truncatedConeLateralSurface_eq_image c T s τ]
      exact image_mono sdiff_subset
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by finiteness)
      (isCompact_closedBall c (T - s)).measure_ne_top) ((measure_mono hsub).trans hbound)
  exact hc.integrableOn_of_subset_isCompact hΓ hΓ.measurableSet Subset.rfl hfinite

/-- Physical energy decreases throughout the open regularity band. -/
theorem ballIntegral_energy_antitoneOn [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {s₀ T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n)
    (hwave : ∀ t ∈ Ioo s₀ T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    AntitoneOn (fun t ↦ ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x))
      c (T - t)) (Ioo s₀ T) := by
  intro s hs τ hτ hsτ
  exact ballIntegral_energy_le_of_le hV hVnonneg hu c hs.1 hsτ hτ.2
    (fun t ht ↦ hwave t ⟨hs.1.trans_le ht.1, ht.2.trans_lt hτ.2⟩)

/-- For a fixed bottom cap, accumulated physical flux increases with the top time. -/
theorem integral_truncatedCone_flux_monotoneOn [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    MonotoneOn (fun τ ↦ (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
      semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n)) (Ico s T) := by
  intro a ha b hb hab
  have hea := ballIntegral_energy_add_truncatedCone_flux hV hu c hs ha.1 ha.2
    (fun t ht ↦ hwave t ⟨ht.1, ht.2.trans_lt ha.2⟩)
  have heb := ballIntegral_energy_add_truncatedCone_flux hV hu c hs hb.1 hb.2
    (fun t ht ↦ hwave t ⟨ht.1, ht.2.trans_lt hb.2⟩)
  have he := ballIntegral_energy_le_of_le hV hVnonneg hu c (hs.trans_le ha.1) hab hb.2
    (fun t ht ↦ hwave t ⟨ha.1.trans ht.1, ht.2.trans_lt hb.2⟩)
  linarith

/-- The null energy flux is integrable on the entire lateral cone below
its vertex. The proof exhausts the surface by interior truncations. -/
theorem integrableOn_cone_dissipation {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^n) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ Metric.ball c (T - t), semilinearWaveOperator V u
      (timeSpaceCons t x) = 0) :
    IntegrableOn (semilinearWaveConeDissipation V u c) {p | s ≤ p 0 ∧ p 0 < T ∧
      ‖spatialPart p - c‖ = T - p 0} (Measure.euclideanHausdorffMeasure n) := by
  let J := {q : ℚ // s ≤ (q : ℝ) ∧ (q : ℝ) < T}
  let A (q : J) := truncatedConeLateralSurface c T s (q : ℚ)
  let D := semilinearWaveConeDissipation V u c
  let E := ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s)
  have hcover : {p | s ≤ p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0} = ⋃ q : J, A q := by
    ext p
    constructor
    · intro hp
      obtain ⟨q, hpq, hqT⟩ := exists_rat_btwn hp.2.1
      exact mem_iUnion.mpr ⟨⟨q, hp.1.trans hpq.le, hqT⟩, hp.1, hpq.le, hp.2.2⟩
    · intro hp
      obtain ⟨q, hq⟩ := mem_iUnion.mp hp
      exact ⟨hq.1, hq.2.1.trans_lt q.property.2, hq.2.2⟩
  have hdir : Directed (· ⊆ ·) A := by
    intro a b
    rcases le_total (a : ℚ) (b : ℚ) with hab | hba
    · refine ⟨b, ?_, Subset.rfl⟩
      exact fun p hp ↦ ⟨hp.1, hp.2.1.trans (Rat.cast_le.mpr hab), hp.2.2⟩
    · refine ⟨a, Subset.rfl, ?_⟩
      exact fun p hp ↦ ⟨hp.1, hp.2.1.trans (Rat.cast_le.mpr hba), hp.2.2⟩
  have hi (q : J) : IntegrableOn D (A q) (Measure.euclideanHausdorffMeasure n) :=
    integrableOn_truncatedCone_dissipation hV.continuous hu c hs q.property.2
  have hnonneg : ∀ p, 0 ≤ D p := semilinearWaveConeDissipation_nonneg hVnonneg u c
  have hb (q : J) : ∫ p in A q, D p ∂Measure.euclideanHausdorffMeasure n ≤ Real.sqrt 2 * E := by
    have h := integral_truncatedCone_flux_le_energy hV hVnonneg hu c hs
      q.property.1 q.property.2 (fun t ht ↦ hwave t ⟨ht.1, ht.2.trans_lt q.property.2⟩)
    have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    change (1 / Real.sqrt 2) * _ ≤ E at h
    rw [one_div, ← div_eq_inv_mul] at h
    exact (div_le_iff₀ hpos).mp h |>.trans_eq (mul_comm E _)
  rw [hcover]
  refine ⟨AEStronglyMeasurable.iUnion (fun q ↦ (hi q).aestronglyMeasurable), ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnonneg)).mpr
  rw [setLIntegral_iUnion_of_directed _ hdir]
  apply lt_of_le_of_lt (b := ENNReal.ofReal (Real.sqrt 2 * E))
  · refine iSup_le fun q ↦ ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hi q) (Filter.Eventually.of_forall hnonneg)]
    exact ENNReal.ofReal_le_ofReal (hb q)
  · exact ENNReal.ofReal_lt_top

end WaveEquation
