/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ForwardAmplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximalExistence

/-!
# Smooth subcritical waves under smoothness of the reaction

The subcritical amplitude estimate excludes a finite lifespan of the maximal smooth wave. This is
Theorem 3 of Evans, §12.3.3, under the standing hypothesis of §12.3.2 that the reaction is smooth,
which Evans keeps for Theorem 3. As in step 1 of his proof, the blow-up alternative of §12.3.2,
Theorem 2(ii), reduces global existence to an amplitude bound on each finite time interval.
Uniqueness among forward classical solutions follows from uniqueness on backward cones.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, standing hypotheses and Theorem 2(ii); §12.3.3,
  Theorem 3 and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter PDE PDE.Common PDE.Analysis WaveEquation
open scoped ENNReal Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A smooth signed-power reaction of subcritical exponent and smooth compact data
construct a global jointly smooth wave, unique among forward classical competitors.
Only terminal-strip unboundedness is used to exclude finite lifespan. -/
theorem exists_unique_global_smooth_wave_of_smooth_signedPower {p : ℝ} (hp : 1 < p) (hp5 : p < 5)
    (hs : ContDiff ℝ (⊤ : ℕ∞) (Real.signedPower p)) (g h : ℝ^3 → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    ∃ u : ℝ^4 → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u {z | 0 ≤ z 0} ∧
      (∀ x, u (timeSpaceCons 0 x) = g x) ∧
      (∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) ∧
      (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) ∧
      ∀ v : ℝ^4 → ℝ,
        ContDiffOn ℝ 2 v {z | 0 < z 0} → ContDiffOn ℝ 1 v {z | 0 ≤ z 0} →
        (∀ x, v (timeSpaceCons 0 x) = g x) →
        (∀ x, HasDerivWithinAt (fun t ↦ v (timeSpaceCons t x)) (h x) (Ici 0) 0) →
        (∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
          waveOperator v (timeSpaceCons t x) + Real.signedPower p (v (timeSpaceCons t x)) = 0) →
        EqOn v u {z | 0 ≤ z 0} := by
  obtain ⟨L, hL, u, hu, hpos, hvel, hwave, _, hblowup⟩ :=
    exists_maximal_smooth_wave hs (by simp [Real.signedPower]) g h hg hh hgc hhc
  have hinfty : L = ∞ := by
    by_contra hfinite
    let T := L.toReal
    have hT : 0 < T := ENNReal.toReal_pos (ne_of_gt hL) hfinite
    have hreg : ContDiffOn ℝ 2 u {z | 0 ≤ z 0 ∧ z 0 < T} :=
      (hu.of_le (by simp)).mono fun z hz ↦
        ⟨hz.1, (ENNReal.ofReal_lt_iff_lt_toReal hz.1 hfinite).mpr hz.2⟩
    have hpde : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0 :=
      fun t ht x ↦ hwave t ht.1 ((ENNReal.ofReal_lt_iff_lt_toReal ht.1.le hfinite).mpr ht.2) x
    obtain ⟨B, _, hB⟩ := exists_uniform_amplitude_bound_of_forward_compact_data hp hp5 T
      (hg.of_le (by simp)) (hh.of_le (by simp)) hgc hhc
    obtain ⟨t, ht, x, hx⟩ := hblowup hfinite (T / 2) (half_lt_self hT) B
    have htpos : 0 < t := (half_pos hT).trans_le ((le_max_right 0 (T / 2)).trans ht.1)
    exact (not_lt_of_ge (hB T u hT le_rfl hreg hpos
      (fun y ↦ (hvel y).derivWithin (uniqueDiffWithinAt_Ici 0)) hpde t ⟨htpos, ht.2⟩ x)) hx
  have hug : ContDiffOn ℝ (⊤ : ℕ∞) u {z | 0 ≤ z 0} := by
    simpa only [hinfty, ENNReal.ofReal_lt_top, and_true] using hu
  have hwg : ∀ t : ℝ, 0 < t → ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0 :=
    fun t ht x ↦ hwave t ht (by simp [hinfty]) x
  refine ⟨u, hug, hpos, hvel, hwg, fun v hv hv₀ hvpos hvvel hvwave p hp ↦ ?_⟩
  change 0 ≤ p 0 at hp
  have hu₂ : ContDiffOn ℝ 2 u {p | 0 < p 0} :=
    (hug.of_le (by simp)).mono fun p hp ↦ by
      change 0 < p 0 at hp
      exact hp.le
  have he := eq_on_closed_cone_forward_locallyLipschitz
    (hs.of_le (by simp)).locallyLipschitz hv hu₂ hv₀ (hug.of_le (by simp))
    (spatialPart p) (T := p 0 + 1) (by linarith) (fun t ht x _ ↦ hvwave t ht.1 x)
    (fun t ht x _ ↦ hwg t ht.1 x) (fun x _ ↦ (hvpos x).trans (hpos x).symm)
    (fun x _ ↦ (hvvel x).derivWithin (uniqueDiffWithinAt_Ici 0) |>.trans
      ((hvel x).derivWithin (uniqueDiffWithinAt_Ici 0)).symm)
    (p 0) ⟨hp, by linarith⟩ (spatialPart p)
    (Metric.mem_closedBall_self (by linarith))
  simpa only [timeSpaceCons_spatialPart] using he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
