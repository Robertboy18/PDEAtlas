/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CompactData
import PDE.Analysis.Calculus.LocalExtension.ForwardBand
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Subcritical amplitude bounds on the forward lifespan

Finite-order extension across the initial time and a terminal cutoff give an ambient representative
of each shorter closed slab. The PDE is transferred by local equality at positive times; the initial
velocity is the right derivative. The result is the bound `‖u‖_{L^∞(ℝ³ × (0,T))} ≤ C(T)` of step 1
of the proof of Theorem 3 of Evans, §12.3.3, for solutions that are C² only on the forward band.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, Theorem 3 and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem exists_contDiff_extension_shorter_band {u : ℝ^4 → ℝ} {S L : ℝ} (hS : 0 < S)
    (hSL : S < L) (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0 ∧ p 0 < L}) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ EqOn v u {p | 0 ≤ p 0 ∧ p 0 ≤ S} := by
  obtain ⟨v, hv, heq⟩ := exists_contDiffOn_extension_halfOpenBand 0 (hS.trans hSL) hu
  let R := (S + L) / 2
  have hSR : S < R := by dsimp only [R]; linarith
  have hRL : R < L := by dsimp only [R]; linarith
  let θ (p : ℝ^4) := Real.smoothTransition ((R - p 0) / (R - S))
  have hθ : ContDiff ℝ 2 θ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ).contDiff).div_const (R - S))
  have hone {p : ℝ^4} (hp : p 0 ≤ S) : θ p = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hSR)).mpr (by linarith))
  have hzero {p : ℝ^4} (hp : R ≤ p 0) : θ p = 0 := Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hp) (sub_nonneg.mpr hSR.le))
  refine ⟨fun p ↦ θ p * v p, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p 0 < L
    · exact hθ.contDiffAt.mul (hv.contDiffAt
        ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).mem_nhds hp))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hRp : R < p 0 := hRL.trans_le (not_lt.mp hp)
      filter_upwards [(isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).mem_nhds hRp]
        with q hq
      simp only [hzero hq.le, zero_mul]
  · intro p hp
    change θ p * v p = u p
    rw [hone hp.2, one_mul, heq hp.1]

private theorem exists_classical_power_representative {p : ℝ} {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    {S L : ℝ} (hS : 0 < S) (hSL : S < L) (hu : ContDiffOn ℝ 2 u {z | 0 ≤ z 0 ∧ z 0 < L})
    (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ EqOn v u {z | 0 ≤ z 0 ∧ z 0 ≤ S} ∧
      (∀ x, v (timeSpaceCons 0 x) = g x) ∧
      (∀ x, (∂[0] v) (timeSpaceCons 0 x) = h x) ∧
      (∀ t ∈ Ioo 0 S, ∀ x,
        waveOperator v (timeSpaceCons t x) + Real.signedPower p (v (timeSpaceCons t x)) = 0) := by
  obtain ⟨v, hv, heq⟩ := exists_contDiff_extension_shorter_band hS hSL hu
  have hpos (y : ℝ^3) : v (timeSpaceCons 0 y) = g y :=
    (heq (by simp only [timeSpaceCons_zero, mem_ofPred_eq]; exact ⟨le_rfl, hS.le⟩)).trans
      (hposition y)
  have hvel (y : ℝ^3) : (∂[0] v) (timeSpaceCons 0 y) = h y := by
    have hd := (hasDerivAt_timeSpaceCons v 0 y
      (hv.differentiable (by norm_num) _)).hasDerivWithinAt (s := Ici 0)
    have hlocal : (fun s ↦ v (timeSpaceCons s y)) =ᶠ[𝓝[Ici 0] 0]
        (fun s ↦ u (timeSpaceCons s y)) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hS)] with s hs hst
      apply heq
      change 0 ≤ s ∧ s ≤ S
      exact ⟨hs, hst.le⟩
    rw [← hd.derivWithin (uniqueDiffWithinAt_Ici 0), hlocal.derivWithin_eq_of_mem (self_mem_Ici)]
    exact hinitial y
  have hw (s : ℝ) (hs : s ∈ Ioo 0 S) (y : ℝ^3) :
      waveOperator v (timeSpaceCons s y) + Real.signedPower p (v (timeSpaceCons s y)) = 0 := by
    have hlocal : v =ᶠ[𝓝 (timeSpaceCons s y)] u := by
      have hopen : IsOpen {q : ℝ^4 | 0 < q 0 ∧ q 0 < S} :=
        (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
          (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
      filter_upwards [hopen.mem_nhds
        (by simpa only [mem_ofPred_eq, timeSpaceCons_zero, mem_Ioo] using hs)] with q hq
      exact heq ⟨hq.1.le, hq.2.le⟩
    rw [waveOperator_congr_nhds hlocal, hlocal.eq_of_nhds]
    exact hwave s ⟨hs.1, hs.2.trans hSL⟩ y
  exact ⟨v, hv, heq, hpos, hvel, hw⟩

/-- The forward C² power wave satisfies the retarded ball formula.
Only right initial traces are used. -/
theorem eq_retarded_ball_of_forward_classical_power_solution {p : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} {S L : ℝ} (hS : 0 < S) (hSL : S < L)
    (hu : ContDiffOn ℝ 2 u {z | 0 ≤ z 0 ∧ z 0 < L}) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0)
    (c : ℝ^3) :
    u (timeSpaceCons S c) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons S c) -
      (1 / (4 * Real.pi)) * ∫ y in ball c S, Real.signedPower p (retardedTrace u c S y) / ‖y -
      c‖ := by
  obtain ⟨v, hv, heq, hpos, hvel, hw⟩ :=
    exists_classical_power_representative hS hSL hu hposition hinitial hwave
  have hrep := eq_retarded_ball_of_classical_power_solution hp hv hg hh hpos hvel c hS hw
  have hvalue : v (timeSpaceCons S c) = u (timeSpaceCons S c) :=
    heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using And.intro hS.le (le_refl S))
  have hint : (∫ y in ball c S, Real.signedPower p (retardedTrace v c S y) / ‖y - c‖) =
      ∫ y in ball c S, Real.signedPower p (retardedTrace u c S y) / ‖y - c‖ := by
    refine setIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
    have hy' : ‖y - c‖ < S := by simpa only [mem_ball, dist_eq_norm] using hy
    have he := heq (show 0 ≤ (backwardConeGraph c S y) 0 ∧
        (backwardConeGraph c S y) 0 ≤ S by
      simp only [backwardConeGraph, timeSpaceCons_zero]
      exact ⟨sub_nonneg.mpr hy'.le, sub_le_self _ (norm_nonneg _)⟩)
    simp only [retardedTrace, Function.comp_apply, he]
  rwa [hvalue, hint] at hrep

/-- Every real subcritical power has a data-dependent amplitude bound on
finite forward lifespans. The candidate is C² only on the half-open forward
band, including its initial face. Its initial velocity is the right
derivative, independent of arbitrary values at negative times. -/
theorem exists_uniform_amplitude_bound_of_forward_compact_data {p : ℝ} (hp : 1 < p) (hp5 : p < 5)
    (T : ℝ) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ B : ℝ, 0 < B ∧ ∀ (L : ℝ) (u : ℝ^4 → ℝ),
      0 < L → L ≤ T → ContDiffOn ℝ 2 u {z | 0 ≤ z 0 ∧ z 0 < L} →
      (∀ x, u (timeSpaceCons 0 x) = g x) →
      (∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) →
      (∀ t ∈ Ioo 0 L, ∀ x,
        waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) →
      ∀ t ∈ Ioo 0 L, ∀ x, |u (timeSpaceCons t x)| ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_amplitude_bound_of_compact_data hp hp5 T hg hh hgs hhs
  refine ⟨B, hB, fun L u _ hLT hu hposition hinitial hwave t ht x ↦ ?_⟩
  obtain ⟨v, hv, heq, hpos, hvel, hw⟩ :=
    exists_classical_power_representative ht.1 ht.2 hu hposition hinitial hwave
  rw [← heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using And.intro ht.1.le (le_refl t))]
  exact hbound t v ht.1 (ht.2.le.trans hLT) hv hpos hvel hw t ⟨ht.1, le_rfl⟩ x

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
