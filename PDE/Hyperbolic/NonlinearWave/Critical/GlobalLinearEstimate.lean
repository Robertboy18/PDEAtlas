/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.ForwardEnergy
public import PDE.Hyperbolic.NonlinearWave.Critical.LinearizedEquation
import PDE.Analysis.Calculus.SpaceTime.SchwartzData
import PDE.Analysis.MeasureTheory.Lp.MixedSections.Complex
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.Hyperbolic.Models.Wave.Calculus.TimeTranslation
import PDE.Hyperbolic.Models.Wave.Strichartz.ClassicalSobolev

/-!
# Whole-space linear estimate for derivatives of the quintic wave

The differentiated equation has forcing `-5u⁴∂ᵢu`. Forward support makes this forcing a Bochner
`L¹(L²)` function on each proper closed prefix. The physical classical L⁶ bound gives one
coefficient before all derivative coordinates, restart times and prefixes; only the initial data
term varies.

This is the L⁶ part of the estimate (4) of Evans, §12.4, Theorem 1, for the derivatives of the
solution on the whole space, which steps 2 and 6 of the proof of Theorem 3 use.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4); Theorem 3, steps 2 and 6 of
  its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric PDE PDE.Common PDE.Analysis
open scoped ENNReal ContDiff SchwartzMap

namespace WaveEquation.Critical

private theorem lpNorm_partialDeriv_le_of_forward_support {u : ℝ^4 → ℝ} {T R s t : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupp : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^
      5 = 0)
    (i : Fin 4) (hs : s ∈ Ioo 0 T) (ht : t ∈ Ico s T) (g h : 𝓢(ℝ^3, ℝ))
    (hpos : ∀ x, (∂[i] u) (timeSpaceCons s x) = g x)
    (hvel : ∀ x, (∂[0] (∂[i] u)) (timeSpaceCons s x) = h x) :
    lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons t x)) 6 volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ) * 6 *
        (‖Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)‖ +
          5 * ∫ q in Icc s t,
            lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x))
              2 volume) := by
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContDiffOn ℝ ∞ (∂[i] u) {p | 0 < p 0 ∧ p 0 < T} :=
    hu.partialDeriv i hopen (by simp)
  obtain ⟨hcont, hcont₁, hcont₂, hd, hd₁, hspatial, hop⟩ :=
    shifted_classical_traces hv hs.1 (b := t - s) (by linarith [ht.2])
  have hucont := (shifted_classical_traces hu hs.1 (b := t - s)
    (by linarith [ht.2])).1
  have htime (q : ℝ) (hq : q ∈ Icc 0 (t - s)) : q + s ∈ Ioo 0 T := by
    constructor <;> linarith [hq.1, hq.2, hs.1, ht.2]
  let F : ℝ × ℝ^3 → ℝ := fun z ↦
    -(5 * (u (timeSpaceCons (z.1 + s) z.2) ^ 4 * (∂[i] u) (timeSpaceCons (z.1 + s) z.2)))
  have hF : ContinuousOn F (Icc 0 (t - s) ×ˢ univ) :=
    ((continuousOn_const.mul ((hucont.pow 4).mul hcont)).neg)
  have hzero : ∀ q ∈ Icc 0 (t - s), ∀ x : ℝ^3,
      x ∉ closedBall 0 (R + T) → F (q, x) = 0 := by
    intro q hq x hx
    have hx' : R + T < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    simp only [F, hsupp (q + s) (htime q hq) x (by linarith [(htime q hq).2]),
      zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_mul, mul_zero, neg_zero]
  obtain ⟨_, f, _, hf, hfnorm⟩ := exists_complex_L1_L2_sections_indicator
    (isCompact_closedBall (0 : ℝ^3) (R + T)) hF hzero (S := univ) MeasurableSet.univ
  simp only [indicator_univ] at hf
  simp only [mem_univ, ofPred_true, Measure.restrict_univ] at hfnorm
  have hw (p : ℝ^4) (hp₀ : 0 < p 0) (hpT : p 0 < T) :
      waveOperator u p + u p ^ 5 = 0 := by
    simpa only [timeSpaceCons_spatialPart] using hwave (p 0) ⟨hp₀, hpT⟩ (spatialPart p)
  have hres : ∀ q ∈ Icc 0 (t - s), ∀ x : ℝ^3, (∂[0] (∂[0] (∂[i] u))) (timeSpaceCons (q + s) x) -
        laplacian (fun y ↦ (∂[i] u) (timeSpaceCons (q + s) y)) x = F (q, x) := by
    intro q hq x
    rw [hop q hq x, waveOperator_partialDeriv_quintic_on_band
      (hu.of_le (by simp)) hw i (by simpa using htime q hq)]
    simp only [F, mul_assoc]
  have hr : ∀ᵐ q ∂volume.restrict (Icc 0 (t - s)), (f q : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
        (((∂[0] (∂[0] (∂[i] u))) (timeSpaceCons (q + s) x) -
          laplacian (fun y ↦ (∂[i] u) (timeSpaceCons (q + s) y)) x : ℝ) : ℂ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with q hq hqt
    exact hq.trans (Eventually.of_forall fun x ↦ congrArg Complex.ofReal (hres q hqt x).symm)
  have h6 := Strichartz.eLpNorm_classicalWave_six_le g h f
    (u := fun q x ↦ (∂[i] u) (timeSpaceCons (q + s) x))
    (U := fun q x ↦ (∂[0] (∂[i] u)) (timeSpaceCons (q + s) x))
    (U₂ := fun q x ↦ (∂[0] (∂[0] (∂[i] u))) (timeSpaceCons (q + s) x))
    hcont hcont₁ hcont₂ hd hd₁ (fun q hq ↦ hspatial q (Ioo_subset_Icc_self hq))
    (by simpa only [zero_add] using hpos) (by simpa only [zero_add] using hvel) hr
    (t - s) ⟨sub_nonneg.mpr ht.1, le_rfl⟩
  let S : NNReal := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2
  let d := Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
    (h.postcompCLM Complex.ofRealCLM)
  have hfinit : (S : ℝ≥0∞) * 6 * (‖d‖ₑ + ‖f‖ₑ) ≠ ⊤ := by finiteness
  have hreal := ENNReal.toReal_mono hfinit h6
  simp only [toReal_eLpNorm, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ENNReal.toReal_ofNat, ENNReal.toReal_add enorm_ne_top enorm_ne_top,
    toReal_enorm, sub_add_cancel] at hreal
  have hpre : (fun q : ℝ ↦ q + s) ⁻¹' Icc s t = Icc 0 (t - s) := by
    ext q
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hm : MeasurePreserving (fun q : ℝ ↦ q + s)
      (volume.restrict (Icc 0 (t - s))) (volume.restrict (Icc s t)) := by
    simpa only [hpre] using (measurePreserving_add_right (volume : Measure ℝ) s).restrict_preimage
        (s := Icc s t) measurableSet_Icc
  have hI := hm.integral_comp (MeasurableEquiv.addRight s).measurableEmbedding
    (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2 volume)
  have hfnorm' : ‖f‖ = 5 * ∫ q in Icc s t,
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x))
        2 volume := by
    rw [hfnorm]
    have hscale (q : ℝ) : lpNorm (fun x ↦ F (q, x)) 2 volume =
        5 * lpNorm (fun x ↦ u (timeSpaceCons (q + s) x) ^ 4 *
          (∂[i] u) (timeSpaceCons (q + s) x)) 2 volume := by
      simp only [F, lpNorm_fun_neg]
      exact lpNorm_fun_natCast_mul 5 _ _ _
    simp_rw [hscale]
    rw [integral_const_mul, hI]
  simpa only [hfnorm'] using hreal

/-- The whole-space derivative hypothesis of critical quintic continuation follows from the
compact-data Cauchy problem. Its coefficient is independent of coordinate, start and prefix; the
data constant is fixed before the prefix. -/
theorem exists_global_derivative_linear_estimate_of_quintic_cauchy {u : ℝ^4 → ℝ} {T : ℝ}
    (hT : 0 < T) (g h : ℝ^3 → ℝ) (hu : ContDiffOn ℝ ∞ u {p | 0 ≤ p 0 ∧ p 0 < T})
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^
      5 = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) :
    ∃ N : ℝ, 0 ≤ N ∧
      ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ t ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons t x)) 6 volume ≤
        A + N * ∫ q in Icc s t,
          lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x))
            2 volume := by
  obtain ⟨R, E, hsupp, _⟩ := exists_support_and_uniform_energy_of_quintic_cauchy
    hT g h (hu.of_le (by simp)) hgc hhc hwave hpos hvel
  have hu' : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T} := hu.mono fun _ hp ↦ ⟨hp.1.le, hp.2⟩
  have hsupp' : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0 :=
    fun q hq ↦ hsupp q ⟨hq.1.le, hq.2⟩
  let S : NNReal := SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2
  refine ⟨(S : ℝ) * 6 * 5, by positivity, ?_⟩
  intro i s hs
  obtain ⟨gₛ, hₛ, hgs, hhs⟩ :=
    exists_schwartz_partialDeriv_cauchyData_of_forward_support hu' hsupp' hs i
  refine ⟨(S : ℝ) * 6 * ‖Strichartz.initialEnergyDatum
    (gₛ.postcompCLM Complex.ofRealCLM) (hₛ.postcompCLM Complex.ofRealCLM)‖, ?_⟩
  intro t ht
  have he := lpNorm_partialDeriv_le_of_forward_support hu' hsupp' hwave i hs ht gₛ hₛ hgs hhs
  simpa only [mul_add, mul_assoc] using he

end WaveEquation.Critical
