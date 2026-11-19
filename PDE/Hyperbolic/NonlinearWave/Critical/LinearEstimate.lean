/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.RestartData
import PDE.Hyperbolic.Models.Wave.Calculus.TimeTranslation
import PDE.Hyperbolic.Models.Wave.Strichartz.CompactForcing
import PDE.Hyperbolic.NonlinearWave.Critical.ForwardEnergy
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# The uniform critical cone estimate

The forward smooth quintic Cauchy problem with compact data supplies the first linear input of
critical continuation. Uniform restart energy, Schwartz data and the physical cone Strichartz
estimate yield constants before all centers, enlarged tips, starts and proper prefixes.

This is the linear estimate (21) of step 4 of the proof of Evans, §12.4, Theorem 3, that is, the
mixed-norm part of the estimate (4) of Theorem 1 on backward cones; step 5 uses it again on enlarged
cones. Derivative estimates and the global classical conclusion are separate results.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4); Theorem 3, steps 4-5 of its
  proof, equation (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric PDE PDE.Common PDE.Analysis
open scoped ENNReal ContDiff SchwartzMap

namespace WaveEquation.Critical

/-- The shifted quintic wave has the sharp cone mixed estimate on every
proper closed prefix, using only its open-band regularity and forward support. -/
private theorem eLpNorm_shifted_quintic_cone_le {u : ℝ^4 → ℝ} {T R s t A : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupp : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^
      5 = 0)
    (hs : s ∈ Ioo 0 T) (ht : t ∈ Ico s T) (hA : T ≤ A) (c : ℝ^3) (g h : 𝓢(ℝ^3, ℝ))
    (hpos : ∀ x, u (timeSpaceCons s x) = g x) (hvel : ∀ x, (∂[0] u) (timeSpaceCons s x) = h x) :
    eLpNorm (fun q ↦ eLpNorm (fun x ↦ u (timeSpaceCons (q + s) x)) 12
      (volume.restrict (ball c ((A - s) - q)))) 4
      (volume.restrict (Icc 0 (t - s))) ≤
      ENNReal.ofReal (Strichartz.energyAdjointBound *
        (‖Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)‖ +
        ∫ q in Icc 0 (t - s), lpNorm (fun x ↦ u (timeSpaceCons (q + s) x) ^ 5) 2
          (volume.restrict (ball c ((A - s) - q))))) := by
  obtain ⟨hcont, hcont₁, hcont₂, hd, hd₁, hspatial, hop⟩ :=
    shifted_classical_traces hu hs.1 (b := t - s) (by linarith [ht.2])
  have htime (q : ℝ) (hq : q ∈ Icc 0 (t - s)) : q + s ∈ Ioo 0 T := by
    constructor <;> linarith [hq.1, hq.2, hs.1, ht.2]
  have hfcont : ContinuousOn (fun z : ℝ × ℝ^3 ↦ -(u (timeSpaceCons (z.1 + s) z.2) ^ 5))
      (Icc 0 (t - s) ×ˢ univ) := (hcont.pow 5).neg
  have hfzero : ∀ q ∈ Icc 0 (t - s), ∀ x : ℝ^3,
      x ∉ closedBall 0 (R + T) → -(u (timeSpaceCons (q + s) x) ^ 5) = 0 := by
    intro q hq x hx
    have hx' : R + T < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hx
    rw [hsupp (q + s) (htime q hq) x (by linarith [(htime q hq).2])]
    norm_num
  have hresidual : ∀ q ∈ Icc 0 (t - s), ∀ x : ℝ^3, (∂[0] (∂[0] u)) (timeSpaceCons (q + s) x) -
        laplacian (fun y ↦ u (timeSpaceCons (q + s) y)) x =
        -(u (timeSpaceCons (q + s) x) ^ 5) := by
    intro q hq x
    rw [hop q hq x]
    linarith [hwave (q + s) (htime q hq) x]
  simpa only [lpNorm_fun_neg] using Strichartz.eLpNorm_classicalWave_cone_le_of_compact_forcing
      (u := fun q x ↦ u (timeSpaceCons (q + s) x))
      (U := fun q x ↦ (∂[0] u) (timeSpaceCons (q + s) x))
      (U₂ := fun q x ↦ (∂[0] (∂[0] u)) (timeSpaceCons (q + s) x))
      (b := t - s) (T := A - s) (by linarith [ht.2]) c g h
      (isCompact_closedBall (0 : ℝ^3) (R + T)) hfcont hfzero
      hcont hcont₁ hcont₂ hd hd₁ (fun q hq ↦ hspatial q (Ioo_subset_Icc_self hq))
      (by simpa only [zero_add] using hpos) (by simpa only [zero_add] using hvel) hresidual

/-- The physical sharp-cone estimate after translation back to the time
variable, with real norms and no totalization ambiguity. -/
private theorem lpNorm_quintic_cone_le_of_support {u : ℝ^4 → ℝ} {T R s t A : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupp : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^
      5 = 0)
    (hs : s ∈ Ioo 0 T) (ht : t ∈ Ico s T) (hA : T ≤ A) (c : ℝ^3) (g h : 𝓢(ℝ^3, ℝ))
    (hpos : ∀ x, u (timeSpaceCons s x) = g x) (hvel : ∀ x, (∂[0] u) (timeSpaceCons s x) = h x) :
    lpNorm (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x)) 12
      (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t)) ≤
      Strichartz.energyAdjointBound *
        (‖Strichartz.initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)‖ +
        ∫ q in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 5) 2
          (volume.restrict (ball c (A - q)))) := by
  have he := eLpNorm_shifted_quintic_cone_le hu hsupp hwave hs ht hA c g h hpos hvel
  have hpre : (fun q : ℝ ↦ q + s) ⁻¹' Icc s t = Icc 0 (t - s) := by
    ext q
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hm : MeasurePreserving (fun q : ℝ ↦ q + s)
      (volume.restrict (Icc 0 (t - s))) (volume.restrict (Icc s t)) := by
    simpa only [hpre] using (measurePreserving_add_right (volume : Measure ℝ) s).restrict_preimage
        (s := Icc s t) measurableSet_Icc
  have hI := hm.integral_comp (MeasurableEquiv.addRight s).measurableEmbedding
    (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 5) 2 (volume.restrict (ball c (A - q))))
  simp_rw [sub_sub, add_comm s] at he
  have hnorm : eLpNorm (fun q ↦ eLpNorm (fun x ↦ u (timeSpaceCons (q + s) x)) 12
      (volume.restrict (ball c (A - (q + s))))) 4 (volume.restrict (Icc 0 (t - s))) =
      eLpNorm (fun q ↦ eLpNorm (fun x ↦ u (timeSpaceCons q x)) 12
        (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t)) := by
    rw [← hm.map_eq]
    exact ((MeasurableEquiv.addRight s).measurableEmbedding.eLpNorm_map_measure
      (g := fun q ↦ eLpNorm (fun x ↦ u (timeSpaceCons q x)) 12
        (volume.restrict (ball c (A - q)))) (p := 4) (μ := volume.restrict (Icc 0 (t - s)))).symm
  rw [hnorm, hI] at he
  have hmem (q : ℝ) (hq : q ∈ Icc s t) :
      MemLp (fun x ↦ u (timeSpaceCons q x)) 12 (volume.restrict (ball c (A - q))) := by
    apply ContinuousOn.memLp_of_subset_isCompact
      (s := closedBall c (A - q)) ?_ (isCompact_closedBall _ _)
      measurableSet_ball ball_subset_closedBall
    exact hu.continuousOn.comp (contDiff_timeSpaceCons_spatial 3 q (m := 1)).continuous.continuousOn
      (fun x _ ↦ by
        change 0 < q ∧ q < T
        exact ⟨hs.1.trans_le hq.1, hq.2.trans_lt ht.2⟩)
  have hn : eLpNorm (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x)) 12
      (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t)) =
      eLpNorm (fun q ↦ eLpNorm (fun x ↦ u (timeSpaceCons q x)) 12
        (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t)) := by
    rw [← eLpNorm_ofReal _ (Eventually.of_forall fun _ ↦ lpNorm_nonneg)]
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with q hq
    exact ofReal_lpNorm (hmem q hq)
  have hK : 0 ≤ Strichartz.energyAdjointBound := Real.sqrt_nonneg _
  have hIpos : 0 ≤ ∫ q in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 5) 2
      (volume.restrict (ball c (A - q))) := integral_nonneg fun _ ↦ lpNorm_nonneg
  change (eLpNorm (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x)) 12
    (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t))).toReal ≤ _
  rw [hn]
  exact (ENNReal.toReal_mono (by simp) he).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg hK (add_nonneg (norm_nonneg _) hIpos)))

/-- The first linear hypothesis of global quintic continuation follows from the compact-data Cauchy
problem. The same constants precede all starts, cone centers, enlarged tips and proper prefixes. -/
theorem exists_uniform_critical_linear_estimate_of_quintic_cauchy {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T)
    (g h : ℝ^3 → ℝ) (hu : ContDiffOn ℝ ∞ u {p | 0 ≤ p 0 ∧ p 0 < T}) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h)
    (hwave : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons q x) + u (timeSpaceCons q x) ^
      5 = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧
      ∀ c : ℝ^3, ∀ A : ℝ, T ≤ A → ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T,
      lpNorm (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x)) 12
        (volume.restrict (ball c (A - q)))) 4 (volume.restrict (Icc s t)) ≤
        C + K * ∫ q in Icc s t, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 5) 2
          (volume.restrict (ball c (A - q))) := by
  obtain ⟨D, hD, hdata⟩ := exists_uniform_schwartz_restart_data_of_quintic_cauchy
    hT g h hu hgc hhc hwave hpos hvel
  obtain ⟨R, E, hsupp, _⟩ := exists_support_and_uniform_energy_of_quintic_cauchy
    hT g h (hu.of_le (by simp)) hgc hhc hwave hpos hvel
  have hK : 0 ≤ Strichartz.energyAdjointBound := Real.sqrt_nonneg _
  refine ⟨Strichartz.energyAdjointBound * D + 1, Strichartz.energyAdjointBound,
    by positivity, hK, ?_⟩
  intro c A hA s hs t ht
  obtain ⟨gₛ, hₛ, hgs, hhs, hbound⟩ := hdata s hs
  have he := lpNorm_quintic_cone_le_of_support (hu.mono fun _ hp ↦ ⟨hp.1.le, hp.2⟩)
    (fun q hq ↦ hsupp q ⟨hq.1.le, hq.2⟩) hwave hs ht hA c gₛ hₛ hgs hhs
  nlinarith [mul_le_mul_of_nonneg_left hbound hK]

end WaveEquation.Critical
