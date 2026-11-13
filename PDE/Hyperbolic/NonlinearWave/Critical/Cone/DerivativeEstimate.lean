/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Hyperbolic.NonlinearWave.Critical.Cone.Localization
public import PDE.Hyperbolic.NonlinearWave.Critical.PersistenceEstimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import PDE.Analysis.Integration.Cone.NormContinuity
import PDE.Analysis.MeasureTheory.Lp.TimeTail

/-!
# Derivative control on a critical cone tail

Finite critical mixed norm supplies a late cone on which the differentiated linear estimate controls
the first derivatives in L⁶. The forcing coefficient is fixed before choosing the tail; the finite
starting-data constant may depend on that selected start.

This is the bound on `Du` and `u_t` in `L⁶(B(x₀, T - t))` that step 4 of the proof of Evans, §12.4,
Theorem 3, obtains from (20) by the absorption argument of step 2; we obtain it on a late time
interval. The linear estimate remains an explicit hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, steps 2 and 4 of its proof, equation (20).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- The differentiated-wave estimate controls coordinate derivatives on a
small-critical-norm cone band. Spatial integrability and norm continuity follow from the classical
field. -/
theorem lpNorm_six_partialDeriv_le_of_small_cone_norm {u : ℝ^4 → ℝ} {T s t A K : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (i : Fin 4) (hs : 0 < s) (hst : s ≤ t)
    (ht : t < T) (hK : 0 ≤ K)
    (hsmall : K * lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Icc s t)) ^ 4 ≤ 1 / 2)
    (hlinear : ∀ r ∈ Icc s t, lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
      (volume.restrict (Metric.ball c (T - r))) ≤ A + K * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2
      (volume.restrict (Metric.ball c (T - q)))) :
    ∀ r ∈ Icc s t, lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
      (volume.restrict (Metric.ball c (T - r))) ≤ 2 * A := by
  have hband : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContinuousOn (∂[i] u) {p | 0 < p 0 ∧ p 0 < T} := by
    exact (hu.continuousOn_fderiv_of_isOpen hband (by norm_num)).clm_apply continuousOn_const
  have hsub : Icc s t ⊆ Ioo 0 T := fun _ hr ↦ ⟨hs.trans_le hr.1, hr.2.trans_lt ht⟩
  have hvc : ContinuousOn (fun r ↦
      lpNorm (fun x ↦ movingConeField (∂[i] u) c T (r, x)) 6 volume) (Icc s t) := by
    apply (PDE.Analysis.continuousOn_lpNorm_six_shrinking_ball hv hs ht c).congr
    intro r hr
    exact lpNorm_movingConeField (hsub hr) 6
  have hsmall' : K * lpNorm (fun r ↦ lpNorm (fun x ↦ movingConeField u c T (r, x)) 12 volume) 4
        (volume.restrict (Icc s t)) ^ 4 ≤ 1 / 2 := by
    rw [mixed_lpNorm_movingConeField hsub measurableSet_Icc]
    exact hsmall
  have hforcing (q : ℝ) (hq : q ∈ Icc s t) : lpNorm (fun x ↦ movingConeField u c T (q, x) ^ 4 •
        movingConeField (∂[i] u) c T (q, x)) 2 volume =
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2
        (volume.restrict (Metric.ball c (T - q))) := by
    classical
    have he : (fun x ↦ movingConeField u c T (q, x) ^ 4 • movingConeField (∂[i] u) c T (q, x)) =
        (Metric.ball c (T - q)).indicator
          (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) := by
      funext x
      rw [congrFun (movingConeField_section (u := u) (c := c) (hsub hq)) x,
        congrFun (movingConeField_section (u := ∂[i] u) (c := c) (hsub hq)) x]
      by_cases hx : x ∈ Metric.ball c (T - q) <;> simp [hx]
    rw [he]
    exact congrArg ENNReal.toReal
      (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet)
  have hb := lpNorm_six_le_two_mul_of_small_critical_norm hst
    (measurable_movingConeField hu.continuousOn c) (measurable_movingConeField hv c) hK
    (fun r hr ↦ memLp_movingConeField hu.continuousOn c (hsub hr) 12)
    (fun r hr ↦ memLp_movingConeField hv c (hsub hr) 6) hvc
    (memLp_four_twelve_movingConeField_local hu.continuousOn c hs ht) hsmall'
    (by
      intro r hr
      rw [lpNorm_movingConeField (hsub hr)]
      convert hlinear r hr using 2
      congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro q hq
      exact hforcing q ⟨hq.1, hq.2.trans hr.2⟩)
  intro r hr
  simpa only [lpNorm_movingConeField (hsub hr)] using hb r hr

/-- Finite critical norm supplies a late cone on which the differentiated
linear estimate bounds every first derivative uniformly up to the terminal time. -/
theorem exists_cone_tail_partialDeriv_bound {u : ℝ^4 → ℝ} {T b K : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (i : Fin 4) (hb : 0 < b) (hbT : b < T)
    (hK : 0 ≤ K)
    (hcritical : MemLp (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (T - r)))) 4 (volume.restrict (Ico b T))) :
    ∃ s ∈ Ioo b T, ∀ A : ℝ,
      (∀ r ∈ Ico s T,
        lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
          (volume.restrict (Metric.ball c (T - r))) ≤
        A + K * ∫ q in Icc s r,
          lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
            (∂[i] u) (timeSpaceCons q x)) 2
              (volume.restrict (Metric.ball c (T - q)))) →
      ∀ r ∈ Ico s T, lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6
        (volume.restrict (Metric.ball c (T - r))) ≤ 2 * A := by
  let f : ℝ → ℝ := fun r ↦ lpNorm (fun x ↦ movingConeField u c T (r, x)) 12 volume
  have hf : Measurable f := ((measurable_movingConeField hu.continuousOn c).eLpNorm_prod_right
    (by norm_num) (by norm_num)).ennreal_toReal
  have hmem : MemLp f 4 (volume.restrict (Ico b T)) := (mixed_memLp_movingConeField_iff
      (fun _ hr ↦ ⟨hb.trans_le hr.1, hr.2⟩) measurableSet_Ico 12 4).mpr hcritical
  have hlim := MeasureTheory.tendsto_lpNorm_restrict_tail_four hbT hf hmem
  have hlim' : Tendsto (fun s ↦ K * lpNorm f 4 (volume.restrict (Icc s T)) ^ 4)
      (𝓝[<] T) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero] using (hlim.pow 4).const_mul K
  have htail : ∀ᶠ s in 𝓝[<] T,
      s ∈ Ioo b T ∧ K * lpNorm f 4 (volume.restrict (Icc s T)) ^ 4 < 1 / 2 :=
    Filter.Eventually.and (Ioo_mem_nhdsLT hbT)
      (hlim'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨s, hsT, hs⟩ := mem_nhdsLT_iff_exists_Ico_subset.mp htail
  have hs' := hs ⟨le_rfl, hsT⟩
  have hmem' : MemLp f 4 (volume.restrict (Icc b T)) := by
    simpa only [restrict_Ico_eq_restrict_Icc] using hmem
  have hmemtail : MemLp f 4 (volume.restrict (Icc s T)) := hmem'.mono_measure
    (Measure.restrict_mono_set _ (Icc_subset_Icc_left hs'.1.1.le))
  refine ⟨s, hs'.1, ?_⟩
  intro A hlinear r hr
  have hsmall : K * lpNorm (fun q ↦ lpNorm (fun x ↦ u (timeSpaceCons q x)) 12
      (volume.restrict (Metric.ball c (T - q)))) 4
        (volume.restrict (Icc s r)) ^ 4 ≤ 1 / 2 := by
    have hsub : Icc s r ⊆ Ioo 0 T := fun _ hq ↦
      ⟨(hb.trans hs'.1.1).trans_le hq.1, hq.2.trans_lt hr.2⟩
    rw [← mixed_lpNorm_movingConeField hsub measurableSet_Icc]
    have hmono : lpNorm f 4 (volume.restrict (Icc s r)) ≤ lpNorm f 4 (volume.restrict (Icc s T)) :=
      ENNReal.toReal_mono hmemtail.eLpNorm_ne_top (eLpNorm_mono_measure f
        (Measure.restrict_mono_set _ (Icc_subset_Icc_right hr.2.le)))
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hmono 4) hK).trans hs'.2.le
  exact lpNorm_six_partialDeriv_le_of_small_cone_norm hu c i (hb.trans hs'.1.1) hr.1 hr.2 hK hsmall
    (fun q hq ↦ hlinear q ⟨hq.1, hq.2.trans_lt hr.2⟩) r (right_mem_Icc.mpr hr.1)

end WaveEquation.Critical
