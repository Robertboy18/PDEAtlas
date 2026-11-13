/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.GlobalDerivativeEstimate
public import PDE.Hyperbolic.NonlinearWave.Critical.GlobalEnergy
import PDE.Hyperbolic.NonlinearWave.Critical.GlobalTail
import PDE.Spaces.Sobolev.Inequalities.Morrey.Classical

/-!
# Late amplitude bounds for the quintic wave

The quintic equation supplies a uniform L⁶ bound. A finite critical mixed norm absorbs the
differentiated linear estimates, and the resulting W^{1,6} bound controls the amplitude. Cone energy
decay and finite localization supply the critical tail.

This is the bound (16) in the proof of Evans, §12.4, Theorem 3, on a late time interval. Steps 3-6
of that proof give the critical tail `u ∈ L⁴(s, T; L¹²(ℝ³))`, and the absorption argument of step 2
turns it into the amplitude bound. The three physical linear estimates, versions of the estimate (4)
of Theorem 1 on backward cones and on the whole space, remain explicit hypotheses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4); Theorem 3, steps 2-6 of its
  proof, equations (16)-(24).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- Energy and differentiated-wave absorption bound the amplitude on a late
interval. The critical norm is finite; the differentiated physical estimate remains
explicit. -/
theorem exists_amplitude_bound_of_critical_tail {u : ℝ^4 → ℝ} {T R b K : ℝ} (hb : 0 < b)
    (hbT : b < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) (hK : 0 ≤ K)
    (hcritical : MemLp (fun t ↦ lpNorm (fun x ↦ u (timeSpaceCons t x)) 12 volume) 4
      (volume.restrict (Ico b T)))
    (hlinear : ∀ i : Fin 4, ∀ s ∈ Ioo b T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 volume ≤ A + K * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2 volume) :
    ∃ s ∈ Ioo b T, ∃ M : ℝ, ∀ t ∈ Ico s T, ∀ x : ℝ^3, ‖u (timeSpaceCons t x)‖ ≤ M := by
  classical
  have : Fact (1 ≤ (6 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨M₀, hM₀⟩ := exists_global_lpNorm_six_bound_of_wave hb hbT hu hwave hsupport
  choose start hstart bound hbound using fun i : Fin 4 ↦
    exists_global_tail_partialDeriv_bound hb hbT (hu.of_le (by norm_num)) i
      hsupport hK hcritical (hlinear i)
  have hlate : ∀ᶠ s in 𝓝[<] T, ∀ i : Fin 4, start i < s := by
    apply Filter.eventually_all.mpr
    intro i
    have ht : ∀ᶠ s in 𝓝[<] T, s ∈ Ioo (start i) T := Ioo_mem_nhdsLT (hstart i).2
    exact ht.mono fun _ hs ↦ hs.1
  have htimes : ∀ᶠ s in 𝓝[<] T, s ∈ Ioo b T := Ioo_mem_nhdsLT hbT
  obtain ⟨s, hs, hstarts⟩ := (htimes.and hlate).exists
  obtain ⟨C, hC⟩ := SobolevSpace.exists_fullENorm_morreyBound
    (n := 3) (p := 6) (by norm_num) (by norm_num)
  let B : ℝ≥0∞ := C * (ENNReal.ofReal M₀ + ∑ i : Fin 3, ENNReal.ofReal (bound i.succ))
  have hB : B ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.sum_ne_top.mpr (fun _ _ ↦ ENNReal.ofReal_ne_top)⟩)
  refine ⟨s, hs, B.toReal, ?_⟩
  intro t ht x
  have ht0 : 0 < t := (hb.trans hs.1).trans_le ht.1
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hut (y : ℝ^3) : ContDiffAt ℝ 2 u (timeSpaceCons t y) :=
    hu.contDiffAt (hopen.mem_nhds (by simpa using And.intro ht0 ht.2))
  have hslice : ContDiff ℝ 1 (fun y ↦ u (timeSpaceCons t y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    exact ((hut y).of_le (by norm_num)).comp y
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).contDiffAt
  have hsupport' : HasCompactSupport (fun y ↦ u (timeSpaceCons t y)) := by
    apply (isCompact_closedBall (0 : ℝ^3) (R + T)).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro y hy
    by_contra hnot
    have hn : R + T < ‖y‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
    exact hy (hsupport t ⟨ht0, ht.2⟩ y (by linarith [ht.2]))
  have hm : MemLp (fun y ↦ u (timeSpaceCons t y)) 6 volume :=
    hslice.continuous.memLp_of_hasCompactSupport hsupport'
  have hdu : ∀ i : Fin 3, MemLp (∂[i] (fun y ↦ u (timeSpaceCons t y))) 6 volume := by
    intro i
    have hc : Continuous (∂[i] (fun y ↦ u (timeSpaceCons t y))) :=
      (hslice.continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact hc.memLp_of_hasCompactSupport (hsupport'.fderiv_apply ℝ (EuclideanSpace.single i 1))
  have hderiv : eLpNorm (fderiv ℝ (fun y ↦ u (timeSpaceCons t y))) 6 volume ≤
      ∑ i : Fin 3, ENNReal.ofReal (bound i.succ) := by
    apply (SobolevSpace.Inequalities.eLpNorm_fderiv_le_sum_eLpNorm_partialDeriv hslice).trans
    apply Finset.sum_le_sum
    intro i _
    rw [← ofReal_lpNorm (hdu i)]
    apply ENNReal.ofReal_le_ofReal
    have he : (∂[i] (fun y ↦ u (timeSpaceCons t y))) =
        fun y ↦ (∂[i.succ] u) (timeSpaceCons t y) := by
      funext y
      exact partialDeriv_timeSpaceCons_spatial i u t y ((hut y).differentiableAt (by norm_num))
    rw [he]
    exact hbound i.succ t ⟨(hstarts i.succ).le.trans ht.1, ht.2⟩
  have hval : eLpNorm (fun y ↦ u (timeSpaceCons t y)) 6 volume ≤ ENNReal.ofReal M₀ := by
    rw [← ofReal_lpNorm hm]
    exact ENNReal.ofReal_le_ofReal (hM₀ t ⟨hs.1.le.trans ht.1, ht.2⟩)
  have hamp : ‖u (timeSpaceCons t x)‖ₑ ≤ B := (le_iSup (fun y ↦ ‖u (timeSpaceCons t y)‖ₑ) x).trans
      ((le_self_add.trans (hC _ hslice)).trans (mul_le_mul_right (add_le_add hval hderiv) _))
  simpa only [toReal_enorm] using ENNReal.toReal_mono hB hamp


/-- Cone energy decay, enlargement and finite localization supply the
critical tail used to bound amplitude. The three physical linear estimates remain explicit
hypotheses. -/
theorem exists_amplitude_bound_of_wave_strichartz {u : ℝ^4 → ℝ} {T R C K L N : ℝ} (hT : 0 < T)
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0)
    (hsupport : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0) (hC : 0 < C)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlinear : ∀ c : ℝ^3, ∀ A : ℝ, T ≤ A → ∀ s ∈ Ioo 0 T, ∀ t ∈ Ico s T,
      lpNorm (fun r ↦ lpNorm (fun x ↦ u (timeSpaceCons r x)) 12
      (volume.restrict (Metric.ball c (A - r)))) 4 (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc
      s t, lpNorm (fun x ↦ u (timeSpaceCons r x) ^ 5) 2 (volume.restrict (Metric.ball c (A - r))))
    (hderivative : ∀ c : ℝ^3, ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 (volume.restrict (Metric.ball c (T - r))) ≤
      A + L * ∫ q in Icc s r, lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 *
      (∂[i] u) (timeSpaceCons q x)) 2 (volume.restrict (Metric.ball c (T - q))))
    (hN : 0 ≤ N)
    (hglobal : ∀ i : Fin 4, ∀ s ∈ Ioo 0 T, ∃ A : ℝ, ∀ r ∈ Ico s T,
      lpNorm (fun x ↦ (∂[i] u) (timeSpaceCons r x)) 6 volume ≤ A + N * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (timeSpaceCons q x) ^ 4 * (∂[i] u) (timeSpaceCons q x)) 2 volume) :
    ∃ s ∈ Ioo 0 T, ∃ M : ℝ, ∀ t ∈ Ico s T, ∀ x : ℝ^3, ‖u (timeSpaceCons t x)‖ ≤ M := by
  obtain ⟨b, hb, hcritical⟩ := exists_global_critical_tail_of_wave_strichartz
    hT hu hwave hsupport hC hK hL hlinear hderivative
  obtain ⟨s, hs, M, hM⟩ := exists_amplitude_bound_of_critical_tail hb.1 hb.2 hu
    hwave hsupport hN hcritical (fun i a ha ↦ hglobal i a ⟨hb.1.trans ha.1, ha.2⟩)
  exact ⟨s, ⟨hb.1.trans hs.1, hs.2⟩, M, hM⟩

end WaveEquation.Critical
