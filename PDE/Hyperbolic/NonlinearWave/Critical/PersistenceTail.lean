/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Critical.PersistenceEstimate
import PDE.Analysis.MeasureTheory.Lp.TimeTail

/-!
# Derivative absorption on a critical tail

Finite critical mixed norm gives a late interval where the differentiated linear estimate is
absorbed. The data constant may be chosen after this interval. The linear estimate remains an
explicit hypothesis.

This is the absorption of step 2 of the proof of Evans, §12.4, Theorem 3, on a late interval
`[s, T)` on which `∫ ‖u‖_{L¹²}⁴ dt` is small, in place of Evans's iteration over the intervals
`[kτ, (k+1)τ]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- A finite critical norm supplies a tail on which every differentiated linear
estimate is absorbed, with its data constant chosen after the tail. -/
theorem exists_tail_lpNorm_six_bound {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
    {u v : ℝ × X → ℝ} {b T K : ℝ} (hbT : b < T) (hu : Measurable u) (hv : Measurable v) (hK : 0 ≤ K)
    (hu12 : ∀ r ∈ Ico b T, MemLp (fun x ↦ u (r, x)) 12 ν)
    (hv6 : ∀ r ∈ Ico b T, MemLp (fun x ↦ v (r, x)) 6 ν)
    (hvc : ∀ s ∈ Ico b T, ∀ t ∈ Ico s T,
      ContinuousOn (fun r ↦ lpNorm (fun x ↦ v (r, x)) 6 ν) (Icc s t))
    (hcritical : MemLp (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) 4 (volume.restrict (Ico b T))) :
    ∃ s ∈ Ioo b T, ∀ A : ℝ, (∀ r ∈ Ico s T, lpNorm (fun x ↦ v (r, x)) 6 ν ≤ A + K * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (q, x) ^ 4 * v (q, x)) 2 ν) → ∀ r ∈ Ico s T, lpNorm (fun x ↦ v (r, x)) 6 ν ≤
      2 * A := by
  let f : ℝ → ℝ := fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν
  have hf : Measurable f :=
    (hu.eLpNorm_prod_right (by norm_num) (by norm_num)).ennreal_toReal
  have hlim := MeasureTheory.tendsto_lpNorm_restrict_tail_four hbT hf hcritical
  have hlim' : Tendsto (fun s ↦ K * lpNorm f 4 (volume.restrict (Icc s T)) ^ 4)
      (𝓝[<] T) (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), mul_zero] using (hlim.pow 4).const_mul K
  have htimes : ∀ᶠ s in 𝓝[<] T, s ∈ Ioo b T := Ioo_mem_nhdsLT hbT
  obtain ⟨s, hs, hsmall⟩ := (htimes.and
    (hlim'.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)))).exists
  have hmem : MemLp f 4 (volume.restrict (Icc b T)) := by
    simpa only [restrict_Ico_eq_restrict_Icc] using hcritical
  have htail := hmem.mono_measure (Measure.restrict_mono_set _ (Icc_subset_Icc_left hs.1.le))
  refine ⟨s, hs, fun A hlinear r hr ↦ ?_⟩
  have hsub : Icc s r ⊆ Ico b T := fun _ hq ↦ ⟨hs.1.le.trans hq.1, hq.2.trans_lt hr.2⟩
  have hprefix := htail.mono_measure (Measure.restrict_mono_set _ (Icc_subset_Icc_right hr.2.le))
  have hmono : lpNorm f 4 (volume.restrict (Icc s r)) ≤ lpNorm f 4 (volume.restrict (Icc s T)) :=
    ENNReal.toReal_mono htail.eLpNorm_ne_top (eLpNorm_mono_measure f
      (Measure.restrict_mono_set _ (Icc_subset_Icc_right hr.2.le)))
  have hsmall' : K * lpNorm f 4 (volume.restrict (Icc s r)) ^ 4 ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lpNorm_nonneg hmono 4) hK).trans hsmall.le
  exact lpNorm_six_le_two_mul_of_small_critical_norm hr.1 hu hv hK
    (fun q hq ↦ hu12 q (hsub hq)) (fun q hq ↦ hv6 q (hsub hq))
    (hvc s ⟨hs.1.le, hs.2⟩ r hr) hprefix hsmall'
    (fun q hq ↦ by
      simpa only [smul_eq_mul] using hlinear q ⟨hq.1, hq.2.trans_lt hr.2⟩)
    r (right_mem_Icc.mpr hr.1)

end WaveEquation.Critical
