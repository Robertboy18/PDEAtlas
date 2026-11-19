/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Analysis.MeasureTheory.Lp.QuinticHolder
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Critical derivative absorption on a compact time band

The maximum of the L⁶ section norm is absorbed using the critical mixed Hölder estimate. The linear
differentiated-wave estimate remains a hypothesis; product forcing integrability is proved. The
coefficient can include the factor 5 in the quintic derivative.

This is the absorption in step 2 of the proof of Evans, §12.4, Theorem 3: with
`‖u⁴Du‖_{L²} ≤ ‖Du‖_{L⁶} ‖u‖_{L¹²}⁴` and `∫ ‖u‖_{L¹²}⁴ dt ≤ 1/(2C)` on the band, the linear estimate
gives `sup ‖Du‖_{L⁶} ≤ C + (1/2) sup ‖Du‖_{L⁶}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set Filter

namespace WaveEquation.Critical

/-- On a band with small critical norm, the linear differentiated-wave estimate
bounds the L6 sections of a vector-valued field. For wave persistence,
take the field to be a spatial derivative or the time derivative of u. -/
theorem lpNorm_six_le_two_mul_of_small_critical_norm {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {ν : Measure X} [SFinite ν] {u : ℝ × X → ℝ} {v : ℝ × X → E}
    {s t A K : ℝ} (hst : s ≤ t) (hu : Measurable u) (hv : Measurable v) (hK : 0 ≤ K)
    (hu12 : ∀ r ∈ Icc s t, MemLp (fun x ↦ u (r, x)) 12 ν)
    (hv6 : ∀ r ∈ Icc s t, MemLp (fun x ↦ v (r, x)) 6 ν)
    (hvc : ContinuousOn (fun r ↦ lpNorm (fun x ↦ v (r, x)) 6 ν) (Icc s t))
    (hu4 : MemLp (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) 4 (volume.restrict (Icc s t)))
    (hsmall : K * lpNorm (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) 4 (volume.restrict (Icc s t)) ^
      4 ≤ 1 / 2)
    (hlinear : ∀ r ∈ Icc s t, lpNorm (fun x ↦ v (r, x)) 6 ν ≤ A + K * ∫ q in Icc s r,
      lpNorm (fun x ↦ u (q, x) ^ 4 • v (q, x)) 2 ν) :
    ∀ r ∈ Icc s t, lpNorm (fun x ↦ v (r, x)) 6 ν ≤ 2 * A := by
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hst) hvc
  have h12 := ae_restrict_of_forall_mem (μ := volume) measurableSet_Icc hu12
  have h6 := ae_restrict_of_forall_mem (μ := volume) measurableSet_Icc hv6
  have hM := ae_restrict_of_forall_mem (μ := volume) measurableSet_Icc (fun q hq ↦ hmax hq)
  have hi := integrable_lpNorm_pow_four_smul hu hv h12 h6 hM hu4
  have hh := integral_lpNorm_pow_four_smul_le hu hv h12 h6 hM hu4
  have hprefix := setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ ↦ lpNorm_nonneg))
    (Filter.Eventually.of_forall (fun _ hq ↦ Icc_subset_Icc_right hr.2 hq))
  have hb := (hlinear r hr).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (hprefix.trans hh) hK))
  have hm := mul_le_mul_of_nonneg_right hsmall
    (lpNorm_nonneg (f := fun x ↦ v (r, x)) (p := 6) (μ := ν))
  have hfinal : lpNorm (fun x ↦ v (r, x)) 6 ν ≤ 2 * A := by
    rw [mul_assoc] at hm
    linarith
  exact fun q hq ↦ (hmax hq).trans hfinal

end WaveEquation.Critical
