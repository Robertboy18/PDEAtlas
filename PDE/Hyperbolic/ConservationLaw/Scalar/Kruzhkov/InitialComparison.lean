/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.Kato
public import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundary

/-!
# Initial trace of the scalar entropy distance

Strong local `L¹` traces of two states give the same trace property for their absolute
difference. In particular, time-dependent compact test pairings attain the expected
initial entropy distance. The local contraction proof in `Kruzhkov.Contraction`
uses this trace. It replaces the convergence `u(·, t), ũ(·, t) → g` in `L¹` as `t → 0` that
step 5 of the proof of Evans, §11.4.3, Theorem 3, combines with (50).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- The absolute difference of two states with strong local `L¹` traces has the
absolute difference of their initial data as its strong local `L¹` trace. -/
theorem entropyDistance_initialTrace {u v : ℝ^2 → ℝ} {u₀ v₀ : ℝ → ℝ}
    (hu : HasInitialTraceLocallyL1 u u₀) (hv : HasInitialTraceLocallyL1 v v₀) :
    HasInitialTraceLocallyL1 (fun p ↦ |u p - v p|) (fun x ↦ |u₀ x - v₀ x|) := by
  have hinit : LocallyIntegrable (fun x ↦ |u₀ x - v₀ x|) volume := by
    refine locallyIntegrable_iff.mpr fun K hK ↦ ?_
    exact ((hu.initial_locallyIntegrable.integrableOn_isCompact hK).sub
      (hv.initial_locallyIntegrable.integrableOn_isCompact hK)).norm
  refine ⟨hinit, fun a b ↦ ?_⟩
  have hu₀ := hu.initial_locallyIntegrable.integrableOn_isCompact (k := Icc a b) isCompact_Icc
  have hv₀ := hv.initial_locallyIntegrable.integrableOn_isCompact (k := Icc a b) isCompact_Icc
  have hi : ∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun x ↦ |u !₂[t, x] - v !₂[t, x]| - |u₀ x - v₀ x|)
        (Icc a b) volume := by
    filter_upwards [hu.eventually_integrableOn_sub a b,
      hv.eventually_integrableOn_sub a b] with t hut hvt
    have hui : IntegrableOn (fun x ↦ u !₂[t, x]) (Icc a b) volume := by
      simpa only [Pi.add_def, sub_add_cancel] using hut.add hu₀
    have hvi : IntegrableOn (fun x ↦ v !₂[t, x]) (Icc a b) volume := by
      simpa only [Pi.add_def, sub_add_cancel] using hvt.add hv₀
    exact (hui.sub hvi).norm.sub (hu₀.sub hv₀).norm
  refine ⟨hi, ?_⟩
  have hlim : Tendsto (fun t : ℝ ↦ (∫ x in Icc a b, ‖u !₂[t, x] - u₀ x‖) +
        ∫ x in Icc a b, ‖v !₂[t, x] - v₀ x‖) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hu.tendsto_setIntegral_norm_sub a b).add (hv.tendsto_setIntegral_norm_sub a b)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hi, hu.eventually_integrableOn_sub a b,
    hv.eventually_integrableOn_sub a b] with t hit hut hvt
  rw [← integral_add hut.norm hvt.norm]
  apply integral_mono_ae hit.norm (hut.norm.add hvt.norm)
  filter_upwards [] with x
  change ‖|u !₂[t, x] - v !₂[t, x]| - |u₀ x - v₀ x|‖ ≤ ‖u !₂[t, x] - u₀ x‖ + ‖v !₂[t, x] - v₀ x‖
  simpa only [add_comm] using norm_abs_sub_sub_abs_sub_le (v !₂[t, x]) (u !₂[t, x]) (v₀ x) (u₀ x)

/-- Compact time-dependent pairings of the entropy distance attain the initial
distance. This is the boundary limit required by initial-time cutoffs. -/
theorem tendsto_integral_entropyDistance_test {u v : ℝ^2 → ℝ} {u₀ v₀ : ℝ → ℝ}
    (hu : HasInitialTraceLocallyL1 u u₀) (hv : HasInitialTraceLocallyL1 v v₀)
    (φ : InitialValueTestFunction) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ !₂[t, x] * |u !₂[t, x] - v !₂[t, x]|)
      (𝓝[>] 0) (𝓝 (∫ x : ℝ, φ !₂[0, x] * |u₀ x - v₀ x|)) :=
  (entropyDistance_initialTrace hu hv).tendsto_integral_test_smul φ

/-- Identical initial data make the local entropy distance vanish at the initial
time. This assertion is a trace limit, not a positive-time uniqueness statement. -/
theorem tendsto_initial_local_distance_zero {u v : ℝ^2 → ℝ} {u₀ : ℝ → ℝ}
    (hu : HasInitialTraceLocallyL1 u u₀) (hv : HasInitialTraceLocallyL1 v u₀) (a b : ℝ) :
    Tendsto (fun t : ℝ ↦ ∫ x in Icc a b, |u !₂[t, x] - v !₂[t, x]|) (𝓝[>] 0) (𝓝 0) := by
  simpa using (entropyDistance_initialTrace hu hv).tendsto_setIntegral_norm_sub a b

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov
