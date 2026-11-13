/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlab
import PDE.Hyperbolic.Classical.ForwardLocalization
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.LinearGrowth
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Conservation with a quadratic lower bound near the vacuum

A `C¹` potential with `V 0 = 0` may have either sign, and its derivative need not be
locally Lipschitz. If `V z ≥ -C z²` near zero, separate compact slices of a `C²` solution give
a common compact support on each finite slab (Baire category and finite propagation for the
modified cone energy), and the energy identity applies there. A `C¹` potential whose derivative
has linear growth at zero satisfies the lower bound.

This is Evans, §12.1.1, Theorem 1, for a `C¹` potential with `V z ≥ -C z²` near zero,
in every positive dimension. The other cases are listed in
`PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardConservation`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Separate compact slices give conservation when the potential is bounded
below by a negative quadratic near zero. The equation is required only at positive times and
compact support only at nonnegative times; common support and endpoint integration are
derived. -/
theorem semilinearWaveSpatialEnergy_eq_of_compact_slices_of_quadratic_lower_bound [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {C : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    semilinearWaveSpatialEnergy V u t = semilinearWaveSpatialEnergy V u 0 := by
  have hpde (s : ℝ) (hs' : 0 ≤ s) (x : ℝ^n) :=
    semilinearWaveOperator_eq_zero_of_nonneg hV.continuous_deriv_one hu hwave hs' x
  obtain ⟨R, _, hR⟩ := exists_uniform_support_on_Icc_of_compact_slices_of_quadratic_lower_bound
    hV hVzero hbound hu hpde hs (show 0 ≤ t + 1 by linarith)
  apply semilinearWaveSpatialEnergy_eq_of_compact_support_on_Icc
    (K := Metric.closedBall (0 : ℝ^n) R) (T := t + 1)
    hV hVzero hu (isCompact_closedBall _ _) (by linarith)
    (fun s hs' x hx ↦ hR s hs' x (by simpa only [Metric.mem_closedBall, dist_zero_right,
      not_le] using hx)) (fun s hs' x ↦ hwave s hs'.1 x)
  exact ⟨ht, by linarith⟩

/-- Conservation under the same local potential bound using only the field
on the closed forward half-space, including its right differential at time zero. -/
theorem forwardSemilinearWaveEnergy_eq_of_compact_slices_of_quadratic_lower_bound [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {C : ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0)
    (hbound : ∀ᶠ z in 𝓝 0, -C * z ^ 2 ≤ V z) (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    forwardSemilinearWaveEnergy V u t = forwardSemilinearWaveEnergy V u 0 := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace 0 2 hu
  rw [forwardSemilinearWaveEnergy_eq_of_extension V hU heq ht,
    forwardSemilinearWaveEnergy_eq_of_extension V hU heq le_rfl]
  apply semilinearWaveSpatialEnergy_eq_of_compact_slices_of_quadratic_lower_bound
    hV hVzero hbound hU _ _ ht
  · intro s hs' x
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons s x) 0 by simpa only [timeSpaceCons_zero] using hs')
    unfold semilinearWaveOperator
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave s hs' x
  · intro s hs'
    have hslice : (fun x : ℝ^n ↦ U (timeSpaceCons s x)) =
        (fun x : ℝ^n ↦ u (timeSpaceCons s x)) := by
      funext x
      exact heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using hs')
    rw [hslice]
    exact hs s hs'

end WaveEquation
