/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlices
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalExtension

/-!
# Energy conservation on the closed forward half-space

A smooth extension across the initial face transfers the compact-slice theorem for a
`C²` potential to fields given only on the closed forward half-space. The initial energy
uses the right derivative in time. This is the energy conservation of Evans,
§12.1.1, Theorem 1, for a `C¹` reaction.

## Versions

Every version concerns solutions whose spatial slices are separately compactly supported. For
a `C²` potential, hence a `C¹` reaction, conservation is proved in every positive dimension
(`forwardSemilinearWaveEnergy_eq_of_compact_slices`).
For a `C¹` potential, whose reaction is only continuous, it is proved

* for `C³` solutions in one dimension, in
  `PDE.Hyperbolic.NonlinearWave.GlobalEnergy.OneDimension.Conservation`;
* for `C⁴` solutions in two dimensions, in
  `PDE.Hyperbolic.NonlinearWave.GlobalEnergy.TwoDimensions.Conservation`;
* for `C²` solutions in every positive dimension when `V z ≥ -C z²` near zero, in
  `PDE.Hyperbolic.NonlinearWave.GlobalEnergy.QuadraticLowerBound`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- Energy conservation for a C² potential with separate compact spatial slices and
closed-forward-halfspace C² regularity of the wave. No negative-time values enter the
initial energy or the hypotheses. -/
theorem forwardSemilinearWaveEnergy_eq_of_compact_slices [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 2 V) (hVzero : V 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0})
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {t : ℝ}
    (ht : 0 ≤ t) :
    forwardSemilinearWaveEnergy V u t = forwardSemilinearWaveEnergy V u 0 := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace 0 2 hu
  rw [forwardSemilinearWaveEnergy_eq_of_extension V hU heq ht,
    forwardSemilinearWaveEnergy_eq_of_extension V hU heq le_rfl]
  apply semilinearWaveSpatialEnergy_eq_of_compact_slices hV hVzero hU _ _ ht
  · intro s hs' x
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons s x) 0 by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using hs')
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
