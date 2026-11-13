/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.TwoDimensions.Stress
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.TwoDimensions.Tails

/-!
# Planar energy conservation with a continuous reaction

Separate compact displacement slices give uniform potential tails on each
finite time interval. The planar stress estimate converts those tails into
a vanishing cutoff error, proving conservation of the physical wave energy.
At time zero the energy uses the right derivative in time.

The field is `C⁴` on the closed forward half-space and the potential is `C¹` with
`V 0 = 0`, so the reaction `deriv V` is only continuous. This is the two-dimensional
case of Evans, §12.1.1, Theorem 1, with no common support and no sign or growth
condition on the potential.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE PDE.Common PDE.Analysis SobolevSpace.Approximation

namespace WaveEquation

/-- Uniform decay of the potential over a finite time interval suffices for
planar energy conservation. No uniform support or derivative decay is assumed. -/
private theorem energy_eq_of_uniform_potential_tails_two {V : ℝ → ℝ} {u : ℝ^3 → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ r ∈ Icc s t, ∀ x : ℝ^2, B ≤ ‖x‖ →
      |V (u (timeSpaceCons r x))| ≤ ε) :
    semilinearWaveSpatialEnergy V u t = semilinearWaveSpatialEnergy V u s := by
  obtain ⟨C, hC, R₀, hR₀, hstress⟩ :=
    exists_radius_cutoffStress_le_potential_value_two hV hVzero hu hwave hs hs0 hst
  obtain ⟨R₁, hR₁, hcap⟩ :=
    exists_radius_energy_sub_eq_scaledCutoffStress hV hVzero hu hwave hs hs0 hst
  let E := semilinearWaveSpatialEnergy V u t - semilinearWaveSpatialEnergy V u s
  let D := C * (t - s) ^ 2
  have hD : 0 ≤ D := mul_nonneg hC (sq_nonneg _)
  have hsmall (ε : ℝ) (hε : 0 < ε) : ‖E‖ ≤ ε := by
    let δ := ε / (D + 1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    obtain ⟨B, hB⟩ := htail δ hδ
    let R := max R₀ (max R₁ (B + (t + 1 - s) + 1))
    have hlarge : R₀ ≤ R := le_max_left _ _
    have hcaplarge : R₁ ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    obtain ⟨r, hr, y, hy, hnorm⟩ := hstress R hlarge
    have hfar : B ≤ ‖y‖ := by
      have hR : B + (t + 1 - s) + 1 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
      linarith
    have hm := hB r hr y hfar
    have hb (τ : ℝ) (hτ : τ ∈ Set.uIoc s t) :
        ‖(t - τ) * cutoffStress (cutoff R) V u τ‖ ≤ (t - s) * (C * δ) := by
      rw [uIoc_of_le hst] at hτ
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hτ.2)]
      apply mul_le_mul (by linarith [hτ.1] : t - τ ≤ t - s)
        ((hnorm τ ⟨hτ.1.le, hτ.2⟩).trans (mul_le_mul_of_nonneg_left hm hC))
        (norm_nonneg _) (sub_nonneg.mpr hst)
    have hE : E = ∫ τ in s..t, (t - τ) * cutoffStress (cutoff R) V u τ := hcap R hcaplarge
    have hbound : ‖E‖ ≤ D * δ := by
      rw [hE]
      calc
        _ ≤ ((t - s) * (C * δ)) * |t - s| := intervalIntegral.norm_integral_le_of_norm_le_const hb
        _ = D * δ := by rw [abs_of_nonneg (sub_nonneg.mpr hst)]; dsimp only [D]; ring
    apply hbound.trans
    have heq : (D + 1) * δ = ε := by
      dsimp only [δ]
      field_simp
    nlinarith [hδ]
  have hzero : ‖E‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖E‖ := lt_of_le_of_ne (norm_nonneg E) (Ne.symm hne)
    have hhalf := hsmall (‖E‖ / 2) (by positivity)
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Planar conservation for a field on the closed forward half-space, with the right
derivative in time at the initial face. The uniform tails concern only potential
values, not derivatives. -/
private theorem forwardEnergy_eq_of_uniform_potential_tails_two {V : ℝ → ℝ} {u : ℝ^3 → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiffOn ℝ 3 u {p | 0 ≤ p 0})
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ r ∈ Icc s t, ∀ x : ℝ^2, B ≤ ‖x‖ →
      |V (u (timeSpaceCons r x))| ≤ ε) :
    forwardSemilinearWaveEnergy V u t = forwardSemilinearWaveEnergy V u s := by
  obtain ⟨U, hU, heq⟩ := exists_contDiff_extension_halfSpace 0 3 hu
  have hU2 : ContDiff ℝ 2 U := hU.of_le (by norm_num)
  have hslice (r : ℝ) (hr : 0 ≤ r) (x : ℝ^2) : U (timeSpaceCons r x) = u (timeSpaceCons r x) :=
    heq (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using hr)
  have hw (r : ℝ) (hr : 0 < r) (x : ℝ^2) :
      semilinearWaveOperator V U (timeSpaceCons r x) = 0 := by
    have hgerm := eventuallyEq_of_eqOn_forward heq
      (show 0 < (timeSpaceCons r x) 0 by simpa only [timeSpaceCons_zero] using hr)
    unfold semilinearWaveOperator
    rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
    exact hwave r hr x
  have hsc (r : ℝ) (hr : 0 ≤ r) :
      HasCompactSupport (fun x : ℝ^2 ↦ U (timeSpaceCons r x)) := by
    simpa only [hslice r hr] using hs r hr
  have htailU : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ r ∈ Icc s t,
      ∀ x : ℝ^2, B ≤ ‖x‖ → |V (U (timeSpaceCons r x))| ≤ ε := by
    intro ε hε
    obtain ⟨B, hB⟩ := htail ε hε
    refine ⟨B, fun r hr x hx ↦ ?_⟩
    rw [hslice r (hs0.trans hr.1)]
    exact hB r hr x hx
  rw [forwardSemilinearWaveEnergy_eq_of_extension V hU2 heq (hs0.trans hst),
    forwardSemilinearWaveEnergy_eq_of_extension V hU2 heq hs0]
  exact energy_eq_of_uniform_potential_tails_two hV hVzero hU hw hsc hs0 hst htailU

/-- In two space dimensions, separate compact displacement slices suffice for
energy conservation. The wave equation supplies uniform potential tails on
each finite time interval; no common support, sign or growth condition is needed. -/
theorem forwardEnergy_eq_of_compact_slices_two {V : ℝ → ℝ} {u : ℝ^3 → ℝ} (hV : ContDiff ℝ 1 V)
    (hVzero : V 0 = 0) (hu : ContDiffOn ℝ 4 u {p | 0 ≤ p 0})
    (hwave : ∀ r, 0 < r → ∀ x, semilinearWaveOperator V u (timeSpaceCons r x) = 0)
    (hs : ∀ r, 0 ≤ r → HasCompactSupport (fun x : ℝ^2 ↦ u (timeSpaceCons r x))) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s ≤ t) :
    forwardSemilinearWaveEnergy V u t = forwardSemilinearWaveEnergy V u s := by
  apply forwardEnergy_eq_of_uniform_potential_tails_two hV hVzero
    (hu.of_le (by norm_num)) hwave hs hs0 hst
  exact fun ε hε ↦ exists_uniform_potential_tail_on_Icc_of_forward_compact_slices_two
    hu hV.continuous_deriv_one hwave hs hV.continuous.continuousAt hVzero hs0 hε

end WaveEquation
