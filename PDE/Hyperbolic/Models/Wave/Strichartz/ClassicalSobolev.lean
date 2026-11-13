/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.ClassicalDuhamel
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.DuhamelSobolev
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergySobolev

/-!
# Uniform spatial Sobolev bound for classical waves

The classical solution agrees at every closed time with the real Fourier wave
and its physical Duhamel integral. Homogeneous Sobolev bounds on these two terms
give the L6 estimate from initial energy and L1L2 forcing.

This is the `sup ‖v(·, t)‖_{L⁶(ℝ³)}` part of the estimate (4) of Evans, §12.4, Theorem 1. Evans
proves it in step 1 of the proof from the energy identity and the Sobolev inequalities of §5.6.3; we
bound the Fourier and Duhamel terms separately.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equation (4), and step 1 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

private theorem sobolev_component_bound (S A B F D : ℝ≥0∞) (hA : A ≤ D) (hB : B ≤ D) :
    S * 3 * (A + B) + S * 3 * F ≤ S * 6 * (D + F) := by
  calc
    _ ≤ S * 3 * (D + D) + S * 3 * F := add_le_add (mul_le_mul_right (add_le_add hA hB) _) le_rfl
    _ = S * 3 * (D + (D + F)) := by rw [← mul_add, add_assoc]
    _ ≤ S * 3 * ((D + F) + (D + F)) := mul_le_mul_right (add_le_add le_self_add le_rfl) _
    _ = _ := by
      rw [← two_mul, ← mul_assoc, mul_assoc S 3 2]
      norm_num

/-- Every closed time slice of the classical wave has the homogeneous
Sobolev estimate, with no displacement L2 term or extra forcing regularity. -/
theorem eLpNorm_classicalWave_six_le {b : ℝ} (g h : 𝓢(ℝ^3, ℝ))
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b))) {u U U₂ : ℝ → ℝ^3 → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ))
    (t : ℝ) (ht : t ∈ Icc 0 b) :
    eLpNorm (u t) 6 volume ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ≥0∞) * 6 *
      (‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM)‖ₑ +
      ‖f‖ₑ) := by
  let G := g.postcompCLM Complex.ofRealCLM
  let H := h.postcompCLM Complex.ofRealCLM
  let d := initialEnergyDatum G H
  have he := Fourier.ae_eq_realSolution_add_duhamelL2_on_Icc g h f
    hu hU hU₂ hdu hdU hu₂ hpos hvel hr t ht
  rw [eLpNorm_congr_ae he]
  have hh := eLpNorm_re_waveSolution_six_le G H t
  have hD := Fourier.eLpNorm_re_duhamelL2_le (q := (6 : NNReal))
    (by norm_num : 0 < 3) (by norm_num) (by norm_num) 0 b t f
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 6)).trans
    ((add_le_add hh hD).trans (sobolev_component_bound _ _ _ _ _
      (WithLp.enorm_fst_le _ d) (WithLp.enorm_snd_le _ d)))


end WaveEquation.Strichartz
