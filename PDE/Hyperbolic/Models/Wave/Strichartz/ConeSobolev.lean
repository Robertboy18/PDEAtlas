/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.ClassicalDuhamel
public import PDE.Hyperbolic.Models.Wave.Strichartz.EnergySobolev
import PDE.Hyperbolic.Models.Wave.Fourier.Lp.ConeLocality
import PDE.Hyperbolic.Models.Wave.Fourier.Lp.DuhamelSobolev

/-!
# Spatial Sobolev control inside a backward cone

Causal identification replaces the forcing by its sharp cone restriction.
The physical homogeneous and Duhamel Sobolev bounds then control every closed
cone slice. Initial data are unchanged and the constant is independent of the
center, tip and prefix. No derivative of a cone indicator is taken.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform Filter Set Metric PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

private theorem eLpNorm_realSolution_add_duhamel_six_le (g h : 𝓢(ℝ^3, ℝ)) (b t : ℝ)
    (k : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b))) :
    eLpNorm (fun x ↦ Fourier.realSolution g h (timeSpaceCons t x) +
      (Fourier.duhamelL2 0 b t k x).re) 6 volume ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ≥0∞) * 3 *
        (‖(initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).fst‖ₑ +
        ‖(initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).snd‖ₑ + ‖k‖ₑ) := by
  have hh := eLpNorm_re_waveSolution_six_le
    (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM) t
  have hD := Fourier.eLpNorm_re_duhamelL2_le (q := (6 : NNReal))
    (by norm_num : 0 < 3) (by norm_num) (by norm_num) 0 b t k
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 6)).trans
    ((add_le_add hh hD).trans_eq (mul_add _ _ _).symm)

private theorem ae_classicalWave_cone_eq {b T : ℝ} (hbT : b < T) (c : ℝ^3) (g h : 𝓢(ℝ^3, ℝ))
    (f k : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b)))
    {u U U₂ : ℝ → ℝ^3 → ℝ} (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ))
    (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ))
    (hk : ∀ᵐ s ∂volume.restrict (Icc 0 b), (k s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      (((ball c (T - s)).indicator (fun y ↦ U₂ s y - laplacian (u s) y) x : ℝ) : ℂ))
    (t : ℝ) (ht : t ∈ Icc 0 b) :
    u t =ᵐ[volume.restrict (ball c (T - t))] fun x ↦
      Fourier.realSolution g h (timeSpaceCons t x) + (Fourier.duhamelL2 0 b t k x).re := by
  have hlocal := Fourier.ae_re_duhamelL2_eq_on_ball_of_forcing_eq_on_Icc 0 b T hbT c f k hf hk
    (Eventually.of_forall fun s ↦ Eventually.of_forall fun x hx ↦
      (indicator_of_mem hx (fun y ↦ U₂ s y - laplacian (u s) y)).symm)
  let v : ℝ^3 → ℝ := fun x ↦
    Fourier.realSolution g h (timeSpaceCons t x) + (Fourier.duhamelL2 0 b t k x).re
  have he : u t =ᵐ[volume.restrict (ball c (T - t))] v := by
    apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [Fourier.ae_eq_realSolution_add_duhamelL2_on_Icc g h f
      hu hU hU₂ hdu hdU hu₂ hpos hvel hf t ht, hlocal t ht] with x hx hl hxc
    dsimp only [v]
    rw [hx, hl hxc]
  exact he

/-- Closed-time cone L6 bound with only the sharply masked forcing. -/
theorem eLpNorm_classicalWave_cone_six_le {b T : ℝ} (hbT : b < T) (c : ℝ^3) (g h : 𝓢(ℝ^3, ℝ))
    (f k : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b)))
    {u U U₂ : ℝ → ℝ^3 → ℝ} (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ))
    (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hf : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ))
    (hk : ∀ᵐ s ∂volume.restrict (Icc 0 b), (k s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      (((ball c (T - s)).indicator (fun y ↦ U₂ s y - laplacian (u s) y) x : ℝ) : ℂ))
    (t : ℝ) (ht : t ∈ Icc 0 b) :
    eLpNorm (u t) 6 (volume.restrict (ball c (T - t))) ≤
      (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^3)) 2 : ℝ≥0∞) * 3 *
        (‖(initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).fst‖ₑ +
        ‖(initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)).snd‖ₑ + ‖k‖ₑ) := by
  have he := ae_classicalWave_cone_eq hbT c g h f k hu hU hU₂ hdu hdU hu₂ hpos hvel hf hk t ht
  rw [eLpNorm_congr_ae he]
  exact (eLpNorm_mono_measure (fun x ↦ Fourier.realSolution g h (timeSpaceCons t x) +
      (Fourier.duhamelL2 0 b t k x).re) (p := 6) Measure.restrict_le_self).trans
    (eLpNorm_realSolution_add_duhamel_six_le g h b t k)

end WaveEquation.Strichartz
