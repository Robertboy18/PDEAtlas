/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.ConeLocality
public import PDE.Hyperbolic.Models.Wave.Strichartz.Classical

/-!
# The classical Strichartz estimate inside a backward cone

The classical wave has an L4 in time, L12 in space bound inside a
backward cone with only the forcing in that cone on the right-hand side.
Backward test propagation identifies the sharply restricted physical forcing
with the full forcing inside the cone. The homogeneous initial data stay
unchanged, so their energy bound is independent of the cone center and tip.

The Bochner forcing classes represent residuals. Their construction from continuous compactly
supported forcing is in `Strichartz.CompactForcing`.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set Metric PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The classical wave inside a backward cone satisfies the physical mixed
estimate with only the sharply restricted forcing. The global residual class
is used for identification; its norm does not occur in the bound. -/
theorem eLpNorm_classicalWave_cone_le {b T : ℝ} (hbT : b < T) (c : ℝ^3) (g h : 𝓢(ℝ^3, ℝ))
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
      (((ball c (T - s)).indicator (fun y ↦ U₂ s y - laplacian (u s) y) x : ℝ) : ℂ)) :
    eLpNorm (fun t ↦ eLpNorm (u t) 12 (volume.restrict (ball c (T - t)))) 4
      (volume.restrict (Icc 0 b)) ≤
      ENNReal.ofReal (energyAdjointBound *
        (‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)‖ + ‖k‖)) := by
  classical
  have hlocal := Fourier.ae_re_duhamelL2_eq_on_ball_of_forcing_eq_on_Icc 0 b T hbT c f k hf hk
    (Eventually.of_forall fun s ↦ Eventually.of_forall fun x hx ↦
      (indicator_of_mem hx (fun y ↦ U₂ s y - laplacian (u s) y)).symm)
  obtain ⟨F, hF, hsection, _⟩ := exists_jointRepresentative_retardedWaveOperator_duhamelL2 0 b k
  let G := g.postcompCLM Complex.ofRealCLM
  let H := h.postcompCLM Complex.ofRealCLM
  let v : ℝ → ℝ^3 → ℝ := fun t x ↦
    (Fourier.waveSolution (𝓕 G : 𝓢(ℝ^3, ℂ)) (𝓕 H : 𝓢(ℝ^3, ℂ)) (t, x)).re + (F (t, x)).re
  have hv : Measurable v.uncurry := (Complex.continuous_re.measurable.comp
    (Fourier.schwartz_wave_regular (𝓕 G) (𝓕 H)).1.continuous.measurable).add
      (Complex.continuous_re.measurable.comp hF)
  let V : ℝ × ℝ^3 → ℝ := {z | dist z.2 c < T - z.1}.indicator v.uncurry
  have hm : Measurable V := hv.indicator (isOpen_lt (continuous_snd.dist continuous_const)
      (continuous_const.sub continuous_fst)).measurableSet
  have hvnorm (t : ℝ) : eLpNorm (fun x ↦ V (t, x)) 12 volume =
      eLpNorm (v t) 12 (volume.restrict (ball c (T - t))) := by
    rw [show (fun x ↦ V (t, x)) = (ball c (T - t)).indicator (v t) from funext fun x ↦ by
        simp only [V, indicator_apply, mem_ofPred_eq, mem_ball, Function.uncurry_apply_pair],
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet]
  have hnorm : eLpNorm (fun t ↦ eLpNorm (u t) 12
      (volume.restrict (ball c (T - t)))) 4 (volume.restrict (Icc 0 b)) ≤
        eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4 volume := by
    calc
      _ = eLpNorm (fun t ↦ eLpNorm (fun x ↦ V (t, x)) 12 volume) 4
          (volume.restrict (Icc 0 b)) := by
        refine eLpNorm_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        rw [hvnorm]
        refine eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr ?_)
        filter_upwards [Fourier.ae_eq_realSolution_add_duhamelL2_on_Icc g h f
          hu hU hU₂ hdu hdU hu₂ hpos hvel hf t ht, hlocal t ht, hsection t] with x hx hl hFx hxc
        dsimp only [v]
        rw [hx, hl hxc, hFx]
        congr 1
      _ ≤ eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4 (volume.restrict (Icc 0 b)) := by
        apply eLpNorm_mono_enorm_ae
          (hm.eLpNorm_prod_right (by norm_num) (by norm_num)).aestronglyMeasurable
        filter_upwards with t
        simp only [enorm_eq_self, hvnorm]
        exact eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfinite : eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4 volume ≠ ∞ := by
    change eLpNorm (fun t ↦ eLpNorm (fun x ↦ _) 12 volume) 4 volume ≠ ∞
    rw [eLpNorm_fourierWave_add_duhamelL2_eq G H 0 b k hF hsection]
    exact enorm_ne_top
  exact hnorm.trans ((ENNReal.ofReal_toReal hfinite).symm.trans_le (ENNReal.ofReal_le_ofReal
    (mixedNorm_fourierWave_add_duhamelL2_le G H 0 b k hF hsection)))

end WaveEquation.Strichartz
