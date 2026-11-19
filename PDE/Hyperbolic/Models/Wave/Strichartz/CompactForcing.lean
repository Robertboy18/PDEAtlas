/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.Cone
import PDE.Analysis.MeasureTheory.Lp.MixedSections.Complex

/-!
# The cone estimate for continuous compact forcing

Continuous forcing on a finite closed slab with common compact spatial support
supplies the full and sharply restricted Bochner classes. The classical cone
estimate then has the restricted forcing integral on its right side.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- A continuous compact classical forcing has the cone estimate without
assuming any Bochner forcing class or linear estimate. -/
theorem eLpNorm_classicalWave_cone_le_of_compact_forcing {b T : ℝ} (hbT : b < T) (c : ℝ^3)
    (g h : 𝓢(ℝ^3, ℝ)) {u U U₂ : ℝ → ℝ^3 → ℝ} {F : ℝ × ℝ^3 → ℝ} {K : Set (ℝ^3)} (hK : IsCompact K)
    (hF : ContinuousOn F (Icc 0 b ×ˢ univ)) (hzero : ∀ t ∈ Icc 0 b, ∀ x, x ∉ K → F (t, x) = 0)
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hwave : ∀ s ∈ Icc 0 b, ∀ x, U₂ s x - laplacian (u s) x = F (s, x)) :
    eLpNorm (fun t ↦ eLpNorm (u t) 12 (volume.restrict (ball c (T - t)))) 4
      (volume.restrict (Icc 0 b)) ≤
      ENNReal.ofReal (energyAdjointBound *
        (‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
          (h.postcompCLM Complex.ofRealCLM)‖ +
        ∫ t in Icc 0 b, lpNorm (fun x ↦ F (t, x)) 2
          (volume.restrict (ball c (T - t))))) := by
  let S : Set (ℝ × ℝ^3) := {z | dist z.2 c < T - z.1}
  have hS : MeasurableSet S := (isOpen_lt (continuous_snd.dist continuous_const)
      (continuous_const.sub continuous_fst)).measurableSet
  obtain ⟨f, k, hf, hk, hknorm⟩ := exists_complex_L1_L2_sections_indicator hK hF hzero hS
  have hforcing : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
        ((U₂ s x - laplacian (u s) x : ℝ) : ℂ) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with s hs hsb
    simpa only [hwave s hsb] using hs
  have hmasked : ∀ᵐ s ∂volume.restrict (Icc 0 b), (k s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
        (((ball c (T - s)).indicator (fun y ↦ U₂ s y - laplacian (u s) y) x : ℝ) : ℂ) := by
    filter_upwards [hk, ae_restrict_mem measurableSet_Icc] with s hs hsb
    filter_upwards [hs] with x hx
    rw [hx]
    by_cases hmem : x ∈ ball c (T - s)
    · have hz : (s, x) ∈ S := hmem
      rw [indicator_of_mem hz, indicator_of_mem hmem, hwave s hsb x]
    · have hz : (s, x) ∉ S := hmem
      rw [indicator_of_notMem hz, indicator_of_notMem hmem]
  have hn : ‖k‖ = ∫ t in Icc 0 b, lpNorm (fun x ↦ F (t, x)) 2
      (volume.restrict (ball c (T - t))) := hknorm
  simpa only [hn] using eLpNorm_classicalWave_cone_le
    hbT c g h f k hu hU hU₂ hdu hdU hu₂ hpos hvel hforcing hmasked

end WaveEquation.Strichartz
