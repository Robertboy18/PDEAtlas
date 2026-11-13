/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Fourier.ClassicalDuhamel
public import PDE.Hyperbolic.Models.Wave.Strichartz.Duhamel

/-!
# The mixed Strichartz estimate for a classical forced wave

Closed forward classical traces and an L1L2 residual identify the wave
with its Fourier homogeneous solution plus physical Duhamel evolution. The
proved operator bound therefore controls the L4 in time, L12 in space
seminorm.

The initial datum norm contains exactly the L2 gradient energy of displacement
and the L2 velocity energy. This is the mixed-norm part `‖v‖_{L⁴(0,T;L¹²(ℝ³))}` of the estimate (4)
of Evans, §12.4, Theorem 1, which Evans states without proof, referring to the literature in step 2
of the proof; the uniform-in-time L6 estimate is in `Strichartz.ClassicalSobolev`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 1, equations (3)-(4), and step 2 of its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set PDE PDE.Common
open scoped ENNReal SchwartzMap

namespace WaveEquation.Strichartz

/-- The classical forced wave has the L4L12 estimate with the initial
energy norm and L1L2 forcing. -/
theorem eLpNorm_classicalWave_le {b : ℝ} (g h : 𝓢(ℝ^3, ℝ))
    (f : Lp (Lp ℂ 2 (volume : Measure (ℝ^3))) 1 (volume.restrict (Icc 0 b))) {u U U₂ : ℝ → ℝ^3 → ℝ}
    (hu : ContinuousOn u.uncurry (Icc 0 b ×ˢ univ)) (hU : ContinuousOn U.uncurry (Icc 0 b ×ˢ univ))
    (hU₂ : ContinuousOn U₂.uncurry (Ioo 0 b ×ˢ univ))
    (hdu : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ u r x) (U s x) s)
    (hdU : ∀ s ∈ Ioo 0 b, ∀ x, HasDerivAt (fun r ↦ U r x) (U₂ s x) s)
    (hu₂ : ∀ s ∈ Ioo 0 b, ContDiff ℝ 2 (u s)) (hpos : ∀ x, u 0 x = g x) (hvel : ∀ x, U 0 x = h x)
    (hr : ∀ᵐ s ∂volume.restrict (Icc 0 b), (f s : ℝ^3 → ℂ) =ᵐ[volume] fun x ↦
      ((U₂ s x - laplacian (u s) x : ℝ) : ℂ)) :
    eLpNorm (fun t ↦ eLpNorm (u t) 12 volume) 4 (volume.restrict (Icc 0 b)) ≤
      ENNReal.ofReal (energyAdjointBound * (‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
      (h.postcompCLM Complex.ofRealCLM)‖ + ‖f‖)) := by
  have hc : Continuous (fun t : ℝ ↦ Fourier.duhamelL2 0 b t f) :=
    (Fourier.lipschitzWith_duhamelL2 0 b f).continuous
  have hex := StronglyMeasurable.exists_jointLpRepresentative
    (p := 2) (ν := (volume : Measure (ℝ^3))) hc.stronglyMeasurable
  let F := hex.choose
  have hF : Measurable F := hex.choose_spec.1
  have hsection (t : ℝ) : (fun x ↦ F (t, x)) =ᵐ[volume]
      (Fourier.duhamelL2 0 b t f : ℝ^3 → ℂ) := hex.choose_spec.2 t
  let G := g.postcompCLM Complex.ofRealCLM
  let H := h.postcompCLM Complex.ofRealCLM
  let v : ℝ → ℝ^3 → ℝ := fun t x ↦
    (Fourier.waveSolution (𝓕 G : 𝓢(ℝ^3, ℂ)) (𝓕 H : 𝓢(ℝ^3, ℂ)) (t, x)).re + (F (t, x)).re
  have he (t : ℝ) (ht : t ∈ Icc 0 b) : u t =ᵐ[volume] v t := by
    have hi := Fourier.ae_eq_realSolution_add_duhamelL2_on_Icc g h f
      hu hU hU₂ hdu hdU hu₂ hpos hvel hr t ht
    filter_upwards [hi, hsection t] with x hx hFx
    dsimp only [v]
    rw [hx, hFx]
    congr 1
  have hnorm : eLpNorm (fun t ↦ eLpNorm (u t) 12 volume) 4
      (volume.restrict (Icc 0 b)) ≤ eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4 volume := by
    calc
      _ = eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4
          (volume.restrict (Icc 0 b)) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact eLpNorm_congr_ae (he t ht)
      _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfinite : eLpNorm (fun t ↦ eLpNorm (v t) 12 volume) 4 volume ≠ ∞ := by
    change eLpNorm (fun t ↦ eLpNorm (fun x ↦ _) 12 volume) 4 volume ≠ ∞
    rw [eLpNorm_fourierWave_add_duhamelL2_eq G H 0 b f hF hsection]
    exact enorm_ne_top
  have hbnd := mixedNorm_fourierWave_add_duhamelL2_le G H 0 b f hF hsection
  exact hnorm.trans ((ENNReal.ofReal_toReal hfinite).symm.trans_le (ENNReal.ofReal_le_ofReal hbnd))

end WaveEquation.Strichartz
