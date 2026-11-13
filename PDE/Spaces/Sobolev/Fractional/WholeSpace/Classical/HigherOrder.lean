/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Classical.Real

/-!
# Higher regularity of canonical Sobolev representatives

The canonical continuous representative gains `r` classical derivatives
above the strict Sobolev threshold `s > dim(E)/2 + r`. Integrable Fourier
moments construct the derivatives. Uniqueness of continuous distributional
representatives identifies this construction with the canonical representative,
so increasing the requested order does not change its point values.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BesselPotentialSpace SchwartzMap BoundedContinuousFunction

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {s : ℝ} {r : ℕ}

/-- The canonical representative has every derivative supplied by the Sobolev
embedding threshold; its point values are independent of the requested order. -/
theorem contDiff_c1Representative_of_order
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1))
    (hr : (Module.finrank ℝ E : ℝ) < 2 * (s - r)) (f : H^{s}(E, F)) :
    ContDiff ℝ r (c1Representative hs f : E → F) := by
  obtain ⟨g, hg, hmom⟩ :=
    PDE.Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev
      hr f.memSobolev_toDistr
  obtain ⟨u, hu, hid⟩ :=
    PDE.Analysis.Fourier.exists_contDiff_representative_of_fourier_eq g hg hmom
  rw [← eq_c1Representative_of_integral_smul hs f hu.continuous hid]
  exact hu

end BesselPotentialSpace

namespace SobolevSpace.Fractional

variable {n r : ℕ} {s : ℝ}

/-- Taking the real part preserves all classical derivatives provided by the
higher Sobolev embedding. No representative regularity is assumed. -/
theorem HsSpaceReal.contDiff_c1Representative_of_order
    (hs : (n : ℝ) < 2 * (s - 1)) (hr : (n : ℝ) < 2 * (s - r))
    (f : HsSpaceReal n s) :
    ContDiff ℝ r (f.c1Representative hs) :=
  Complex.reCLM.contDiff.comp
    (BesselPotentialSpace.contDiff_c1Representative_of_order
      (by simpa using hs) (by simpa using hr) f.1)

end SobolevSpace.Fractional
