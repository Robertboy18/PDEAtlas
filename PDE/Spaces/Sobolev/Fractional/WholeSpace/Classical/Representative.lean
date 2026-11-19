/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SobolevMoments
public import PDE.Analysis.Fourier.L1Reconstruction
public import PDE.DistributionTheory.TemperedDistribution.Representative.Uniqueness
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# The canonical C¹ representative of fractional Sobolev data

Above the strict `dim(E)/2 + 1` threshold a Bessel-potential datum has
a unique continuous representative. It is bounded and `C¹`. The construction
uses the integrable Fourier moments; uniqueness makes it independent
of the chosen Fourier representative.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap BesselPotentialSpace BoundedContinuousFunction

namespace BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {s : ℝ}

/-- The strict fractional Sobolev threshold provides a bounded `C¹`
representative of the original distribution. -/
theorem exists_contDiff_one_representative
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1)) (f : H^{s}(E, F)) :
    ∃ u : E →ᵇ F, ContDiff ℝ 1 (u : E → F) ∧
      ∀ φ : 𝓢(E, ℂ), (∫ x, φ x • u x) = f.toDistr φ := by
  obtain ⟨g, hg, hmom⟩ :=
    PDE.Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev
      (r := 1) (by simpa using hs) f.memSobolev_toDistr
  exact PDE.Analysis.Fourier.exists_contDiff_representative_of_fourier_eq g hg hmom

/-- The unique continuous representative of a fractional Sobolev datum
above the first-derivative embedding threshold. -/
def c1Representative (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1))
    (f : H^{s}(E, F)) : E →ᵇ F :=
  (exists_contDiff_one_representative hs f).choose

/-- The canonical representative has continuous first derivatives. -/
theorem contDiff_c1Representative
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1)) (f : H^{s}(E, F)) :
    ContDiff ℝ 1 (c1Representative hs f : E → F) :=
  (exists_contDiff_one_representative hs f).choose_spec.1

/-- The canonical representative is the original Sobolev distribution. -/
theorem integral_smul_c1Representative
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1)) (f : H^{s}(E, F))
    (φ : 𝓢(E, ℂ)) :
    (∫ x, φ x • c1Representative hs f x) = f.toDistr φ :=
  (exists_contDiff_one_representative hs f).choose_spec.2 φ

/-- Any continuous representative of the original distribution equals the
canonical representative pointwise. -/
theorem eq_c1Representative_of_integral_smul
    (hs : (Module.finrank ℝ E : ℝ) < 2 * (s - 1)) (f : H^{s}(E, F))
    {u : E → F} (hu : Continuous u)
    (h : ∀ φ : 𝓢(E, ℂ), (∫ x, φ x • u x) = f.toDistr φ) :
    u = c1Representative hs f :=
  hu.eq_of_integral_schwartz_smul_eq (c1Representative hs f).continuous
    (fun φ ↦ (h φ).trans (integral_smul_c1Representative hs f φ).symm)

end BesselPotentialSpace
