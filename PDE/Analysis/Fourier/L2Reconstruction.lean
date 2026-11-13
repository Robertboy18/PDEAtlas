/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.L2Compatibility

/-!
# Recovering integrable Fourier data from an L² inverse

If an integrable datum has a square-integrable inverse Fourier integral, then it
is the Fourier transform of that `L²` class. Schwartz-test uniqueness recovers the
datum without assuming its square-integrability in advance. This also shows that
an integrable datum belongs to `L²` exactly when its inverse integral does.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap

namespace PDE.Analysis.Fourier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An integrable datum whose inverse integral represents an `L²` class is the
Fourier transform of that class. No `L²` premise on the datum is required. -/
theorem fourier_eq_of_fourierInvIntegral_eq_ae {g : E → F} (hg : Integrable g)
    (W : Lp F 2 (volume : Measure E)) (hW : 𝓕⁻ g =ᵐ[volume] W) :
    (𝓕 W : Lp F 2 (volume : Measure E)) =ᵐ[volume] g := by
  have h₁ : MemLp g 1 volume := memLp_one_iff_integrable.mpr hg
  apply ae_eq_of_integral_schwartz_smul_eq
    ((Lp.memLp (𝓕 W)).locallyIntegrable (by norm_num)) hg.locallyIntegrable
  intro φ
  have hdist := congrArg (fun T : 𝓢'(E, F) ↦ T φ)
    (Lp.fourier_toTemperedDistribution_eq W)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at hdist
  calc
    _ = ∫ x, 𝓕 φ x • W x := hdist.symm
    _ = ∫ x, 𝓕 φ x • 𝓕⁻ (h₁.toLp g : E → F) x := by
      apply integral_congr_ae
      filter_upwards [hW] with x hx
      rw [Real.fourierInv_congr_ae h₁.coeFn_toLp x, hx]
    _ = (𝓕⁻ (h₁.toLp g : 𝓢'(E, F))) (𝓕 φ) :=
      integral_smul_fourierInv_eq (h₁.toLp g) (𝓕 φ)
    _ = ∫ x, φ x • g x := by
      rw [TemperedDistribution.fourierInv_apply, fourierInv_fourier_eq,
        Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [h₁.coeFn_toLp] with x hx
      rw [hx]

/-- For integrable data, square-integrability of the inverse Fourier integral is
equivalent to square-integrability of the datum itself. -/
theorem memLp_fourierInvIntegral_iff {g : E → F} (hg : Integrable g) :
    MemLp (𝓕⁻ g) 2 volume ↔ MemLp g 2 volume := by
  constructor
  · intro h
    exact (memLp_congr_ae
      (fourier_eq_of_fourierInvIntegral_eq_ae hg (h.toLp _) h.coeFn_toLp.symm)).mp
        (Lp.memLp _)
  · intro h
    exact (memLp_congr_ae (fourierInvIntegral_eq_L2_ae hg (h.toLp _) h.coeFn_toLp.symm)).mpr
      (Lp.memLp _)

end PDE.Analysis.Fourier
