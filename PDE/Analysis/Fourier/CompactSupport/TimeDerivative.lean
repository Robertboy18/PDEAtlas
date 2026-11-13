/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform
public import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport

/-!
# Time differentiation of compactly supported Fourier integrals

Local continuity of a family and its time derivative, together with a
common compact spatial support, justify time differentiation of the Fourier
integral.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Fourier transformation commutes with the time derivative of a
locally compactly supported continuous family. -/
theorem hasDerivAt_fourier_of_locally_uniform_compact_support
    {u D : ℝ → V → E} {I : Set ℝ} {K : Set V}
    (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContinuousOn u.uncurry (I ×ˢ univ))
    (hD : ContinuousOn D.uncurry (I ×ˢ univ))
    (hd : ∀ t ∈ I, ∀ x, HasDerivAt (fun s ↦ u s x) (D t x) t)
    (hs : ∀ t ∈ I, ∀ x ∉ K, u t x = 0)
    {t : ℝ} (ht : t ∈ I) (ξ : V) :
    HasDerivAt (fun s ↦ (𝓕 (u s)) ξ) ((𝓕 (D t)) ξ) t := by
  let c : V → ℂ := fun x ↦ Complex.exp ((↑(-2 * Real.pi * ⟪x, ξ⟫)) * Complex.I)
  have hc : Continuous c := by fun_prop
  simp_rw [Real.fourier_eq']
  apply hasDerivAt_integral_of_locally_uniform_compact_support
    (f := fun s x ↦ c x • u s x) (D := fun s x ↦ c x • D s x)
    (μ := volume) hI hK
    ((hc.comp continuous_snd).continuousOn.smul hu)
    ((hc.comp continuous_snd).continuousOn.smul hD)
  · intro s hsI x
    exact (hd s hsI x).const_smul (c x)
  · intro s hsI x hx
    simp only [hs s hsI x hx, smul_zero]
  · exact ht

end PDE.Analysis.Fourier
