/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Joint continuity of Fourier integrals with compact support

A continuous family with common compact spatial support has a Fourier transform
jointly continuous in the original parameter and frequency.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace

namespace PDE.Analysis.Fourier

variable {X V E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A common compact support gives joint parameter-frequency continuity of the
Fourier integral. -/
theorem continuousOn_fourier_of_uniform_compact_support
    {f : X × V → E} {I : Set X} {K : Set V} (hK : IsCompact K)
    (hf : ContinuousOn f (I ×ˢ univ))
    (hs : ∀ t ∈ I, ∀ x ∉ K, f (t, x) = 0) :
    ContinuousOn (fun p : X × V ↦ 𝓕 (fun x ↦ f (p.1, x)) p.2) (I ×ˢ univ) := by
  let c : (X × V) × V → ℂ :=
    fun p ↦ Complex.exp ((↑(-2 * Real.pi * ⟪p.2, p.1.2⟫)) * Complex.I)
  have hc : Continuous c := by fun_prop
  have hg : ContinuousOn (fun p : (X × V) × V ↦ f (p.1.1, p.2))
      ((I ×ˢ univ) ×ˢ univ) :=
    hf.comp (continuous_fst.fst.prodMk continuous_snd).continuousOn
      (fun p hp ↦ ⟨hp.1.1, mem_univ p.2⟩)
  simp_rw [Real.fourier_eq']
  apply continuousOn_integral_of_compact_support (μ := volume)
    (f := fun p x ↦ c (p, x) • f (p.1, x)) hK (hc.continuousOn.smul hg)
  intro p x hp hx
  simp only [hs p.1 hp.1 x hx, smul_zero]

end PDE.Analysis.Fourier
