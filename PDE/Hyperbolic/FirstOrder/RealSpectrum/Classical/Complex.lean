/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.RealSpectrum.Reconstruction
public import PDE.Analysis.Fourier.MatrixSymbol.DifferentialIdentity

/-!
# A classical real-spectrum evolution from fractional Sobolev data

The inverse Fourier integral is a single jointly `C¹` function, and its
Fréchet derivative satisfies the full system at every signed time. The input
is fractional Sobolev membership; Fourier moments and differentiability
are derived.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped SchwartzMap Matrix.Norms.L2Operator

namespace PDE.Hyperbolic.FirstOrder

variable {n m : ℕ}

/-- A real-spectrum system has a joint classical Fourier solution
from a fractional Sobolev datum. The same solution attains the initial
distribution and satisfies the PDE at time zero as well as at positive times. -/
theorem exists_jointC1_realSpectrumEvolution_of_memSobolev (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n, ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0) {s : ℝ}
    (hs : (n : ℝ) < 2 * (s - m)) {f : 𝓢'(ℝ^n, EuclideanSpace ℂ (Fin m))}
    (hf : TemperedDistribution.MemSobolev s 2 f) :
    ∃ g : Lp (EuclideanSpace ℂ (Fin m)) 1 (volume : Measure (ℝ^n)),
      𝓕 f = (g : 𝓢'(ℝ^n, EuclideanSpace ℂ (Fin m))) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ^n ↦ realSpectrumFourierEvolution A g p.1 p.2) ∧
      (∀ p : ℝ × ℝ^n,
        Analysis.Fourier.symbolContraction A
          (fderiv ℝ (fun q : ℝ × ℝ^n ↦ realSpectrumFourierEvolution A g q.1 q.2) p) = 0) ∧
      ∀ φ : 𝓢(ℝ^n, ℂ),
        (∫ x, φ x • realSpectrumFourierEvolution A g 0 x) = f φ := by
  have hs' : (Module.finrank ℝ (ℝ^n) : ℝ) < 2 * (s - m) := by simpa using hs
  obtain ⟨g, hg, hmom⟩ :=
    Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev (r := m) hs' hf
  refine ⟨g, hg, (Analysis.Fourier.contDiff_one_symbolEvolution A hA g hmom).1, ?_, ?_⟩
  · exact Analysis.Fourier.symbolContraction_fderiv_symbolEvolution A hA g hmom
  · intro φ
    rw [realSpectrumFourierEvolution_zero,
      Analysis.Fourier.integral_smul_fourierInv_eq, ← hg, fourierInv_fourier_eq]

end PDE.Hyperbolic.FirstOrder
