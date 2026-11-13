/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SobolevMoments
public import PDE.Analysis.Fourier.MatrixSymbol.Regularity

/-!
# Spatial Fourier reconstruction for a real-spectrum system

For constant matrices `Aⱼ`, the Fourier evolution is multiplication by
`exp(-2πit ∑ⱼ ξⱼ Aⱼ)`. The factor `2π` matches Mathlib's Fourier convention.
If every real-frequency symbol has real spectrum, the exponential has polynomial
growth of degree at most `m - 1`, even when the symbol has Jordan blocks.

For Sobolev data of real order `s > n/2 + m`, this polynomial bound makes the
evolved Fourier datum and its first frequency moment integrable. Inverse Fourier
integration therefore constructs a `C¹` spatial representative at every
nonnegative time. The representatives are jointly continuous in space and time,
including at zero. Their initial Schwartz-test integrals equal the prescribed
Sobolev distribution.

This is the reconstruction step in the proof of Theorem 5 of Evans, §7.3.3: the solution formula
(39), justified in steps 2-6 of that proof. Evans bounds the exponential through the contour
integral (45) instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.3, proof of Theorem 5, equations (36)-(49).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform NormedSpace
open scoped BigOperators SchwartzMap Matrix.Norms.L2Operator ContDiff

namespace PDE.Hyperbolic.FirstOrder

variable {n m : ℕ}

/-- Inverse Fourier evolution for a constant matrix system, using Mathlib's
`2π` convention. Integrability and regularity are proved below. -/
def realSpectrumFourierEvolution
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1
      (volume : Measure (ℝ^n)))
    (t : ℝ) : ℝ^n → EuclideanSpace ℂ (Fin m) :=
  𝓕⁻ (fun ξ : ℝ^n ↦
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)
      (exp ((2 * Real.pi * t) • (-Complex.I • (∑ j, ξ j • A j)))) (g ξ))

/-- At time zero the constructed evolution is exactly the inverse Fourier
integral of the datum. -/
theorem realSpectrumFourierEvolution_zero (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1 (volume : Measure (ℝ^n))) :
    realSpectrumFourierEvolution A g 0 = 𝓕⁻ (g : ℝ^n → EuclideanSpace ℂ (Fin m)) := by
  simp [realSpectrumFourierEvolution]

/-- The polynomial propagator bound gives joint continuity of the inverse
Fourier construction on every bounded nonnegative time interval. The domination
is independent of the spatial point, so the conclusion includes the initial
time and arbitrary simultaneous space-time approaches to it. -/
theorem continuousOn_realSpectrumFourierEvolution (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n, ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1 (volume : Measure (ℝ^n)))
    (hmom : Integrable (fun ξ : ℝ^n ↦ ‖ξ‖ ^ (m - 1) * ‖g ξ‖)) {T : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ^n ↦
      realSpectrumFourierEvolution A g p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) := by
  let M : ℝ → ℝ^n → EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    PDE.Analysis.Fourier.symbolMultiplier A
  let K : (ℝ × ℝ^n) → ℝ^n → EuclideanSpace ℂ (Fin m) :=
    fun p ξ ↦ Real.fourierChar (inner ℝ ξ p.2) • M p.1 ξ (g ξ)
  obtain ⟨C, _, hC⟩ := PDE.Analysis.Fourier.exists_norm_symbolMultiplier_le A hA (T := T)
  have hdom : Integrable (fun ξ : ℝ^n ↦
      C * (1 + ‖ξ‖ ^ (m - 1)) * ‖g ξ‖) := by
    convert ((L1.integrable_coeFn g).norm.add hmom).const_mul C using 1
    ext ξ
    dsimp only [Pi.add_apply]
    ring
  have hmeas (p : ℝ × ℝ^n) :
      AEStronglyMeasurable (K p) volume := by
    have hMg : AEStronglyMeasurable (fun ξ ↦ M p.1 ξ (g ξ)) volume :=
      PDE.Analysis.Fourier.aestronglyMeasurable_symbolMultiplier_apply A p.1
        (Lp.memLp g).aestronglyMeasurable
    exact (Real.continuous_fourierChar.comp
      (continuous_id.inner continuous_const)).aestronglyMeasurable.fun_smul hMg
  have hbound (p : ℝ × ℝ^n) (hp : p ∈ Set.Icc 0 T ×ˢ Set.univ) :
      ∀ᵐ ξ, ‖K p ξ‖ ≤ C * (1 + ‖ξ‖ ^ (m - 1)) * ‖g ξ‖ := by
    filter_upwards with ξ
    dsimp only [K]
    rw [Circle.norm_smul]
    exact ((M p.1 ξ).le_opNorm (g ξ)).trans (mul_le_mul_of_nonneg_right
        (hC p.1 (by simpa only [abs_of_nonneg hp.1.1] using hp.1.2) ξ) (norm_nonneg _))
  have hcont (ξ : ℝ^n) :
      Continuous (fun p : ℝ × ℝ^n ↦ K p ξ) := by
    have hM : Continuous (fun p : ℝ × ℝ^n ↦ M p.1 ξ) := by
      have htime : Continuous (fun t : ℝ ↦ PDE.Analysis.Fourier.symbolMultiplier A t ξ) :=
        continuous_iff_continuousAt.mpr fun t ↦
          (PDE.Analysis.Fourier.hasDerivAt_symbolMultiplier A ξ t).continuousAt
      exact htime.comp continuous_fst
    exact (Real.continuous_fourierChar.comp
      (continuous_const.inner continuous_snd)).smul (hM.clm_apply continuous_const)
  have h := continuousOn_of_dominated (fun p _ ↦ hmeas p) hbound hdom
    (Filter.Eventually.of_forall fun ξ ↦ (hcont ξ).continuousOn)
  simpa only [realSpectrumFourierEvolution, Real.fourierInv_eq, K, M,
    PDE.Analysis.Fourier.symbolMultiplier] using h

/-- Real-spectrum coefficients and Sobolev regularity produce a single Fourier
datum whose inverse evolution is jointly continuous, has `C¹` spatial slices,
and attains the prescribed initial distribution. The construction includes zero dimensions.
No diagonalizability or integral identities are hypotheses. -/
theorem exists_realSpectrumFourierEvolution_of_memSobolev (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n, ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0) {s : ℝ}
    (hs : (n : ℝ) < 2 * (s - m)) {f : 𝓢'(ℝ^n, EuclideanSpace ℂ (Fin m))}
    (hf : TemperedDistribution.MemSobolev s 2 f) :
    ∃ g : Lp (EuclideanSpace ℂ (Fin m)) 1
        (volume : Measure (ℝ^n)),
      𝓕 f = (g : 𝓢'(ℝ^n, EuclideanSpace ℂ (Fin m))) ∧
      (∀ t : ℝ, 0 ≤ t → ContDiff ℝ 1 (realSpectrumFourierEvolution A g t)) ∧
      (∀ T : ℝ, 0 ≤ T → ContinuousOn
        (fun p : ℝ × ℝ^n ↦ realSpectrumFourierEvolution A g p.1 p.2)
        (Set.Icc 0 T ×ˢ Set.univ)) ∧
      ∀ φ : 𝓢(ℝ^n, ℂ),
        (∫ x, φ x • realSpectrumFourierEvolution A g 0 x) = f φ := by
  have hs' : (Module.finrank ℝ (ℝ^n) : ℝ) < 2 * (s - m) := by
    simpa only [finrank_euclideanSpace_fin (𝕜 := ℝ)] using hs
  obtain ⟨g, hg, hmom⟩ :=
    PDE.Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev (r := m) hs' hf
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro t _
    have hpre : ContDiff ℝ 1 (fun x : ℝ^n ↦ (t, x)) := contDiff_const.prodMk contDiff_id
    have hc := (PDE.Analysis.Fourier.contDiff_one_symbolEvolution A hA g hmom).1.comp hpre
    exact hc
  · exact fun T _ ↦ continuousOn_realSpectrumFourierEvolution A hA g
      (hmom (m - 1) (Nat.sub_le m 1))
  · intro φ
    rw [realSpectrumFourierEvolution_zero, PDE.Analysis.Fourier.integral_smul_fourierInv_eq, ← hg,
      fourierInv_fourier_eq]

end PDE.Hyperbolic.FirstOrder
