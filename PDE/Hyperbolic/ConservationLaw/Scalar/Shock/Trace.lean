/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Shock.Interface
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Testing a distribution supported on a moving graph

Every compactly supported C¹ function of time is the trace of a compactly
supported C¹ spacetime test along a C¹ graph. Consequently a continuous jump
coefficient is determined pointwise by its distribution on that graph.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common TopologicalSpace
open scoped Distributions

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Shock

/-- Extend a time test along the graph by a compactly supported normal cutoff. -/
theorem exists_testFunction_trace {s : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    ∃ φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ), ∀ t, φ (interface s t) = g t := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨1, 2, zero_lt_one, by norm_num⟩
  let f : ℝ^2 → ℝ := fun p ↦ g (p 0) * b (p 1 - s (p 0))
  have hf : ContDiff ℝ 1 f := by
    dsimp [f]
    have h0 : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 0) := by fun_prop
    have h1 : ContDiff ℝ 1 (fun p : ℝ^2 ↦ p 1) := by fun_prop
    exact (hg.comp h0).mul (b.contDiff.comp (h1.sub (hs.comp h0)))
  let shear : ℝ × ℝ → ℝ^2 := fun z ↦ !₂[z.1, z.2 + s z.1]
  have hshear : Continuous shear := by
    change Continuous (fun z : ℝ × ℝ ↦ WithLp.toLp 2 ![z.1, z.2 + s z.1])
    fun_prop
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro ((hgc.prod b.hasCompactSupport).image hshear) ?_
    intro p hp
    by_cases hg0 : g (p 0) = 0
    · simp [f, hg0]
    by_cases hb0 : b (p 1 - s (p 0)) = 0
    · simp [f, hb0]
    exfalso
    apply hp
    refine ⟨(p 0, p 1 - s (p 0)), ⟨subset_tsupport _ hg0, subset_tsupport _ hb0⟩, ?_⟩
    ext i
    fin_cases i <;> simp [shear]
  refine ⟨⟨f, hf, hfc, subset_univ _⟩, fun t ↦ ?_⟩
  have hb : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  change f (interface s t) = g t
  simp [f, interface, hb]

/-- A continuous coefficient with zero pairing against all spacetime tests on
the graph vanishes at every time. -/
theorem eq_zero_of_integral_mul_trace_eq_zero {s c : ℝ → ℝ} (hs : ContDiff ℝ 1 s)
    (hc : Continuous c) (h : ∀ φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ), (∫ t, c t * φ (interface s t)) = 0) :
    ∀ t, c t = 0 := by
  have hae : ∀ᵐ t, c t = 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable
      (fun g hg hgc ↦ by
        obtain ⟨φ, hφ⟩ := exists_testFunction_trace hs (hg.of_le (by simp)) hgc
        simpa only [hφ, smul_eq_mul, mul_comm] using h φ)
  exact fun t ↦ congrFun (Measure.eq_of_ae_eq hae hc continuous_const) t

end PDE.Hyperbolic.ConservationLaw.Scalar.Shock
