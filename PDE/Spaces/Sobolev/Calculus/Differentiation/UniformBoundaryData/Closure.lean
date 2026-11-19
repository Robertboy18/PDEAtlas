/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Algebra

/-!
# Classical closure regularity from continuous derivative extensions

On a bounded domain, continuous derivative extensions to the closure are uniformly
continuous there. These constructors connect finite continuous jet calculations with
the raw classical regularity predicate, without requiring differentiability
of the extensions across the boundary.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.ContDiffUpToBoundary

open Set

variable {n k : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}

/-- Raw closure data are integrable on a bounded open domain. -/
theorem integrableOn (hf : ContDiffUpToBoundary k f Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    MeasureTheory.IntegrableOn f Ω :=
  MeasureTheory.memLp_one_iff_integrable.mp
    (hf.memLp_iteratedPartialDeriv hopen hbounded 1 [] (Nat.zero_le k))

/-- Continuous extensions of all classical derivatives through order `k` supply
the raw closure regularity on a bounded domain. -/
theorem of_continuous_derivative_extensions (hf : ContDiffOn ℝ k f Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hext : ∀ α : List (Fin n), α.length ≤ k →
      ∃ g : ℝ^n → ℝ, ContinuousOn g (closure Ω) ∧
        EqOn g (iteratedPartialDeriv α f) Ω) :
    ContDiffUpToBoundary k f Ω := by
  refine ⟨hf, fun α hα ↦ ?_⟩
  obtain ⟨g, hg, heq⟩ := hext α hα
  exact ((hbounded.isCompact_closure.uniformContinuousOn_of_continuous hg).mono
    subset_closure).congr heq

/-- Ambient finite classical regularity supplies raw closure data on any bounded set. -/
theorem of_contDiff (hf : ContDiff ℝ k f) (hbounded : Bornology.IsBounded Ω) :
    ContDiffUpToBoundary k f Ω :=
  of_continuous_derivative_extensions hf.contDiffOn hbounded fun α hα ↦
    ⟨_, (PDE.contDiff_iteratedPartialDeriv_of_le hf α hα).continuous.continuousOn,
      fun _ _ ↦ rfl⟩

/-- At first order, continuous value and partial-derivative extensions suffice. -/
theorem of_continuous_first_derivative_extensions (hf : ContDiffOn ℝ 1 f Ω)
    (hbounded : Bornology.IsBounded Ω)
    {F : ℝ^n → ℝ} (hF : ContinuousOn F (closure Ω)) (hFf : EqOn F f Ω)
    (hpartial : ∀ i, ∃ g : ℝ^n → ℝ, ContinuousOn g (closure Ω) ∧
      EqOn g (∂[i] f) Ω) :
    ContDiffUpToBoundary 1 f Ω := by
  apply of_partialDeriv hf
    (((hbounded.isCompact_closure.uniformContinuousOn_of_continuous hF).mono
      subset_closure).congr hFf)
  intro i
  obtain ⟨g, hg, heq⟩ := hpartial i
  exact of_uniformContinuousOn
    (((hbounded.isCompact_closure.uniformContinuousOn_of_continuous hg).mono
      subset_closure).congr heq)

end SobolevSpace.ContDiffUpToBoundary
