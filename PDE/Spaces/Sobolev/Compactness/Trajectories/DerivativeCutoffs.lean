/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.Compactness.LocalTrials
public import PDE.Spaces.Sobolev.Compactness.RellichKondrachov.DerivativeCutoff

/-!
# Uniform local convergence of recovered Sobolev derivatives

An energy bound and scalar time estimates on a dense family of trial tests
select one weak trajectory and one subsequence. Every bounded linear recovery
into a finite-exponent Sobolev space then converges uniformly in time after
localization and differentiation below the top order.

The subsequence is chosen before the dimension, exponent, Sobolev order,
recovery map, derivative word, and test function. Different recovered fields
therefore share the same limit without a further subsequence extraction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace TopologicalSpace
open scoped ENNReal Topology BoundedContinuousFunction Distributions Sobolev

namespace PDE.Analysis.Evolution

/-- Uniform energy bounds and eventual scalar time bounds for each fixed trial
test give a common weak trajectory with uniform convergence of all localized
Sobolev derivatives below the recovered order. The exponent is finite and at
least one; the recovery maps and cutoffs are chosen after the subsequence. -/
theorem StableTrialSystem.exists_trajectory_with_derivative_cutoffs
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : GelfandTriple (V := V) (H := H)} (trials : StableTrialSystem T)
    {a b : ℝ} (u : ℕ → Icc a b →ᵇ H) (M : ℝ)
    (hbound : ∀ k t, ‖u k t‖ ≤ M)
    (hpair : ∀ j (v : trials.space j),
      ∃ g : ℕ → Lp ℝ 2 (volume.restrict (Ioc a b)), ∃ B : ℝ,
        (∀ k, j ≤ k → ‖g k‖ ≤ B) ∧
        ∀ k, j ≤ k → ∀ s t : Icc a b,
          inner ℝ (T.inclusion (v : V)) (u k t) -
            inner ℝ (T.inclusion (v : V)) (u k s) =
          ∫ r in (s : ℝ)..(t : ℝ), g k r) :
    ∃ uLimit : Icc a b → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, ‖uLimit t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (uLimit t)) ∧
      (∀ v : H, TendstoUniformly (fun k t ↦ inner ℝ v (u (φ k) t))
        (fun t ↦ inner ℝ v (uLimit t)) atTop) ∧
      ∀ (n m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
        ∀ (A : H →L[ℝ] W^{m,p}(ℝ^n))
          (α : List (Fin n)) (hα : α.length + 1 ≤ m)
          (χ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
          TendstoUniformly
            (fun k t ↦ cutoffDerivativeCLM α hα χ (A (u (φ k) t)))
            (fun t ↦ cutoffDerivativeCLM α hα χ (A (uLimit t))) atTop := by
  obtain ⟨uLimit, φ, hφ, hlimit, hcont, hweak, hlocal⟩ :=
    trials.exists_weak_trajectory_with_uniform_local_convergence u M hbound hpair
  refine ⟨uLimit, φ, hφ, hlimit, hcont, hweak, ?_⟩
  intro n m p _ hp A α hα χ
  exact hlocal (DerivLp n p univ) ((cutoffDerivativeCLM α hα χ).comp A)
    ((cutoffDerivativeCLM_isCompactOperator hp α hα χ).comp_clm A)

end PDE.Analysis.Evolution
