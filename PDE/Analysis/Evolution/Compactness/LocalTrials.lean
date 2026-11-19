/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.FixedTests

/-!
# Local strong convergence of Galerkin trajectories

Uniform energy bounds and eventual scalar L² time bounds for each fixed trial test give
one weakly continuous pivot-valued trajectory. Every fixed pivot pairing converges uniformly
on the time interval. Trial density supplies separability and the dense test family.

Every compact continuous linear observation converges strongly, uniformly in time,
to the observation of that same trajectory. The subsequence is chosen before the target
space and observation map, so any number of compact observations share one limit.
The time estimates concern only scalar pairings after the fixed test enters the trial
space. They do not require a bound for the full drift in the energy space.
-/

@[expose] public section

noncomputable section


open Filter MeasureTheory Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace PDE.Analysis.Evolution

/-- An energy-bounded Galerkin sequence has one weakly continuous pivot limit. All fixed
pivot pairings and every compact continuous linear observation converge uniformly along
the same subsequence. Scalar time bounds may depend on the fixed trial test and need hold
only from its inclusion index onward. Finite trial density supplies pivot separability. -/
theorem StableTrialSystem.exists_weak_trajectory_with_uniform_local_convergence
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {T : GelfandTriple (V := V) (H := H)} (trials : StableTrialSystem T)
    {a b : ℝ} (u : ℕ → Icc a b →ᵇ H) (M : ℝ)
    (hbound : ∀ n t, ‖u n t‖ ≤ M)
    (hpair : ∀ k (v : trials.space k),
      ∃ g : ℕ → Lp ℝ 2 (volume.restrict (Ioc a b)), ∃ C : ℝ,
        (∀ n, k ≤ n → ‖g n‖ ≤ C) ∧
        ∀ n, k ≤ n → ∀ s t : Icc a b,
          inner ℝ (T.inclusion (v : V)) (u n t) -
            inner ℝ (T.inclusion (v : V)) (u n s) =
          ∫ r in (s : ℝ)..(t : ℝ), g n r) :
    ∃ uLimit : Icc a b → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ t, ‖uLimit t‖ ≤ M) ∧
      Continuous (fun t ↦ toWeakSpace ℝ H (uLimit t)) ∧
      (∀ v : H, TendstoUniformly (fun n t ↦ inner ℝ v (u (φ n) t))
        (fun t ↦ inner ℝ v (uLimit t)) atTop) ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
        (J : H →L[ℝ] E), IsCompactOperator J →
        TendstoUniformly (fun n t ↦ J (u (φ n) t)) (fun t ↦ J (uLimit t)) atTop := by
  let test : (Σ k, trials.space k) → H := fun v ↦ T.inclusion (v.2 : V)
  have hdense : DenseRange test := trials.denseRange_inclusion_sigma
  let : ∀ k, FiniteDimensional ℝ (trials.space k) := trials.finiteDimensional
  let : ∀ k, TopologicalSpace.SeparableSpace (trials.space k) := fun _ ↦ inferInstance
  let : TopologicalSpace.SeparableSpace H := hdense.separableSpace
    (continuous_sigma fun _ ↦ T.inclusion.continuous.comp continuous_subtype_val)
  obtain ⟨uLimit, φ, hφ, hlimitBound, hweakCont, hweak⟩ :=
    exists_subsequence_tendstoUniformly_pairings test hdense u M hbound
      (trials.equicontinuous_pairing_of_integral u hpair)
  refine ⟨uLimit, φ, hφ, hlimitBound, hweakCont, hweak, ?_⟩
  intro E _ _ J hcompact
  exact tendstoUniformly_compactOperator_of_dense_pairings _ hcompact id denseRange_id
    (fun n t ↦ u (φ n) t) uLimit M (fun n t ↦ hbound (φ n) t) hlimitBound hweak

end PDE.Analysis.Evolution
