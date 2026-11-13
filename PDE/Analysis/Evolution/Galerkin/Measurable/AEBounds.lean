/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.Measurable.Existence
public import PDE.Analysis.Evolution.Integrated.FormCongruence
public import PDE.Analysis.Evolution.Integrated.GardingSolution

/-!
# Evolution equations with almost-everywhere form bounds

Measurable coefficients often satisfy their norm bound and Gårding inequality
`θ ‖v‖² ≤ B(t)(v, v) + γ ‖ι v‖²` only at almost every time. Replacing `B(t)` on the
exceptional null set by `θ` times the Riesz map gives a pointwise bounded Gårding
representative that agrees with `B` almost everywhere. The Galerkin construction and
invariance of weak solutions under null-set changes of the form then give a Gårding weak
solution of the original equation, with its weak derivative and initial trace.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set InnerProductSpace
open scoped ENNReal NNReal

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If `‖B(t)‖ ≤ MB` and the Gårding inequality hold for almost every `t ∈ (a, b]`, then `B`
agrees almost everywhere with a form `B'` that is bounded and satisfies the Gårding inequality
at every time, and `t ↦ B'(t) v` is almost everywhere strongly measurable for each `v`. -/
theorem exists_bounded_garding_representative
    (T : GelfandTriple (V := V) (H := H))
    {a b theta gamma : ℝ} (hgamma : 0 ≤ gamma)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (MB : ℝ≥0)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2) :
    ∃ (B' : ℝ → V →L[ℝ] StrongDual ℝ V) (M : ℝ≥0),
      B' =ᵐ[volume.restrict (Ioc a b)] B ∧
      (∀ v, AEStronglyMeasurable (fun t ↦ B' t v) (volume.restrict (Icc a b))) ∧
      (∀ t, ‖B' t‖ ≤ M) ∧
      ∀ t, ∀ v : V, theta * ‖v‖ ^ 2 ≤ B' t v v + gamma * ‖T.inclusion v‖ ^ 2 := by
  classical
  let B₀ : V →L[ℝ] StrongDual ℝ V :=
    theta • (toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap
  have hB₀ (v : V) :
      theta * ‖v‖ ^ 2 ≤ B₀ v v + gamma * ‖T.inclusion v‖ ^ 2 := by
    change theta * ‖v‖ ^ 2 ≤ theta * inner ℝ v v + gamma * ‖T.inclusion v‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
    exact le_add_of_nonneg_right (mul_nonneg hgamma (sq_nonneg _))
  let good (t : ℝ) := ‖B t‖ ≤ MB ∧
    ∀ v : V, theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2
  let B' (t : ℝ) := if good t then B t else B₀
  have heq : B' =ᵐ[volume.restrict (Ioc a b)] B := by
    filter_upwards [hbound, hGarding] with t ht hg
    exact ite_eq_left ⟨ht, hg⟩
  refine ⟨B', MB + ‖B₀‖₊, heq, ?_, ?_, ?_⟩
  · intro v
    rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := volume) (a := a) (b := b))]
    exact (hB v).congr (heq.fun_comp (fun L ↦ L v)).symm
  · intro t
    dsimp only [B']
    split_ifs with ht
    · exact ht.1.trans (le_add_of_nonneg_right (norm_nonneg B₀))
    · exact le_add_of_nonneg_left MB.2
  · intro t v
    dsimp only [B']
    split_ifs with ht
    · exact ht.2 v
    · exact hB₀ v

/-- Galerkin existence under almost-everywhere bounds. If `t ↦ B(t) v` is measurable for
each `v`, and `‖B(t)‖ ≤ MB` and `θ ‖v‖² ≤ B(t)(v, v) + γ ‖ι v‖²` with `θ > 0` hold for almost
every `t`, then for every `ℓ ∈ L²(a, b; V*)` and `uInit ∈ H` there is a Gårding weak solution,
with weak derivative and continuous initial trace. -/
theorem GardingWeakSolutionOn.nonempty_of_ae_garding
    [CompleteSpace H] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace (StrongDual ℝ V)] [BorelSpace (StrongDual ℝ V)]
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hfinite : ∀ n, FiniteDimensional ℝ (S n))
    {K : ℝ≥0} (P : ∀ n, StableTrialProjection T (S n) K)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ w : S n, ‖v - (w : V)‖ < ε)
    (B : ℝ → V →L[ℝ] StrongDual ℝ V)
    {a b theta gamma : ℝ}
    (ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
    (hab : a < b) (htheta : 0 < theta) (hgamma : 0 ≤ gamma)
    (hB : ∀ v, AEStronglyMeasurable (fun t ↦ B t v) (volume.restrict (Ioc a b)))
    (MB : ℝ≥0)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    (hGarding : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v : V,
      theta * ‖v‖ ^ 2 ≤ B t v v + gamma * ‖T.inclusion v‖ ^ 2)
    (uInit : H) :
    Nonempty (GardingWeakSolutionOn T B ell uInit a b theta gamma) := by
  obtain ⟨B', M, heq, hmeas, hnorm, hgarding⟩ :=
    exists_bounded_garding_representative T hgamma B hB MB hbound hGarding
  obtain ⟨u, g, E, hu, hunique, hweak, htrace, hresidual, henergy⟩ :=
    IsGelfandIntegratedWeakSolution.exists_of_measurable_galerkin_garding_L2_full
      T S hfinite P hdenseEnergy B' ell hab htheta hmeas M
      (fun t _ ↦ hnorm t) (fun t _ ↦ hgarding t) uInit
  refine ⟨⟨u, g, E, ⟨hu.congr_form_ae heq, ?_, hweak, htrace, ?_, henergy⟩⟩⟩
  · intro v hv
    exact hunique v (hv.congr_form_ae heq.symm)
  · filter_upwards [hresidual, heq] with t ht hBt
    rw [ht, hBt]

end PDE.Analysis.Evolution
