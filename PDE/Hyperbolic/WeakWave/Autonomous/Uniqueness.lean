/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.WeakWave.EvansCoefficientIntegrability

/-!
# Uniqueness for autonomous weak waves

Two weak waves with the same forcing and initial traces agree for time-independent
coefficients when the principal form is symmetric and coercive and the lower-order
form is bounded in the pivot norm in its first argument. This is the reverse
pivot-energy bound obtained by integration by parts for a smooth drift.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Evolution

namespace Hyperbolic.Variational.IsGelfandWeakWaveSolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}

/-- For a symmetric coercive principal form and a lower-order form bounded in the
pivot norm in its first argument, two autonomous Gelfand weak waves with the same
forcing and initial traces have equal displacement, velocity and acceleration in `L²`.
This is the autonomous form of backward-test uniqueness. -/
theorem eq_of_autonomous {A R : V →L[ℝ] StrongDual ℝ V} (hsymm : ∀ x y : V, A x y = A y x)
    {κ LR : ℝ} (hκ : 0 < κ) (hLR : 0 ≤ LR) (hcoerc : ∀ x : V, κ * ‖x‖ ^ 2 ≤ A x x)
    (hR : ∀ x y : V, |R x y| ≤ LR * ‖T.inclusion x‖ * ‖y‖)
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))} {q₀ : V} {p₀ : H}
    {u₁ u₂ : Lp V 2 (volume.restrict (Ioc a b))} {v₁ v₂ : Lp H 2 (volume.restrict (Ioc a b))}
    {w₁ w₂ : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (h₁ : IsGelfandWeakWaveSolution T (fun _ ↦ A + R) ell u₁ v₁ w₁ q₀ p₀)
    (h₂ : IsGelfandWeakWaveSolution T (fun _ ↦ A + R) ell u₂ v₂ w₂ q₀ p₀) :
    u₁ = u₂ ∧ v₁ = v₂ ∧ w₁ = w₂ := by
  let : MeasurableSpace V := borel V
  have : BorelSpace V := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ V) := borel (StrongDual ℝ V)
  have : BorelSpace (StrongDual ℝ V) := ⟨rfl⟩
  exact h₁.eq_of_evans_coefficients_of_operator_measurable h₂
    (A := fun _ ↦ A) (Adot := fun _ ↦ 0) (R := fun _ ↦ R) (fun _ _ _ _ ↦ rfl)
    (LipschitzWith.const A).lipschitzOnWith.absolutelyContinuousOnInterval
    (Filter.Eventually.of_forall fun t ↦ hasDerivAt_const (𝕜 := ℝ) t A)
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _ _ ↦ hsymm) κ 0 LR hκ le_rfl hLR (fun _ _ ↦ hcoerc)
    (fun _ _ _ ↦ by simp) (fun _ _ ↦ hR)

end Hyperbolic.Variational.IsGelfandWeakWaveSolution
