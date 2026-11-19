/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MovingPlanes.LocalComparison
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Compact continuation of reflection comparison

Weak reflection comparison is closed in the plane parameter. Strict comparison
above the plane and local directional decrease along its flat face make it open
at a positive parameter. Compactness of the closed ball gives one neighborhood
of that parameter valid for every interior point.

These lemmas are calculus and compactness statements. A differential equation
must supply their strict-comparison and directional-decrease hypotheses.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set Metric Filter
open scoped Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weak reflection comparison in an open ball is closed in the plane displacement. -/
theorem isClosed_setOf_le_reflection {u : E → ℝ} (hu : Continuous u) (e : E) :
    IsClosed {a : ℝ | ∀ x ∈ ball (0 : E) 1,
      a < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e a x)} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  have heq : {a : ℝ | a < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e a x)} =
      {a : ℝ | ⟪x, e⟫ ≤ a} ∪ {a : ℝ | u x ≤ u (reflectHyperplane e a x)} := by
    ext a
    simp [imp_iff_not_or]
  rw [heq]
  exact (isClosed_le continuous_const continuous_id).union
    (isClosed_le continuous_const
      (hu.comp ((continuous_reflectHyperplane e).comp
        (continuous_id.prodMk continuous_const))))

/-- Strict comparison above a plane and local directional decrease on it persist as
weak comparison for all sufficiently nearby planes, uniformly over the open ball. -/
theorem eventually_le_reflection [ProperSpace E] {u : E → ℝ}
    (hu : Differentiable ℝ u) {e : E} {a : ℝ} (he : ‖e‖ = 1) (ha : 0 < a)
    (hstrict : ∀ x ∈ closedBall (0 : E) 1, a < ⟪x, e⟫ →
      u x < u (reflectHyperplane e a x))
    (hflat : ∀ x ∈ closedBall (0 : E) 1, ⟪x, e⟫ = a →
      ∀ᶠ y in 𝓝 x, y ∈ ball (0 : E) 1 → fderiv ℝ u y e < 0) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ ball (0 : E) 1,
      b < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e b x) := by
  have hlocal (x : E) (hx : x ∈ closedBall (0 : E) 1) :
      ∀ᶠ p : ℝ × E in 𝓝 (a, x), p.2 ∈ ball (0 : E) 1 →
        p.1 < ⟪p.2, e⟫ → u p.2 ≤ u (reflectHyperplane e p.1 p.2) := by
    rcases lt_trichotomy ⟪x, e⟫ a with hbelow | hplane | habove
    · have hnear : ∀ᶠ p : ℝ × E in 𝓝 (a, x), ⟪p.2, e⟫ < p.1 :=
        (continuous_snd.inner continuous_const).continuousAt.eventually_lt
          continuous_fst.continuousAt hbelow
      exact hnear.mono fun _ h _ hp ↦ False.elim ((not_lt_of_ge h.le) hp)
    · exact (eventually_lt_reflection_of_eventually_fderiv_neg hu he ha hplane
        (hflat x hx hplane)).mono fun _ h hy hp ↦ (h hy hp).le
    · have hnear : ∀ᶠ p : ℝ × E in 𝓝 (a, x),
          u p.2 < u (reflectHyperplane e p.1 p.2) :=
        (hu.continuous.comp continuous_snd).continuousAt.eventually_lt
          (hu.continuous.comp (continuous_reflectHyperplane e)).continuousAt
          (hstrict x hx habove)
      exact hnear.mono fun _ h _ _ ↦ h.le
  filter_upwards [(isCompact_closedBall (0 : E) 1).eventually_forall_of_forall_eventually
    (P := fun b x ↦ x ∈ ball (0 : E) 1 →
      b < ⟪x, e⟫ → u x ≤ u (reflectHyperplane e b x)) hlocal] with b hb x hx hcoord
  exact hb x (ball_subset_closedBall hx) hx hcoord

end PDE.Analysis
