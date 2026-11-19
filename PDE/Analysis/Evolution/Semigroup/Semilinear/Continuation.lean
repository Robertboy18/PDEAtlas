/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Semilinear.UniformLifespan

/-!
# Continuation at finite endpoints of semilinear mild solutions

A uniform local existence time for bounded initial states permits extension
from a bounded terminal state. For a solution on a half-open interval, bounded
states arbitrarily close to its endpoint suffice: restart at such a state and
use uniqueness to identify the extension on the whole earlier interval.

Consequently, if no extension exists, the state norm eventually exceeds every
threshold near the finite endpoint. The nonlinearity must be Lipschitz on each
norm ball. These results extend a given solution; maximal solutions are
constructed in `Semilinear.Maximal`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bound on the terminal state gives a positive extension length independent of
the preceding solution and its lifetime. The extension agrees with the whole earlier curve. -/
theorem exists_pos_forall_exists_mild_extension_of_lipschitzOn_closedBall
    (T : StronglyContinuousSemigroup E) {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ (τ : NNReal) (x₀ : E)
      (u : C(Icc (0 : ℝ) (τ : ℝ), E)),
      T.IsMildSolutionOn F x₀ τ u →
      ‖u ⟨τ, τ.coe_nonneg, le_rfl⟩‖ ≤ R →
      ∃ w : C(Icc (0 : ℝ) ((τ + δ : NNReal) : ℝ), E),
        T.IsMildSolutionOn F x₀ (τ + δ) w ∧
          restrictMildCurve (show τ ≤ τ + δ from le_add_of_nonneg_right δ.coe_nonneg) w = u := by
  obtain ⟨δ, hδ, hlocal⟩ :=
    T.exists_pos_forall_existsUnique_mildSolutionOn_of_lipschitzOn_closedBall hF hR
  refine ⟨δ, hδ, fun τ x₀ u hu hterminal ↦ ?_⟩
  obtain ⟨v, hv, _⟩ := hlocal (u ⟨τ, τ.coe_nonneg, le_rfl⟩) hterminal
  refine ⟨glueMildCurves u v hv.initial_value.symm, hu.glue hv, ?_⟩
  ext t
  change glueMildCurves u v hv.initial_value.symm
    ⟨t, t.property.1, t.property.2.trans (le_add_of_nonneg_right δ.coe_nonneg)⟩ = u t
  rw [glueMildCurves_apply_left u v hv.initial_value.symm _ t.property.2]
  exact IccExtend_val τ.coe_nonneg u t

omit [CompleteSpace E] in
/-- A continuous mild solution before a finite terminal time. Values of `u` outside
`[0,b)` are immaterial; every integral in the equation lies in a compact prefix. -/
structure IsMildSolutionBefore (T : StronglyContinuousSemigroup E)
    (F : C(E, E)) (x₀ : E) (b : ℝ) (u : ℝ → E) : Prop where
  /-- Continuity in the Banach state space at every preterminal time. -/
  continuousOn : ContinuousOn u (Ico 0 b)
  /-- Variation of constants on each compact initial interval. -/
  equation : ∀ t ∈ Ico 0 b, u t = T t.toNNReal x₀ + T.duhamel (fun s ↦ F (u s)) t

omit [CompleteSpace E] in
/-- The continuous curve associated with a compact prefix of a preterminal solution. -/
def IsMildSolutionBefore.restrictCurve {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : T.IsMildSolutionBefore F x₀ b u)
    {τ : NNReal} (hτ : (τ : ℝ) < b) : C(Icc (0 : ℝ) (τ : ℝ), E) where
  toFun t := u t
  continuous_toFun := continuousOn_iff_continuous_domRestrict.mp
    (hu.continuousOn.mono fun _ ht ↦ ⟨ht.1, ht.2.trans_lt hτ⟩)

omit [CompleteSpace E] in
/-- A compact prefix of a preterminal solution satisfies the finite-interval
mild-solution predicate, with the same initial state. -/
theorem IsMildSolutionBefore.isMildSolutionOn_restrictCurve
    {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : T.IsMildSolutionBefore F x₀ b u)
    {τ : NNReal} (hτ : (τ : ℝ) < b) :
    T.IsMildSolutionOn F x₀ τ (hu.restrictCurve hτ) := by
  intro t
  change u t = _
  rw [hu.equation t ⟨t.property.1, t.property.2.trans_lt hτ⟩]
  congr 1
  apply T.duhamel_congr t.property.1
  intro s hs
  have hsτ : s ∈ Icc (0 : ℝ) τ := ⟨hs.1, hs.2.trans t.property.2⟩
  change F (u s) = F (IccExtend τ.coe_nonneg (hu.restrictCurve hτ) s)
  rw [IccExtend_of_mem τ.coe_nonneg (hu.restrictCurve hτ) hsτ]
  rfl

/-- Bounded states arbitrarily close to a finite endpoint permit an extension
past that endpoint. The hypothesis only asks for one such state in each terminal interval,
not a uniform bound on the full trajectory. -/
theorem IsMildSolutionBefore.exists_extension_of_bounded_near_endpoint
    {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : T.IsMildSolutionBefore F x₀ b u)
    {R : ℝ} (hR : 0 ≤ R)
    (hnear : ∀ ε : ℝ, 0 < ε →
      ∃ t ∈ Ico 0 b, b - t < ε ∧ ‖u t‖ ≤ R) :
    ∃ ρ : NNReal, b < (ρ : ℝ) ∧
      ∃ w : C(Icc (0 : ℝ) (ρ : ℝ), E),
        T.IsMildSolutionOn F x₀ ρ w ∧
          EqOn (IccExtend ρ.coe_nonneg w) u (Ico 0 b) := by
  obtain ⟨δ, hδ, hextend⟩ :=
    T.exists_pos_forall_exists_mild_extension_of_lipschitzOn_closedBall hF hR
  obtain ⟨a, ha, hclose, hnorm⟩ := hnear δ hδ
  let τ : NNReal := .mk a ha.1
  have hτ : (τ : ℝ) < b := ha.2
  obtain ⟨w, hw, _⟩ :=
    hextend τ x₀ (hu.restrictCurve hτ) (hu.isMildSolutionOn_restrictCurve hτ) hnorm
  have hb : b < ((τ + δ : NNReal) : ℝ) := by
    change b < a + (δ : ℝ)
    linarith
  refine ⟨τ + δ, hb, w, hw, ?_⟩
  intro t ht
  let η : NNReal := .mk t ht.1
  have hη : (η : ℝ) < b := ht.2
  have hηρ : η ≤ τ + δ := (ht.2.trans hb).le
  have heq :
      restrictMildCurve hηρ w = hu.restrictCurve hη :=
    (hw.restrict hηρ).eq_of_locallyLipschitz
      (locallyLipschitz_of_lipschitzOn_closedBall_zero hF)
      (hu.isMildSolutionOn_restrictCurve hη)
  have hvalue := congrArg
    (fun v : C(Icc (0 : ℝ) (η : ℝ), E) ↦ v ⟨η, η.coe_nonneg, le_rfl⟩) heq
  have htρ : t ∈ Icc (0 : ℝ) ((τ + δ : NNReal) : ℝ) :=
    ⟨ht.1, (ht.2.trans hb).le⟩
  exact (IccExtend_of_mem (τ + δ).coe_nonneg w htρ).trans hvalue

/-- A solution bounded on its finite preterminal interval extends beyond the endpoint,
provided the nonlinearity is Lipschitz on each norm ball. -/
theorem IsMildSolutionBefore.exists_extension_of_bounded
    {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : T.IsMildSolutionBefore F x₀ b u) (hb : 0 < b)
    {R : ℝ} (hR : 0 ≤ R) (hbounded : ∀ t ∈ Ico 0 b, ‖u t‖ ≤ R) :
    ∃ ρ : NNReal, b < (ρ : ℝ) ∧
      ∃ w : C(Icc (0 : ℝ) (ρ : ℝ), E),
        T.IsMildSolutionOn F x₀ ρ w ∧
          EqOn (IccExtend ρ.coe_nonneg w) u (Ico 0 b) := by
  apply hu.exists_extension_of_bounded_near_endpoint hF hR
  intro ε hε
  let t : ℝ := max 0 (b - ε / 2)
  have ht : t ∈ Ico 0 b := by
    refine ⟨le_max_left _ _, max_lt hb ?_⟩
    linarith
  refine ⟨t, ht, ?_, hbounded t ht⟩
  have hle : b - ε / 2 ≤ t := le_max_right _ _
  linarith

/-- If no mild extension past a finite endpoint exists, the state norm eventually
exceeds every real threshold. This is the finite-time blowup alternative in an
explicit terminal-neighborhood form. -/
theorem IsMildSolutionBefore.norm_eventually_gt_of_not_exists_extension
    {T : StronglyContinuousSemigroup E} {F : C(E, E)}
    (hF : ∀ R : ℝ, 0 < R →
      ∃ L : NNReal, LipschitzOnWith L F (Metric.closedBall (0 : E) R))
    {x₀ : E} {b : ℝ} {u : ℝ → E}
    (hu : T.IsMildSolutionBefore F x₀ b u)
    (hno : ¬ ∃ ρ : NNReal, b < (ρ : ℝ) ∧
      ∃ w : C(Icc (0 : ℝ) (ρ : ℝ), E),
        T.IsMildSolutionOn F x₀ ρ w ∧
          EqOn (IccExtend ρ.coe_nonneg w) u (Ico 0 b)) :
    ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Ico 0 b, b - t < ε → R < ‖u t‖ := by
  classical
  intro R
  have hnear : ¬ (∀ ε : ℝ, 0 < ε →
      ∃ t ∈ Ico 0 b, b - t < ε ∧ ‖u t‖ ≤ max R 0) := by
    intro h
    exact hno (hu.exists_extension_of_bounded_near_endpoint hF (le_max_right R 0) h)
  push Not at hnear
  obtain ⟨ε, hε, he⟩ := hnear
  exact ⟨ε, hε, fun t ht hclose ↦ (le_max_left R 0).trans_lt (he t ht hclose)⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
