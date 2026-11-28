/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import PDE.Analysis.Calculus.FDeriv
public import PDE.Analysis.Scalar.Definitions
public import PDE.Analysis.Topology.Continuity

set_option linter.style.header false

/-!
# Gluing pieces along the level sets of a function

A function that is given by different formulas between consecutive levels of a continuous function
`π` inherits continuity from continuous pieces that agree on the level sets. The Lipschitz and
derivative results also need bounds or matching derivatives, respectively.
BlowupZoo's library `NavierStokes/Unforced/`, the Lean proof of Alpöge and Buckmaster for the
Navier–Stokes equations without a force, needs this for fields that are defined piece by piece
between the knots of a spline.

Let `l` be a strictly increasing list of levels and let `F k` be the formula used where exactly `k`
entries of `l` are at most `π`, that is where `PDE.Analysis.belowCount l (π p) = k`. If consecutive
formulas agree on the level set `π p = l[k]`, the glued function `q ↦ F (belowCount l (π q)) q`
inherits continuity; if their derivatives agree there too, it inherits differentiability, with the
glued derivative; and pieces that are Lipschitz on a convex set with one constant glue to a function
that is Lipschitz with that constant. The proofs are inductions on the list: the step glues the
first formula to the rest along one level.

## Main results

* `PDE.Analysis.continuous_glue_belowCount`: Gluing continuous pieces along the level sets of a
  continuous `π : ℝ × ℝ → ℝ`. Let `l` be a strictly increasing list and `F k` continuous functions
  with `F k p = F (k + 1) p` where `π p = l[k]`. Then `q ↦ F (belowCount l (π q)) q` is continuous.
  A case of `PDE.Analysis.continuous_glue_of_eq_at_breakpoints`.
* `PDE.Analysis.hasFDerivAt_glue_belowCount_of_eq`: Gluing differentiable pieces along the level
  sets of a continuous `π : ℝ × ℝ → ℝ`, with no hypothesis of continuity on the derivatives. Let `l`
  be a strictly increasing list and let `F k` have the derivative `F' k p` at every `p`, with
  `F k p = F (k + 1) p` and `F' k p = F' (k + 1) p` where `π p = l[k]`. Then
  `q ↦ F (belowCount l (π q)) q` has the derivative `F' (belowCount l (π p)) p` at every `p`.
* `PDE.Analysis.hasFDerivAt_glue_belowCount`: Gluing differentiable pieces along the level sets of a
  continuous `π : ℝ × ℝ → ℝ`. Let `l` be a strictly increasing list and `F k` functions with
  continuous derivatives `F' k` such that `F k` and `F (k + 1)`, and their derivatives, agree where
  `π p = l[k]`. Then `q ↦ F (belowCount l (π q)) q` has the derivative `F' (belowCount l (π p)) p`
  at every `p`, and this derivative is continuous.
* `PDE.Analysis.lipschitzOnWith_glue_belowCount`: Gluing Lipschitz pieces. Let `π` be a continuous
  linear functional on `ℝ × ℝ`, `U` a convex set, `l` a strictly increasing list and `F' k`
  functions that are Lipschitz on `U` with the constant `K`, with `F' k p = F' (k + 1) p` where
  `π p = l[k]`. Then `p ↦ F' (belowCount l (π p)) p` is Lipschitz on `U` with the constant `K`.
* `PDE.Analysis.belowCount_tail_head_eq_zero`: For a strictly increasing list `b :: bs`, no entry of
  `bs` is at most `b`: `belowCount bs b = 0`.

## Implementation notes

The pieces are defined on `ℝ × ℝ`. The continuity and derivative results are complex-valued:
the cases that BlowupZoo's library `NavierStokes/Unforced/` uses. The proofs do not use these
choices. The Lipschitz estimate allows any real normed space as its target.
`PDE.Analysis.hasFDerivAt_glue_belowCount` repeats the induction of
`PDE.Analysis.hasFDerivAt_glue_belowCount_of_eq` and is not derived from it.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- For a strictly increasing list `b :: bs`, no entry of `bs` is at most `b`:
`belowCount bs b = 0`. -/
theorem belowCount_tail_head_eq_zero (b : ℝ) (bs : List ℝ) (h : (b :: bs).Pairwise (· < ·)) :
    belowCount bs b = 0 := by
  unfold belowCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro c hc
  have := List.rel_of_pairwise_cons h hc
  simp only [decide_eq_true_eq, not_le]
  exact this

/-- Gluing continuous pieces along the level sets of a continuous `π : ℝ × ℝ → ℝ`. Let `l` be a
strictly increasing list and `F k` continuous functions with `F k p = F (k + 1) p` where `π p =
l[k]`. Then `q ↦ F (belowCount l (π q)) q` is continuous. A case of
`PDE.Analysis.continuous_glue_of_eq_at_breakpoints`. -/
theorem continuous_glue_belowCount (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ), l.Pairwise
    (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ), (∀ k, Continuous (F k)) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p) →
    Continuous (fun q ↦ F (belowCount l (π q)) q) :=
  fun l hl F hF hj ↦ continuous_glue_of_eq_at_breakpoints π hπ l hl F (fun k _ ↦ hF k) hj

/-- Gluing Lipschitz pieces. Let `π` be a continuous linear functional on `ℝ × ℝ`, `U` a convex set,
`l` a strictly increasing list and `F' k` functions that are Lipschitz on `U` with the constant `K`,
with `F' k p = F' (k + 1) p` where `π p = l[k]`. Then `p ↦ F' (belowCount l (π p)) p` is Lipschitz
on `U` with the constant `K`. -/
theorem lipschitzOnWith_glue_belowCount {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (π : ℝ × ℝ →L[ℝ] ℝ)
    {U : Set (ℝ × ℝ)} (hU : Convex ℝ U) {K : NNReal} : ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F' : ℕ → ℝ × ℝ → E), (∀ k, LipschitzOnWith K (F' k) U) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F' k p = F' (k + 1) p) →
    LipschitzOnWith K (fun p ↦ F' (belowCount l (π p)) p) U
  | [], _, F', hF', _ => by
    simpa [belowCount] using hF' 0
  | b :: bs, hl, F', hF', hj => by
    have hbs : bs.Pairwise (· < ·) := hl.of_cons
    have ih := lipschitzOnWith_glue_belowCount π hU bs hbs (fun k ↦ F' (k + 1))
        (fun k ↦ hF' (k + 1))
      (fun k hk p hp ↦ hj (k + 1) (by simp; omega) p (by simpa using hp))
    have h0 : ∀ u, b ≤ u → u ≤ b → belowCount bs u = 0 := by
      intro u h1 h2
      unfold belowCount
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      have := List.rel_of_pairwise_cons hl hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e2 : (fun p ↦ F' (belowCount (b :: bs) (π p)) p) =
        fun p ↦ if b ≤ π p then F' (belowCount bs (π p) + 1) p else F' 0 p := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    rw [e2]
    exact lipschitzOnWith_ite_of_convex_of_eq (A := F' 0)
        (B := fun q ↦ F' (belowCount bs (π q) + 1) q) π b hU (hF' 0) ih
      (fun p hp ↦ by
        show F' (belowCount bs (π p) + 1) p = F' 0 p
        rw [h0 (π p) hp.le hp.ge]
        exact (hj 0 (by simp) p (by simpa using hp.symm)).symm)

/-- Gluing differentiable pieces along the level sets of a continuous `π : ℝ × ℝ → ℝ`, with no
hypothesis of continuity on the derivatives. Let `l` be a strictly increasing list and let `F k`
have the derivative `F' k p` at every `p`, with `F k p = F (k + 1) p` and `F' k p = F' (k + 1) p`
where `π p = l[k]`. Then `q ↦ F (belowCount l (π q)) q` has the derivative
`F' (belowCount l (π p)) p` at every `p`. -/
theorem hasFDerivAt_glue_belowCount_of_eq (π : ℝ × ℝ → ℝ) (hπ : Continuous π) : ∀ (l : List ℝ),
    l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ) (F' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)),
    (∀ k p, HasFDerivAt (F k) (F' k p) p) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p ∧ F' k p = F' (k + 1) p) →
    ∀ p, HasFDerivAt (fun q ↦ F (belowCount l (π q)) q) (F' (belowCount l (π p)) p) p
  | [], _, F, F', hF, _ => by
    simpa [belowCount] using hF 0
  | b :: bs, hl, F, F', hF, hj => by
    have ih := hasFDerivAt_glue_belowCount_of_eq π hπ bs hl.of_cons (fun k ↦ F (k + 1))
        (fun k ↦ F' (k + 1))
      (fun k p ↦ hF (k + 1) p) (fun k hk p hp ↦ hj (k + 1) (by simp; omega) p (by simpa using hp))
    have e1 : (fun q ↦ F (belowCount (b :: bs) (π q)) q) =
        fun q ↦ if b ≤ π q then F (belowCount bs (π q) + 1) q else F 0 q := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    have e2 : ∀ p, F' (belowCount (b :: bs) (π p)) p =
        if b ≤ π p then F' (belowCount bs (π p) + 1) p else F' 0 p := by
      intro q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    intro p
    rw [e1, e2]
    refine hasFDerivAt_ite_of_eq_of_fderiv_eq (A := F 0)
        (B := fun q ↦ F (belowCount bs (π q) + 1) q) (A' := F' 0)
      (B' := fun q ↦ F' (belowCount bs (π q) + 1) q) π hπ b (hF 0) ih ?_ ?_ p
    · intro q hq
      show F (belowCount bs (π q) + 1) q = F 0 q
      rw [← hq, belowCount_tail_head_eq_zero b bs hl]
      exact (hj 0 (by simp) q (by simpa using hq.symm)).1.symm
    · intro q hq
      show F' (belowCount bs (π q) + 1) q = F' 0 q
      rw [← hq, belowCount_tail_head_eq_zero b bs hl]
      exact (hj 0 (by simp) q (by simpa using hq.symm)).2.symm

/-- Gluing differentiable pieces along the level sets of a continuous `π : ℝ × ℝ → ℝ`. Let `l` be a
strictly increasing list and `F k` functions with continuous derivatives `F' k` such that `F k` and
`F (k + 1)`, and their derivatives, agree where `π p = l[k]`. Then `q ↦ F (belowCount l (π q)) q`
has the derivative `F' (belowCount l (π p)) p` at every `p`, and this derivative is continuous. -/
theorem hasFDerivAt_glue_belowCount (π : ℝ × ℝ → ℝ) (hπ : Continuous π) :
    ∀ (l : List ℝ), l.Pairwise (· < ·) →
    ∀ (F : ℕ → ℝ × ℝ → ℂ) (F' : ℕ → ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)),
    (∀ k p, HasFDerivAt (F k) (F' k p) p) → (∀ k, Continuous (F' k)) →
    (∀ k (hk : k < l.length) p, π p = l[k] → F k p = F (k + 1) p ∧ F' k p = F' (k + 1) p) →
    (∀ p, HasFDerivAt (fun q ↦ F (belowCount l (π q)) q) (F' (belowCount l (π p)) p) p) ∧
      Continuous (fun p ↦ F' (belowCount l (π p)) p)
  | [], _, F, F', hF, hF', _ => by
    simp only [belowCount, List.filter_nil, List.length_nil]
    exact ⟨hF 0, hF' 0⟩
  | b :: bs, hl, F, F', hF, hF', hj => by
    obtain ⟨ih1, ih2⟩ := hasFDerivAt_glue_belowCount π hπ bs hl.of_cons (fun k ↦ F (k + 1))
      (fun k ↦ F' (k + 1)) (fun k p ↦ hF (k + 1) p) (fun k ↦ hF' (k + 1))
      (fun k hk p hp ↦ hj (k + 1) (by simp; omega) p (by simpa using hp))
    have hz : ∀ p, π p = b → belowCount bs (π p) = 0 := fun p hp ↦
      belowCount_eq_zero_of_lt bs fun c hc ↦ hp ▸ List.rel_of_pairwise_cons hl hc
    have hg := hasFDerivAt_ite_and_continuous_of_eq (A := F 0)
      (B := fun q ↦ F (belowCount bs (π q) + 1) q) (A' := F' 0)
      (B' := fun q ↦ F' (belowCount bs (π q) + 1) q) π hπ b (hF 0) ih1 (hF' 0) ih2
      (fun p hp ↦ by simpa [hz p hp] using (hj 0 (by simp) p (by simpa using hp)).1)
      (fun p hp ↦ by simpa [hz p hp] using (hj 0 (by simp) p (by simpa using hp)).2)
    have e1 : (fun q ↦ F (belowCount (b :: bs) (π q)) q) =
        fun q ↦ if b ≤ π q then F (belowCount bs (π q) + 1) q else F 0 q := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    have e2 : (fun p ↦ F' (belowCount (b :: bs) (π p)) p) =
        fun p ↦ if b ≤ π p then F' (belowCount bs (π p) + 1) p else F' 0 p := by
      funext q
      rw [belowCount_cons b bs hl]
      split_ifs <;> rfl
    refine ⟨fun p ↦ ?_, e2 ▸ hg.2⟩
    rw [e1, congrFun e2 p]
    exact hg.1 p

end PDE.Analysis
