/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Defs -- shake: keep
import Mathlib.Tactic.Positivity.Finset

/-!
# Finite continuation of interval ODE solutions

Two classical trajectories for the same nonautonomous vector field `f : ℝ → E → E` can
be glued when their values agree at a common endpoint. Iterating this construction over
a finite arithmetic partition `a, a + d, …, a + N d = b` turns uniformly available
cellwise solutions into a solution on the whole closed interval `[a, b]`.

This is the elementary continuation step in the existence theory for ODEs: a local
existence theorem that works from any admissible initial state, on cells of a fixed
length, yields a solution on any finite interval. Evans argues this way in step 3 of the
proof of §9.2.1, Theorem 2, where the cell length depends only on a Lipschitz constant.
Here the step also extends Galerkin approximants from a short time interval to a full
interval; Evans takes the global solution of his linear Galerkin system from standard ODE
theory (§7.1.2, proof of Theorem 1).

Solutions are understood in the one-sided sense `HasDerivWithinAt u (f t (u t)) (Icc a b) t`
at every `t ∈ [a, b]`, so the derivative at each endpoint is one-sided and no smoothness
across the endpoints is needed.

## Main results

* `glue_ode_solution_Icc`: two solutions on `[a, c]` and `[c, b]` with `u c = v c` glue to
  a solution on `[a, b]`; the one-sided derivatives at `c` agree because the states do.
* `exists_ode_solution_Icc_of_partition`: uniformly available cellwise solutions from
  every state give a solution on `[a, b]` with prescribed initial value.
* `exists_ode_solution_Icc_of_partition_of_invariant`,
  `_of_timeDependentInvariant`: the same when local solutions are only available from
  states in a set `K` (or `K t`) and remain in it, so the glued solution stays in `K`.
* `exists_ode_solution_Icc_of_partition_of_energy_bound`,
  `_of_partition_of_energyEnvelope`: the invariant-set statements specialised to a
  sublevel set `energy x ≤ C` or to a time-dependent envelope
  `energy t x ≤ bound t x`, the form in which an a priori energy estimate enters.

## Implementation notes

The partition is arithmetic with a nonnegative step `d` and `N > 0` cells; the induction
is on the number of cells. The invariant set `K` carries no topological or convexity
assumptions, since its only role is to bound the set of initial states from which local
solutions are required. The gluing uses `HasDerivWithinAt.union`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.1, proof of Theorem 2, step 3, and §7.1.2, proof of
  Theorem 1. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

section FiniteContinuation

/--
Glue two solutions of the same nonautonomous ODE at a common endpoint.

Solutions of `u' = f(t, u)` on `[a, c]` and `[c, b]` with `u(c) = v(c)` glue to a
solution on `[a, b]` that agrees with `u` on `[a, c]` and with `v` on `[c, b]`.
At `t = c` both one-sided derivatives equal `f(c, u(c))`, so
`HasDerivWithinAt.union` gives the derivative within `[a, b]`.
-/
theorem glue_ode_solution_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (u v : ℝ → E) (hmatch : u c = v c)
    (hu : ∀ t ∈ Set.Icc a c,
      HasDerivWithinAt u (f t (u t)) (Set.Icc a c) t)
    (hv : ∀ t ∈ Set.Icc c b,
      HasDerivWithinAt v (f t (v t)) (Set.Icc c b) t) :
    ∃ w : ℝ → E,
      (∀ t ∈ Set.Icc a c, w t = u t) ∧
      (∀ t ∈ Set.Icc c b, w t = v t) ∧
      ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt w (f t (w t)) (Set.Icc a b) t := by
  let w : ℝ → E := fun t ↦ if t ≤ c then u t else v t
  have hw_left : ∀ t ∈ Set.Icc a c, w t = u t := fun t ht ↦ by simp [w, ht.2]
  have hw_right : ∀ t ∈ Set.Icc c b, w t = v t := fun t ht ↦ by
    rcases ht.1.eq_or_lt with rfl | htc
    · simp [w, hmatch]
    · simp [w, not_le.2 htc]
  refine ⟨w, hw_left, hw_right, fun t ht ↦ ?_⟩
  rcases lt_trichotomy t c with htc | rfl | hct
  · have htleft : t ∈ Set.Icc a c := ⟨ht.1, htc.le⟩
    rw [hw_left t htleft]
    exact ((hu t htleft).congr_of_mem hw_left htleft).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Iio c, isOpen_Iio, htc, fun s hs ↦ ⟨hs.2.1, hs.1.le⟩⟩)
  · have hleft : t ∈ Set.Icc a t := ⟨hac, le_rfl⟩
    have hright : t ∈ Set.Icc t b := ⟨le_rfl, hcb⟩
    rw [← Set.Icc_union_Icc_eq_Icc hac hcb]
    exact ((hu t hleft).congr_of_mem hw_left hleft |>.congr_deriv (by rw [hw_left t hleft])).union
      ((hv t hright).congr_of_mem hw_right hright |>.congr_deriv (by rw [hw_right t hright]))
  · have htright : t ∈ Set.Icc c b := ⟨hct.le, ht.2⟩
    rw [hw_right t htright]
    exact ((hv t htright).congr_of_mem hw_right htright).mono_of_mem_nhdsWithin
      (mem_nhdsWithin.2 ⟨Ioi c, isOpen_Ioi, hct, fun s hs ↦ ⟨hs.1.le, hs.2.2⟩⟩)

/--
Finite continuation from local solutions that preserve a time-dependent
family of invariant sets.

At the left endpoint of each partition cell, the current state belongs to
the corresponding set `K t`. The local solution must then remain in `K t`
at every time in that cell. Recursive gluing preserves this pointwise
invariant on the whole interval.
-/
theorem exists_ode_solution_Icc_of_partition_of_timeDependentInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (K : ℝ → Set E) {a b d : ℝ} (hd : 0 ≤ d)
    (N : ℕ) (hN : 0 < N)
    (hendpoint : a + (N : ℝ) * d = b)
    (u₀ : E) (hu₀K : u₀ ∈ K a)
    (hlocal : ∀ n : ℕ, n < N →
      ∀ x ∈ K (a + (n : ℝ) * d),
        ∃ u : ℝ → E,
          u (a + (n : ℝ) * d) = x ∧
          (∀ t ∈ Set.Icc (a + (n : ℝ) * d)
                (a + ((n + 1 : ℕ) : ℝ) * d),
              HasDerivWithinAt u (f t (u t))
                (Set.Icc (a + (n : ℝ) * d)
                  (a + ((n + 1 : ℕ) : ℝ) * d)) t) ∧
          ∀ t ∈ Set.Icc (a + (n : ℝ) * d)
              (a + ((n + 1 : ℕ) : ℝ) * d),
            u t ∈ K t) :
    ∃ u : ℝ → E, u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (f t (u t)) (Set.Icc a b) t) ∧
      ∀ t ∈ Set.Icc a b, u t ∈ K t := by
  have hpartial : ∀ n : ℕ, n < N →
      ∃ u : ℝ → E, u a = u₀ ∧
        (∀ t ∈ Set.Icc a (a + ((n + 1 : ℕ) : ℝ) * d),
            HasDerivWithinAt u (f t (u t))
              (Set.Icc a (a + ((n + 1 : ℕ) : ℝ) * d)) t) ∧
        ∀ t ∈ Set.Icc a (a + ((n + 1 : ℕ) : ℝ) * d),
          u t ∈ K t := by
    intro n
    induction n with
    | zero =>
        intro hn
        obtain ⟨u, hu₀, hu, huK⟩ := hlocal 0 hn u₀ (by simpa using hu₀K)
        exact ⟨u, by simpa using hu₀, by simpa using hu, by simpa using huK⟩
    | succ n ih =>
        intro hn
        obtain ⟨u, hu₀, hu, huK⟩ := ih (Nat.lt_of_succ_lt hn)
        let c : ℝ := a + ((n + 1 : ℕ) : ℝ) * d
        let e : ℝ := a + ((n + 2 : ℕ) : ℝ) * d
        have hac : a ≤ c := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hd)
        obtain ⟨v, hv₀, hv, hvK⟩ := hlocal (n + 1) hn (u c) (by simpa [c] using huK c ⟨hac, le_rfl⟩)
        have hvK' : ∀ t ∈ Set.Icc c e, v t ∈ K t := by simpa [c, e, Nat.add_assoc] using hvK
        obtain ⟨w, hwleft, hwright, hw⟩ := glue_ode_solution_Icc f (b := e) hac
          (by dsimp only [c, e]; push_cast; linarith) u v (by simpa [c] using hv₀.symm) hu
          (by simpa [c, e, Nat.add_assoc] using hv)
        have hwK : ∀ t ∈ Set.Icc a e, w t ∈ K t := fun t ht ↦ by
          rcases le_total t c with htc | hct
          · simpa only [hwleft t ⟨ht.1, htc⟩] using huK t ⟨ht.1, htc⟩
          · simpa only [hwright t ⟨hct, ht.2⟩] using hvK' t ⟨hct, ht.2⟩
        exact ⟨w, (hwleft a ⟨le_rfl, hac⟩).trans hu₀, by simpa [e, Nat.add_assoc] using hw,
          by simpa [e, Nat.add_assoc] using hwK⟩
  obtain ⟨u, hu₀, hu, huK⟩ := hpartial (N - 1) (Nat.sub_lt hN one_pos)
  have hnadd : N - 1 + 1 = N := Nat.sub_add_cancel hN
  exact ⟨u, hu₀, by simpa [hnadd, hendpoint] using hu, by simpa [hnadd, hendpoint] using huK⟩

/--
Finite continuation from local solutions that preserve an invariant set.

Every state in `K` is assumed to start a solution on the next partition cell that
remains in `K`. Recursive gluing then produces a whole-interval solution that stays
in `K`. The set `K` need not be closed.
-/
theorem exists_ode_solution_Icc_of_partition_of_invariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (K : Set E) {a b d : ℝ} (hd : 0 ≤ d)
    (N : ℕ) (hN : 0 < N)
    (hendpoint : a + (N : ℝ) * d = b)
    (u₀ : E) (hu₀K : u₀ ∈ K)
    (hlocal : ∀ n : ℕ, n < N → ∀ x ∈ K,
      ∃ u : ℝ → E,
        u (a + (n : ℝ) * d) = x ∧
        (∀ t ∈ Set.Icc (a + (n : ℝ) * d)
              (a + ((n + 1 : ℕ) : ℝ) * d),
            HasDerivWithinAt u (f t (u t))
              (Set.Icc (a + (n : ℝ) * d)
                (a + ((n + 1 : ℕ) : ℝ) * d)) t) ∧
        ∀ t ∈ Set.Icc (a + (n : ℝ) * d)
            (a + ((n + 1 : ℕ) : ℝ) * d),
          u t ∈ K) :
    ∃ u : ℝ → E, u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (f t (u t)) (Set.Icc a b) t) ∧
      ∀ t ∈ Set.Icc a b, u t ∈ K := by
  exact exists_ode_solution_Icc_of_partition_of_timeDependentInvariant
    f (fun _ ↦ K) hd N hN hendpoint u₀ hu₀K hlocal

/--
Finite continuation from uniformly available local solutions.

The hypothesis supplies one solution on every consecutive cell of an
arithmetic partition, for every possible state at the left endpoint. The
proof applies invariant-set continuation to the whole state space.
-/
theorem exists_ode_solution_Icc_of_partition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) {a b d : ℝ} (hd : 0 ≤ d)
    (N : ℕ) (hN : 0 < N)
    (hendpoint : a + (N : ℝ) * d = b)
    (u₀ : E)
    (hlocal : ∀ n : ℕ, n < N → ∀ x : E,
      ∃ u : ℝ → E,
        u (a + (n : ℝ) * d) = x ∧
        ∀ t ∈ Set.Icc (a + (n : ℝ) * d)
            (a + ((n + 1 : ℕ) : ℝ) * d),
          HasDerivWithinAt u (f t (u t))
            (Set.Icc (a + (n : ℝ) * d)
              (a + ((n + 1 : ℕ) : ℝ) * d)) t) :
    ∃ u : ℝ → E, u a = u₀ ∧
      ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (f t (u t)) (Set.Icc a b) t := by
  obtain ⟨u, hu₀, hu, _huK⟩ :=
    exists_ode_solution_Icc_of_partition_of_invariant
      f Set.univ hd N hN hendpoint u₀ (Set.mem_univ u₀) (by
        intro n hn x _hx
        obtain ⟨v, hv₀, hv⟩ := hlocal n hn x
        exact ⟨v, hv₀, hv, fun _t _ht ↦ Set.mem_univ _⟩)
  exact ⟨u, hu₀, hu⟩

/--
Finite continuation controlled by an a priori energy sublevel.

If every state with `energy x ≤ C` starts a solution on the next partition
cell and that solution obeys the same bound, then the cellwise solutions glue
to a whole-interval trajectory satisfying `energy (u t) ≤ C`. The function
`energy : E → ℝ` is arbitrary.
-/
theorem exists_ode_solution_Icc_of_partition_of_energy_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (energy : E → ℝ) {a b d C : ℝ} (hd : 0 ≤ d)
    (N : ℕ) (hN : 0 < N)
    (hendpoint : a + (N : ℝ) * d = b)
    (u₀ : E) (hu₀_energy : energy u₀ ≤ C)
    (hlocal : ∀ n : ℕ, n < N → ∀ x : E, energy x ≤ C →
      ∃ u : ℝ → E,
        u (a + (n : ℝ) * d) = x ∧
        (∀ t ∈ Set.Icc (a + (n : ℝ) * d)
              (a + ((n + 1 : ℕ) : ℝ) * d),
            HasDerivWithinAt u (f t (u t))
              (Set.Icc (a + (n : ℝ) * d)
                (a + ((n + 1 : ℕ) : ℝ) * d)) t) ∧
        ∀ t ∈ Set.Icc (a + (n : ℝ) * d)
            (a + ((n + 1 : ℕ) : ℝ) * d),
          energy (u t) ≤ C) :
    ∃ u : ℝ → E, u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (f t (u t)) (Set.Icc a b) t) ∧
      ∀ t ∈ Set.Icc a b, energy (u t) ≤ C := by
  simpa only [Set.mem_ofPred_eq] using
    exists_ode_solution_Icc_of_partition_of_invariant
      f {x | energy x ≤ C} hd N hN hendpoint u₀ hu₀_energy hlocal

/--
Finite continuation controlled by a time-dependent energy envelope.

The allowable energy bound may vary with time. If every local solution
starting below the envelope at a cell's left endpoint remains below it
throughout that cell, then the glued whole-interval solution obeys the same
pointwise bound.
-/
theorem exists_ode_solution_Icc_of_partition_of_energyEnvelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → E) (energy bound : ℝ → E → ℝ)
    {a b d : ℝ} (hd : 0 ≤ d)
    (N : ℕ) (hN : 0 < N)
    (hendpoint : a + (N : ℝ) * d = b)
    (u₀ : E) (hu₀_energy : energy a u₀ ≤ bound a u₀)
    (hlocal : ∀ n : ℕ, n < N → ∀ x : E,
      energy (a + (n : ℝ) * d) x ≤ bound (a + (n : ℝ) * d) x →
        ∃ u : ℝ → E,
          u (a + (n : ℝ) * d) = x ∧
          (∀ t ∈ Set.Icc (a + (n : ℝ) * d)
                (a + ((n + 1 : ℕ) : ℝ) * d),
              HasDerivWithinAt u (f t (u t))
                (Set.Icc (a + (n : ℝ) * d)
                  (a + ((n + 1 : ℕ) : ℝ) * d)) t) ∧
          ∀ t ∈ Set.Icc (a + (n : ℝ) * d)
              (a + ((n + 1 : ℕ) : ℝ) * d),
            energy t (u t) ≤ bound t (u t)) :
    ∃ u : ℝ → E, u a = u₀ ∧
      (∀ t ∈ Set.Icc a b,
        HasDerivWithinAt u (f t (u t)) (Set.Icc a b) t) ∧
      ∀ t ∈ Set.Icc a b, energy t (u t) ≤ bound t (u t) := by
  simpa only [Set.mem_ofPred_eq] using
    exists_ode_solution_Icc_of_partition_of_timeDependentInvariant
      f (fun t ↦ {x | energy t x ≤ bound t x}) hd N hN hendpoint
      u₀ hu₀_energy hlocal

end FiniteContinuation

end PDE.Analysis.Evolution
