/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

public import PDE.Analysis.Evolution.Gelfand.Equation
public import PDE.Analysis.Evolution.Gelfand.PivotDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Analysis.Evolution.Core.EnergyIdentity

/-!
# Uniqueness for smooth Gelfand evolutions

Let `V ↪ H` be a Gelfand triple and let `B(t) : V → V*` be a family of bounded
forms. A trajectory `u : ℝ → V` is a *smooth* Gelfand evolution on `[a, b]` when
the pivot-space curve `t ↦ i(u t)` has a classical derivative `duH t ∈ H` at every
`t ∈ [a, b]`, this derivative represents the dual derivative `du t` through the pivot
inner product (`RepresentsPivotDerivative`), and the weak equation
`du t + B(t) (u t) = ℓ(t)` holds in `V*` (`SatisfiesGelfandWeakEvolutionAt`).

The uniqueness proof is the pivot-energy method. For a homogeneous solution the
energy `E(t) = ½ ‖i(u t)‖_H²` has derivative `⟪duH t, i(u t)⟫ = (du t)(u t) =
-B(t)(u t)(u t) ≤ 0`, so `E` is antitone and vanishes identically once `u a = 0`.
Only nonnegativity of `B(t)` along the trajectory is used. Evans proves uniqueness of weak
solutions of second-order parabolic equations by the same energy argument (§7.1.2,
Theorem 4), with Gårding's inequality and Grönwall's inequality in place of nonnegativity. We
run it for an abstract Gelfand triple and a trajectory with a pointwise-in-time derivative.

## Main results

* `gelfandWeakEvolution_zero_of_initial`: a homogeneous smooth evolution with
  `u a = 0` vanishes on `[a, b]`.
* `gelfandWeakEvolution_unique`: two smooth evolutions with the same forcing
  and the same initial value agree on `[a, b]`.

## Implementation notes

The differentiability hypothesis `hu` is a `HasDerivAt` of the `H`-valued curve at each
time of the closed interval, so these results apply to classical (strong) solutions. The
equation is stated pointwise; `SatisfiesGelfandWeakEvolutionOn` unfolds to the same
hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 4 (uniqueness of weak solutions).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace Topology

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Homogeneous uniqueness for a time-dependent form: if `u` is a smooth solution of
`u' + B(t) u = 0` on `[a, b]` with `u(a) = 0` and `B(t)(u(t), u(t)) ≥ 0`, then `u = 0` on
`[a, b]`. This is the smooth-trajectory form of Evans' parabolic uniqueness argument.
-/
theorem gelfandWeakEvolution_zero_of_initial
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → V) (du : ℝ → StrongDual ℝ V) (duH : ℝ → H)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s ↦ T.inclusion (u s)) (duH t) t)
    (hrep : ∀ t ∈ Set.Icc a b, RepresentsPivotDerivative T (du t) (duH t))
    (hB : ∀ t ∈ Set.Icc a b, 0 ≤ B t (u t) (u t))
    (heq : ∀ t ∈ Set.Icc a b,
      SatisfiesGelfandWeakEvolutionAt (B t) 0 (u t) (du t))
    (hinit : u a = 0) :
    ∀ t ∈ Set.Icc a b, u t = 0 := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖T.inclusion (u t)‖ ^ 2
  have hEderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt E (inner ℝ (duH t) (T.inclusion (u t))) t :=
    hasDerivAt_half_norm_sq (hu t ht)
  have hEcont : ContinuousOn E (Set.Icc a b) := by
    intro t ht
    exact (hEderiv t ht).continuousAt.continuousWithinAt
  have hEanti : AntitoneOn E (Set.Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hEcont
    · intro t ht
      exact (hEderiv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have htIcc := interior_subset ht
      have heqSelf := heq t htIcc (u t)
      have hpivot := hrep t htIcc (u t)
      simp only [zero_apply] at heqSelf
      linarith [hB t htIcc]
  intro t ht
  have hEa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hEle : E t ≤ E a := hEanti hEa ht ht.1
  have hEzero : E a = 0 := by simp [E, hinit]
  have hEnonneg : 0 ≤ E t := by positivity
  have hnorm : ‖T.inclusion (u t)‖ = 0 := by
    rw [hEzero] at hEle
    dsimp [E] at hEle hEnonneg
    nlinarith [sq_nonneg ‖T.inclusion (u t)‖]
  have hinclusion : T.inclusion (u t) = 0 := norm_eq_zero.mp hnorm
  exact T.injective (by simpa using hinclusion)

/-- Uniqueness of smooth Gelfand evolutions for a time-dependent form with
the same forcing and initial datum. A time-independent form is the case
`B := fun _ ↦ B`. -/
theorem gelfandWeakEvolution_unique
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V)
    (u v : ℝ → V) (du dv : ℝ → StrongDual ℝ V) (duH dvH : ℝ → H)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s ↦ T.inclusion (u s)) (duH t) t)
    (hv : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s ↦ T.inclusion (v s)) (dvH t) t)
    (hurep : ∀ t ∈ Set.Icc a b, RepresentsPivotDerivative T (du t) (duH t))
    (hvrep : ∀ t ∈ Set.Icc a b, RepresentsPivotDerivative T (dv t) (dvH t))
    (hB : ∀ t ∈ Set.Icc a b, ∀ z : V, 0 ≤ B t z z)
    (heu : ∀ t ∈ Set.Icc a b,
      SatisfiesGelfandWeakEvolutionAt (B t) (ell t) (u t) (du t))
    (hev : ∀ t ∈ Set.Icc a b,
      SatisfiesGelfandWeakEvolutionAt (B t) (ell t) (v t) (dv t))
    (hinit : u a = v a) :
    ∀ t ∈ Set.Icc a b, u t = v t := by
  let w : ℝ → V := fun t ↦ u t - v t
  let dw : ℝ → StrongDual ℝ V := fun t ↦ du t - dv t
  let dwH : ℝ → H := fun t ↦ duH t - dvH t
  have hwderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivAt (fun s ↦ T.inclusion (w s)) (dwH t) t := by
    have hfun :
        (fun s ↦ T.inclusion (w s)) =
          (fun s ↦ T.inclusion (u s)) - fun s ↦ T.inclusion (v s) := by
      funext s
      simp [w]
    rw [hfun]
    simpa [dwH] using (hu t ht).sub (hv t ht)
  have hwrep (t : ℝ) (ht : t ∈ Set.Icc a b) :
      RepresentsPivotDerivative T (dw t) (dwH t) := by
    simpa [dw, dwH] using (hurep t ht).sub (hvrep t ht)
  have hweq (t : ℝ) (ht : t ∈ Set.Icc a b) :
      SatisfiesGelfandWeakEvolutionAt (B t) 0 (w t) (dw t) := by
    simpa [w, dw] using
      (heu t ht).difference_same_forcing_homogeneous (hev t ht)
  have hwinit : w a = 0 := by simp [w, hinit]
  have hwzero := gelfandWeakEvolution_zero_of_initial T B hab w dw dwH
    hwderiv hwrep (fun t ht ↦ hB t ht (w t)) hweq hwinit
  intro t ht
  simpa [w, sub_eq_zero] using hwzero t ht

end PDE.Analysis.Evolution
