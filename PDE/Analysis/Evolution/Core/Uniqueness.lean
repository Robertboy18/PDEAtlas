/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PDE.Analysis.Evolution.Core.WeakEvolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Analysis.Evolution.Core.EnergyIdentity

/-!
# Energy uniqueness for weak evolutions

Evans's Hilbert-space uniqueness argument. If `u` is differentiable within
`[a, b]` and solves the homogeneous weak equation `⟪u', v⟫ + B(t)(u, v) = 0`
with `B(t)(u(t), u(t)) ≥ 0`, then `½ ‖u‖²` is nonincreasing, so `u(a) = 0`
forces `u = 0` on `[a, b]`. Two such solutions of the same forced equation with
equal initial values therefore agree on `[a, b]`. The form may depend on time,
with no regularity in `t`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 4 (uniqueness of weak solutions), whose
  proof tests the homogeneous equation with the solution itself.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- For a homogeneous equation with a nonnegative form, the Hilbert energy
has nonpositive derivative. -/
theorem weakEvolution_homogeneous_energy_deriv_nonpos
    (B : V →L[ℝ] StrongDual ℝ V) {u du : V}
    (hB : 0 ≤ B u u)
    (heq : SatisfiesWeakEvolutionAt B 0 u du) :
    inner ℝ du u ≤ 0 := by
  have h := heq u
  simp only [zero_apply] at h
  linarith

/-- Evans's energy uniqueness argument: a homogeneous weak evolution with zero
initial value and nonnegative forms `B(t)` vanishes on `[a, b]`.

No differentiability of `t ↦ B(t)` is needed: testing the homogeneous weak
equation by `u(t)` and assuming nonnegativity of `B(t)` makes the Hilbert
energy nonincreasing.
-/
theorem weakEvolution_zero_of_initial
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (u du : ℝ → V)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hB : ∀ t ∈ Set.Icc a b, 0 ≤ B t (u t) (u t))
    (heq : ∀ t ∈ Set.Icc a b, SatisfiesWeakEvolutionAt (B t) 0 (u t) (du t))
    (hinit : u a = 0) :
    ∀ t ∈ Set.Icc a b, u t = 0 := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖u t‖ ^ 2
  have hEderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt E (inner ℝ (du t) (u t)) (Set.Icc a b) t := by
    exact hasDerivWithinAt_half_norm_sq (hu t ht)
  have hEcont : ContinuousOn E (Set.Icc a b) := by
    intro t ht
    exact (hEderiv t ht).continuousWithinAt
  have hEanti : AntitoneOn E (Set.Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hEcont
    · intro t ht
      exact (hEderiv t (interior_subset ht)).mono interior_subset
    · intro t ht
      exact weakEvolution_homogeneous_energy_deriv_nonpos (B t)
        (hB t (interior_subset ht)) (heq t (interior_subset ht))
  intro t ht
  have hEa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hEle : E t ≤ E a := hEanti hEa ht ht.1
  have hEzero : E a = 0 := by simp [E, hinit]
  have hEnonneg : 0 ≤ E t := by positivity
  have hnorm : ‖u t‖ = 0 := by
    rw [hEzero] at hEle
    dsimp [E] at hEle hEnonneg
    nlinarith [sq_nonneg ‖u t‖]
  exact norm_eq_zero.mp hnorm

/-- Uniqueness for differentiable-in-time weak solutions of a parabolic weak
equation with time-dependent nonnegative forms, the same forcing and the same
initial datum. A time-independent form is the case `B := fun _ ↦ B`. -/
theorem weakEvolution_unique
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V)
    (u v du dv : ℝ → V)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hv : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt v (dv t) (Set.Icc a b) t)
    (hB : ∀ t ∈ Set.Icc a b, ∀ w : V, 0 ≤ B t w w)
    (heu : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (B t) (ell t) (u t) (du t))
    (hev : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (B t) (ell t) (v t) (dv t))
    (hinit : u a = v a) :
    ∀ t ∈ Set.Icc a b, u t = v t := by
  let w : ℝ → V := fun t ↦ u t - v t
  let dw : ℝ → V := fun t ↦ du t - dv t
  have hwderiv (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt w (dw t) (Set.Icc a b) t := by
    exact (hu t ht).sub (hv t ht)
  have hweq (t : ℝ) (ht : t ∈ Set.Icc a b) :
      SatisfiesWeakEvolutionAt (B t) 0 (w t) (dw t) := by
    simpa [w, dw] using
      (heu t ht).difference_same_forcing_homogeneous (hev t ht)
  have hwinit : w a = 0 := by simp [w, hinit]
  have hwzero := weakEvolution_zero_of_initial B hab w dw hwderiv
    (fun t ht ↦ hB t ht (w t)) hweq hwinit
  intro t ht
  have := hwzero t ht
  simpa [w, sub_eq_zero] using this

end PDE.Analysis.Evolution
