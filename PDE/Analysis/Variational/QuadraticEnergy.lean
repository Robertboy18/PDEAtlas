/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import PDE.Analysis.Variational.WeakSolution
import PDE.Analysis.Operator.Coercivity
import PDE.Analysis.Variational.LaxMilgram

/-!
# Quadratic variational energies

For a symmetric bounded bilinear form `B` and a continuous load `ell`, the quadratic energy is

`J(v) = (1 / 2) B(v, v) - ell(v)`.

The completion-of-the-square identity gives the abstract Dirichlet
principle: weak solutions minimize `J`, and coercivity makes the minimizer
strict. Only the final existence direction uses the Hilbert-space
Lax-Milgram theorem. For the Dirichlet form on `H¹₀(Ω)` this is
Dirichlet's principle: the weak solution of `-Δu = f` is the unique minimiser
of `½ ∫ |∇v|² - ∫ f v`.

## Main results

* `energy B ell v`: the functional `J(v) = ½ B v v - ell v`.
* `energy_sub_energy_eq`: completion of the square at a weak solution.
* `IsWeakSolution.energy_le`, `IsWeakSolution.energy_lt_of_ne`: a weak
  solution minimises `J`, strictly when `B` is coercive.
* `IsWeakSolution.eq_of_minimizes_energy`: conversely, a global minimiser of
  `J` agrees with any weak solution of a symmetric coercive problem; no
  completeness is needed for this.
* `IsWeakSolution.energy_minimizer_iff`: on a Hilbert space, where Lax–Milgram
  supplies a weak solution, minimisers are exactly the weak solutions.
* `IsWeakSolution.tendsto_of_tendsto_energy`: energy convergence to the
  minimum implies norm convergence to the weak solution.

## How it works

Dirichlet's principle is classical: Evans, §2.2.5, Theorem 17, proves it for `C²` solutions of
Poisson's equation with the Cauchy-Schwarz and Cauchy inequalities, and the converse by the first
variation. We work with weak solutions of an abstract symmetric form and use instead the identity
`J(v) - J(u) = ½ B(v - u, v - u)` of `energy_sub_energy_eq`, valid whenever `u` is a weak solution
(`B u w = ell w` for all `w`) and `B` is symmetric. Everything else follows: nonnegativity of `B`
on the diagonal makes `u` a minimiser, and coercivity `B w w ≥ c ‖w‖²` makes it the unique
minimiser and turns convergence of energies into strong convergence, since
`c ‖v - u‖² ≤ 2 (J(v) - J(u))`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.5, Theorem 17 (Dirichlet's principle), pp. 42-43,
  and §8.1.2, Examples 1 and 2 (the generalized Dirichlet principle for symmetric coefficients),
  p. 456. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The quadratic energy associated with a bilinear form and a load. -/
def energy
    (B : V →L[ℝ] V →L[ℝ] ℝ) (ell : StrongDual ℝ V) (v : V) : ℝ :=
  (1 / 2 : ℝ) * B v v - ell v

/-- Completion of the square at a weak solution of a symmetric variational
problem. -/
theorem energy_sub_energy_eq
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u : V}
    (hBsymm : ∀ v w, B v w = B w v)
    (hu : IsWeakSolution B ell u) (v : V) :
    energy B ell v - energy B ell u =
      (1 / 2 : ℝ) * B (v - u) (v - u) := by
  have huv : B u v = ell v := hu v
  have huu : B u u = ell u := hu u
  have hvu : B v u = ell v := by rw [hBsymm v u, huv]
  simp only [energy, map_sub, sub_apply]
  rw [huv, huu, hvu]
  ring

/-- A weak solution minimizes the quadratic energy when the symmetric form
is nonnegative on the diagonal. -/
theorem IsWeakSolution.energy_le
    {B : V →L[ℝ] V →L[ℝ] ℝ} {ell : StrongDual ℝ V} {u : V}
    (hBsymm : ∀ v w, B v w = B w v)
    (hBnonneg : ∀ w, 0 ≤ B w w)
    (hu : IsWeakSolution B ell u) (v : V) :
    energy B ell u ≤ energy B ell v := by
  have hdiff := energy_sub_energy_eq hBsymm hu v
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * B (v - u) (v - u) :=
    mul_nonneg (by norm_num) (hBnonneg (v - u))
  linarith

/-- Equality with the weak-solution energy forces equality with the weak
solution for a coercive symmetric form. -/
theorem IsWeakSolution.eq_of_energy_eq
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u v : V}
    (hBsymm : ∀ x y, B x y = B y x)
    (hu : IsWeakSolution B ell u)
    (hv : energy B ell v = energy B ell u) :
    v = u := by
  have hdiff := energy_sub_energy_eq hBsymm hu v
  have hBzero : B (v - u) (v - u) = 0 := by
    rw [hv] at hdiff
    linarith
  rcases coercive with ⟨C, hC, hcoercive⟩
  have hbound := hcoercive (v - u)
  rw [hBzero] at hbound
  have hnorm : ‖v - u‖ = 0 := by
    by_contra hne
    have hnorm_pos : 0 < ‖v - u‖ :=
      lt_of_le_of_ne (norm_nonneg (v - u)) (Ne.symm hne)
    have hproduct_pos : 0 < C * ‖v - u‖ * ‖v - u‖ :=
      mul_pos (mul_pos hC hnorm_pos) hnorm_pos
    exact (not_lt_of_ge hbound) hproduct_pos
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Equality with the weak-solution energy is equivalent to equality with
the weak solution. -/
theorem IsWeakSolution.energy_eq_iff
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u v : V}
    (hBsymm : ∀ x y, B x y = B y x)
    (hu : IsWeakSolution B ell u) :
    energy B ell v = energy B ell u ↔ v = u := by
  constructor
  · intro hv
    exact hu.eq_of_energy_eq coercive hBsymm hv
  · intro hv
    subst hv
    rfl

/-- For a symmetric coercive problem, convergence of energies to the minimum
forces strong convergence to the weak solution. -/
theorem IsWeakSolution.tendsto_of_tendsto_energy
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u : V}
    (hBsymm : ∀ x y, B x y = B y x)
    (hu : IsWeakSolution B ell u)
    {ι : Type*} {l : Filter ι} (v : ι → V)
    (henergy :
      Filter.Tendsto (fun i ↦ energy B ell (v i)) l
        (nhds (energy B ell u))) :
    Filter.Tendsto v l (nhds u) := by
  have hgap :
      Filter.Tendsto
        (fun i ↦ energy B ell (v i) - energy B ell u) l (nhds 0) := by
    simpa using henergy.sub_const (energy B ell u)
  have hform :
      Filter.Tendsto (fun i ↦ B (v i - u) (v i - u)) l (nhds 0) := by
    have htwice := hgap.const_mul 2
    convert htwice using 1
    · funext i
      have hdiff := energy_sub_energy_eq hBsymm hu (v i)
      linarith
    · simp
  rcases coercive with ⟨C, hC, hcoercive⟩
  have hnormSq :
      Filter.Tendsto (fun i ↦ ‖v i - u‖ ^ 2) l (nhds 0) := by
    apply squeeze_zero
    · exact fun i ↦ sq_nonneg ‖v i - u‖
    · intro i
      apply (le_div_iff₀ hC).2
      calc
        ‖v i - u‖ ^ 2 * C =
            C * ‖v i - u‖ * ‖v i - u‖ := by ring
        _ ≤ B (v i - u) (v i - u) := hcoercive (v i - u)
    · simpa using hform.div_const C
  have hnorm :
      Filter.Tendsto (fun i ↦ ‖v i - u‖) l (nhds 0) := by
    have hsqrt :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hnormSq
    convert hsqrt using 1
    · funext i
      exact (Real.sqrt_sq (norm_nonneg (v i - u))).symm
    · simp
  have hsub : Filter.Tendsto (fun i ↦ v i - u) l (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [sub_add_cancel, zero_add] using hsub.add_const u

/-- A symmetric coercive weak solution is a strict energy minimizer. -/
theorem IsWeakSolution.energy_lt_of_ne
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u v : V}
    (hBsymm : ∀ x y, B x y = B y x)
    (hu : IsWeakSolution B ell u) (hvu : v ≠ u) :
    energy B ell u < energy B ell v := by
  have hle : energy B ell u ≤ energy B ell v :=
    hu.energy_le hBsymm coercive.self_nonneg v
  exact lt_of_le_of_ne hle (by
    intro hEq
    exact hvu ((hu.energy_eq_iff coercive hBsymm).mp hEq.symm))

/-- A global minimizer of the energy agrees with a weak solution of a
symmetric coercive problem. -/
theorem IsWeakSolution.eq_of_minimizes_energy
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u v : V}
    (hBsymm : ∀ x y, B x y = B y x)
    (hu : IsWeakSolution B ell u)
    (hv : ∀ w, energy B ell v ≤ energy B ell w) :
    v = u := by
  apply hu.eq_of_energy_eq coercive hBsymm
  exact le_antisymm (hv u)
    (hu.energy_le hBsymm coercive.self_nonneg v)

end NormedSpace

section Hilbert

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- For a symmetric coercive form, global energy minimizers are exactly the
variational weak solutions. -/
theorem IsWeakSolution.energy_minimizer_iff
    {B : V →L[ℝ] V →L[ℝ] ℝ} (coercive : IsCoercive B)
    {ell : StrongDual ℝ V} {u : V}
    (hBsymm : ∀ x y, B x y = B y x) :
    (∀ v, energy B ell u ≤ energy B ell v) ↔ IsWeakSolution B ell u := by
  constructor
  · intro hmin
    have hu : u = solve B coercive ell :=
      (solve.isWeakSolution B coercive ell).eq_of_minimizes_energy
        coercive hBsymm hmin
    rw [hu]
    exact solve.isWeakSolution B coercive ell
  · intro hu v
    exact hu.energy_le hBsymm coercive.self_nonneg v

end Hilbert

end PDE.Analysis.Variational
