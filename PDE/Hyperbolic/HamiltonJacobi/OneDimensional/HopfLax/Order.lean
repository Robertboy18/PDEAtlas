/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset

/-!
# Order properties of the one-dimensional Hopf–Lax operator

The Hopf–Lax formula

`hopfLax H φ t x = inf_y (φ(y) + t L((x - y) / t))`, `L = H*`,

is an infimum of translates of the datum, so it inherits the elementary order
properties of infima: it is monotone in `φ`, commutes with adding a constant
to `φ`, and commutes with spatial translation. We prove these facts
under the minimal hypothesis that the relevant integrand is bounded below
(`HopfLaxBddBelow`), which is what makes the real-valued infimum meaningful.
They are the analytic core of comparison and uniform nonexpansivity for the
evolution.

## Main results

* `hopfLax_mono_phi`: `φ ≤ ψ` pointwise implies `hopfLax H φ ≤ hopfLax H ψ`.
* `hopfLax_add_const`: adding `c` to the datum adds `c` to the value.
* `hopfLax_le_self`: the competitor `y = x` gives
  `hopfLax H φ t x ≤ φ(x) + t L(0)`.
* `hopfLax_comp_add_left`: translating the datum translates the profile.
* `hopfLax_add_affine_hamiltonian`: replacing `H` by `H + a p + b` transports
  the profile with velocity `a` and subtracts the constant cost `t b`.
* `hopfLax_le_of_phi_le_add_const`: `φ ≤ ψ + c` implies
  `hopfLax H φ ≤ hopfLax H ψ + c`, the one-sided form of nonexpansivity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

set_option linter.missingDocs true

/-- Adding a constant to the initial datum preserves boundedness below of the integrand. -/
theorem HopfLaxBddBelow.add_const {H φ : ℝ → ℝ} {t x c : ℝ} (hbb : HopfLaxBddBelow H φ t x) :
    HopfLaxBddBelow H (fun y ↦ φ y + c) t x := by
  obtain ⟨B, hB⟩ := hbb
  refine ⟨B + c, Set.forall_mem_range.2 fun y ↦ ?_⟩
  have hy : B ≤ hopfLaxIntegrand H φ t x y := hB ⟨y, rfl⟩
  have hI : hopfLaxIntegrand H (fun y ↦ φ y + c) t x y = hopfLaxIntegrand H φ t x y + c := by
    simp only [hopfLaxIntegrand]
    ring
  linarith

/-- Monotonicity in the initial data `φ` (order-preserving), assuming bounded-below. -/
theorem hopfLax_mono_phi {H φ ψ : ℝ → ℝ} {t x : ℝ}
    (hbb : HopfLaxBddBelow H φ t x) (hφψ : ∀ y : ℝ, φ y ≤ ψ y) :
    hopfLax H φ t x ≤ hopfLax H ψ t x :=
  le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦
    (hopfLax_le_integrand (y := y) hbb).trans (by unfold hopfLaxIntegrand; gcongr; exact hφψ y))

/-- A direct upper bound obtained by evaluating the integrand at `y = x`. -/
theorem hopfLax_le_self {H φ : ℝ → ℝ} {t x : ℝ} (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H φ t x ≤ φ x + t * legendreTransform H 0 := by
  simpa [hopfLaxIntegrand] using hopfLax_le_integrand (y := x) hbb

/-- The Hopf–Lax operator commutes with addition of a constant to the initial datum. -/
theorem hopfLax_add_const {H φ : ℝ → ℝ} {t x c : ℝ} (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H (fun y ↦ φ y + c) t x = hopfLax H φ t x + c := by
  have hI (y : ℝ) :
      hopfLaxIntegrand H (fun y ↦ φ y + c) t x y = hopfLaxIntegrand H φ t x y + c := by
    simp only [hopfLaxIntegrand]
    ring
  refine le_antisymm ?_ (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦ ?_))
  · rw [← sub_le_iff_le_add]
    refine le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦ ?_)
    linarith [hopfLax_le_integrand (y := y) (HopfLaxBddBelow.add_const (c := c) hbb), hI y]
  · linarith [hopfLax_le_integrand (y := y) hbb, hI y]

/-- Spatial translation of the initial datum translates the Hopf–Lax
profile by the same amount. -/
theorem hopfLax_comp_add_left (H φ : ℝ → ℝ) (a t x : ℝ) :
    hopfLax H (fun y ↦ φ (a + y)) t x = hopfLax H φ t (a + x) := by
  have h : (fun y ↦ hopfLaxIntegrand H (fun y ↦ φ (a + y)) t x y) =
      (fun z ↦ hopfLaxIntegrand H φ t (a + x) z) ∘ (a + ·) := by
    funext y
    simp [hopfLaxIntegrand, add_sub_add_left_eq_sub]
  rw [hopfLax, hopfLax, h, (add_left_surjective a).range_comp]

/-- An affine perturbation `p ↦ a * p + b` of the Hamiltonian transports the
Hopf–Lax profile with velocity `a` and subtracts the accumulated constant
cost `t * b`. -/
theorem hopfLax_add_affine_hamiltonian {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {a b t x : ℝ}
    (ht : t ≠ 0) (hbb : HopfLaxBddBelow H φ t (x - a * t)) :
    hopfLax (fun p ↦ H p + a * p + b) φ t x = hopfLax H φ t (x - a * t) - t * b := by
  have hslope (y : ℝ) : (x - y) / t - a = ((x - a * t) - y) / t := by
    field_simp
    ring
  rw [sub_eq_add_neg, ← hopfLax_add_const hbb]
  unfold hopfLax
  congr 2
  funext y
  simp only [hopfLaxIntegrand, legendreTransform_add_affine hFin, hslope]
  ring

/-- An upper comparison up to a constant transfers boundedness below between Hopf–Lax data. -/
theorem hopfLax_bddBelow_of_le_add_const {H φ ψ : ℝ → ℝ} {t x c : ℝ}
    (hbb : HopfLaxBddBelow H φ t x) (hφψ : ∀ y : ℝ, φ y ≤ ψ y + c) :
    HopfLaxBddBelow H ψ t x := by
  obtain ⟨B, hB⟩ := hbb
  refine ⟨B - c, Set.forall_mem_range.2 fun y ↦ ?_⟩
  have hy : B ≤ hopfLaxIntegrand H φ t x y := hB ⟨y, rfl⟩
  have hI : hopfLaxIntegrand H φ t x y ≤ hopfLaxIntegrand H ψ t x y + c := by
    simp only [hopfLaxIntegrand]
    linarith [hφψ y]
  linarith

/-- Pointwise domination of initial data up to `c` yields the same domination after Hopf–Lax
evolution. -/
theorem hopfLax_le_of_phi_le_add_const {H φ ψ : ℝ → ℝ} {t x c : ℝ}
    (hbb : HopfLaxBddBelow H φ t x) (hφψ : ∀ y : ℝ, φ y ≤ ψ y + c) :
    hopfLax H φ t x ≤ hopfLax H ψ t x + c :=
  (hopfLax_mono_phi hbb hφψ).trans_eq (hopfLax_add_const (hopfLax_bddBelow_of_le_add_const hbb hφψ))

end

end HopfLax1D
