/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Coefficient agreement in a distinguished variable

Agreement on a lower set of exponents is preserved by multiplication and
admissible substitution. In particular, coefficients through a fixed time degree
can be compared without truncating the spatial variables. Differentiating in a
different variable preserves this agreement.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ τ κ R : Type*}

section Semiring

variable [CommSemiring R]

/-- Multiplication preserves coefficient agreement on a lower set of exponents. -/
theorem eqOn_coeff_mul {s : Set (σ →₀ ℕ)}
    (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    {f₁ f₂ g₁ g₂ : MvPowerSeries σ R}
    (hf : Set.EqOn (fun a ↦ coeff a f₁) (fun a ↦ coeff a f₂) s)
    (hg : Set.EqOn (fun a ↦ coeff a g₁) (fun a ↦ coeff a g₂) s) :
    Set.EqOn (fun a ↦ coeff a (f₁ * g₁)) (fun a ↦ coeff a (f₂ * g₂)) s := by
  classical
  intro a ha
  change coeff a (f₁ * g₁) = coeff a (f₂ * g₂)
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = a := Finset.mem_antidiagonal.mp hp
  have h₁ : p.1 ≤ a := hp' ▸ le_self_add
  have h₂ : p.2 ≤ a := hp' ▸ le_add_self
  exact congrArg₂ (· * ·) (hf (hs ha h₁)) (hg (hs ha h₂))

/-- Raising to a natural power preserves agreement on a lower set of exponents. -/
theorem eqOn_coeff_pow {s : Set (σ →₀ ℕ)}
    (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    {f g : MvPowerSeries σ R}
    (h : Set.EqOn (fun a ↦ coeff a f) (fun a ↦ coeff a g) s) (n : ℕ) :
    Set.EqOn (fun a ↦ coeff a (f ^ n)) (fun a ↦ coeff a (g ^ n)) s := by
  induction n with
  | zero => intro a ha; rfl
  | succ n ih =>
    simpa only [pow_succ] using eqOn_coeff_mul hs ih h

/-- Finite products preserve coefficient agreement on a lower set of exponents. -/
theorem eqOn_coeff_prod {s : Set (σ →₀ ℕ)}
    (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    (t : Finset κ) {f g : κ → MvPowerSeries σ R}
    (h : ∀ j ∈ t, Set.EqOn (fun a ↦ coeff a (f j)) (fun a ↦ coeff a (g j)) s) :
    Set.EqOn (fun a ↦ coeff a (∏ j ∈ t, f j)) (fun a ↦ coeff a (∏ j ∈ t, g j)) s := by
  classical
  induction t using Finset.induction_on with
  | empty => intro a ha; simp
  | @insert j t hj ih =>
    simp only [Finset.prod_insert hj]
    exact eqOn_coeff_mul hs (h j (Finset.mem_insert_self _ _))
      (ih fun k hk ↦ h k (Finset.mem_insert_of_mem hk))

end Semiring

section Ring

variable [CommRing R]

/-- Admissible substitution preserves agreement of the substituted series on a lower set.
No positivity of their orders in the distinguished variable is required. -/
theorem eqOn_coeff_subst {s : Set (τ →₀ ℕ)}
    (hs : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ≤ a → b ∈ s)
    {a b : σ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b)
    (h : ∀ j, Set.EqOn (fun e ↦ coeff e (a j)) (fun e ↦ coeff e (b j)) s)
    (f : MvPowerSeries σ R) :
    Set.EqOn (fun e ↦ coeff e (subst a f)) (fun e ↦ coeff e (subst b f)) s := by
  intro e he
  change coeff e (subst a f) = coeff e (subst b f)
  rw [coeff_subst ha, coeff_subst hb]
  apply finsum_congr
  intro d
  congr 1
  exact eqOn_coeff_prod hs d.support (fun j _ ↦ eqOn_coeff_pow hs (h j) (d j)) he

/-- Differentiation in another variable preserves agreement through a fixed coordinate degree. -/
theorem coeff_pderiv_eq_of_coordinate_eq {i j : σ} (hji : j ≠ i) {n : ℕ}
    {f g : MvPowerSeries σ R}
    (h : ∀ a, a i ≤ n → coeff a f = coeff a g) :
    ∀ a, a i ≤ n → coeff a (pderiv j f) = coeff a (pderiv j g) := by
  classical
  intro a ha
  rw [coeff_pderiv, coeff_pderiv, h (a + Finsupp.single j 1)]
  simpa [Finsupp.single_apply, hji] using ha

end Ring

section DistinguishedVariable

variable [CommSemiring R] {d : ℕ}

/-- The distinguished partial derivative becomes the ordinary formal derivative
under Mathlib's equivalence that separates the first variable. -/
theorem finSuccEquiv_pderiv_zero (f : MvPowerSeries (Fin (d + 1)) R) :
    finSuccEquiv R d (pderiv 0 f) = PowerSeries.derivative (finSuccEquiv R d f) := by
  apply PowerSeries.ext
  intro k
  apply ext
  intro a
  have ha : a.cons k + Finsupp.single 0 1 = a.cons (k + 1) := by
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp
  have hmul (q : MvPowerSeries (Fin d) R) :
      coeff a (q * (k + 1 : MvPowerSeries (Fin d) R)) = coeff a q * (k + 1 : R) := by
    simpa [nsmul_eq_mul, mul_comm] using map_nsmul (coeff a) (k + 1) q
  rw [coeff_coeff_finSuccEquiv, coeff_pderiv, PowerSeries.coeff_derivative,
    hmul, coeff_coeff_finSuccEquiv, ha, Finsupp.cons_zero]

/-- Spatial differentiation acts separately on every coefficient in the distinguished variable. -/
theorem coeff_finSuccEquiv_pderiv_succ
    (f : MvPowerSeries (Fin (d + 1)) R) (j : Fin d) (k : ℕ) :
    PowerSeries.coeff k (finSuccEquiv R d (pderiv j.succ f)) =
      pderiv j (PowerSeries.coeff k (finSuccEquiv R d f)) := by
  classical
  apply ext
  intro a
  have ha : a.cons k + Finsupp.single j.succ 1 = (a + Finsupp.single j 1).cons k := by
    ext l
    refine Fin.cases ?_ (fun i ↦ ?_) l <;> simp [Finsupp.single_apply]
  rw [coeff_coeff_finSuccEquiv, coeff_pderiv, coeff_pderiv,
    coeff_coeff_finSuccEquiv, ha, Finsupp.cons_succ]

end DistinguishedVariable

end MvPowerSeries
