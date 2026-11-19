/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Coefficients
public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Moments

/-!
# Moments of `cos β` times a table supported on even `β` frequencies

If the coefficients of `p` vanish outside one mode pair `(I₀, J₀)` and outside the even `β`
frequencies `K = 2m + 2`, with value `g m T` there, then `cos β · p` has the coefficients
`(g i T + g (i - 1) T) / 2` at the odd frequencies `2i + 1` (`moment_cosβ_mul_of_evenBlock`).
-/

@[expose] public section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {R : Type} [Field R] {Mβ Mθ Nβ Nθ : ℕ}

theorem coeffN_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R)
    (I J : Fin 2) (K T : ℕ) :
    (monomial i j k l c).coeffN I J K T = if I = i ∧ J = j ∧ K = k ∧ T = l then c else 0 := by
  unfold coeffN monomial
  split_ifs with h1 h2 h2 <;> simp_all [Fin.ext_iff]
  omega

theorem sum_range_two_mul_of_even_zero {M : Type*} [AddCommMonoid M] {h : ℕ → M}
    (heven : ∀ i, h (2 * i) = 0) (n : ℕ) :
    ∑ K ∈ range (2 * n), h K = ∑ i ∈ range n, h (2 * i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, heven, add_zero]

/-- **The moments of `cos β · p` for a block on even frequencies.** -/
theorem moment_cosβ_mul_of_evenBlock {n : ℕ} (p : TrigPoly2 Nβ Nθ ℝ) (hn : Nβ = 2 * n)
    (I₀ J₀ : Fin 2) (g : ℕ → ℕ → ℝ)
    (hp : ∀ I J K T, p.coeffN I J K T =
      if I = I₀ ∧ J = J₀ ∧ K % 2 = 0 ∧ 2 ≤ K then g (K / 2 - 1) T else 0)
    (a b : ℕ) :
    ((cosβ : TrigPoly2 1 0 ℝ).mul p).moment a b =
      ∑ i ∈ range (n + 1), ∑ T ∈ range (Nθ + 1),
        |(g i T + (if 1 ≤ i then g (i - 1) T else 0)) / 2| * ((2 * i + 1 : ℕ) : ℝ) ^ a *
          (T : ℝ) ^ b := by
  subst hn
  rw [moment_eq_sum_range]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, coeffN_cosβ_mul]
  have hzero : ∀ I J, ¬(I = I₀ ∧ J = J₀) → ∀ K T,
      ((p.coeffN I J (K + 1) T + (if 1 ≤ K then p.coeffN I J (K - 1) T else 0) +
        (if K = 1 then (if I = 0 then 1 else -1) * p.coeffN I J 0 T else 0)) / 2 : ℝ) = 0 := by
    intro I J hIJ K T
    have h0 : ∀ x : ℕ, ¬(I = I₀ ∧ J = J₀ ∧ x % 2 = 0 ∧ 2 ≤ x) := fun x hx ↦ hIJ ⟨hx.1, hx.2.1⟩
    simp only [hp, h0, ↓reduceIte]
    simp
  rw [Fintype.sum_eq_single I₀ fun I hI ↦ ?_, Fintype.sum_eq_single J₀ fun J hJ ↦ ?_]
  rotate_left
  · exact sum_eq_zero fun K _ ↦ sum_eq_zero fun T _ ↦ by
      rw [hzero I₀ J (fun h ↦ hJ h.2) K T]; simp
  · exact sum_eq_zero fun J _ ↦ sum_eq_zero fun K _ ↦ sum_eq_zero fun T _ ↦ by
      rw [hzero I J (fun h ↦ hI h.1) K T]; simp
  rw [show 1 + 2 * n + 1 = 2 * (n + 1) by ring]
  rw [sum_range_two_mul_of_even_zero (h := fun K ↦ ∑ T ∈ range (0 + Nθ + 1),
    |(p.coeffN I₀ J₀ (K + 1) T + (if 1 ≤ K then p.coeffN I₀ J₀ (K - 1) T else 0) +
      (if K = 1 then (if I₀ = 0 then 1 else -1) * p.coeffN I₀ J₀ 0 T else 0)) / 2| *
        (K : ℝ) ^ a * (T : ℝ) ^ b) (fun i ↦ sum_eq_zero fun T _ ↦ by
          simp only [hp, true_and]
          have h1 : ¬((2 * i + 1) % 2 = 0 ∧ 2 ≤ 2 * i + 1) := fun h ↦ by omega
          have h2 : ¬((2 * i - 1) % 2 = 0 ∧ 2 ≤ 2 * i - 1) := fun h ↦ by omega
          have h3 : ¬(2 ≤ 0) := by omega
          simp [h2])]
  rw [show 0 + Nθ + 1 = Nθ + 1 by ring]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun T _ ↦ ?_
  congr 3
  simp only [hp, true_and]
  have e1 : (2 * i + 1 + 1) % 2 = 0 ∧ 2 ≤ 2 * i + 1 + 1 := ⟨by omega, by omega⟩
  have e2 : (2 * i + 1 + 1) / 2 - 1 = i := by omega
  have e3 : 1 ≤ 2 * i + 1 := by omega
  have e4 : 2 * i + 1 - 1 = 2 * i := by omega
  by_cases hi : 1 ≤ i
  · have e5 : (2 * i) % 2 = 0 ∧ 2 ≤ 2 * i := ⟨by omega, by omega⟩
    simp [e1, e2, e3, e4, e5, hi]
  · have hi0 : i = 0 := by omega
    subst hi0
    simp

end PDE.Analysis.TrigPoly2
