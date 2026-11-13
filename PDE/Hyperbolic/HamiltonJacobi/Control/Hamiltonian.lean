/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The control Hamiltonian in the forward-time convention

The terminal value has Hamiltonian `inf v, ⟪p, f x v⟫ + h x v`.
Reversing time negates this Hamiltonian. `controlHamiltonian` carries that forward-time sign,
matching `IsSpatialViscositySubsolution` and the initial-value comparison theorem.

Uniform bounds on velocity and running cost make the infimum finite for every
position and momentum. A common control compares two infima, giving momentum
Lipschitz constant `M` and spatial bound `(K * ‖p‖ + L) * ‖x-y‖`.

The terminal Hamiltonian is (23) in Remark (i) after Theorem 2 of Evans, §10.3.3, with an
infimum in place of his minimum over a compact control set, and the sign change is his
Remark (iii). The two bounds are the estimates (3) of §10.2, which Evans derives in Remark (i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.3, Remarks (i) and (iii) after Theorem 2, equation
  (23); §10.2, condition (3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace HamiltonJacobi

variable {E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The negative of the terminal control infimum, as required after time reversal.
The arguments are momentum followed by position. Bounds below justify the real
infimum for bounded velocities and running costs on a nonempty control space. -/
def controlHamiltonian (f : E → A → E) (h : E → A → ℝ) (p x : E) : ℝ :=
  -sInf (range (fun v ↦ ⟪p, f x v⟫_ℝ + h x v))

variable (f : E → A → E) (h : E → A → ℝ) (M C : NNReal)
  (hM : ∀ x v, ‖f x v‖ ≤ (M : ℝ)) (hC : ∀ x v, |h x v| ≤ (C : ℝ))

include hM hC

/-- Bounded speed controls the linear momentum term uniformly over controls. -/
private theorem control_pairing_bound (p x : E) (v : A) :
    |⟪p, f x v⟫_ℝ + h x v| ≤ ‖p‖ * (M : ℝ) + (C : ℝ) :=
  (abs_add_le _ _).trans (add_le_add ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hM x v) (norm_nonneg p))) (hC x v))

/-- The costs defining the Hamiltonian are bounded below before taking their infimum. -/
private theorem bddBelow_control_pairings (p x : E) :
    BddBelow (range (fun v ↦ ⟪p, f x v⟫_ℝ + h x v)) := by
  refine ⟨-(‖p‖ * (M : ℝ) + (C : ℝ)), ?_⟩
  rintro _ ⟨v, rfl⟩
  exact (abs_le.mp (control_pairing_bound f h M C hM hC p x v)).1

/-- The control Hamiltonian has at most linear growth in momentum, uniformly in position. -/
theorem abs_controlHamiltonian_le (p x : E) :
    |controlHamiltonian f h p x| ≤ ‖p‖ * (M : ℝ) + (C : ℝ) := by
  rcases isEmpty_or_nonempty A with hA | hA
  · rw [controlHamiltonian, range_eq_empty, Real.sInf_empty, neg_zero, abs_zero]
    positivity
  have hlow : -(‖p‖ * (M : ℝ) + (C : ℝ)) ≤
      sInf (range (fun v ↦ ⟪p, f x v⟫_ℝ + h x v)) := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨v, rfl⟩
    exact (abs_le.mp (control_pairing_bound f h M C hM hC p x v)).1
  obtain ⟨v⟩ := ‹Nonempty A›
  have hu := csInf_le (bddBelow_control_pairings f h M C hM hC p x) (mem_range_self v)
  have hb := (abs_le.mp (control_pairing_bound f h M C hM hC p x v)).2
  rw [controlHamiltonian, abs_neg]
  exact abs_le.mpr ⟨hlow, hu.trans hb⟩

/-- A common control bounds the change of the Hamiltonian in both variables.
The spatial error uses the second momentum; setting the momenta equal gives
exactly the growth allowed by the position-dependent comparison theorem. -/
theorem abs_controlHamiltonian_sub_le (K L : NNReal) (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (p q x y : E) :
    |controlHamiltonian f h p x - controlHamiltonian f h q y| ≤
      (M : ℝ) * ‖p - q‖ + ((K : ℝ) * ‖q‖ + (L : ℝ)) * ‖x - y‖ := by
  rcases isEmpty_or_nonempty A with hA | hA
  · simp only [controlHamiltonian, range_eq_empty, Real.sInf_empty, neg_zero, sub_self, abs_zero]
    positivity
  let D := (M : ℝ) * ‖p - q‖ + ((K : ℝ) * ‖q‖ + (L : ℝ)) * ‖x - y‖
  let F (r z : E) (v : A) := ⟪r, f z v⟫_ℝ + h z v
  have hd (v : A) : |F p x v - F q y v| ≤ D := by
    have hfxy : ‖f x v - f y v‖ ≤ (K : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm] using (hK v).dist_le_mul x y
    have hhxy : |h x v - h y v| ≤ (L : ℝ) * ‖x - y‖ := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using (hL v).dist_le_mul x y
    calc
      |F p x v - F q y v| =
          |⟪p - q, f x v⟫_ℝ + ⟪q, f x v - f y v⟫_ℝ + (h x v - h y v)| := by
        dsimp only [F]
        rw [inner_sub_left, inner_sub_right]
        congr 1
        ring
      _ ≤ |⟪p - q, f x v⟫_ℝ| + |⟪q, f x v - f y v⟫_ℝ| + |h x v - h y v| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ ‖p - q‖ * (M : ℝ) + ‖q‖ * ((K : ℝ) * ‖x - y‖) + (L : ℝ) * ‖x - y‖ :=
        add_le_add (add_le_add ((abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left (hM x v) (norm_nonneg _)))
          ((abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_left hfxy (norm_nonneg q)))) hhxy
      _ = D := by dsimp only [D]; ring
  have hp : ∀ v, sInf (range (F p x)) ≤ F p x v :=
    fun v ↦ csInf_le (bddBelow_control_pairings f h M C hM hC p x) (mem_range_self v)
  have hq : ∀ v, sInf (range (F q y)) ≤ F q y v :=
    fun v ↦ csInf_le (bddBelow_control_pairings f h M C hM hC q y) (mem_range_self v)
  have hl : sInf (range (F p x)) - D ≤ sInf (range (F q y)) := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨v, rfl⟩
    have hb := (abs_le.mp (hd v)).2
    linarith only [hp v, hb]
  have hr : sInf (range (F q y)) - D ≤ sInf (range (F p x)) := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨v, rfl⟩
    have hb := (abs_le.mp (hd v)).1
    linarith only [hq v, hb]
  change |-(sInf (range (F p x))) - -(sInf (range (F q y)))| ≤ D
  exact abs_le.mpr ⟨by linarith only [hl], by linarith only [hr]⟩

/-- Bounded speed gives the uniform momentum Lipschitz bound needed for comparison. -/
theorem lipschitzWith_controlHamiltonian (x : E) :
    LipschitzWith M (fun p ↦ controlHamiltonian f h p x) := by
  refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
  have he := abs_controlHamiltonian_sub_le (fun _ : E ↦ f x) (fun _ : E ↦ h x) M C
    (fun _ ↦ hM x) (fun _ ↦ hC x) 0 0
    (fun v ↦ LipschitzWith.const (f x v)) (fun v ↦ LipschitzWith.const (h x v)) p q x x
  simpa only [controlHamiltonian, Real.dist_eq, sub_self, norm_zero, mul_zero,
    add_zero, dist_eq_norm, Real.norm_eq_abs] using he

/-- Uniform state Lipschitz bounds give the spatial comparison estimate
with constant `K+L` for the forward-time control Hamiltonian. -/
theorem abs_controlHamiltonian_sub_position_le (K L : NNReal)
    (hK : ∀ v, LipschitzWith K (fun x ↦ f x v))
    (hL : ∀ v, LipschitzWith L (fun x ↦ h x v)) (p x y : E) :
    |controlHamiltonian f h p x - controlHamiltonian f h p y| ≤
      ((K + L : NNReal) : ℝ) * ‖x - y‖ * (1 + ‖p‖) := by
  have he := abs_controlHamiltonian_sub_le f h M C hM hC K L hK hL p p x y
  simp only [sub_self, norm_zero, mul_zero, zero_add] at he
  apply he.trans
  have hcoeff : (K : ℝ) * ‖p‖ + (L : ℝ) ≤ ((K : ℝ) + (L : ℝ)) * (1 + ‖p‖) := by
    calc
      (K : ℝ) * ‖p‖ + (L : ℝ) ≤ (K : ℝ) * ‖p‖ + (L : ℝ) + ((K : ℝ) + (L : ℝ) * ‖p‖) :=
        le_add_of_nonneg_right (add_nonneg K.property (mul_nonneg L.property (norm_nonneg p)))
      _ = ((K : ℝ) + (L : ℝ)) * (1 + ‖p‖) := by ring
  have hm := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg (x - y))
  simpa only [NNReal.coe_add, mul_assoc, mul_comm ‖x - y‖ (1 + ‖p‖)] using hm

end HamiltonJacobi
