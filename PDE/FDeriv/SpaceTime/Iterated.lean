/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.SpaceTime

/-!
# Time differentiation of finite spatial derivative words

A word of `j` spatial derivatives costs `j` derivatives of joint
regularity. One more joint derivative permits time differentiation and commutation
with the entire word.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- A spatial derivative word lowers local joint regularity by its length. -/
theorem contDiffAt_iteratedPartialDeriv_prod_spaceSlice
    (indices : List (Fin n)) (f : ℝ^n × ℝ → E) (m : ℕ) (xt : ℝ^n × ℝ)
    (hf : ContDiffAt ℝ (m + indices.length : ℕ) f xt) :
    ContDiffAt ℝ m
      (fun q : ℝ^n × ℝ ↦
        iteratedPartialDeriv indices (fun y ↦ f (y, q.2)) q.1) xt := by
  induction indices generalizing m with
  | nil => simpa only [List.length_nil, Nat.add_zero, iteratedPartialDeriv,
      Prod.mk.eta] using hf
  | cons i rest ih =>
      have hrest := ih (m + 1) (by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hf)
      exact contDiffAt_partialDeriv_prod_spaceSlice i _ m xt hrest

/-- A finite joint germ supplies the time derivative of an arbitrary spatial
derivative word. Neighborhood equality is enough at each commutation step. -/
theorem hasDerivAt_iteratedPartialDeriv_timeSlice_of_contDiffAt
    (indices : List (Fin n)) (f : ℝ^n × ℝ → E) (x : ℝ^n) (t : ℝ)
    (hf : ContDiffAt ℝ (indices.length + 1 : ℕ) f (x, t)) :
    HasDerivAt (fun s ↦ iteratedPartialDeriv indices (fun y ↦ f (y, s)) x)
      (iteratedPartialDeriv indices (fun y ↦ deriv (fun s ↦ f (y, s)) t) x) t := by
  induction indices generalizing x with
  | nil =>
      exact ((hf.differentiableAt (by simp)).comp t (by fun_prop)).hasDerivAt
  | cons i rest ih =>
      have hrest : ContDiffAt ℝ 2
          (fun q : ℝ^n × ℝ ↦
            iteratedPartialDeriv rest (fun y ↦ f (y, q.2)) q.1) (x, t) :=
        contDiffAt_iteratedPartialDeriv_prod_spaceSlice rest f 2 (x, t)
          (by
            convert hf using 1
            simp only [List.length_cons]
            congr 1
            omega)
      have hder := hasDerivAt_partialDeriv_timeSlice_of_contDiffAt_two i _ x t hrest
      have hf' : ContDiffAt ℝ (rest.length + 1 : ℕ) f (x, t) :=
        hf.of_le (by simp only [List.length_cons]; exact_mod_cast
          (show rest.length + 1 ≤ rest.length + 1 + 1 by omega))
      have hnear := (continuousAt_id.prodMk continuousAt_const).eventually
        (hf'.eventually (by simp))
      have heq : (fun y ↦ deriv
          (fun s ↦ iteratedPartialDeriv rest (fun z ↦ f (z, s)) y) t) =ᶠ[𝓝 x]
          fun y ↦ iteratedPartialDeriv rest (fun z ↦ deriv (fun s ↦ f (z, s)) t) y :=
        hnear.mono fun y hy ↦ (ih y hy).deriv
      apply hder.congr_deriv
      exact congrArg (fun L : ℝ^n →L[ℝ] E ↦ L (EuclideanSpace.single i 1)) heq.fderiv_eq

/-- Differentiating an evolution equation in space only needs the equation on a
spatial neighborhood and one extra joint derivative beyond the derivative word. -/
theorem hasDerivAt_iteratedPartialDeriv_of_equation
    (indices : List (Fin n)) (f : ℝ^n × ℝ → E) (v : ℝ^n → E)
    (x : ℝ^n) (t : ℝ)
    (hf : ContDiffAt ℝ (indices.length + 1 : ℕ) f (x, t))
    (heq : ∀ᶠ y in 𝓝 x, HasDerivAt (fun s ↦ f (y, s)) (v y) t) :
    HasDerivAt (fun s ↦ iteratedPartialDeriv indices (fun y ↦ f (y, s)) x)
      (iteratedPartialDeriv indices v x) t := by
  apply (hasDerivAt_iteratedPartialDeriv_timeSlice_of_contDiffAt indices f x t hf)
    |>.congr_deriv
  have h : (fun y ↦ deriv (fun s ↦ f (y, s)) t) =ᶠ[𝓝 x] v :=
    heq.mono fun _ hy ↦ hy.deriv
  exact (h.iteratedPartialDeriv indices).eq_of_nhds

end PDE
