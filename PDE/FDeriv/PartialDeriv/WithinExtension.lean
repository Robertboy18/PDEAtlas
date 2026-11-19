/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.HalfSpaceLimit
public import PDE.FDeriv.PartialDeriv.OpenSet

/-!
# Derivatives within a set from a local extension

Let a scalar function `f` agree on `s ∩ V` with a function `h` that is `Cᵏ` on the open set
`V`, where `s` has unique derivatives. Then every iterated partial derivative of `f` within `s`
along a word of length at most `k` agrees on `s ∩ V` with the ordinary iterated partial
derivative of `h`. At a boundary point of `s` this identifies the derivatives up to the boundary
with those of any local `Cᵏ` extension; the agreement holds on the relative neighbourhood `s ∩ V`
at every order, not only at the point.

On `V` the ordinary iterated partial derivatives of a `Cᵏ` function along words of length at most
`k` depend only on the letters of the word; in the plane every word is a permutation of
`replicate a 0 ++ replicate b 1`.

## Main results

* `eqOn_iteratedPartialDerivWithin_of_eqOn`: if `f = h` on `s ∩ V` and `h` is `C^{|w|}` on `V`,
  the iterated partial derivatives of `f` within `s` along `w` are those of `h` on `s ∩ V`.
* `eqOn_iteratedPartialDerivWithin_of_contDiffAt`: where `h` is `Cᵏ`, its iterated partial
  derivatives within `s` along words of length at most `k` are the ordinary ones.
* `eqOn_iteratedPartialDeriv_of_perm`: on an open set where `h` is `C^{|w|}`, the iterated
  partial derivatives along two permutations of a word agree.
* `perm_replicate_count_two`: in the plane every word is a permutation of
  `replicate a 0 ++ replicate b 1`.
* `iteratedPartialDerivWithin_append`: concatenated words of derivatives within `s` compose.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {f h : ℝ^n → ℝ} {s V : Set (ℝ^n)}

/-- **Derivatives within `s` from a local extension.** If `f = h` on `s ∩ V`, `V` open, `s` has
unique derivatives and `h` is `C^{|w|}` on `V`, the iterated partial derivatives of `f` within `s`
along `w` are those of `h` on `s ∩ V`. -/
theorem eqOn_iteratedPartialDerivWithin_of_eqOn (hV : IsOpen V) (hs : UniqueDiffOn ℝ s)
    (indices : List (Fin n)) (hh : ContDiffOn ℝ indices.length h V) (heq : EqOn f h (s ∩ V)) :
    EqOn (iteratedPartialDerivWithin indices f s) (iteratedPartialDeriv indices h) (s ∩ V) := by
  induction indices with
  | nil => exact heq
  | cons i rest ih =>
    have hh' : ContDiffOn ℝ ((rest.length + 1 : ℕ) : WithTop ℕ∞) h V := by
      simpa using hh
    have hrest := ih (hh'.of_le (by norm_cast; omega))
    have hreg := contDiffOn_iteratedPartialDeriv hV rest hh'
    intro x hx
    have hev : iteratedPartialDerivWithin rest f s =ᶠ[𝓝[s] x] iteratedPartialDeriv rest h :=
      eventuallyEq_of_mem (inter_mem_nhdsWithin s (hV.mem_nhds hx.2)) hrest
    have hdiff : DifferentiableAt ℝ (iteratedPartialDeriv rest h) x :=
      ((hreg.differentiableOn one_ne_zero) x hx.2).differentiableAt (hV.mem_nhds hx.2)
    rw [iteratedPartialDerivWithin_cons, partialDerivWithin, hev.fderivWithin_eq (hrest hx),
      fderivWithin_eq_fderiv (hs x hx.1) hdiff]
    rfl

/-- The points where a function is `Cⁿ`, `n` finite, form an open set. -/
theorem isOpen_setOf_contDiffAt (k : ℕ) : IsOpen {x : ℝ^n | ContDiffAt ℝ k h x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  exact (show ContDiffAt ℝ k h x from hx).eventually (by simp)

/-- A function is `Cⁿ` on the open set of the points where it is `Cⁿ`. -/
theorem contDiffOn_setOf_contDiffAt (k : ℕ) : ContDiffOn ℝ k h {x : ℝ^n | ContDiffAt ℝ k h x} :=
  fun _ hx ↦ (show ContDiffAt ℝ k h _ from hx).contDiffWithinAt

/-- **Derivatives within `s` of a function `Cᵏ` near the points of `s`.** Where `h` is `Cᵏ` (as
a function on the whole space), its iterated partial derivatives within `s` along words of length
at most `k` are the ordinary ones, at interior and at boundary points of `s`. -/
theorem eqOn_iteratedPartialDerivWithin_of_contDiffAt (hs : UniqueDiffOn ℝ s)
    (indices : List (Fin n)) {k : ℕ} (hk : indices.length ≤ k) :
    EqOn (iteratedPartialDerivWithin indices h s) (iteratedPartialDeriv indices h)
      (s ∩ {x : ℝ^n | ContDiffAt ℝ k h x}) :=
  eqOn_iteratedPartialDerivWithin_of_eqOn (isOpen_setOf_contDiffAt k) hs indices
    ((contDiffOn_setOf_contDiffAt k).of_le (by exact_mod_cast hk)) (fun _ _ ↦ rfl)

/-- Two coordinate derivatives of a `C²` function commute on an open set. -/
theorem eqOn_partialDeriv_partialDeriv_comm (hV : IsOpen V) (i j : Fin n)
    (hh : ContDiffOn ℝ 2 h V) :
    EqOn (partialDeriv i (fun y ↦ partialDeriv j h y))
      (partialDeriv j (fun y ↦ partialDeriv i h y)) V := fun _ hx ↦
  partialDeriv_partialDeriv_comm_at i j (hh.contDiffAt (hV.mem_nhds hx))

/-- **Words with the same letters agree.** On an open set where `h` is `C^{|w|}`, the iterated
partial derivatives along two permutations of a word agree. -/
theorem eqOn_iteratedPartialDeriv_of_perm (hV : IsOpen V) {w w' : List (Fin n)} (hp : w.Perm w')
    (hh : ContDiffOn ℝ w.length h V) :
    EqOn (iteratedPartialDeriv w h) (iteratedPartialDeriv w' h) V := by
  induction hp with
  | nil => exact fun _ _ ↦ rfl
  | cons i p ih =>
    rename_i l₁ l₂
    have hh' : ContDiffOn ℝ l₁.length h V := hh.of_le (by norm_cast; simp)
    have heq := ih hh'
    intro x hx
    have hev : iteratedPartialDeriv l₁ h =ᶠ[𝓝 x] iteratedPartialDeriv l₂ h :=
      eventuallyEq_of_mem (hV.mem_nhds hx) heq
    exact partialDeriv_eq_of_fderiv_eq (hev.fderiv_eq (𝕜 := ℝ)) i
  | swap i j l =>
    have hh' : ContDiffOn ℝ ((l.length + 2 : ℕ) : WithTop ℕ∞) h V :=
      hh.of_le (by simp only [List.length_cons]; norm_cast)
    have hreg := contDiffOn_iteratedPartialDeriv hV l hh'
    intro x hx
    exact eqOn_partialDeriv_partialDeriv_comm hV j i hreg hx
  | trans p₁ p₂ ih₁ ih₂ =>
    exact (ih₁ hh).trans (ih₂ (by rwa [← p₁.length_eq]))

/-- In the plane every word is a permutation of `replicate a 0 ++ replicate b 1`, with `a` and `b`
the numbers of its letters `0` and `1`. -/
theorem perm_replicate_count_two (w : List (Fin 2)) :
    w.Perm (List.replicate (w.count 0) 0 ++ List.replicate (w.count 1) 1) := by
  rw [List.perm_iff_count]
  intro a
  fin_cases a <;> simp [List.count_replicate]

/-- Concatenated words of derivatives within `s` compose. -/
theorem iteratedPartialDerivWithin_append (left right : List (Fin n)) (f : ℝ^n → ℝ)
    (s : Set (ℝ^n)) :
    iteratedPartialDerivWithin (left ++ right) f s =
      iteratedPartialDerivWithin left (iteratedPartialDerivWithin right f s) s := by
  induction left with
  | nil => rfl
  | cons i rest ih => simp only [List.cons_append, iteratedPartialDerivWithin_cons, ih]

/-- Words of derivatives within `s` of functions that agree on `s` agree on `s`. -/
theorem eqOn_iteratedPartialDerivWithin_congr (indices : List (Fin n)) {g : ℝ^n → ℝ}
    (hfg : EqOn f g s) :
    EqOn (iteratedPartialDerivWithin indices f s) (iteratedPartialDerivWithin indices g s) s := by
  induction indices with
  | nil => exact hfg
  | cons i rest ih => exact partialDerivWithin_eqOn i ih

/-- Words of derivatives within a set with unique derivatives commute with negation. -/
theorem iteratedPartialDerivWithin_neg (hs : UniqueDiffOn ℝ s) (indices : List (Fin n)) :
    EqOn (iteratedPartialDerivWithin indices (fun y ↦ -f y) s)
      (fun y ↦ -iteratedPartialDerivWithin indices f s y) s := by
  induction indices with
  | nil => exact fun _ _ ↦ rfl
  | cons i rest ih =>
    intro x hx
    rw [iteratedPartialDerivWithin_cons, partialDerivWithin_congr i ih hx]
    simp only [partialDerivWithin, fderivWithin_fun_neg (hs x hx),
      neg_apply, iteratedPartialDerivWithin_cons]

/-- A word in the plane has `w.count 0 + w.count 1 = w.length` letters. -/
theorem count_zero_add_count_one (w : List (Fin 2)) : w.count 0 + w.count 1 = w.length := by
  simpa using (perm_replicate_count_two w).length_eq.symm

end PDE
