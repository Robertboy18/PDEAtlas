/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.Classical.OneDimensional.Dirichlet

/-!
# Regularity bootstrap for `-f'' - a² f = g`

A `C²` solution of `-f'' - a² f = g` on the line has two more derivatives than the forcing:
`f'' = -a² f - g`, so `g ∈ Cⁿ` gives `f ∈ C^(n+2)` by induction on `n`. In particular the
variation-of-constants inverse `dirichletSolution` of a `Cⁿ` forcing is `C^(n+2)`.

## Main results

* `contDiff_of_neg_deriv_deriv_sub_sq_mul`: a `C²` solution of `-f'' - a² f = g` with `g ∈ Cⁿ`
  is `C^(n+2)`.
* `contDiff_dirichletSolution_of_contDiff`: `dirichletSolution` of a `Cⁿ` forcing is `C^(n+2)`.
-/

@[expose] public section

namespace PDE.Elliptic.Classical.OneDimensional

/-- A `C²` solution of `-f'' - a² f = g` with `g ∈ Cⁿ` is `C^(n+2)`. -/
theorem contDiff_of_neg_deriv_deriv_sub_sq_mul {a : ℝ} {f g : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ n g)
    (heq : ∀ β, -deriv (deriv f) β - a ^ 2 * f β = g β) :
    ContDiff ℝ (n + 2 : ℕ) f := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have hfn : ContDiff ℝ (n + 2 : ℕ) f := ih (hg.of_le (by norm_cast; omega))
    have hsecond : deriv (deriv f) = fun β ↦ -(a ^ 2 * f β) - g β := by
      funext β
      linarith [heq β]
    have hdd : ContDiff ℝ (n + 1 : ℕ) (deriv (deriv f)) := by
      rw [hsecond]
      exact (contDiff_const.mul (hfn.of_le (by norm_cast; omega))).neg.sub hg
    have hd : ContDiff ℝ (n + 2 : ℕ) (deriv f) := by
      have h := contDiff_succ_iff_deriv.mpr
        ⟨hf.differentiable_deriv_two, by simp, hdd⟩
      exact_mod_cast h
    have h := contDiff_succ_iff_deriv.mpr ⟨hf.differentiable (by norm_num), by simp, hd⟩
    exact_mod_cast h

/-- The variation-of-constants inverse of a `Cⁿ` forcing is `C^(n+2)`. -/
theorem contDiff_dirichletSolution_of_contDiff {a : ℝ} (ha : a ≠ 0) (L : ℝ) {g : ℝ → ℝ}
    {n : ℕ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ (n + 2 : ℕ) (dirichletSolution a L g) :=
  contDiff_of_neg_deriv_deriv_sub_sq_mul (contDiff_dirichletSolution ha L hg.continuous) hg
    (dirichletSolution_equation ha L hg.continuous)

end PDE.Elliptic.Classical.OneDimensional
