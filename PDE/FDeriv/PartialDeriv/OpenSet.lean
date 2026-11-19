/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Regularity
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Coordinate derivatives on an open set

On an open set `U`, coordinate derivatives of functions that agree on `U` agree on `U`, the sum,
difference, constant multiple and product rules hold pointwise on `U` for functions differentiable
on `U`, and iterated coordinate derivatives of a `C^k` function on `U` along a word of length `j`
are `C^{k - j}` on `U`. These identities let one expand derivatives of nonlinear expressions in
fields that are smooth only on an open set, such as fields given on a half-space.

## Main results

* `eqOn_partialDeriv`: functions that agree on `U` have the same coordinate derivatives on `U`.
* `eqOn_partialDeriv_add`: `∂ᵢ (f + g) = ∂ᵢ f + ∂ᵢ g` on `U`.
* `eqOn_partialDeriv_mul`: `∂ᵢ (f g) = (∂ᵢ f) g + f ∂ᵢ g` on `U`.
* `eqOn_partialDeriv_partialDeriv_mul`:
  `∂ᵢ∂ₖ(f g) = (∂ᵢ∂ₖ f) g + ∂ₖ f ∂ᵢ g + ∂ᵢ f ∂ₖ g + f ∂ᵢ∂ₖ g` on `U`.
* `contDiffOn_iteratedPartialDeriv`: iterated coordinate derivatives along a word of length `j`
  of a function `C^{j + m}` on `U` are `C^m` there.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE

variable {n : ℕ} {U : Set (ℝ^n)} {f g F G : ℝ^n → ℝ}

/-- Functions that agree on an open set `U` have the same coordinate derivatives on `U`. -/
theorem eqOn_partialDeriv (hU : IsOpen U) (h : EqOn F G U) (i : Fin n) :
    EqOn (∂[i] F) (∂[i] G) U := fun _ hx ↦
  partialDeriv_eq_of_fderiv_eq ((eventuallyEq_of_mem (hU.mem_nhds hx) h).fderiv_eq (𝕜 := ℝ)) i

/-- The sum rule `∂ᵢ (f + g) = ∂ᵢ f + ∂ᵢ g` on an open set `U` where `f` and `g` are differentiable.
-/
theorem eqOn_partialDeriv_add (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hg : DifferentiableOn ℝ g U) (i : Fin n) :
    EqOn (∂[i] (fun x ↦ f x + g x)) (fun x ↦ (∂[i] f) x + (∂[i] g) x) U := fun x hx ↦
  partialDeriv_add ((hf x hx).differentiableAt (hU.mem_nhds hx))
    ((hg x hx).differentiableAt (hU.mem_nhds hx))

/-- The difference rule `∂ᵢ (f - g) = ∂ᵢ f - ∂ᵢ g` on an open set `U` where `f` and `g` are
differentiable. -/
theorem eqOn_partialDeriv_sub (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hg : DifferentiableOn ℝ g U) (i : Fin n) :
    EqOn (∂[i] (fun x ↦ f x - g x)) (fun x ↦ (∂[i] f) x - (∂[i] g) x) U := fun x hx ↦
  partialDeriv_sub ((hf x hx).differentiableAt (hU.mem_nhds hx))
    ((hg x hx).differentiableAt (hU.mem_nhds hx))

/-- The product rule `∂ᵢ (f g) = (∂ᵢ f) g + f ∂ᵢ g` on an open set `U` where `f` and `g` are
differentiable. -/
theorem eqOn_partialDeriv_mul (hU : IsOpen U) (hf : DifferentiableOn ℝ f U)
    (hg : DifferentiableOn ℝ g U) (i : Fin n) :
    EqOn (∂[i] (fun x ↦ f x * g x)) (fun x ↦ (∂[i] f) x * g x + f x * (∂[i] g) x) U :=
  fun x hx ↦ partialDeriv_mul ((hf x hx).differentiableAt (hU.mem_nhds hx))
    ((hg x hx).differentiableAt (hU.mem_nhds hx))

/-- `∂ᵢ (c f) = c ∂ᵢ f` as an equality of functions, with no differentiability hypothesis. -/
theorem partialDeriv_const_mul_fun (c : ℝ) (i : Fin n) :
    ∂[i] (fun x ↦ c * f x) = fun x ↦ c * (∂[i] f) x := by
  funext x
  simpa [smul_eq_mul] using partialDeriv_const_smul (i := i) (f := f) (x := x) c

/-- `∂ᵢ (-f) = -∂ᵢ f` as an equality of functions. -/
theorem partialDeriv_neg_fun (i : Fin n) :
    ∂[i] (fun x ↦ -f x) = fun x ↦ -(∂[i] f) x := by
  funext x
  exact partialDeriv_neg (f := f)

/-- `∂ᵢ (c f) = c ∂ᵢ f` on every set. -/
theorem eqOn_partialDeriv_const_mul (c : ℝ) (i : Fin n) :
    EqOn (∂[i] (fun x ↦ c * f x)) (fun x ↦ c * (∂[i] f) x) U := fun x _ ↦ by
  rw [partialDeriv_const_mul_fun]

/-- Second coordinate derivatives of a sum on an open set. -/
theorem eqOn_partialDeriv_partialDeriv_add (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) (i k : Fin n) :
    EqOn (∂[i] (∂[k] (fun x ↦ f x + g x)))
      (fun x ↦ (∂[i] (∂[k] f)) x + (∂[i] (∂[k] g)) x) U := by
  have h1 := eqOn_partialDeriv_add hU (hf.differentiableOn (by norm_num))
    (hg.differentiableOn (by norm_num)) k
  refine (eqOn_partialDeriv hU h1 i).trans ?_
  exact eqOn_partialDeriv_add hU ((hf.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn
    (by norm_num)) ((hg.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn (by norm_num)) i

/-- Second coordinate derivatives of a difference on an open set. -/
theorem eqOn_partialDeriv_partialDeriv_sub (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) (i k : Fin n) :
    EqOn (∂[i] (∂[k] (fun x ↦ f x - g x)))
      (fun x ↦ (∂[i] (∂[k] f)) x - (∂[i] (∂[k] g)) x) U := by
  have h1 := eqOn_partialDeriv_sub hU (hf.differentiableOn (by norm_num))
    (hg.differentiableOn (by norm_num)) k
  refine (eqOn_partialDeriv hU h1 i).trans ?_
  exact eqOn_partialDeriv_sub hU ((hf.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn
    (by norm_num)) ((hg.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn (by norm_num)) i

/-- Second coordinate derivatives of a constant multiple. -/
theorem partialDeriv_partialDeriv_const_mul (c : ℝ) (i k : Fin n) :
    ∂[i] (∂[k] (fun x ↦ c * f x)) = fun x ↦ c * (∂[i] (∂[k] f)) x := by
  rw [partialDeriv_const_mul_fun, partialDeriv_const_mul_fun]

/-- **Leibniz rule for two coordinate derivatives** on an open set:
`∂ᵢ∂ₖ(f g) = (∂ᵢ∂ₖ f) g + ∂ₖ f ∂ᵢ g + ∂ᵢ f ∂ₖ g + f ∂ᵢ∂ₖ g`. -/
theorem eqOn_partialDeriv_partialDeriv_mul (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hg : ContDiffOn ℝ 2 g U) (i k : Fin n) :
    EqOn (∂[i] (∂[k] (fun x ↦ f x * g x)))
      (fun x ↦ (∂[i] (∂[k] f)) x * g x + (∂[k] f) x * (∂[i] g) x +
        ((∂[i] f) x * (∂[k] g) x + f x * (∂[i] (∂[k] g)) x)) U := by
  have hf1 : DifferentiableOn ℝ f U := hf.differentiableOn (by norm_num)
  have hg1 : DifferentiableOn ℝ g U := hg.differentiableOn (by norm_num)
  have hfk : DifferentiableOn ℝ (∂[k] f) U :=
    (hf.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn (by norm_num)
  have hgk : DifferentiableOn ℝ (∂[k] g) U :=
    (hg.partialDeriv k hU (k := 1) (by norm_num)).differentiableOn (by norm_num)
  have h1 := eqOn_partialDeriv_mul hU hf1 hg1 k
  refine (eqOn_partialDeriv hU h1 i).trans ?_
  refine (eqOn_partialDeriv_add hU (hfk.mul hg1) (hf1.mul hgk) i).trans ?_
  intro x hx
  rw [show (∂[k] f * g) = fun x ↦ (∂[k] f) x * g x from rfl,
    show (f * ∂[k] g) = fun x ↦ f x * (∂[k] g) x from rfl]
  simp only
  rw [eqOn_partialDeriv_mul hU hfk hg1 i hx, eqOn_partialDeriv_mul hU hf1 hgk i hx]

/-- Iterated coordinate derivatives along a word of length `j` of a function `C^{j + m}` on an
open set are `C^m` there. -/
theorem contDiffOn_iteratedPartialDeriv (hU : IsOpen U) (indices : List (Fin n)) {m : ℕ}
    (hf : ContDiffOn ℝ ((indices.length + m : ℕ) : WithTop ℕ∞) f U) :
    ContDiffOn ℝ m (iteratedPartialDeriv indices f) U := by
  induction indices generalizing m with
  | nil => simpa [iteratedPartialDeriv] using hf
  | cons i rest ih =>
    have hf' : ContDiffOn ℝ ((rest.length + (m + 1) : ℕ) : WithTop ℕ∞) f U := by
      have : (i :: rest).length + m = rest.length + (m + 1) := by simp; omega
      rwa [this] at hf
    have := (ih hf').partialDeriv i hU (k := m) (by norm_cast)
    exact this

end PDE
