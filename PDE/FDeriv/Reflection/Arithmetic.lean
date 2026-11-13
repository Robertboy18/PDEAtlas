/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Reflection.Local

/-!
# Reflection parity of sums, products and constants

`PDE.Common.IsReflectionEigenfunctionOn U i ε f` (`f ∘ σᵢ = ε f` on `U`) is closed under the
pointwise operations: products multiply the parities, sums, differences, negatives and constant
multiples of functions of parity `ε` have parity `ε`, and constants are even.

## Main results

* `IsReflectionEigenfunctionOn.mul`: the parity of a product is the product of the parities.
* `IsReflectionEigenfunctionOn.add`: a sum of functions of the same parity has that parity.
* `IsReflectionEigenfunctionOn.const_mul`: a constant multiple keeps the parity.
* `IsReflectionEigenfunctionOn.const`: a constant is even.
-/

@[expose] public section

namespace PDE.Common.IsReflectionEigenfunctionOn

variable {n : ℕ} {i : Fin n} {ε ε' : ℝ} {U : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- The parity of a product is the product of the parities. -/
theorem mul (hf : IsReflectionEigenfunctionOn U i ε f) (hg : IsReflectionEigenfunctionOn U i ε' g) :
    IsReflectionEigenfunctionOn U i (ε * ε') (fun x ↦ f x * g x) := fun x hx ↦ by
  dsimp only
  rw [hf x hx, hg x hx]; ring

/-- A sum of functions of the same parity has that parity. -/
theorem add (hf : IsReflectionEigenfunctionOn U i ε f) (hg : IsReflectionEigenfunctionOn U i ε g) :
    IsReflectionEigenfunctionOn U i ε (fun x ↦ f x + g x) := fun x hx ↦ by
  dsimp only
  rw [hf x hx, hg x hx]; ring

/-- A difference of functions of the same parity has that parity. -/
theorem sub (hf : IsReflectionEigenfunctionOn U i ε f) (hg : IsReflectionEigenfunctionOn U i ε g) :
    IsReflectionEigenfunctionOn U i ε (fun x ↦ f x - g x) := fun x hx ↦ by
  dsimp only
  rw [hf x hx, hg x hx]; ring

/-- A constant multiple keeps the parity. -/
theorem const_mul (hf : IsReflectionEigenfunctionOn U i ε f) (a : ℝ) :
    IsReflectionEigenfunctionOn U i ε (fun x ↦ a * f x) := fun x hx ↦ by
  dsimp only
  rw [hf x hx]; ring

/-- The negative keeps the parity. -/
theorem neg (hf : IsReflectionEigenfunctionOn U i ε f) :
    IsReflectionEigenfunctionOn U i ε (fun x ↦ -f x) := fun x hx ↦ by
  dsimp only
  rw [hf x hx]; ring

/-- A constant is even. -/
theorem const (a : ℝ) : IsReflectionEigenfunctionOn U i 1 (fun _ ↦ a) :=
  fun _ _ ↦ by dsimp only; ring

/-- The parity transfers to a function equal everywhere. -/
theorem congr (hf : IsReflectionEigenfunctionOn U i ε f) (hfg : ∀ x, f x = g x) :
    IsReflectionEigenfunctionOn U i ε g := by
  obtain rfl : f = g := funext hfg
  exact hf

end PDE.Common.IsReflectionEigenfunctionOn
