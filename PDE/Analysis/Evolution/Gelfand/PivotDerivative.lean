/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple

/-!
# Pivot representatives of dual derivatives

A derivative in `V*` can be represented in the pivot space `H` of a Gelfand
triple. The representation links the weak equation to differentiation of the
pivot-space energy.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.1, where the inner product `(u', v)` of equation (9)
  becomes the pairing `⟨u', v⟩` of `H⁻¹` with `H¹₀`. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A pivot-space vector represents a dual time derivative when its pivot
inner product against every included test vector equals the dual pairing. -/
def RepresentsPivotDerivative
    (T : GelfandTriple (V := V) (H := H))
    (du : StrongDual ℝ V) (duH : H) : Prop :=
  ∀ v : V, du v = inner ℝ duH (T.inclusion v)

namespace RepresentsPivotDerivative

variable {T : GelfandTriple (V := V) (H := H)}
variable {du du₁ du₂ : StrongDual ℝ V} {duH duH₁ duH₂ : H}

/-- The zero pivot vector represents the zero dual derivative. -/
@[simp]
theorem zero (T : GelfandTriple (V := V) (H := H)) :
    RepresentsPivotDerivative T 0 0 := by
  intro v
  simp

/-- Pivot derivative representations are closed under addition. -/
theorem add
    (h₁ : RepresentsPivotDerivative T du₁ duH₁)
    (h₂ : RepresentsPivotDerivative T du₂ duH₂) :
    RepresentsPivotDerivative T (du₁ + du₂) (duH₁ + duH₂) := by
  intro v
  simp [h₁ v, h₂ v, inner_add_left]

/-- Negating a pivot derivative representation negates both representatives. -/
theorem neg
    (h : RepresentsPivotDerivative T du duH) :
    RepresentsPivotDerivative T (-du) (-duH) := by
  intro v
  simp [h v]

/-- Subtracting pivot derivative representations subtracts both representatives. -/
theorem sub
    (h₁ : RepresentsPivotDerivative T du₁ duH₁)
    (h₂ : RepresentsPivotDerivative T du₂ duH₂) :
    RepresentsPivotDerivative T (du₁ - du₂) (duH₁ - duH₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

/-- Scaling a pivot derivative representation scales both representatives. -/
theorem smul (c : ℝ)
    (h : RepresentsPivotDerivative T du duH) :
    RepresentsPivotDerivative T (c • du) (c • duH) := by
  intro v
  calc
    (c • du) v = c * du v := by simp
    _ = c * inner ℝ duH (T.inclusion v) := by rw [h v]
    _ = inner ℝ (c • duH) (T.inclusion v) := by
      rw [real_inner_smul_left]

/-- Linear combinations of two pivot derivative representations. -/
theorem linear_combination (c₁ c₂ : ℝ)
    (h₁ : RepresentsPivotDerivative T du₁ duH₁)
    (h₂ : RepresentsPivotDerivative T du₂ duH₂) :
    RepresentsPivotDerivative T (c₁ • du₁ + c₂ • du₂)
      (c₁ • duH₁ + c₂ • duH₂) :=
  (h₁.smul c₁).add (h₂.smul c₂)

end RepresentsPivotDerivative

end PDE.Analysis.Evolution
