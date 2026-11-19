/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Superlinear costs and their dual Hamiltonians

The growth assumption says that `L` lies above every multiple of the norm,
up to an additive constant. It supplies bounds for the real-valued
suprema and infima used below; totalized `sSup` and `sInf` alone do not.

The Hamiltonian is constructed from the Lagrangian. Neither function needs to be differentiable or
strictly convex. Identifying this construction with a separately prescribed Hamiltonian requires a
duality theorem.

The Hamiltonian is the Legendre transform (13)-(14) of Evans, §3.3.2(a), and its convexity is part
of Theorem 3(i) there. Evans states superlinearity as the limit (12); for continuous functions,
`PDE.Hyperbolic.HamiltonJacobi.HopfLax.Growth` shows that the two forms agree.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(a), (12)-(14) and Theorem 3(i).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

set_option linter.missingDocs true

section Growth

variable {E : Type*} [NormedAddCommGroup E]

/-- Uniform affine lower bounds with arbitrarily large norm coefficient. -/
def Superlinear (L : E → ℝ) : Prop :=
  ∀ A : ℝ, ∃ B : ℝ, ∀ q : E, A * ‖q‖ - B ≤ L q

end Growth

section Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The dual Hamiltonian `H(p) = sup_q (⟪p,q⟫ - L(q))`.
Finiteness is proved from `Superlinear L`. -/
def hamiltonian (L : E → ℝ) (p : E) : ℝ :=
  sSup (Set.range fun q : E ↦ inner ℝ p q - L q)

/-- Superlinear growth bounds every dual supremum from above. -/
theorem bddAbove_dual {L : E → ℝ} (hL : Superlinear L) (p : E) :
    BddAbove (Set.range fun q : E ↦ inner ℝ p q - L q) := by
  obtain ⟨B, hB⟩ := hL ‖p‖
  refine ⟨B, ?_⟩
  rintro _ ⟨q, rfl⟩
  linarith [hB q, real_inner_le_norm p q]

/-- Fenchel's inequality for the Hamiltonian constructed from `L`. -/
theorem le_hamiltonian {L : E → ℝ} (hL : Superlinear L) (p q : E) :
    inner ℝ p q - L q ≤ hamiltonian L p :=
  le_csSup (bddAbove_dual hL p) ⟨q, rfl⟩

/-- The dual Hamiltonian is convex, whether or not the original cost is. -/
theorem convexOn_hamiltonian {L : E → ℝ} (hL : Superlinear L) :
    ConvexOn ℝ Set.univ (hamiltonian L) := by
  refine ⟨convex_univ, fun p₁ _ p₂ _ a b ha hb hab ↦ ?_⟩
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨q, rfl⟩
  have h₁ := mul_le_mul_of_nonneg_left (le_hamiltonian hL p₁ q) ha
  have h₂ := mul_le_mul_of_nonneg_left (le_hamiltonian hL p₂ q) hb
  have hsum := congrArg (fun c : ℝ ↦ c * L q) hab
  simp only [add_mul, one_mul] at hsum
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  linarith

/-- In finite dimension the finite dual Hamiltonian is continuous.
This uses Mathlib's continuity theorem for convex functions on open sets. -/
theorem continuous_hamiltonian [FiniteDimensional ℝ E] {L : E → ℝ} (hL : Superlinear L) :
    Continuous (hamiltonian L) :=
  continuousOn_univ.mp ((convexOn_hamiltonian hL).continuousOn isOpen_univ)

end Dual

end HamiltonJacobi.HopfLax

end
