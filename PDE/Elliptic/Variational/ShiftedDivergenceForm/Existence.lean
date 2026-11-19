/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.LaxMilgram
public import PDE.Elliptic.Variational.LowerOrderForm

/-!
# Unique weak solvability of shifted divergence-form problems

Let `B` be the full divergence-form bilinear form on `H¹₀(Ω)` with lower-order terms,

`B(u,v) = ∑ᵢⱼ ⟪Aᵢⱼ ∂ⱼu, ∂ᵢv⟫ + ∑ᵢ ⟪bᵢ ∂ᵢu, v⟫ + ⟪c u, v⟫`.

The Gårding inequality of `PDE.Elliptic.Variational.LowerOrderForm` shows that
`B_μ(u,v) = B(u,v) + μ ⟪u, v⟫_{L²}` is coercive once `μ` is at least the explicit threshold
`coerciveShift alpha beta gamma`. Lax–Milgram then gives a unique weak solution of
`B_μ(u, ·) = F` for every load in the `H⁻¹` representation
`F(v) = ⟪f₀, v⟫ + ∑ᵢ ⟪fᵢ, ∂ᵢv⟫`. This is Evans's First Existence Theorem for weak solutions
(§6.2.2, Theorem 3) with an explicit shift, for the right-hand sides `f₀ - ∑ᵢ ∂ᵢfᵢ` that he
treats right after it.

## Main results

* `existsUnique_shiftedDivergence_weakSolution`: unique solvability at the threshold.
* `existsUnique_shifted_weakSolution_of_coerciveShift_le`: unique solvability for every
  shift above the threshold.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 2 (Energy estimates) and Theorem 3
  (First Existence Theorem for weak solutions), pp. 318-319, and the right-hand sides
  `f₀ - ∑ᵢ ∂ᵢfᵢ` of (9), p. 320.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set Function ENNReal
open PDE.Analysis.Variational
open scoped Topology NNReal InnerProductSpace

namespace GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

/-- If `A` is uniformly elliptic with constant `alpha` and `b`, `c` satisfy the lower-order
bounds `beta`, `gamma`, then at the shift `coerciveShift alpha beta gamma` the problem
`B_μ(u, ·) = F` has a unique weak solution in `H¹₀(Ω)` for the load
`F(v) = ⟪f₀, v⟫ + ∑ᵢ ⟪fᵢ, ∂ᵢv⟫`. -/
theorem existsUnique_shiftedDivergence_weakSolution
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω))) (c : L2 →L[ℝ] L2)
    {alpha beta gamma : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakSolution
        (shiftedDivergenceForm (n := n) (Ω := Ω) A b c
          (coerciveShift (n := n) alpha beta gamma))
        (generalizedLoad (n := n) (Ω := Ω) f0 f) u := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c
      (coerciveShift (n := n) alpha beta gamma)
  have hB : IsCoercive B :=
    shiftedDivergenceForm_isCoercive (n := n) (Ω := Ω) A b c hA hbc
  change ∃! u : H¹₀(Ω),
    IsWeakSolution B (generalizedLoad (n := n) (Ω := Ω) f0 f) u
  exact IsWeakSolution.existsUnique (V := H¹₀(Ω)) B hB
    (generalizedLoad (n := n) (Ω := Ω) f0 f)

/-- Evans §6.2.2, Theorem 3 for every shift above the explicit coercive
threshold. The theorem above takes the threshold itself; this
theorem exposes the full parameter range `coerciveShift ≤ mu`. -/
theorem existsUnique_shifted_weakSolution_of_coerciveShift_le
    (A : (Fin n → Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (b : (Fin n → (DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω)))
    (c : L2 →L[ℝ] L2)
    {alpha beta gamma mu : ℝ}
    (hA : IntegratedElliptic (n := n) (Ω := Ω) A alpha)
    (hbc : LowerOrderBounds (n := n) (Ω := Ω) b c beta gamma)
    (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)
    (f0 : L2) (f : Fin n → L2) :
    ∃! u : H¹₀(Ω),
      IsWeakSolution
        (shiftedDivergenceForm (n := n) (Ω := Ω) A b c mu)
        (generalizedLoad (n := n) (Ω := Ω) f0 f) u := by
  let B : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    shiftedDivergenceForm (n := n) (Ω := Ω) A b c mu
  have hB : IsCoercive B := by
    dsimp only [B]
    exact shiftedDivergenceForm_isCoercive_of_coerciveShift_le
      (n := n) (Ω := Ω) A b c hA hbc hmu
  change ∃! u : H¹₀(Ω),
    IsWeakSolution B
      (generalizedLoad (n := n) (Ω := Ω) f0 f) u
  exact IsWeakSolution.existsUnique (V := H¹₀(Ω)) B hB
    (generalizedLoad (n := n) (Ω := Ω) f0 f)

end GraphSpace

end SobolevSpace
