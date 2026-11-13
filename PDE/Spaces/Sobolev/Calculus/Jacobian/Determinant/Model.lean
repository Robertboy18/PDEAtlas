/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Jacobian.Minors.Model

/-!
# The Sobolev Jacobian determinant

The determinant is taken after unflattening the vector weak gradient.
Its Lebesgue exponent is divided by the dimension. The full determinant is the
minor selecting every spatial direction. No construction assumes that the weak
Jacobian is invertible.

For `u ∈ W^{1,p}(Ω; ℝⁿ)` the class `wkpJacobianDetLp u` is `det Du ∈ L^{p/n}(Ω)`. Evans works with
`det Du` in `L^{q/n}(U)` in the lemma on weak continuity of determinants (§8.2.4(b)), using the
pointwise bound `|det Du| ≤ C |Du|ⁿ`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), Lemma (Weak continuity of determinants), p. 476,
  and step 4 of its proof, p. 478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The Jacobian determinant `det Du` of `u : Fin n → W^{1,p}(Ω)`, as an element of
`L^{p/n}(Ω)`: the minor `wkpJacobianMinorLp id u` selecting every direction. -/
def wkpJacobianDetLp (u : Fin n → W^{1,p}(Ω)) :
    Lp ℝ (p / ENNReal.ofReal (n : ℝ)) (domainMeasure n Ω) :=
  wkpJacobianMinorLp id u

/-- Almost everywhere, `wkpJacobianDetLp u` is the determinant of the matrix of weak partial
derivatives `∂_j u_i`, the derivative coordinates of the graphs of the `u i`. -/
theorem coeFn_wkpJacobianDetLp (u : Fin n → W^{1,p}(Ω)) :
    wkpJacobianDetLp u =ᵐ[domainMeasure n Ω] fun x ↦
      Matrix.det (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex n j) (u i) x) := by
  exact coeFn_wkpJacobianMinorLp id u

end SobolevSpace.GraphSpace
