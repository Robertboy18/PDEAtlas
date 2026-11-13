/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.CoefficientCommutator

/-!
# Boundary regularity: signed tangential tests

Evans proves boundary `H²` regularity on a half-ball, testing the weak
equation with `v = -Dₖ⁻ʰ(ζ² Dₖʰ u)` for a cutoff `ζ` and a tangential direction
`k ≠ n` (§6.3.2, proof of Theorem 4, step 3). We work on the whole flattened
half-space `Ω⁺` and drop the cutoff: because tangential translation preserves
the half-space, `v = -Dₖ⁻ʰ(Dₖʰ u)` lies in `H¹₀(Ω⁺)` whenever `u` does, with no
support collar. We define the test, compute its Sobolev coordinates, bound its
base coordinate by the tangential quotient energy of the gradient, and evaluate
the variational equation on it.

## Main results

* `signedBackwardTangentialTestH10`: the test `-Dₖ⁻ʰ(Dₖʰ u)` as an element of
  `H¹₀(Ω⁺)`.
* `signedBackwardTangentialTestH10_coordinate`,
  `derivCoord_signedBackwardTangentialTestH10`,
  `baseCoord_signedBackwardTangentialTestH10`: its coordinates are the
  corresponding signed backward `L²` quotients.
* `norm_baseCoord_signedBackwardTangentialTestH10_sq_le`: the base coordinate
  satisfies `‖v₀‖² ≤ ‖u‖²_{H¹₀} + ∑ᵢ ‖Dₖʰ ∂ᵢ u‖²`, uniformly in `h ≠ 0`.
* `abs_source_pairing_signedBackwardTangentialTestH10_le_young`: the forcing
  term `|⟪f, v₀⟫|` after Young's inequality with a free parameter `gamma`,
  with no inverse power of `h`.
* `weakDivergence_multiplication_signedBackwardTangential`: the flattened
  weak equation evaluated on this test, written coordinatewise.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 3 of the proof of Theorem 4, p. 335.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Evans' admissible signed backward tangential test
`-D_k^{-h}(D_k^h u)` on the flattened half-space. -/
noncomputable def signedBackwardTangentialTestH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    H¹₀(HalfSpace.upper n) :=
  -tangentialDifferenceQuotientH10 k hk (-h)
    (tangentialDifferenceQuotientH10 k hk h u)

/-- Coordinate formula for Evans' signed backward test.  This is exactly
the test factor appearing in `tangentialPrincipal_energyBalance`. -/
theorem signedBackwardTangentialTestH10_coordinate
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n))
    (q : DerivIndex n 1) :
    ((((signedBackwardTangentialTestH10 k hk h u :
        H¹₀(HalfSpace.upper n)) :
        H¹(HalfSpace.upper n)) :
      WkpAmbientOn n 1 2 (HalfSpace.upper n)) q) =
      -tangentialDifferenceQuotientLp 2 k hk (-h)
        (tangentialDifferenceQuotientLp 2 k hk h
          ((((u : H¹(HalfSpace.upper n)) :
            WkpAmbientOn n 1 2 (HalfSpace.upper n)) q))) := by
  change -((((tangentialDifferenceQuotientH10 k hk (-h)
      (tangentialDifferenceQuotientH10 k hk h u) :
        H¹₀(HalfSpace.upper n)) :
      H¹(HalfSpace.upper n)) :
        WkpAmbientOn n 1 2 (HalfSpace.upper n)) q) = _
  rw [tangentialDifferenceQuotientH10_coordinate,
    tangentialDifferenceQuotientH10_coordinate]

/-- Derivative coordinate of the admissible signed tangential test. -/
theorem derivCoord_signedBackwardTangentialTestH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n))
    (i : Fin n) :
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i
        (signedBackwardTangentialTestH10 k hk h u) =
      -tangentialDifferenceQuotientLp 2 k hk (-h)
        (tangentialDifferenceQuotientLp 2 k hk h
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)) := by
  simpa only [derivCoordCLM_apply] using
      signedBackwardTangentialTestH10_coordinate k hk h u
        (singleDerivIndex n i)

/-- Base coordinate of the admissible signed tangential test. -/
theorem baseCoord_signedBackwardTangentialTestH10
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    (h : ℝ)
    (u : H¹₀(HalfSpace.upper n)) :
    baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
        (signedBackwardTangentialTestH10 k hk h u) =
      -tangentialDifferenceQuotientLp 2 k hk (-h)
        (tangentialDifferenceQuotientLp 2 k hk h
          (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u)) := by
  simpa only [baseCoordCLM_apply] using
      signedBackwardTangentialTestH10_coordinate k hk h u
        (baseIndex n 1)

/-- The base coordinate of Evans' signed test is controlled by the original
`H¹` norm and the tangential quotient energy of the gradient.  The bound is
uniform in the nonzero step size. -/
theorem norm_baseCoord_signedBackwardTangentialTestH10_sq_le
    [Fact (0 < n)] (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n)) :
    ‖baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
      (signedBackwardTangentialTestH10 k hk h u)‖ ^ 2 ≤
      ‖u‖ ^ 2 +
        ∑ i : Fin n,
          ‖tangentialDifferenceQuotientLp 2 k hk h
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2 := by
  let w := tangentialDifferenceQuotientH10 k hk h u
  have hback := norm_baseCoord_tangentialDifferenceQuotientH10_le
    k hk (neg_ne_zero.mpr hh) w
  have hbackSq :
      ‖baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
        (tangentialDifferenceQuotientH10 k hk (-h) w)‖ ^ 2 ≤ ‖w‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hback 2
  have hforward := norm_baseCoord_tangentialDifferenceQuotientH10_le
    k hk hh u
  have hforwardSq :
      ‖tangentialDifferenceQuotientLp 2 k hk h
        (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    have hforward' :
        ‖tangentialDifferenceQuotientLp 2 k hk h
          (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u)‖ ≤ ‖u‖ := by
      rw [baseCoord_tangentialDifferenceQuotientH10] at hforward
      exact hforward
    exact pow_le_pow_left₀ (norm_nonneg _) hforward' 2
  rw [baseCoord_signedBackwardTangentialTestH10, norm_neg]
  calc
    ‖tangentialDifferenceQuotientLp 2 k hk (-h)
        (tangentialDifferenceQuotientLp 2 k hk h
          (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u))‖ ^ 2 ≤
        ‖w‖ ^ 2 := by
      rw [baseCoord_tangentialDifferenceQuotientH10] at hbackSq
      have hwbase := baseCoord_tangentialDifferenceQuotientH10 k hk h u
      change baseCoordCLM (n := n) (Ω := HalfSpace.upper n) w = _ at hwbase
      rw [hwbase] at hbackSq
      exact hbackSq
    _ = ‖tangentialDifferenceQuotientLp 2 k hk h
          (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u)‖ ^ 2 +
        ∑ i : Fin n,
          ‖tangentialDifferenceQuotientLp 2 k hk h
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2 :=
      norm_tangentialDifferenceQuotientH10_sq k hk h u
    _ ≤ _ := add_le_add hforwardSq le_rfl

/-- Young-absorbed forcing estimate for Evans' signed boundary test.  The
only quotient energy retained on the right is the tangential quotient of
the gradient, with no inverse power of the step size. -/
theorem abs_source_pairing_signedBackwardTangentialTestH10_le_young
    [Fact (0 < n)]
    (f : DerivLp n 2 (HalfSpace.upper n))
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0)
    (u : H¹₀(HalfSpace.upper n))
    {gamma : ℝ} (hgamma : 0 < gamma) :
    |inner ℝ f
      (baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
        (signedBackwardTangentialTestH10 k hk h u))| ≤
      ‖f‖ ^ 2 / gamma + (gamma / 4) *
        (‖u‖ ^ 2 +
          ∑ i : Fin n,
            ‖tangentialDifferenceQuotientLp 2 k hk h
              (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2) := by
  let testBase := baseCoordCLM (n := n) (Ω := HalfSpace.upper n)
    (signedBackwardTangentialTestH10 k hk h u)
  have hbaseSq :=
    norm_baseCoord_signedBackwardTangentialTestH10_sq_le k hk hh u
  calc
    |inner ℝ f testBase| ≤ ‖f‖ * ‖testBase‖ :=
      abs_real_inner_le_norm f testBase
    _ ≤ ‖f‖ ^ 2 / gamma + (gamma / 4) * ‖testBase‖ ^ 2 :=
      DifferenceQuotient.mul_le_sq_div_add_quarter hgamma ‖f‖ ‖testBase‖
    _ ≤ ‖f‖ ^ 2 / gamma + (gamma / 4) *
        (‖u‖ ^ 2 +
          ∑ i : Fin n,
            ‖tangentialDifferenceQuotientLp 2 k hk h
              (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2) := by
      have hbaseSq' : ‖testBase‖ ^ 2 ≤
          ‖u‖ ^ 2 +
            ∑ i : Fin n,
              ‖tangentialDifferenceQuotientLp 2 k hk h
                (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)‖ ^ 2 := by
        simpa [testBase] using hbaseSq
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbaseSq'
          (div_nonneg hgamma.le (by norm_num : (0 : ℝ) ≤ 4)))

/-- The flattened weak equation tested by Evans' admissible signed
tangential quotient.  This theorem joins the variational formulation to the
coordinatewise energy identity without any extra test-function hypothesis. -/
theorem weakDivergence_multiplication_signedBackwardTangential
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      inner ℝ
        (A i j • derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u)
        (-tangentialDifferenceQuotientLp 2 k hk (-h)
          (tangentialDifferenceQuotientLp 2 k hk h
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u)))) =
      inner ℝ f
        (-tangentialDifferenceQuotientLp 2 k hk (-h)
          (tangentialDifferenceQuotientLp 2 k hk h
            (baseCoordCLM (n := n) (Ω := HalfSpace.upper n) u))) := by
  let v := signedBackwardTangentialTestH10 k hk h u
  have hweak := hu v
  have hform := variableCoeffForm_apply
    (n := n) (Ω := HalfSpace.upper n)
    (multiplicationCoefficientOperator
      (n := n) (Ω := HalfSpace.upper n) A) u v
  have hload := loadFunctional_apply
    (n := n) (Ω := HalfSpace.upper n) f v
  dsimp only [v] at hform hload hweak
  simp only [multiplicationCoefficientOperator_apply] at hform
  simp_rw [derivCoord_signedBackwardTangentialTestH10] at hform
  rw [baseCoord_signedBackwardTangentialTestH10] at hload
  calc
    _ = variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A) u
        (signedBackwardTangentialTestH10 k hk h u) := hform.symm
    _ = loadFunctional (n := n) (Ω := HalfSpace.upper n) f
        (signedBackwardTangentialTestH10 k hk h u) := hweak
    _ = _ := hload

end GraphSpace.BoundaryRegularity
end SobolevSpace
