/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.ShiftedGeneration
public import PDE.Elliptic.Variational.Operator.Dirichlet

/-!
# Autonomous divergence-form parabolic semigroups

Uniform ellipticity and bounded coefficients give a Gårding inequality for the full Dirichlet form,
including drift and potential, with the explicit shift `coerciveShift` and no Poincaré inequality
(`garding_bound`). The shifted form construction then gives a strongly continuous semigroup on `L²`
with `‖S(t)‖ ≤ exp (γ t)` for `γ = coerciveShift` (`semigroup`, `norm_semigroup_le`). Its generator
is the negative weak Dirichlet operator, with equal domains (`generatorPMap_semigroup`). For a
bounded domain with `C²` graph boundary, `C¹` principal coefficients and continuous lower-order
coefficients, `PDE.Parabolic.Evolution.Semigroup.ClassicalDomain` identifies this domain with
`H² ∩ H¹₀`.

This is Evans's §7.4.3(a), Theorem 5, for bounded measurable coefficients on any open set, with the
weak domain in place of `H¹₀(U) ∩ H²(U)`, (25). Evans assumes smooth coefficients and a bounded open
set with smooth boundary, and his energy estimate (27), from §6.2.2, Theorem 2, uses Poincaré's
inequality.

## How it works

Evans verifies the hypotheses of the `ω`-contractive variant (23) of the Hille-Yosida theorem, with
`ω = γ` from the energy estimate (27). Our `garding_bound` is (27) with `β = α / 2` and
`γ = coerciveShift`, so the shifted form `B + γ (u, v)` is nonnegative and coercive
(`isCoercive_form_add_mass`). We apply the contraction form of the theorem to the shifted form and
multiply the resulting contraction semigroup by `exp (γ t)` (`shiftedFormSemigroup`). The rescaling
adds `γ` back to the generator, so the generator is the negative weak Dirichlet operator of the
unshifted form (`generatorPMap_semigroup`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.2, Theorem 2 (Energy estimates) and its proof,
  pp. 318-319; §7.4.2, Theorem 4 (Hille-Yosida Theorem), p. 439, and the remark after its proof,
  (23), p. 441; §7.4.3(a), (24)-(32) and Theorem 5 (Second-order parabolic PDE as semigroups) and
  its proof, pp. 441-443.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace HeatEquation.Semigroup.Divergence

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

variable (hopen : IsOpen Ω)
variable (a : Fin n → Fin n → DerivLp n ∞ Ω)
  (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)

/-- The lower-order terms are bounded by the coefficient norms `∑ i, ‖b i‖` and `‖c‖`. -/
theorem lowerOrderBounds_coefficients :
    LowerOrderBounds (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
      (∑ i, ‖b i‖) ‖c‖ := by
  apply lowerOrderBounds_multiplication b c
    (Finset.sum_nonneg fun i _ ↦ norm_nonneg (b i)) (norm_nonneg c)
    (fun i ↦ Finset.single_le_sum (fun j _ ↦ norm_nonneg (b j)) (Finset.mem_univ i)) le_rfl

/-- The explicit Gårding shift controls the full `H¹₀` norm with coefficient `α / 2`. -/
theorem garding_bound {α : ℝ} (ha : AEUniformlyElliptic a α) (u : H¹₀(Ω)) :
    α / 2 * ‖u‖ ^ 2 ≤
      fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) u u +
      coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖ * ‖baseCoordCLM u‖ ^ 2 := by
  simpa only [shiftedDivergenceForm_apply, real_inner_self_eq_norm_sq, pow_two, mul_assoc]
    using shiftedDivergenceForm_coercive_bound
      (multiplicationCoefficientOperator a) (multiplicationFirstOrderOperator b)
      (multiplicationZeroOrderOperator c) (integratedElliptic_multiplication_of_ae a ha)
      (lowerOrderBounds_coefficients b c) u

/-- The full Dirichlet form is coercive after the explicit Gårding shift. -/
theorem isCoercive_form_add_mass {α : ℝ} (ha : AEUniformlyElliptic a α) :
    IsCoercive
      (fullDivergenceForm (multiplicationCoefficientOperator a)
        (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) +
        coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖ •
          (h10L2GelfandTriple hopen).energyToDual) := by
  have hform :
      shiftedDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c)
          (coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖) =
        fullDivergenceForm (multiplicationCoefficientOperator a)
          (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) +
          coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖ •
            (h10L2GelfandTriple hopen).energyToDual := by
    ext u v
    simp only [shiftedDivergenceForm_apply, add_apply, smul_apply,
      GelfandTriple.energyToDual_apply, h10L2GelfandTriple_inclusion_apply, smul_eq_mul]
  rw [← hform]
  exact shiftedDivergenceForm_isCoercive _ _ _
    (integratedElliptic_multiplication_of_ae a ha) (lowerOrderBounds_coefficients b c)

/-- The Gårding exponent used for the full form is nonnegative. -/
theorem coerciveShift_nonneg {α : ℝ} (hα : 0 < α) :
    0 ≤ coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖ := by
  unfold coerciveShift gardingMass
  positivity

variable {α : ℝ} (ha : AEUniformlyElliptic a α)

/-- The autonomous Dirichlet semigroup: the contraction semigroup of the Gårding-shifted form,
multiplied by `exp (ω t)` for the shift `ω = coerciveShift α (∑ i, ‖b i‖) ‖c‖`. -/
def semigroup : StronglyContinuousSemigroup L2 :=
  (h10L2GelfandTriple hopen).shiftedFormSemigroup
    (fullDivergenceForm (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c))
    (coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖)
    (isCoercive_form_add_mass hopen a b c ha)

/-- The constructed parabolic semigroup has the explicit Gårding exponential bound. -/
theorem norm_semigroup_le (t : NNReal) :
    ‖semigroup hopen a b c ha t‖ ≤
      Real.exp (coerciveShift (n := n) α (∑ i, ‖b i‖) ‖c‖ * (t : ℝ)) :=
  (h10L2GelfandTriple hopen).norm_shiftedFormSemigroup_le _ _ _ t

/-- The generator of the semigroup is the negative weak Dirichlet operator, with equal
domains. -/
theorem generatorPMap_semigroup :
    (semigroup hopen a b c ha).generatorPMap = negativeDirichletOperator hopen a b c :=
  (h10L2GelfandTriple hopen).generatorPMap_shiftedFormSemigroup _ _ _

/-- The semigroup has generator value `f` at `x` exactly when `x` is the class of some
`u ∈ H¹₀` solving the weak full divergence-form equation with right side `-f`. -/
theorem hasGeneratorAt_semigroup_iff (x f : L2) :
    (semigroup hopen a b c ha).HasGeneratorAt x f ↔
      ∃ u : H¹₀(Ω), baseCoordCLM u = x ∧
        IsWeakShiftedFullDivergenceSolution a b c 0 (-f) 0 u := by
  rw [StronglyContinuousSemigroup.hasGeneratorAt_iff_mem_generatorPMap_graph,
    generatorPMap_semigroup, mem_negativeDirichletOperator_graph_iff]

end HeatEquation.Semigroup.Divergence
