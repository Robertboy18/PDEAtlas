/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator
import CAS.ExactTactic

/-!
# Exponential rescaling of a strongly continuous semigroup

Multiplication by `exp(ωt)` shifts the generator by `ωI`, with exactly the same domain.
In particular, rescaling a contraction semigroup gives the exponential bound
`‖S(t)‖ ≤ e^{ωt}` of an `ω`-contractive semigroup, the case covered by the variant of the
Hille–Yosida theorem in the remark after Evans §7.4.2, Theorem 4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.4.2, the remark after Theorem 4, (23), p. 441.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exponential rescaling of an operator semigroup. -/
def expRescale (T : StronglyContinuousSemigroup E) (ω : ℝ) :
    StronglyContinuousSemigroup E where
  toMonoidHom :=
    { toFun := fun t ↦ Real.exp (ω * (t.toAdd : ℝ)) • T t.toAdd
      map_one' := by simp
      map_mul' := by
        intro s t
        change Real.exp (ω * ((s.toAdd + t.toAdd : NNReal) : ℝ)) • T (s.toAdd + t.toAdd) =
          (Real.exp (ω * (s.toAdd : ℝ)) • T s.toAdd) *
            (Real.exp (ω * (t.toAdd : ℝ)) • T t.toAdd)
        ext x
        simp only [NNReal.coe_add, mul_add, Real.exp_add, smul_apply,
          mul_apply_eq_comp, T.map_add_apply, map_smul, smul_smul, mul_comm] }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    intro x
    exact (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul
      (T.continuous_orbit x)

/-- Rescaling acts by the scalar exponential at each nonnegative time. -/
@[simp]
theorem expRescale_apply (T : StronglyContinuousSemigroup E) (ω : ℝ) (t : NNReal) :
    T.expRescale ω t = Real.exp (ω * (t : ℝ)) • T t :=
  rfl

/-- Successive exponential rescalings add their exponents. -/
theorem expRescale_expRescale (T : StronglyContinuousSemigroup E) (ω η : ℝ) :
    (T.expRescale ω).expRescale η = T.expRescale (η + ω) := by
  ext t x
  simp only [expRescale_apply, smul_apply, smul_smul,
    add_mul, Real.exp_add]

/-- Rescaling by zero leaves the semigroup unchanged. -/
@[simp]
theorem expRescale_zero (T : StronglyContinuousSemigroup E) :
    T.expRescale 0 = T := by
  ext t x
  simp

/-- Multiplication by the scalar exponential adds `ωx` to the generator value at `x`. -/
theorem HasGeneratorAt.expRescale {T : StronglyContinuousSemigroup E} {x y : E}
    (h : T.HasGeneratorAt x y) (ω : ℝ) :
    (T.expRescale ω).HasGeneratorAt x (y + ω • x) := by
  have he : HasDerivAt (fun t : ℝ ↦ Real.exp (ω * t)) ω 0 := by cas
  have hd := he.hasDerivWithinAt.fun_smul h
  have hd' : HasDerivWithinAt (fun t : ℝ ↦ Real.exp (ω * t) • T.realOrbit x t)
      (y + ω • x) (Set.Ici 0) 0 := by
    simpa [realOrbit, T.map_zero_apply] using hd
  apply hd'.congr_of_mem _ Set.self_mem_Ici
  intro t ht
  simp only [realOrbit, expRescale_apply, smul_apply,
    Real.coe_toNNReal t ht]

/-- The rescaled generator has exactly the original domain and the shifted value. -/
theorem hasGeneratorAt_expRescale_iff (T : StronglyContinuousSemigroup E) (ω : ℝ)
    (x y : E) :
    (T.expRescale ω).HasGeneratorAt x y ↔ T.HasGeneratorAt x (y - ω • x) := by
  constructor
  · intro h
    simpa [expRescale_expRescale, sub_eq_add_neg] using h.expRescale (-ω)
  · intro h
    simpa using h.expRescale ω

/-- Rescaling a contraction semigroup gives the corresponding exponential norm bound. -/
theorem IsContraction.norm_expRescale_le {T : StronglyContinuousSemigroup E}
    (hT : T.IsContraction) (ω : ℝ) (t : NNReal) :
    ‖T.expRescale ω t‖ ≤ Real.exp (ω * (t : ℝ)) := by
  rw [expRescale_apply, norm_smul, Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_of_le_one_right (Real.exp_nonneg _) (hT t)

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
