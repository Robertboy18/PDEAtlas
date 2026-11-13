/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.NormalFlux
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Recovery of the normal-normal derivative

Subtracting the differentiated tangential cross-flux from the normal flux gives the normal
derivative of `Aₙₙ ∂ₙu` (`normalCoefficientNormalGradient.exists_normalDerivative_with_norm`).
Uniform ellipticity then supplies a positive reciprocal for `Aₙₙ`, which recovers the missing
normal-normal weak derivative with its quantitative bound
(`normalNormalWeakDerivative.exists_with_norm`). These are the divergence-form counterparts of
Evans's (53) and (55) in step 5 of the proof of §6.3.2, Theorem 4, where `aⁿⁿ ≥ θ > 0`, (54), allows
the division.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 4, (52)-(55),
  pp. 336-337.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- Bound for the normal derivative of `aₙₙ Dₙu`, obtained by subtracting
the differentiated cross-flux from the differentiated normal flux. -/
noncomputable def normalCoefficientNormalGradient.derivativeBound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) (alpha : ℝ) : ℝ :=
  normalFlux.derivativeBound A C f u alpha +
    tangentialFluxSum.normalDerivativeBound A a C haLip haRep f u alpha
      (PDE.Common.lastIndex (n := n))

/-- The normal-normal coefficient times the normal gradient component has an
`L²` normal weak derivative.  This is obtained by subtracting the
tangential cross-flux from the normal flux, the divergence-form counterpart of
Evans's (53), retaining the quantitative subtraction bound. -/
theorem normalCoefficientNormalGradient.exists_normalDerivative_with_norm
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤
          normalCoefficientNormalGradient.derivativeBound A a C haLip haRep f u alpha ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦
          (A (PDE.Common.lastIndex (n := n)) (PDE.Common.lastIndex (n := n)) :
            ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
            (PDE.Common.lastIndex (n := n)) u : ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  classical
  let normal := PDE.Common.lastIndex (n := n)
  obtain ⟨dq, hdqNorm, hdq⟩ := divergenceFluxL2.exists_normalDerivative_with_norm
    A a C haLip haRep hA halpha f u hu
  obtain ⟨dcross, hdcrossNorm, hdcross⟩ := tangentialFluxSum.exists_normalDerivative_with_norm
    A a C haLip haRep hA halpha f u hu normal
  refine ⟨dq - dcross, (norm_sub_le dq dcross).trans (add_le_add hdqNorm hdcrossNorm),
    (hasWeakDerivativeOn_sub [normal] hdq hdcross).congr_ae ?_ (Lp.coeFn_sub _ _).symm⟩
  filter_upwards [divergenceFluxL2.apply_ae A u normal] with x hx
  rw [hx, ← Finset.add_sum_erase _ _ (Finset.mem_univ normal), add_sub_cancel_right]

/-- Qualitative form of normal differentiation of `aₙₙ Dₙu`. -/
theorem normalCoefficientNormalGradient.exists_normalDerivative
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦
          (A (PDE.Common.lastIndex (n := n)) (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
            (PDE.Common.lastIndex (n := n)) u : ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  exact (normalCoefficientNormalGradient.exists_normalDerivative_with_norm A a C haLip haRep hA
    halpha f u hu).imp fun _ ↦ And.right

/-- Bound obtained when the normal derivative of `Aₙₙ Dₙu` is multiplied by
the `W¹⁻∞` reciprocal of the uniformly positive normal coefficient. -/
noncomputable def normalNormalWeakDerivative.bound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ} (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) : ℝ :=
  let Ω := HalfSpace.upper n
  let normal := PDE.Common.lastIndex (n := n)
  let reciprocal : W^{1,∞}(Ω) :=
    positiveReciprocalW1Top (HalfSpace.measurableSet_upper (n := n))
      halpha (a normal normal) (C normal normal) (haLip normal normal)
  let un : DerivLp n 2 Ω :=
    derivCoordCLM (n := n) (Ω := Ω) normal u
  let annUn : DerivLp n 2 Ω := A normal normal • un
  ‖((reciprocal : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) :
      DerivLp n ∞ Ω)‖ *
      normalCoefficientNormalGradient.derivativeBound A a C haLip haRep f u alpha +
    ‖((reciprocal : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n normal) :
      DerivLp n ∞ Ω)‖ * ‖annUn‖

/-- Quantitative recovery of the missing normal-normal derivative.
Uniform ellipticity gives `Aₙₙ ≥ alpha > 0` almost everywhere. Multiplying
the differentiated normal flux by the clipped reciprocal of the Lipschitz
representative of `Aₙₙ` recovers `∂ₙu` and retains the product-rule norm
bound. -/
theorem normalNormalWeakDerivative.exists_with_norm
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ normalNormalWeakDerivative.bound A a C haLip haRep halpha f u ∧
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
          (PDE.Common.lastIndex (n := n)) u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  let normal := PDE.Common.lastIndex (n := n)
  have hmeas := HalfSpace.measurableSet_upper (n := n)
  let un : DerivLp n 2 (HalfSpace.upper n) :=
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) normal u
  obtain ⟨dannUn, hdannUnNorm, hdannUn⟩ :=
    normalCoefficientNormalGradient.exists_normalDerivative_with_norm
      A a C haLip haRep hA halpha f u hu
  have hannUn := Lp.coeFn_lpSMul (r := 2) (A normal normal) un
  obtain ⟨g, hgNorm, hg⟩ := (positiveReciprocalW1Top hmeas halpha (a normal normal)
    (C normal normal) (haLip normal normal)).exists_weakDerivative_mul_W1Top_first_with_norm
      (HalfSpace.isOpen_upper n) normal (A normal normal • un) dannUn
      (hdannUn.congr_ae hannUn.symm .rfl)
  refine ⟨g, hgNorm.trans
    (add_le_add (mul_le_mul_of_nonneg_left hdannUnNorm (norm_nonneg _)) le_rfl),
    hg.congr_ae ?_ .rfl⟩
  filter_upwards [positiveReciprocalW1Top_base_ae hmeas halpha (a normal normal) (C normal normal)
    (haLip normal normal), hannUn, haRep normal normal,
    aeUniformlyElliptic_diagonal_lower_bound A hA normal] with x hr hav hrep hpos
  have hpos : alpha ≤ a normal normal x := hpos.trans_eq hrep
  rw [hr, hav, Pi.smul_apply', smul_eq_mul, hrep, positiveReciprocal_eq_inv hpos,
    inv_mul_cancel_left₀ (halpha.trans_le hpos).ne']

/-- Qualitative form of normal-normal derivative recovery. -/
theorem normalNormalWeakDerivative.exists
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    {alpha : ℝ}
    (hA : AEUniformlyElliptic (n := n) (Ω := HalfSpace.upper n) A alpha)
    (halpha : 0 < alpha)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (hu : PDE.Analysis.Variational.IsWeakSolution
      (variableCoeffForm (n := n) (Ω := HalfSpace.upper n)
        (multiplicationCoefficientOperator
          (n := n) (Ω := HalfSpace.upper n) A))
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n)
          (PDE.Common.lastIndex (n := n)) u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  exact (normalNormalWeakDerivative.exists_with_norm A a C haLip haRep hA halpha f u hu).imp
    fun _ ↦ And.right

end GraphSpace.BoundaryRegularity
end SobolevSpace
