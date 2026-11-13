/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.DivergenceFlux
public import PDE.Elliptic.Regularity.Boundary.H2.FluxDerivatives
public import PDE.Elliptic.Regularity.Boundary.H2.TangentialDifferenceQuotient
import PDE.Elliptic.Regularity.Boundary.H2.TangentialCommutator
import PDE.Elliptic.Regularity.Boundary.H2.TangentialEstimate
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.Localized
import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.WeakDerivative

/-!
# Tangential derivatives of the divergence flux

For the flux rows `qᵢ = ∑ⱼ aⁱʲ ∂ⱼ u` of a weak solution on the upper half-space, we prove
that each row has a tangential weak derivative in `L²`, with a quantitative bound. This is the
hypothesis needed by our normal-flux recovery step (`NormalFlux`).

The method is the difference-quotient method of step 4 of Evans's proof of §6.3.2, Theorem 4.
A tangential difference quotient
of a product obeys the discrete Leibniz rule

`D_k^h (a ∂ⱼ u) = (τ_h a) · D_k^h(∂ⱼ u) + (D_k^h a) · ∂ⱼ u`,

where `τ_h` is the tangential translation. The first term is bounded in `L²` uniformly in `h` by
the tangential second-derivative estimate for `u`, the second by the Lipschitz constant of the
coefficient times `‖∂ⱼ u‖`. Uniformly bounded difference quotients of an `L²` function have a
weak limit which is the weak derivative (Evans's §5.8.2, Theorem 3(ii)), first for the zero
extension of the
flux row to all of `ℝ^n` and then, by restriction, on the half-space itself.

## Main results

* `tangentialDifferenceQuotientL2.divergenceFlux`: the exact discrete Leibniz decomposition of a
  tangential difference quotient of a flux row.
* `divergenceFluxL2.tangentialDerivativeBound`, `divergenceFluxL2.tangentialQuotient_norm_le`:
  the uniform `L²` bound `∑ⱼ (‖aⁱʲ‖_∞ · B + C_{ij} ‖∂ⱼ u‖)` for the quotients, where `B` is the
  tangential second-derivative bound.
* `divergenceFluxL2.exists_global_tangentialWeakDerivative_with_norm`: a tangential weak
  derivative of the zero-extended flux row on `ℝ^n` with the same bound.
* `divergenceFluxL2.exists_tangentialWeakDerivative_with_norm`,
  `divergenceFluxL2.exists_tangentialWeakDerivative`: the tangential weak derivative of each flux
  row on the half-space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2(a), Theorem 3 (Difference quotients and weak
  derivatives) and its proof, pp. 292-293; §6.3.1, the product rule (17), p. 329; §6.3.2, step 4 of
  the proof of Theorem 4, (49)-(51), p. 336.
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

/-- Taking a tangential difference quotient of a flux row gives the exact
finite-sum Leibniz decomposition into the translated principal term and the
coefficient commutator. -/
theorem tangentialDifferenceQuotientL2.divergenceFlux
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n))
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) (h : ℝ) :
    tangentialDifferenceQuotientLp 2 k hk h (divergenceFluxL2 A u row) =
      ∑ j : Fin n,
        (tangentialTranslateLp ∞ k hk h (A row j) •
            tangentialDifferenceQuotientLp 2 k hk h
              (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u) +
          tangentialDifferenceQuotientLp ∞ k hk h (A row j) •
            derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u) := by
  let du : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun j ↦
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u
  change tangentialDifferenceQuotientLp 2 k hk h
      (∑ j : Fin n, A row j • du j) = _
  simp only [tangentialDifferenceQuotientLp, map_sum]
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact tangentialDifferenceQuotientL2_lpSMul
    k hk h (A row j) (du j)

/-- Bound for a tangential derivative of one divergence-form flux row. -/
noncomputable def divergenceFluxL2.tangentialDerivativeBound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (C : Fin n → Fin n → NNReal)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) (alpha : ℝ)
    (row : Fin n) : ℝ :=
  ∑ j : Fin n,
    (‖A row j‖ * tangentialSecondWeakDerivative.bound C f u alpha +
      (C row j : ℝ) *
        ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖)

/-- Uniform `L²` bound for tangential quotients of a divergence-form flux
row.  The first summand is controlled by the elliptic gradient estimate and
the second by the Lipschitz coefficient constants. -/
theorem divergenceFluxL2.tangentialQuotient_norm_le
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
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n))
    {h : ℝ} (hh : h ≠ 0) :
    ‖tangentialDifferenceQuotientLp 2 k hk h
        (divergenceFluxL2 A u row)‖ ≤
      ∑ j : Fin n,
        (‖A row j‖ *
          Real.sqrt (((∑ r : Fin n,
              (∑ l : Fin n, (C r l : ℝ) *
                ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) l u‖) ^ 2 /
                alpha) + ‖f‖ ^ 2 / alpha +
              (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2)) +
          (C row j : ℝ) *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖) := by
  let du : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun j ↦
    derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u
  let K : ℝ := Real.sqrt (((∑ r : Fin n,
      (∑ l : Fin n, (C r l : ℝ) * ‖du l‖) ^ 2 / alpha) +
    ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2))
  have hdu (j : Fin n) :
      ‖tangentialDifferenceQuotientLp 2 k hk h (du j)‖ ≤ K := by
    rw [← tangentialDifferenceQuotientL2.norm_zeroExtend_eq k hk h]
    simpa only [K, du] using
      (norm_zeroExtend_tangentialGradientQuotient_le
        A a C haLip haRep hA halpha f u hu k hk j hh)
  rw [tangentialDifferenceQuotientL2.divergenceFlux A u row k hk h]
  calc
    ‖∑ j : Fin n,
        (tangentialTranslateLp ∞ k hk h (A row j) •
            tangentialDifferenceQuotientLp 2 k hk h (du j) +
          tangentialDifferenceQuotientLp ∞ k hk h (A row j) • du j)‖ ≤
      ∑ j : Fin n,
        ‖tangentialTranslateLp ∞ k hk h (A row j) •
            tangentialDifferenceQuotientLp 2 k hk h (du j) +
          tangentialDifferenceQuotientLp ∞ k hk h (A row j) • du j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j : Fin n,
        (‖A row j‖ * K + (C row j : ℝ) * ‖du j‖) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        ‖tangentialTranslateLp ∞ k hk h (A row j) •
              tangentialDifferenceQuotientLp 2 k hk h (du j) +
            tangentialDifferenceQuotientLp ∞ k hk h (A row j) • du j‖ ≤
          ‖tangentialTranslateLp ∞ k hk h (A row j) •
              tangentialDifferenceQuotientLp 2 k hk h (du j)‖ +
            ‖tangentialDifferenceQuotientLp ∞ k hk h (A row j) • du j‖ :=
              norm_add_le _ _
        _ ≤ ‖A row j‖ * ‖tangentialDifferenceQuotientLp 2 k hk h (du j)‖ +
            (C row j : ℝ) * ‖du j‖ := add_le_add
              (by
                calc
                  ‖tangentialTranslateLp ∞ k hk h (A row j) •
                      tangentialDifferenceQuotientLp 2 k hk h (du j)‖ ≤
                    ‖tangentialTranslateLp ∞ k hk h (A row j)‖ *
                      ‖tangentialDifferenceQuotientLp 2 k hk h (du j)‖ :=
                        MeasureTheory.Lp.norm_smul_le _ _
                  _ = ‖A row j‖ *
                      ‖tangentialDifferenceQuotientLp 2 k hk h (du j)‖ := by
                        rw [tangentialTranslateLp.norm])
              (tangentialCoefficientCommutatorL2.norm_le
                k hk (A row j) (a row j) (haLip row j) (haRep row j)
                  h hh (du j))
        _ ≤ ‖A row j‖ * K + (C row j : ℝ) * ‖du j‖ :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hdu j) (norm_nonneg _)) le_rfl
    _ = _ := by rfl

/-- Uniform tangential flux quotients produce a whole-space weak derivative
of the zero-extended flux row with the same quantitative bound. -/
theorem divergenceFluxL2.exists_global_tangentialWeakDerivative_with_norm
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
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 Set.univ,
      ‖g‖ ≤ divergenceFluxL2.tangentialDerivativeBound A C f u alpha row ∧
        HasWeakDerivativeOn (n := n) Set.univ [k]
        ((Extension.Lp.zeroExtendLp
          (n := n) (p := 2) (Ω := HalfSpace.upper n)
          (HalfSpace.measurableSet_upper (n := n))
          (divergenceFluxL2 A u row) : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  let step : ℕ → ℝ := DifferenceQuotient.collarStep 1
  let K : ℝ := Real.sqrt (((∑ r : Fin n,
      (∑ l : Fin n, (C r l : ℝ) *
        ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) l u‖) ^ 2 / alpha) +
    ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2))
  let fluxBound : ℝ := ∑ j : Fin n,
    (‖A row j‖ * K + (C row j : ℝ) *
      ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖)
  have hstepZero : Filter.Tendsto step Filter.atTop (nhds 0) := by
    simpa [step] using DifferenceQuotient.tendsto_collarStep_zero (1 : ℝ)
  have hstepNe (m : ℕ) : step m ≠ 0 :=
    DifferenceQuotient.collarStep_ne_zero (by norm_num) m
  obtain ⟨g, hgNorm, hg⟩ :=
    DifferenceQuotient.exists_L2_weakDerivative_of_bounded_differenceQuotients_with_norm
      k step hstepZero hstepNe
      (Extension.Lp.zeroExtendLp
        (n := n) (p := 2) (Ω := HalfSpace.upper n)
        (HalfSpace.measurableSet_upper (n := n))
        (divergenceFluxL2 A u row)) fluxBound (by
          intro m
          rw [tangentialDifferenceQuotientL2.norm_zeroExtend_eq
            k hk (step m)]
          simpa only [fluxBound, K] using
            (divergenceFluxL2.tangentialQuotient_norm_le
              A a C haLip haRep hA halpha f u hu row k hk (hstepNe m)))
  exact ⟨g, by simpa [divergenceFluxL2.tangentialDerivativeBound,
    tangentialSecondWeakDerivative.bound, fluxBound, K] using hgNorm, hg⟩

/-- Qualitative form of the whole-space tangential flux derivative. -/
theorem divergenceFluxL2.exists_global_tangentialWeakDerivative
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
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 Set.univ,
      HasWeakDerivativeOn (n := n) Set.univ [k]
        ((Extension.Lp.zeroExtendLp
          (n := n) (p := 2) (Ω := HalfSpace.upper n)
          (HalfSpace.measurableSet_upper (n := n))
          (divergenceFluxL2 A u row) : DerivLp n 2 Set.univ) : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    divergenceFluxL2.exists_global_tangentialWeakDerivative_with_norm
    A a C haLip haRep hA halpha f u hu row k hk
  exact ⟨g, hg⟩

/-- Tangential weak derivatives of every physical flux row exist directly
on the flattened half-space with the whole-space quotient bound. -/
theorem divergenceFluxL2.exists_tangentialWeakDerivative_with_norm
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
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ divergenceFluxL2.tangentialDerivativeBound A C f u alpha row ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [k]
        (divergenceFluxL2 A u row : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨G, hGnorm, hG⟩ :=
    divergenceFluxL2.exists_global_tangentialWeakDerivative_with_norm
      A a C haLip haRep hA halpha f u hu row k hk
  obtain ⟨g, hgNorm, hg⟩ :=
    exists_restrictedWeakDerivative_of_zeroExtend_with_norm
      (HalfSpace.measurableSet_upper (n := n)) k
      (divergenceFluxL2 A u row) G hG
  exact ⟨g, hgNorm.trans hGnorm, hg⟩

/-- Qualitative form of the tangential physical-flux derivative. -/
theorem divergenceFluxL2.exists_tangentialWeakDerivative
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
      (loadFunctional (n := n) (Ω := HalfSpace.upper n) f) u)
    (row k : Fin n) (hk : k ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [k]
        (divergenceFluxL2 A u row : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  obtain ⟨g, _hgNorm, hg⟩ :=
    divergenceFluxL2.exists_tangentialWeakDerivative_with_norm
      A a C haLip haRep hA halpha f u hu row k hk
  exact ⟨g, hg⟩

end GraphSpace.BoundaryRegularity
end SobolevSpace
