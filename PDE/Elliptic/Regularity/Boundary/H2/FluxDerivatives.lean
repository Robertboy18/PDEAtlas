/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Calculus.Divergence.Component
import PDE.Elliptic.Regularity.Boundary.H2.TangentialEstimate
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
public import PDE.Spaces.Sobolev.Calculus.Product.LipschitzCoefficient

/-!
# Boundary regularity: flux derivatives

After the boundary is flattened, one has a weak solution `u ∈ H¹₀` of `-∂ᵢ(aⁱʲ ∂ⱼ u) = f` on the
half-space, with Lipschitz coefficients. The tangential estimate (`TangentialEstimate`) gives
all second derivatives `∂ₖ∂ⱼ u` with at least one tangential index. In step 5 of the proof of
§6.3.2, Theorem 4, Evans recovers the remaining normal-normal derivative `∂ₙ∂ₙ u` from the
nondivergence form (52)-(53) of the equation, which holds almost everywhere by interior
regularity. We recover it from the weak equation instead: writing the flux rows
`qᵢ = ∑ⱼ aⁱʲ ∂ⱼ u`, the weak equation says `-∑ᵢ ∂ᵢ qᵢ = f` distributionally, so

`∂ₙ qₙ = -f - ∑_{i ≠ n} ∂ᵢ qᵢ`

as long as each tangential flux row `qᵢ`, `i ≠ n`, has a tangential weak derivative in `L²`.
Since `qₙ = aⁿⁿ ∂ₙ u + ∑_{j ≠ n} aⁿʲ ∂ⱼ u`, and the second group of terms has an `L²` normal
derivative by the product rule (Lipschitz coefficient times a gradient component whose normal
derivative is a mixed derivative already controlled), one can then solve for `∂ₙ(aⁿⁿ ∂ₙ u)` and
finally for `∂ₙ∂ₙ u` using ellipticity `aⁿⁿ ≥ α`.

We prove the differentiation steps of that argument: the mixed derivatives
`∂ₙ(∂ⱼ u) = ∂ⱼ(∂ₙ u)`, the `W^{1,∞} × H¹` product rule for coefficient times gradient component,
the sum over the non-normal terms of a flux row, and the abstract weak-divergence recovery of
`∂ₙ qₙ`. Each quantitative statement is paired with a qualitative one.

## Main results

* `tangentialGradientComponent.exists_normalDerivative_with_norm`: for `j ≠ n`, `∂ⱼ u` has an `L²`
  normal weak derivative bounded by `tangentialSecondWeakDerivative.bound`.
* `coefficientTangentialGradient.exists_normalDerivative_with_norm`: `aⁱʲ ∂ⱼ u` (with `j ≠ n`) has
  an `L²` normal weak derivative with the product bound.
* `tangentialFluxSum.exists_normalDerivative_with_norm`: the non-normal part
  `∑_{j ≠ n} aⁱʲ ∂ⱼ u` of a flux row has an `L²` normal weak derivative.
* `normalFlux.hasWeakDerivative_of_weakDivergence`: if `-∑ᵢ ∂ᵢ qᵢ = f` weakly and each tangential
  row `qᵢ` has an `L²` tangential weak derivative `dqᵢ`, then `qₙ` has normal weak derivative
  `-f - ∑_{i ≠ n} dqᵢ`.

## Implementation notes

Coefficients enter twice: as `L∞` elements `A i j` used in the variational form and as Lipschitz
representatives `a i j` with constants `C i j`, linked by `haRep`. The Lipschitz representative
supplies the `W^{1,∞}` structure needed for the product rule. The sign in the recovered derivative
`-f - ∑ dqᵢ` reflects the convention `∫ q · ∂φ = ∫ f φ` for the weak divergence identity.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 5 of the proof of Theorem 4, (52)-(55),
  pp. 336-337.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace GraphSpace.BoundaryRegularity

variable {n : ℕ}

/-- The common `L²` bound for tangential and mixed second derivatives in the
flattened-boundary argument. -/
noncomputable def tangentialSecondWeakDerivative.bound
    [Fact (0 < n)]
    (C : Fin n → Fin n → NNReal)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) (alpha : ℝ) : ℝ :=
  Real.sqrt (((∑ r : Fin n,
      (∑ l : Fin n, (C r l : ℝ) *
        ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) l u‖) ^ 2 / alpha) +
    ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2))

/-- Mixed weak derivatives commute at the flattened boundary.  In
particular, the tangential estimate for `∂ⱼ(∂ₙu)` also supplies the normal
derivative `∂ₙ(∂ⱼu)` needed to differentiate the non-normal terms in the
normal flux. -/
theorem tangentialGradientComponent.exists_normalDerivative_with_norm
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
    (j : Fin n) (hj : j ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ Real.sqrt (((∑ r : Fin n,
          (∑ l : Fin n, (C r l : ℝ) *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) l u‖) ^ 2 / alpha) +
        ‖f‖ ^ 2 / alpha + (alpha / 4) * ‖u‖ ^ 2) / (alpha / 2)) ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  obtain ⟨g, hgNorm, hg⟩ := tangentialSecondWeakDerivative.exists_with_norm
    A a C haLip haRep hA halpha f u hu j hj PDE.Common.lastIndex
  let U : H¹(HalfSpace.upper n) := u
  have hfirst (i : Fin n) : HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
      ((U : WkpAmbientOn n 1 2 (HalfSpace.upper n)) (baseIndex n 1) : DerivLp n 2 _)
      (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) i u) := by
    simpa only [firstDerivIndex_one, derivCoordCLM_apply] using
      U.property.hasWeakDerivativeOn_first (by norm_num) i
  exact ⟨g, hgNorm, (hfirst j).cancel_prefix_append_single _
    (((hfirst _).append_single j hg).perm (List.Perm.swap _ _ []))⟩

/-- Qualitative form of mixed normal-tangential derivative recovery. -/
theorem tangentialGradientComponent.exists_normalDerivative
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
    (j : Fin n) (hj : j ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ)
        (g : ℝ^n → ℝ) := by
  exact (tangentialGradientComponent.exists_normalDerivative_with_norm A a C haLip haRep hA halpha
    f u hu j hj).imp fun _ ↦ And.right

/-- Every non-normal term in the normal flux has an `L²` normal weak
derivative.  The coefficient derivative comes canonically from its
Lipschitz representative, and the gradient derivative is the mixed weak
derivative recovered above.  This quantitative form retains the exact
`W^{1,∞} × W^{1,2}` product bound. -/
theorem coefficientTangentialGradient.exists_normalDerivative_with_norm
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
    (row j : Fin n) (hj : j ≠ PDE.Common.lastIndex (n := n)) :
    let coeff : W^{1,∞}(HalfSpace.upper n) :=
      w1TopOfLipschitzRepresentative
        (HalfSpace.measurableSet_upper (n := n)) (A row j) (a row j)
          (C row j) (haLip row j) (haRep row j)
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤
          ‖((coeff : WkpAmbientOn n 1 ∞ (HalfSpace.upper n))
            (baseIndex n 1) : DerivLp n ∞ (HalfSpace.upper n))‖ *
              tangentialSecondWeakDerivative.bound C f u alpha +
          ‖((coeff : WkpAmbientOn n 1 ∞ (HalfSpace.upper n))
            (singleDerivIndex n (PDE.Common.lastIndex (n := n))) :
              DerivLp n ∞ (HalfSpace.upper n))‖ *
            ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖ ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦ (A row j : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u :
              ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  dsimp only
  have hmeas := HalfSpace.measurableSet_upper (n := n)
  obtain ⟨du, hduNorm, hdu⟩ := tangentialGradientComponent.exists_normalDerivative_with_norm
    A a C haLip haRep hA halpha f u hu j hj
  obtain ⟨g, hgNorm, hg⟩ := (w1TopOfLipschitzRepresentative hmeas (A row j) (a row j) (C row j)
    (haLip row j) (haRep row j)).exists_weakDerivative_mul_W1Top_first_with_norm
      (HalfSpace.isOpen_upper n) _ _ du hdu
  refine ⟨g, hgNorm.trans (add_le_add (mul_le_mul_of_nonneg_left hduNorm (norm_nonneg _)) le_rfl),
    hg.congr_ae ?_ .rfl⟩
  filter_upwards [w1TopOfLipschitzRepresentative_base_ae hmeas (A row j) (a row j) (C row j)
    (haLip row j) (haRep row j)] with x hx
  rw [hx]

/-- Qualitative form of the differentiated coefficient-times-tangential-gradient term. -/
theorem coefficientTangentialGradient.exists_normalDerivative
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
    (row j : Fin n) (hj : j ≠ PDE.Common.lastIndex (n := n)) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦ (A row j : ℝ^n → ℝ) x *
          (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  exact (coefficientTangentialGradient.exists_normalDerivative_with_norm A a C haLip haRep hA
    halpha f u hu row j hj).imp fun _ ↦ And.right

/-- Sum of the quantitative product bounds for the non-normal terms in one
flux row. -/
noncomputable def tangentialFluxSum.normalDerivativeBound
    [Fact (0 < n)]
    (A : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n))
    (a : Fin n → Fin n → ℝ^n → ℝ)
    (C : Fin n → Fin n → NNReal)
    (haLip : ∀ i j, LipschitzWith (C i j) (a i j))
    (haRep : ∀ i j,
      (A i j : ℝ^n → ℝ) =ᵐ[domainMeasure n (HalfSpace.upper n)] a i j)
    (f : DerivLp n 2 (HalfSpace.upper n))
    (u : H¹₀(HalfSpace.upper n)) (alpha : ℝ)
    (row : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)),
    (let coeff : W^{1,∞}(HalfSpace.upper n) :=
      w1TopOfLipschitzRepresentative
        (HalfSpace.measurableSet_upper (n := n)) (A row j) (a row j)
          (C row j) (haLip row j) (haRep row j)
     ‖((coeff : WkpAmbientOn n 1 ∞ (HalfSpace.upper n))
        (baseIndex n 1) : DerivLp n ∞ (HalfSpace.upper n))‖ *
          tangentialSecondWeakDerivative.bound C f u alpha +
      ‖((coeff : WkpAmbientOn n 1 ∞ (HalfSpace.upper n))
        (singleDerivIndex n (PDE.Common.lastIndex (n := n))) :
          DerivLp n ∞ (HalfSpace.upper n))‖ *
        ‖derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u‖)

/-- The tangential part of any flux row has an `L²` normal weak derivative.
This is the finite-sum form used when the normal row is split into its
normal-normal term and the remaining cross terms.  The derivative norm is
bounded by the sum of the quantitative product bounds. -/
theorem tangentialFluxSum.exists_normalDerivative_with_norm
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
    (row : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      ‖g‖ ≤ tangentialFluxSum.normalDerivativeBound A a C haLip haRep f u alpha row ∧
        HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦ ∑ j ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)),
          (A row j : ℝ^n → ℝ) x *
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u :
                ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  classical
  let tangential := Finset.univ.erase (PDE.Common.lastIndex (n := n))
  choose d hdNorm hd using fun (j : Fin n) (hj : j ∈ tangential) ↦
    coefficientTangentialGradient.exists_normalDerivative_with_norm A a C haLip haRep hA halpha f
      u hu row j (Finset.mem_erase.mp hj).1
  let dq : Fin n → DerivLp n 2 (HalfSpace.upper n) := fun j ↦
    if hj : j ∈ tangential then d j hj else 0
  refine ⟨∑ j ∈ tangential, dq j,
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ by simpa [dq, hj] using hdNorm j hj),
    (hasWeakDerivativeOn_finsetSum tangential _ (fun j ↦ (dq j : ℝ^n → ℝ)) _ fun j hj ↦ by
      simpa [dq, hj] using hd j hj).congr_ae .rfl (Lp.coeFn_fun_finsetSum _ _).symm⟩

/-- Qualitative form of the differentiated tangential flux sum. -/
theorem tangentialFluxSum.exists_normalDerivative
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
    (row : Fin n) :
    ∃ g : DerivLp n 2 (HalfSpace.upper n),
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
        [PDE.Common.lastIndex (n := n)]
        (fun x ↦ ∑ j ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)),
          (A row j : ℝ^n → ℝ) x *
            (derivCoordCLM (n := n) (Ω := HalfSpace.upper n) j u : ℝ^n → ℝ) x)
        (g : ℝ^n → ℝ) := by
  exact (tangentialFluxSum.exists_normalDerivative_with_norm A a C haLip haRep hA halpha f u hu
    row).imp fun _ ↦ And.right

/-- Normal-flux recovery from the weak divergence equation.  If every
tangential flux component has its matching tangential weak derivative in
`L²`, then the divergence identity determines the normal weak derivative of
the normal flux. This replaces the nondivergence form (52)-(53) in step 5 of
Evans's proof of §6.3.2, Theorem 4, in the recovery of the missing
normal-normal derivative. -/
theorem normalFlux.hasWeakDerivative_of_weakDivergence
    [Fact (0 < n)]
    (q dq : Fin n → DerivLp n 2 (HalfSpace.upper n))
    (f : DerivLp n 2 (HalfSpace.upper n))
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport φ.toFun ⊆ HalfSpace.upper n →
        (∑ i : Fin n,
          ∫ x, (q i : ℝ^n → ℝ) x *
            iteratedPartialDeriv (n := n) [i] φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n)) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
            ∂domainMeasure n (HalfSpace.upper n))
    (htangential : ∀ i : Fin n, i ≠ PDE.Common.lastIndex (n := n) →
      HasWeakDerivativeOn (n := n) (HalfSpace.upper n) [i]
        (q i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
      [PDE.Common.lastIndex (n := n)]
      (q (PDE.Common.lastIndex (n := n)) : ℝ^n → ℝ)
      (fun x ↦ -(f : ℝ^n → ℝ) x -
        (∑ i ∈ Finset.univ.erase (PDE.Common.lastIndex (n := n)),
          (dq i : ℝ^n → ℝ) x)) := by
  exact hasWeakDerivativeOn_component_of_weakDivergence
    (PDE.Common.lastIndex (n := n)) q dq f hdiv htangential

end GraphSpace.BoundaryRegularity
end SobolevSpace
