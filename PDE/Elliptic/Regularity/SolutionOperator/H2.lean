/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.Lift
public import PDE.Elliptic.Variational.DivergenceSolution
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
import PDE.Elliptic.Regularity.Global.H2
import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# The global `L² → H²` elliptic solution operator

On a bounded domain with a `C2BoundaryAtlas`, for uniformly elliptic principal coefficients with
`C¹` representatives on `ℝⁿ`, the weak Dirichlet solution of `-∂ᵢ(aᵢⱼ ∂ⱼu) = f` depends linearly and
boundedly on `f ∈ L²` as an element of `H²` (`globalH2SolveCLM`, `globalH2SolveCLM_base_ae`,
`globalH2SolveCLM_orderOne`). It is the order-zero case of the closed-graph construction of
`PDE.Elliptic.Regularity.SolutionOperator.Lift`, with the qualitative theorem
`exists_global_h2_of_isWeakDivergenceSolution` as input. For symmetric coefficients, every `H¹₀`
minimizer of the energy solves the weak equation and has a unique `H²` representative with the same
bound (`existsUnique_global_h2_with_norm_of_energy_minimizer`). The operator acts pointwise on
Bochner `L²` families with the same bound (`globalH2SolveLpCLM`, `globalH2SolveLpCLM_norm_le`).

For an `H²` field `G`, `strongLoad A G` is `-∂ᵢ(aᵢⱼ ∂ⱼG)` written with weak derivatives, and an
`H¹₀` function represented by `G` solves the weak equation with this load
(`strongLoad_isWeakDivergenceSolution`).

The operator norm of `globalH2SolveCLM` is a constant for the estimate `‖u‖_{H²(U)} ≤ C ‖f‖_{L²(U)}`
of Remark (i) after Evans's §6.3.2, Theorem 4, for an operator without lower-order terms. Evans
assumes `aⁱʲ ∈ C¹(Ū)`, (38), and a `C²` boundary, (41). He applies Theorem 4 at almost every time in
step 3 of his proof of §7.1.3, Theorem 5, (49); `globalH2SolveLpCLM` is the corresponding operator
on Bochner families.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 4 (Boundary H²-regularity), (38)-(42), and
  Remark (i) after it, pp. 334-335; §7.1.3, Theorem 5 (Improved regularity) and steps 3-4 of its
  proof, (49)-(51), pp. 382-384, and the proof of Theorem 6 (Higher regularity), p. 387; §7.2.3,
  step 2 of the proof of Theorem 6, (69), p. 413; §8.1.2, Example 2 (Generalized Dirichlet's
  principle), p. 456.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

variable {n : ℕ}

section EvansOperator

variable {Omega : Set (ℝ^n)}

/-- The `L∞` coefficient matrix represented by the base coordinates of the
`W¹,∞` coefficient bundle used in the global regularity theorem. -/
noncomputable def coefficientBase
    (A : Fin n → Fin n → W^{1,∞}(Omega)) :
    Fin n → Fin n → DerivLp n ∞ Omega :=
  fun i j ↦
    ((A i j : WkpAmbientOn n 1 ∞ Omega)
      (baseIndex n 1) : DerivLp n ∞ Omega)

/-- The pointwise ellipticity hypothesis on a chosen `C¹` representative
implies the almost-everywhere ellipticity hypothesis needed by the
Lax-Milgram solver. The finite coordinate family lets all representative
equalities be placed on one common full-measure set. -/
theorem coefficientBase_aeUniformlyElliptic
    (hOmegaMeasurable : MeasurableSet Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    AEUniformlyElliptic (n := n) (Ω := Omega)
      (coefficientBase A) alpha := by
  refine ⟨halpha, ?_⟩
  filter_upwards [ae_all_iff.2 fun i ↦ ae_all_iff.2 fun j ↦ haRep i j,
    MeasureTheory.ae_restrict_mem hOmegaMeasurable] with x hx hxOmega xi
  simp only [coefficientBase] at hx ⊢
  simp_rw [hx]
  simpa [MatrixEllipticLowerBound, dotProduct, principalEnergy,
    pow_two, mul_comm, mul_left_comm, mul_assoc] using hElliptic x hxOmega xi

/-- Pointwise symmetry of the chosen coefficient representative induces the
almost-everywhere symmetry required by the variational operator. -/
theorem coefficientBase_aeSymmetric
    (hOmegaMeasurable : MeasurableSet Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (hSymm : ∀ x ∈ Omega, ∀ i j, a x i j = a x j i) :
    AESymmetricCoefficient (n := n) (Ω := Omega)
      (coefficientBase A) := by
  intro i j
  filter_upwards [haRep i j, haRep j i,
    MeasureTheory.ae_restrict_mem hOmegaMeasurable] with x hij hji hx
  exact hij.trans ((hSymm x hx i j).trans hji.symm)

/--
The `L²` strong load represented by an `H²` field:

`-∂ᵢ(aᵢⱼ ∂ⱼG) = -aᵢⱼ ∂ᵢ∂ⱼG - (∂ᵢaᵢⱼ) ∂ⱼG`.

The derivative word `[j, i]` records first taking `∂ⱼ` and then `∂ᵢ`.
For an `H²` datum `G` and an operator without lower-order terms, `f(0) - strongLoad A G`
is the initial value of `u'` in the parabolic case and of `u''` in the hyperbolic case:
Evans's `g̃ = f(·, 0) - Lg` in the proof of §7.1.3, Theorem 6, and `h̃` in (69) of the
proof of §7.2.3, Theorem 6. In his proof of §7.1.3, Theorem 5(ii), the equation (16) at
`t = 0` gives the corresponding bound in (51).
-/
noncomputable def strongLoad
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (G : W^{2,2}(Omega)) :
    DerivLp n 2 Omega :=
  -∑ i : Fin n, ∑ j : Fin n, (
    ((A i j : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) •
      ((G : WkpAmbientOn n 2 2 Omega)
        (pairDerivIndex n j i) :
          DerivLp n 2 Omega) +
    ((A i j : WkpAmbientOn n 1 ∞ Omega)
        (singleDerivIndex n i) : DerivLp n ∞ Omega) •
      ((G : WkpAmbientOn n 2 2 Omega)
        (firstDerivIndex n 2 (by norm_num) j) :
          DerivLp n 2 Omega))

/--
An `H¹₀` function with `H²` representative `G` solves the divergence-form equation
whose forcing is `strongLoad A G`.

The proof is the weak Leibniz rule followed by integration by parts against `H¹₀` test
functions. The parabolic and hyperbolic regularity theorems use it for the initial data
of the time-differentiated problem.
-/
theorem strongLoad_isWeakDivergenceSolution
    (hOmegaOpen : IsOpen Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (G : W^{2,2}(Omega))
    (g : H¹₀(Omega))
    (hG :
      lowerOrderCLM
          (n := n) (k := 1) (m := 2) (p := 2) (Ω := Omega)
          (by omega) G =
        h10SubtypeL (n := n) (Ω := Omega) g) :
    IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (coefficientBase A) (strongLoad A G) g := by
  classical
  let a0 : Fin n → Fin n → DerivLp n ∞ Omega := fun i j ↦
    (A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1)
  let da : Fin n → Fin n → DerivLp n ∞ Omega := fun i j ↦
    (A i j : WkpAmbientOn n 1 ∞ Omega) (singleDerivIndex n i)
  let dG : Fin n → DerivLp n 2 Omega := fun j ↦
    (G : WkpAmbientOn n 2 2 Omega) (firstDerivIndex n 2 (by norm_num) j)
  let ddG : Fin n → Fin n → DerivLp n 2 Omega := fun i j ↦
    (G : WkpAmbientOn n 2 2 Omega) (pairDerivIndex n j i)
  let q : Fin n → Fin n → DerivLp n 2 Omega := fun i j ↦ a0 i j • ddG i j + da i j • dG j
  have hGDeriv (j : Fin n) : dG j = derivCoordCLM (n := n) (Ω := Omega) j g := by
    simpa [dG, lowerOrderCLM_apply, derivCoordCLM_apply, h10SubtypeL_apply, firstDerivIndex] using
      congrArg (fun U : H¹(Omega) ↦
        ((U : WkpAmbientOn n 1 2 Omega) (singleDerivIndex n j) : DerivLp n 2 Omega)) hG
  have hGWeak (i j : Fin n) :
      HasWeakDerivativeOn (n := n) Omega [i] (dG j : ℝ^n → ℝ) (ddG i j : ℝ^n → ℝ) := by
    simpa [dG, ddG, firstDerivIndex, pairDerivIndex, secondDerivIndex] using
      G.property.hasWeakDerivativeOn_from_coordinate [j] [i] (by simp)
  have hqWeak (i j : Fin n) : HasWeakDerivativeOn (n := n) Omega [i]
      (a0 i j • dG j : DerivLp n 2 Omega) (q i j : DerivLp n 2 Omega) := by
    refine ((A i j).hasWeakDerivativeOn_mul_W1Top_first hOmegaOpen i (dG j) (ddG i j)
      (hGWeak i j)).congr_ae (mulLpLeft_apply_ae (a0 i j) (dG j)).symm ?_
    filter_upwards [Lp.coeFn_add (a0 i j • ddG i j) (da i j • dG j),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (a0 i j) (ddG i j),
      Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (da i j) (dG j)] with x hxadd hxa hxda
    simp only [q]
    rw [hxadd, Pi.add_apply, hxa, hxda]
    rfl
  refine (isWeakSolution_iff_isWeakDivergenceSolution hOmegaOpen _ _ g).1 fun v ↦ ?_
  change (∑ i : Fin n, ∑ j : Fin n, inner ℝ
      (coefficientBase A i j • derivCoordCLM (n := n) (Ω := Omega) j g)
      (derivCoordCLM (n := n) (Ω := Omega) i v)) =
    inner ℝ (strongLoad A G) (baseCoordCLM (n := n) (Ω := Omega) v)
  calc _ = ∑ i : Fin n, ∑ j : Fin n,
        -inner ℝ (q i j) (baseCoordCLM (n := n) (Ω := Omega) v) := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        rw [← hGDeriv j]
        exact weakDerivative_integrationByParts_H10 i (a0 i j • dG j) (q i j) (hqWeak i j) v
    _ = _ := by simp [strongLoad, q, a0, da, dG, ddG, sum_inner]

variable [Fact (0 < n)]

/-- The bounded `L² → H¹₀` weak-solution operator for the principal coefficients
`coefficientBase A`. -/
noncomputable def globalH2WeakSolveCLM
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    DerivLp n 2 Omega →L[ℝ]
      H¹₀(Omega) :=
  let hAE := coefficientBase_aeUniformlyElliptic
    hOmega.toC1ExtensionAtlas.isOpen.measurableSet
      A a haRep alpha halpha hElliptic
  variableCoeffSolveCLM
    (n := n) (Ω := Omega)
    (Fact.out : 0 < n) hOmega.toC1ExtensionAtlas.bounded
    (multiplicationCoefficientOperator
      (n := n) (Ω := Omega) (coefficientBase A))
    (integratedElliptic_multiplication_of_ae
      (n := n) (Ω := Omega)
      (coefficientBase A) hAE)

/-- The canonical `H¹₀` value used by the global `H²` operator satisfies the
original divergence-form weak equation. -/
theorem globalH2WeakSolveCLM_isWeakDivergenceSolution
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : DerivLp n 2 Omega) :
    IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (coefficientBase A) f
      (globalH2WeakSolveCLM
        hOmega A a haRep alpha halpha hElliptic f) := by
  simpa [globalH2WeakSolveCLM] using variableCoeffSolve_isWeakDivergenceSolution
    (n := n) (Ω := Omega) hOmega.toC1ExtensionAtlas.isOpen (Fact.out : 0 < n)
    hOmega.toC1ExtensionAtlas.bounded (coefficientBase A)
    (integratedElliptic_multiplication_of_ae (n := n) (Ω := Omega) (coefficientBase A)
      (coefficientBase_aeUniformlyElliptic hOmega.toC1ExtensionAtlas.isOpen.measurableSet
        A a haRep alpha halpha hElliptic)) f

/-- Uniqueness identifies any weak solution with the canonical value used by
the global `H²` operator. -/
theorem eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (coefficientBase A) f u) :
    u = globalH2WeakSolveCLM
      hOmega A a haRep alpha halpha hElliptic f := by
  obtain ⟨w, -, huniq⟩ := IsWeakDivergenceSolution.existsUnique_of_ae (n := n) (Ω := Omega)
    hOmega.toC1ExtensionAtlas.isOpen (Fact.out : 0 < n) hOmega.toC1ExtensionAtlas.bounded
    (coefficientBase A) (coefficientBase_aeUniformlyElliptic
      hOmega.toC1ExtensionAtlas.isOpen.measurableSet A a haRep alpha halpha hElliptic) f
  exact (huniq u hu).trans (huniq _ (globalH2WeakSolveCLM_isWeakDivergenceSolution
    hOmega A a haRep alpha halpha hElliptic f)).symm

/-- Every value of the canonical weak-solution operator has an `H²` representative, by the
global regularity theorem `exists_global_h2_of_isWeakDivergenceSolution`. -/
private theorem globalH2WeakSolve_hasRegularity
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : DerivLp n 2 Omega) :
    ∃ W : W^{2,2}(Omega),
      ⇑((W : WkpAmbientOn n 2 2 Omega)
          (baseIndex n 2) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑((((globalH2WeakSolveCLM hOmega A a haRep alpha halpha hElliptic f :
              H¹₀(Omega)) :
            H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) := by
  exact exists_global_h2_of_isWeakDivergenceSolution hOmega A a haRep haC1 f _
    (globalH2WeakSolveCLM_isWeakDivergenceSolution hOmega A a haRep alpha halpha hElliptic f)
    alpha halpha hElliptic

/-- The global `H²` solution operator.

On a bounded domain equipped with `C2BoundaryAtlas`, with uniformly elliptic
principal coefficients admitting global `C¹` representatives, the
homogeneous-Dirichlet weak solution depends boundedly and linearly on its
`L²` forcing datum, with values in `H²(Ω)`. The operator norm is a constant for the
estimate `‖u‖_{H²(U)} ≤ C ‖f‖_{L²(U)}` of Remark (i) after Evans's §6.3.2, Theorem 4,
for an operator without lower-order terms.
-/
noncomputable def globalH2SolveCLM
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    DerivLp n 2 Omega →L[ℝ] W^{2,2}(Omega) :=
  (higherSolutionOperator (m := 0)
      hOmega.toC1ExtensionAtlas.isOpen
      (globalH2WeakSolveCLM hOmega A a haRep alpha halpha hElliptic)
      (hasHigherSolutionLift_zero
        (globalH2WeakSolveCLM
          hOmega A a haRep alpha halpha hElliptic)
        (fun g ↦ by
          simpa only [wkpBaseCoordinateCLM_apply, h10SubtypeL_apply] using
            globalH2WeakSolve_hasRegularity
              hOmega A a haRep haC1 alpha halpha hElliptic g))).comp
    (orderZeroSobolevCLM
      (n := n) (p := 2) (Omega := Omega))

/-- The `H²` solution operator represents the canonical `H¹₀` weak
solution almost everywhere. -/
theorem globalH2SolveCLM_base_ae
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : DerivLp n 2 Omega) :
    ⇑((globalH2SolveCLM hOmega A a haRep haC1 alpha halpha hElliptic f :
          WkpAmbientOn n 2 2 Omega)
        (baseIndex n 2) : DerivLp n 2 Omega)
      =ᵐ[domainMeasure n Omega]
        ⇑((((globalH2WeakSolveCLM hOmega A a haRep alpha halpha hElliptic f :
              H¹₀(Omega)) :
            H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) := by
  have hbase : wkpBaseCoordinateCLM (n := n) (m := 2) (p := 2) (Ω := Omega)
        (globalH2SolveCLM hOmega A a haRep haC1 alpha halpha hElliptic f) =
      wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
        (h10SubtypeL (n := n) (Ω := Omega)
          (globalH2WeakSolveCLM hOmega A a haRep alpha halpha hElliptic f)) := by
    rw [globalH2SolveCLM, ContinuousLinearMap.comp_apply, higherSolutionOperator_base]
    simp only [higherWeakSolutionBaseCLM, ContinuousLinearMap.comp_apply,
      orderZeroSobolevCLM_base]
  rw [← wkpBaseCoordinateCLM_apply, ← wkpBaseCoordinateCLM_apply, hbase]
  simp [h10SubtypeL_apply]

/-- Restricting the global `H²` solution to `H¹` gives the canonical weak
Dirichlet solution. -/
theorem globalH2SolveCLM_orderOne
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : DerivLp n 2 Omega) :
    lowerOrderCLM
        (n := n) (k := 1) (m := 2) (p := 2) (Ω := Omega)
        (by omega)
        (globalH2SolveCLM hOmega A a haRep haC1
          alpha halpha hElliptic f) =
      h10SubtypeL (n := n) (Ω := Omega)
        (globalH2WeakSolveCLM
          hOmega A a haRep alpha halpha hElliptic f) := by
  apply WkpSpaceOn.ext_of_base_ae hOmega.toC1ExtensionAtlas.isOpen
  simpa [lowerOrderCLM_apply, h10SubtypeL_apply] using
      globalH2SolveCLM_base_ae
        hOmega A a haRep haC1 alpha halpha hElliptic f

/-- A global minimizer of the symmetric divergence-form energy satisfies the
Euler-Lagrange weak equation and is represented by a unique `H²` field. The
representative obeys the same operator-norm estimate as the canonical global
solution.

This combines the generalized Dirichlet principle of Evans's §8.1.2, Example 2, stated
there for smooth minimizers, with the global `H²` theorem. The minimizer is only assumed
to lie in `H¹₀`. -/
theorem existsUnique_global_h2_with_norm_of_energy_minimizer
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hSymmetric : ∀ x ∈ Omega, ∀ i j, a x i j = a x j i)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hmin : ∀ v : H¹₀(Omega),
      variableCoeffEnergy
          (multiplicationCoefficientOperator
            (fun i j ↦
              ((A i j : WkpAmbientOn n 1 ∞ Omega)
                (baseIndex n 1) : DerivLp n ∞ Omega))) f u ≤
        variableCoeffEnergy
          (multiplicationCoefficientOperator
            (fun i j ↦
              ((A i j : WkpAmbientOn n 1 ∞ Omega)
                (baseIndex n 1) : DerivLp n ∞ Omega))) f v) :
    IsWeakDivergenceSolution
        (fun i j ↦
          ((A i j : WkpAmbientOn n 1 ∞ Omega)
            (baseIndex n 1) : DerivLp n ∞ Omega)) f u ∧
      ∃! W : W^{2,2}(Omega),
        lowerOrderCLM
            (n := n) (k := 1) (m := 2) (p := 2) (Ω := Omega)
            (by omega) W =
          h10SubtypeL (n := n) (Ω := Omega) u ∧
        ‖W‖ ≤
          ‖globalH2SolveCLM hOmega A a haRep haC1
            alpha halpha hElliptic‖ * ‖f‖ := by
  have hweak : IsWeakDivergenceSolution (coefficientBase A) f u :=
    (IsWeakDivergenceSolution.energy_minimizer_iff hOmega.toC1ExtensionAtlas.isOpen
      (Fact.out : 0 < n) hOmega.toC1ExtensionAtlas.bounded (coefficientBase A)
      (coefficientBase_aeUniformlyElliptic hOmega.toC1ExtensionAtlas.isOpen.measurableSet
        A a haRep alpha halpha hElliptic)
      (coefficientBase_aeSymmetric hOmega.toC1ExtensionAtlas.isOpen.measurableSet
        A a haRep hSymmetric) f).mp hmin
  have horderOne := globalH2SolveCLM_orderOne hOmega A a haRep haC1 alpha halpha hElliptic f
  rw [← eq_globalH2WeakSolveCLM_of_isWeakDivergenceSolution
    hOmega A a haRep alpha halpha hElliptic f u hweak] at horderOne
  refine ⟨hweak, _, ⟨horderOne,
    (globalH2SolveCLM hOmega A a haRep haC1 alpha halpha hElliptic).le_opNorm f⟩, fun Z hZ ↦ ?_⟩
  apply wkpBaseCoordinateCLM_injective hOmega.toC1ExtensionAtlas.isOpen
  simpa [lowerOrderCLM_apply] using congrArg
    (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)) (hZ.1.trans horderOne.symm)

/-- Apply the global elliptic `H²` solution operator pointwise to a
Bochner-`L²` family.  Continuity of the spatial operator supplies both strong
measurability and square integrability; no measurable choice of pointwise
regularity witnesses is involved. -/
noncomputable def globalH2SolveLpCLM
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    Lp (DerivLp n 2 Omega) 2 μ →L[ℝ]
      Lp (W^{2,2}(Omega)) 2 μ :=
  (globalH2SolveCLM
    hOmega A a haRep haC1 alpha halpha hElliptic).compLpL 2 μ

/-- Almost-everywhere formula for the Bochner lift. -/
theorem globalH2SolveLpCLM_apply_ae
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (F : Lp (DerivLp n 2 Omega) 2 μ) :
    globalH2SolveLpCLM μ hOmega A a haRep haC1
        alpha halpha hElliptic F
      =ᵐ[μ] fun t ↦
        globalH2SolveCLM hOmega A a haRep haC1
          alpha halpha hElliptic (F t) :=
  (globalH2SolveCLM
    hOmega A a haRep haC1 alpha halpha hElliptic).coeFn_compLpL F

/-- The spatial global elliptic estimate integrates directly over any
parameter measure. -/
theorem globalH2SolveLpCLM_norm_le
    {τ : Type*} [MeasurableSpace τ] (μ : Measure τ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (F : Lp (DerivLp n 2 Omega) 2 μ) :
    ‖globalH2SolveLpCLM μ hOmega A a haRep haC1
        alpha halpha hElliptic F‖ ≤
      ‖globalH2SolveCLM hOmega A a haRep haC1
        alpha halpha hElliptic‖ * ‖F‖ :=
  (globalH2SolveCLM
    hOmega A a haRep haC1 alpha halpha hElliptic).norm_compLp_le F

end EvansOperator

end SobolevSpace.GraphSpace.BoundaryRegularity
