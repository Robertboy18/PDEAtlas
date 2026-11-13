/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.ChartCoefficientRegularity
public import PDE.Elliptic.Regularity.Boundary.ZeroTracePullback
public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Elliptic.Regularity.Boundary.H2.NormalFluxRecovery.FlattenedH2
import PDE.Elliptic.Regularity.Boundary.HalfSpaceWeakEquation

/-!
# Applying the flattened half-space `H²` theorem

We join the boundary-chart transport theorem to the half-space estimate `exists_flattened_h2`. The
transformed coefficient and zero-extended forcing are placed in the `L∞` and `L²` spaces used by the
variational theory. No classical derivative is assigned to the weak solution: its gradient remains
the derivative coordinate of `flattenH10`. This is the analogue of steps 1-5 of Evans's proof of
§6.3.2, Theorem 4, applied to the transformed equation as in his step 10.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 1-5 and 10 of the proof of Theorem 4,
  pp. 335-340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- Expanding `principalPairing` under an integral gives the finite sum used
by `IsWeakDivergenceSolution`.  Integrability follows from the `L∞ × L² × L²`
Hölder pairing, not from a formal interchange of potentially nonintegrable
sums. -/
theorem integral_principalPairing_test_eq_sum
    {Omega : Set (ℝ^n)}
    (a : Fin n → Fin n → DerivLp n ∞ Omega)
    (u : H¹₀(Omega)) (phi : TestFunctionOn n Omega) :
    (∫ x,
        principalPairing
          (fun i j ↦ (a i j : ℝ^n → ℝ) x)
          (fun j ↦
            (derivCoordCLM (n := n) (Ω := Omega) j u :
              ℝ^n → ℝ) x)
          (fun i ↦ (∂[i] phi.1.toFun) x)
      ∂domainMeasure n Omega) =
      ∑ i : Fin n, ∑ j : Fin n,
        ∫ x, (a i j : ℝ^n → ℝ) x *
            (derivCoordCLM (n := n) (Ω := Omega) j u :
              ℝ^n → ℝ) x *
            (∂[i] phi.1.toFun) x
          ∂domainMeasure n Omega := by
  classical
  have hterm (i j : Fin n) : Integrable (fun x ↦ (a i j : ℝ^n → ℝ) x *
      (derivCoordCLM (n := n) (Ω := Omega) j u : ℝ^n → ℝ) x * (∂[i] phi.1.toFun) x)
      (domainMeasure n Omega) := by
    refine (L2.integrable_inner (𝕜 := ℝ) (multiplicationCoefficientOperator a i j
      (derivCoordCLM j u)) (derivCoordCLM i (testFunctionToH10 phi))).congr ?_
    filter_upwards [multiplicationCoefficientOperator_apply_ae a i j (derivCoordCLM j u),
      derivCoordCLM_testFunction_apply_ae i phi] with x hcoeff htest
    rw [hcoeff, htest, RCLike.inner_apply, conj_trivial]
    ring
  simp only [principalPairing]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hterm i j]
  exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hterm i j

variable [Fact (0 < n)]

/-- Quantitative chart bounds transport physical ellipticity to the globally
extended coefficient on the upper half-space.  A nonzero target cutoff puts
the point inside the chart target; together with the upper-half-space
condition this places its inverse image in the physical domain. -/
theorem matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt_on_upper
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N) (beta : ℝ)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (Jzero alpha m : ℝ)
    (hJzero : 0 ≤ Jzero) (halpha : 0 ≤ alpha)
    (hbeta : Jzero * alpha * m ^ 2 ≤ beta)
    (hPhysical : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha)
    (hJacobian : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (n := n) (Ω := Omega) i).toFun y ≠ 0 →
      Jzero ≤ inverseChartJacobianWeight (n := n) (hOmega.chart i) y)
    (hGradient : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (n := n) (Ω := Omega) i).toFun y ≠ 0 →
      HasGradientLowerBound
        (chartDerivativeMatrix (n := n) (hOmega.chart i)
          ((hOmega.chart i).symm y)) m) :
    ∀ y ∈ HalfSpace.upper n,
      MatrixEllipticLowerBound
        (extendedFlattenedPrincipalCoefficientAt
          (n := n) hOmega i beta a y)
        (Jzero * alpha * m ^ 2) := by
  intro y hyUpper
  refine matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt (n := n) hOmega i beta
    _ a y hbeta fun hcutoff ↦ ?_
  have hyTarget : y ∈ (hOmega.chart i).target :=
    Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_targetSupportCutoff_subset_target
      (n := n) (Ω := Omega) i (subset_tsupport _ (Function.mem_support.2 hcutoff))
  have hxOmega : (hOmega.chart i).symm y ∈ Omega :=
    (hOmega.chart_mem_iff_upper i _ ((hOmega.chart i).map_target hyTarget)).2
      (by simpa only [(hOmega.chart i).right_inv hyTarget] using hyUpper)
  exact matrixEllipticLowerBound_flattenedAt (n := n) (hOmega.chart i) a y Jzero alpha m hJzero
    (hJacobian y hcutoff) halpha (hPhysical _ hxOmega) (hGradient y hcutoff)

/-- Boundary-chart `H²` application.

Once the globally extended transformed coefficients are `C¹` and uniformly
elliptic, the localized physical weak solution becomes an `H²` field on the
flattened upper half-space.  The hypotheses are stated for the ordinary
representative-level transformed matrix; the `Lp`, variational, and Sobolev
formulations are handled inside the proof. -/
theorem exists_flattenedBoundary_h2_of_extended_coefficients
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (beta : ℝ)
    (hC1 : ∀ k l, ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hOmega i beta
        a y k l))
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ y ∈ HalfSpace.upper n,
      MatrixEllipticLowerBound
        (extendedFlattenedPrincipalCoefficientAt (n := n) hOmega i beta
          a y)
        alpha) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((((Extension.C1.BoundaryPiece.flattenH10 hOmega i u :
              H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) :
                DerivLp n 2 (HalfSpace.upper n))) x) := by
  classical
  let coeff : Fin n → Fin n → DerivLp n ∞ (HalfSpace.upper n) :=
    extendedFlattenedPrincipalCoefficientsLpTop (n := n) hOmega i beta a hC1 (HalfSpace.upper n)
  let uUpper : H¹₀(HalfSpace.upper n) := Extension.C1.BoundaryPiece.flattenH10 hOmega i u
  obtain ⟨forcing, hforcing⟩ :=
    exists_flattenedLocalized_l2_equation_on_upper hOmega i A a haRep f u hu beta
  have hcoeffRep := extendedFlattenedPrincipalCoefficientsLpTop_coe_ae (n := n) hOmega i beta a
    hC1 (HalfSpace.upper n)
  have hcoeffRepAll : ∀ᵐ y ∂domainMeasure n (HalfSpace.upper n), ∀ k l, (coeff k l : ℝ^n → ℝ) y =
      extendedFlattenedPrincipalCoefficientAt (n := n) hOmega i beta a y k l :=
    ae_all_iff.2 fun k ↦ ae_all_iff.2 (hcoeffRep k)
  have hWeakDivergence : IsWeakDivergenceSolution coeff forcing uUpper := by
    refine ⟨HalfSpace.isOpen_upper (n := n), fun phi ↦ ?_⟩
    rw [← integral_principalPairing_test_eq_sum coeff uUpper phi, ← hforcing phi]
    refine integral_congr_ae ?_
    filter_upwards [hcoeffRepAll] with y hy
    simp only [principalPairing, hy]
    rfl
  have hAElliptic : AEUniformlyElliptic coeff alpha := by
    refine ⟨halpha, ?_⟩
    filter_upwards [hcoeffRepAll, ae_restrict_mem (HalfSpace.measurableSet_upper (n := n))]
      with y hy hyUpper xi
    simpa [MatrixEllipticLowerBound, dotProduct, principalEnergy, pow_two, hy, mul_comm,
      mul_left_comm, mul_assoc] using hElliptic y hyUpper xi
  obtain ⟨W, hWBase⟩ := exists_flattened_h2 coeff _ _
    (lipschitzWith_extendedFlattenedPrincipalCoefficient_entries (n := n) hOmega i beta a hC1)
    hcoeffRep hAElliptic halpha forcing uUpper
    ((isWeakSolution_iff_isWeakDivergenceSolution hWeakDivergence.isOpen coeff forcing
      uUpper).2 hWeakDivergence)
  exact ⟨W, by simpa [baseRepresentative, uUpper] using hWBase⟩

/-- The chart application with ellipticity discharged from the standard
physical and geometric hypotheses.  This is the form used by the global
boundary regularity proof: positive lower bounds for the inverse Jacobian and
the chart derivative's least singular value produce the flattened
ellipticity constant `Jzero * alpha * m²`. -/
theorem exists_flattenedBoundary_h2_of_chart_bounds
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (beta Jzero alpha m : ℝ)
    (hTransformedC1 : ∀ k l, ContDiffOn ℝ 1
      (fun y ↦ flattenedPrincipalCoefficientAt
        (n := n) (hOmega.chart i) a y k l)
      (hOmega.chart i).target)
    (hJzero : 0 < Jzero) (halpha : 0 < alpha) (hm : 0 < m)
    (hbeta : Jzero * alpha * m ^ 2 ≤ beta)
    (hPhysical : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha)
    (hJacobian : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (n := n) (Ω := Omega) i).toFun y ≠ 0 →
      Jzero ≤ inverseChartJacobianWeight (n := n) (hOmega.chart i) y)
    (hGradient : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (n := n) (Ω := Omega) i).toFun y ≠ 0 →
      HasGradientLowerBound
        (chartDerivativeMatrix (n := n) (hOmega.chart i)
          ((hOmega.chart i).symm y)) m) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((((Extension.C1.BoundaryPiece.flattenH10 hOmega i u :
              H¹(HalfSpace.upper n)) :
                WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) :
                DerivLp n 2 (HalfSpace.upper n))) x) := by
  exact exists_flattenedBoundary_h2_of_extended_coefficients hOmega i A a haRep f u hu beta
    (fun k l ↦ contDiff_extendedFlattenedPrincipalCoefficientAt hOmega i beta a k l
      (hTransformedC1 k l)) (by positivity)
    (matrixEllipticLowerBound_extendedFlattenedPrincipalCoefficientAt_on_upper hOmega i beta a
      Jzero alpha m hJzero.le halpha.le hbeta hPhysical hJacobian hGradient)

/-- Local boundary `H²` conclusion under the assumptions of Evans's §6.3.2,
Theorem 4: a `C²` boundary and `C¹` principal coefficients.  Compared with
`exists_flattenedBoundary_h2_of_chart_bounds`, the transformed
coefficient regularity is not an external hypothesis; it is derived
from the chart calculus. -/
theorem exists_flattenedBoundary_h2_of_c2_boundary_atlas_with_bounds
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (haC1 : ∀ r s, ContDiff ℝ 1 (fun x ↦ a x r s))
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (beta Jzero alpha m : ℝ)
    (hJzero : 0 < Jzero) (halpha : 0 < alpha) (hm : 0 < m)
    (hbeta : Jzero * alpha * m ^ 2 ≤ beta)
    (hPhysical : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha)
    (hJacobian : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (hΩ := hOmega.toC1ExtensionAtlas) i).toFun y ≠ 0 →
      Jzero ≤ inverseChartJacobianWeight
        (n := n) (hOmega.toC1ExtensionAtlas.chart i) y)
    (hGradient : ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (hΩ := hOmega.toC1ExtensionAtlas) i).toFun y ≠ 0 →
      HasGradientLowerBound
        (chartDerivativeMatrix (n := n) (hOmega.toC1ExtensionAtlas.chart i)
          ((hOmega.toC1ExtensionAtlas.chart i).symm y)) m) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((((Extension.C1.BoundaryPiece.flattenH10
              hOmega.toC1ExtensionAtlas i u :
                H¹(HalfSpace.upper n)) :
                  WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) :
                DerivLp n 2 (HalfSpace.upper n))) x) := by
  apply exists_flattenedBoundary_h2_of_chart_bounds
    hOmega.toC1ExtensionAtlas i A a haRep f u hu beta Jzero alpha m
    (fun k l ↦
      contDiffOn_flattenedPrincipalCoefficientAt_of_c2BoundaryAtlas
        hOmega a haC1 i k l)
    hJzero halpha hm hbeta hPhysical hJacobian hGradient

/-- Local boundary `H²` conclusion.

For a `C²` boundary and `C¹` principal coefficients, a localized weak
solution pulls forward to an `H²` function on the flat half-space.  The
positive Jacobian and least-singular-value bounds are consequences of the
compactly supported chart cutoff, so they do not appear in the public
statement. -/
theorem exists_flattenedBoundary_h2_of_c2_boundary_atlas
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N)
    (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ r s,
      ((((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n
          Omega] fun x ↦ a x r s)
    (haC1 : ∀ r s, ContDiff ℝ 1 (fun x ↦ a x r s))
    (f : DerivLp n 2 Omega)
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun r s ↦ ((A r s : WkpAmbientOn n 1 ∞ Omega)
        (baseIndex n 1) : DerivLp n ∞ Omega)) f u)
    (alpha : ℝ) (halpha : 0 < alpha)
    (hPhysical : ∀ x ∈ Omega,
      MatrixEllipticLowerBound (a x) alpha) :
    ∃ W : W^{2,2}(HalfSpace.upper n),
      baseRepresentative W =ᵐ[domainMeasure n (HalfSpace.upper n)]
        (fun x ↦
          ⇑((((Extension.C1.BoundaryPiece.flattenH10
              hOmega.toC1ExtensionAtlas i u :
                H¹(HalfSpace.upper n)) :
                  WkpAmbientOn n 1 2 (HalfSpace.upper n))
              (baseIndex n 1) :
                DerivLp n 2 (HalfSpace.upper n))) x) := by
  obtain ⟨Jzero, hJzero, hJacobian⟩ :=
    exists_inverseChartJacobianWeight_lowerBound_on_cutoff hOmega i
  obtain ⟨m, hm, hGradient⟩ := exists_gradientLowerBound_on_cutoff hOmega i
  exact exists_flattenedBoundary_h2_of_c2_boundary_atlas_with_bounds hOmega i A a haRep haC1 f u
    hu _ Jzero alpha m hJzero halpha hm le_rfl hPhysical hJacobian hGradient

end SobolevSpace.GraphSpace.BoundaryRegularity
