/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.GradientDensity
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Linearization
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.MeasurableCoefficients
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Linear elliptic equations for the weak gradient

For an autonomous uniformly convex `C²` density with bounded Hessian, an
`H¹` Euler–Lagrange solution first acquires interior `H²` regularity. Its
first derivatives then satisfy uniformly elliptic linear divergence equations
with the measurable coefficients `D(∇L)(Du)`.

The source is `H¹`. Both its differentiated scalar form and the divergence
forcing `-f eₖ` are derived. The solution has no prescribed continuous gradient
representative. This supplies the measurable linear equations at the start of
the higher nonlinear regularity argument in Evans §8.3.2.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- An `H¹` Euler–Lagrange solution has an interior `H²` representative
whose first derivatives solve uniformly elliptic measurable-coefficient
equations. The coefficient bounds, their identification with the Hessian at
the weak gradient, and both forms of the differentiated equation are derived.
There is no assumed regularity of the gradient beyond its original `L²` class. -/
theorem exists_interior_linearizedEquations_of_gradientDensity
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 2 L)
    {Λ : ℝ≥0} (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpositive : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u F : H¹(Ω))
    (hweak : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) =
        ∫ x, wkpBaseCoordinateCLM F x * baseCoordCLM v x ∂domainMeasure n Ω) :
    ∃ W : W^{2,2}(V), ∃ B : Fin n → Fin n → DerivLp n ∞ V,
      lowerOrderCLM (by omega : 1 ≤ 2) W =
        restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
      (∀ i j, (B i j : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
        fun x ↦ jacobianMatrix (∇ L)
          (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) i j) ∧
      (∀ i j, ‖B i j‖ ≤ Λ) ∧ AEUniformlyElliptic B θ ∧
      (∀ k, IsInteriorWeakDivergenceSolution B
        (wkpCoordinateCLM (singleDerivIndex n k)
          (restrictCLM hV.measurableSet (subset_closure.trans hVΩ) F)) (∂[k] W)) ∧
      ∀ k (v : H¹₀(V)),
        interiorVariableCoeffForm (multiplicationCoefficientOperator B) (∂[k] W) v =
          -⟪restrictDerivLp (subset_closure.trans hVΩ) (wkpBaseCoordinateCLM F),
            derivCoordCLM k v⟫ := by
  let hsub : V ⊆ Ω := subset_closure.trans hVΩ
  have hLip := lipschitzWith_gradient_of_hessian_bound hL hbound
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hbounded hLip u
  have hweakq (v : H¹₀(Ω)) :
      (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪wkpBaseCoordinateCLM F, baseCoordCLM v⟫ := by
    rw [← (hpair v).2, hweak v, L2.inner_def]
    exact integral_congr_ae (.of_forall fun x ↦
      mul_comm (wkpBaseCoordinateCLM F x) (baseCoordCLM v x))
  obtain ⟨K, hK, hreg⟩ :=
    exists_interior_H2_of_gradientDensity hΩ hbounded hV hVc hVΩ hθ Λ
  obtain ⟨W, hW, _hnorm, _hsecond, _hint⟩ :=
    hreg L hL hbound hpositive u (wkpBaseCoordinateCLM F) hweak
  let FV : H¹(V) := restrictCLM hV.measurableSet hsub F
  let qV (i : Fin n) : DerivLp n 2 V := restrictDerivLp hsub (q i)
  have hweakV (v : H¹₀(V)) :
      (∑ i, ⟪qV i, derivCoordCLM i v⟫) = ⟪wkpBaseCoordinateCLM FV, baseCoordCLM v⟫ := by
    let vΩ := ZeroTrace.zeroExtendH10ToSuperset hV hΩ hsub v
    calc
      _ = ∑ i, ⟪q i, derivCoordCLM i vΩ⟫ := Finset.sum_congr rfl fun i _ ↦
        (ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
          hV hΩ hsub (q i) v (singleDerivIndex n i)).symm
      _ = ⟪wkpBaseCoordinateCLM F, baseCoordCLM vΩ⟫ := hweakq vΩ
      _ = _ := ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
        hV hΩ hsub (wkpBaseCoordinateCLM F) v (baseIndex n 1)
  have hgrad :
      (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n V] ∇ u := by
    rw [hW]
    have hrows := ae_all_iff.mpr fun i ↦
      restrictCLM_apply_ae hV.measurableSet hsub u (singleDerivIndex n i)
    filter_upwards [wkpGradientCLM_apply_ae (restrictCLM hV.measurableSet hsub u),
      ae_mono (domainMeasure_le hsub) (wkpGradientCLM_apply_ae u), hrows]
      with x hsmall hbig hrow
    exact PiLp.ext fun i ↦ (hsmall i).trans ((hrow i).trans (hbig i).symm)
  have hqV : ∀ᵐ x ∂domainMeasure n V,
      ∇ L (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W) x) = Lp.euclideanTuple qV x := by
    have hrestrict := ae_all_iff.mpr fun i ↦ restrictDerivLp_apply_ae hsub (q i)
    filter_upwards [hgrad, ae_mono (domainMeasure_le hsub) hq,
      ae_mono (domainMeasure_le hsub) (Lp.euclideanTuple_apply_ae q),
      Lp.euclideanTuple_apply_ae qV, hrestrict] with x hx hqx htuple htupleV hres
    rw [hx, hqx]
    exact PiLp.ext fun i ↦ (htuple i).trans ((hres i).symm.trans (htupleV i).symm)
  obtain ⟨B, hBrep, hBbound, hB⟩ :=
    exists_measurable_linearizedCoefficients_of_gradientDensity hL hbound hθ hpositive
      (Lp.aestronglyMeasurable (∇ (lowerOrderCLM (by omega : 1 ≤ 2) W)))
  have heq (k : Fin n) := isInteriorWeakDivergenceSolution_linearized hV
    (hbounded.subset hsub) (contDiff_gradient_of_contDiff_two hL) hLip W FV qV hqV hweakV
    Filter.EventuallyEq.rfl B hBrep k
  refine ⟨W, B, hW, hBrep, hBbound, hB, heq, ?_⟩
  intro k v
  have hF : HasWeakDerivativeOn V [k]
      (wkpBaseCoordinateCLM FV) (wkpCoordinateCLM (singleDerivIndex n k) FV) := by
    simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply] using
      FV.property.hasWeakDerivativeOn_first (by norm_num) k
  have hparts := weakDerivative_integrationByParts_H10 k
    (wkpBaseCoordinateCLM FV) (wkpCoordinateCLM (singleDerivIndex n k) FV) hF v
  rw [(heq k).2]
  exact neg_eq_iff_eq_neg.mpr hparts |>.symm

end PDE.Elliptic.Regularity.Quasilinear
