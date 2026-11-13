/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import PDE.Elliptic.Regularity.Boundary.ChartCoefficients
public import PDE.Elliptic.Regularity.Boundary.Domain
import Mathlib.Analysis.Calculus.Deriv.Abs
import PDE.Elliptic.Regularity.Boundary.ChartWeakEquation
public import PDE.Spaces.Sobolev.Calculus.Composition.Reciprocal -- shake: keep

/-!
# Regularity of globally extended boundary-chart coefficients

Our boundary `H²` argument applies the whole-half-space theorem `exists_flattened_h2` to
coefficients that agree with the transformed physical coefficients on the chart core and with a
constant elliptic matrix away from a compact target patch. We turn the classical `C¹` regularity of
these coefficients into the global Lipschitz and Sobolev coefficient data that `exists_flattened_h2`
requires. Evans instead works on a half-ball inside the image of the chart, in steps 7-9 of the
proof of §6.3.2, Theorem 4, and needs no extension; at the end of step 9 he observes that the
transformed coefficients are `C¹` because the chart and its inverse are `C²`.

The coefficient extension uses the canonical smooth cutoff, whose construction proves that its
values lie in `[0, 1]`. Thus the extension is a smooth convex gluing, with no nonsmooth clipping
operation in its definition.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, steps 7-9 of the proof of Theorem 4, (58)-(70),
  pp. 338-340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal InnerProduct

variable {n : ℕ}

/-- A smooth compactly supported multiplier globalizes a `C^m` function
defined on an open neighborhood of its support.  Outside that neighborhood
the multiplier vanishes in a neighborhood, so no regularity of `f` is used
there. -/
theorem contDiff_mul_testFunction_of_contDiffOn
    {m : ℕ∞} (eta : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) {U : Set (ℝ^n)}
    (hU : IsOpen U) (hetaU : tsupport eta.toFun ⊆ U)
    (f : ℝ^n → ℝ) (hf : ContDiffOn ℝ m f U) :
    ContDiff ℝ m (fun x ↦ eta.toFun x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact (eta.contDiff.of_le (by simp)).contDiffAt.mul
      (hf.contDiffAt (hU.mem_nhds hx))
  · have hxSupport : x ∉ tsupport eta.toFun := fun h ↦ hx (hetaU h)
    have hetaZero : eta.toFun =ᶠ[nhds x] 0 :=
      (notMem_tsupport_iff_eventuallyEq).1 hxSupport
    have hproductZero : (fun y ↦ eta.toFun y * f y) =ᶠ[nhds x]
        fun _ ↦ (0 : ℝ) := by
      filter_upwards [hetaZero] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hproductZero

/-- A first derivative entry of a `C^{m+1}` chart, evaluated along a `C^m`
inverse chart, is `C^m`.  This is the componentwise chart regularity used
in transformed principal coefficients. -/
theorem contDiff_chartDerivativeMatrix_comp_symm
    {m : ℕ}
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ (m + 1) (fun x ↦ E x))
    (hSymm : ContDiff ℝ m (fun y ↦ E.symm y))
    (r k : Fin n) :
    ContDiff ℝ m
      (fun y ↦ chartDerivativeMatrix (n := n) E (E.symm y) r k) := by
  have hfderiv : ContDiff ℝ m (fderiv ℝ (fun x ↦ E x)) := hE.fderiv_right (by simp)
  rw [funext fun y ↦ chartDerivativeMatrix_eq_fderiv_apply E (hE.of_le (by simp)) (E.symm y) r k]
  exact ((PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n ↦ ℝ) k).contDiff.comp
    (hfderiv.clm_apply (contDiff_const (c := EuclideanSpace.single r (1 : ℝ))))).comp hSymm


/-- The determinant of the Fréchet derivative of a `C^{m+1}` Euclidean map
is `C^m`. -/
theorem contDiff_det_fderiv
    {m : ℕ} (f : ℝ^n → ℝ^n)
    (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun x ↦ (fderiv ℝ f x).det) := by
  classical
  have hfderiv : ContDiff ℝ m (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hentry (i j : Fin n) :
      ContDiff ℝ m (fun x ↦ ((fderiv ℝ f x) (EuclideanSpace.single j (1 : ℝ))) i) :=
    (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin n ↦ ℝ) i).contDiff.comp
      (hfderiv.clm_apply (contDiff_const (c := EuclideanSpace.single j (1 : ℝ))))
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmatrix : ContDiff ℝ m (fun x ↦
      (LinearMap.toMatrix b b ((fderiv ℝ f x : ℝ^n →L[ℝ] ℝ^n) : ℝ^n →ₗ[ℝ] ℝ^n)).det) := by
    simp_rw [Matrix.det_apply']
    refine ContDiff.sum fun sigma _ ↦ contDiff_const.mul (contDiff_prod fun j _ ↦ ?_)
    simpa [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using hentry (sigma j) j
  simpa only [LinearMap.det_toMatrix] using hmatrix


/-- Multiplication by the chart derivative matrix is the Hilbert-space
adjoint of its Fréchet derivative. This identifies the coordinate formula
used by the PDE layer with the operator-norm calculus used for quantitative
chart bounds. -/
theorem mulVec_chartDerivativeMatrix_eq_adjoint
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (x : ℝ^n) (eta : ℝ^n) (i : Fin n) :
    Matrix.mulVec (chartDerivativeMatrix (n := n) E x) eta i =
      ((fderiv ℝ (fun z ↦ E z) x)†) eta i := by
  rw [← EuclideanSpace.inner_basisFun_real (i := i)
    (x := ((fderiv ℝ (fun z ↦ E z) x)†) eta)]
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [Matrix.mulVec, PiLp.inner_apply,
    EuclideanSpace.basisFun_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro k _
  change chartDerivativeMatrix (n := n) E x i k * eta.ofLp k = _
  rw [chartDerivativeMatrix_eq_fderiv_apply E hE x i k]

/-- At a target point, the derivative of a `C¹` chart at the inverse point composed with the
derivative of its `C¹` inverse is the identity. -/
private theorem fderiv_comp_fderiv_symm_eq_id
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) :
    (fderiv ℝ (fun z ↦ E z) (E.symm y)).comp (fderiv ℝ (fun z ↦ E.symm z) y) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  have hround : id =ᶠ[nhds y] fun z ↦ E (E.symm z) :=
    Filter.eventually_of_mem (E.open_target.mem_nhds hy) fun z hz ↦ (E.right_inv hz).symm
  exact ((((hE.differentiable (by norm_num) _).hasFDerivAt).comp y
    (hSymm.differentiable (by norm_num) y).hasFDerivAt).congr_of_eventuallyEq hround).unique
    (hasFDerivAt_id y)

/-- At a target point, the Jacobian determinants of a `C¹` chart and of its `C¹` inverse
multiply to one. -/
private theorem det_fderiv_mul_det_fderiv_symm
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x)) (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) :
    (fderiv ℝ (fun z ↦ E z) (E.symm y)).det * (fderiv ℝ (fun z ↦ E.symm z) y).det = 1 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ← LinearMap.det_comp,
    ← ContinuousLinearMap.toLinearMap_comp, fderiv_comp_fderiv_symm_eq_id E hE hSymm hy]
  simp

/-- A pointwise operator-norm bound for the inverse chart derivative gives
the exact lower singular-value estimate used by transformed ellipticity. -/
theorem hasGradientLowerBound_of_inverseDerivative_norm_le
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) {C : ℝ}
    (hC : 0 < C)
    (hBound : ‖fderiv ℝ (fun z ↦ E.symm z) y‖ ≤ C) :
    HasGradientLowerBound
      (chartDerivativeMatrix (n := n) E (E.symm y)) C⁻¹ := by
  let A : ℝ^n →L[ℝ] ℝ^n := fderiv ℝ (fun z ↦ E z) (E.symm y)
  let B : ℝ^n →L[ℝ] ℝ^n := fderiv ℝ (fun z ↦ E.symm z) y
  intro eta
  let etaE : ℝ^n := WithLp.toLp 2 eta
  have hinverseAdjoint : (B†) ((A†) etaE) = etaE := by
    simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg (fun L : ℝ^n →L[ℝ] ℝ^n ↦ (L†) etaE) (fderiv_comp_fderiv_symm_eq_id E hE hSymm hy)
  have hscaled : C⁻¹ * ‖etaE‖ ≤ ‖(A†) etaE‖ := by
    rw [inv_mul_le_iff₀ hC]
    calc ‖etaE‖ = ‖(B†) ((A†) etaE)‖ := by rw [hinverseAdjoint]
      _ ≤ ‖B‖ * ‖(A†) etaE‖ := by simpa using (B†).le_opNorm ((A†) etaE)
      _ ≤ C * ‖(A†) etaE‖ := by gcongr
  have hgradient : Matrix.mulVec (chartDerivativeMatrix (n := n) E (E.symm y)) eta =
      fun i ↦ ((A†) etaE) i := funext fun i ↦ by
    simpa [etaE, PiLp.toLp_apply] using
      mulVec_chartDerivativeMatrix_eq_adjoint E hE (E.symm y) etaE i
  have hetaNorm : ‖etaE‖ ^ 2 = eta ⬝ᵥ eta := by
    simpa [dotProduct, pow_two, etaE, PiLp.toLp_apply] using EuclideanSpace.real_norm_sq_eq etaE
  rw [hgradient]
  calc C⁻¹ ^ 2 * (eta ⬝ᵥ eta) = (C⁻¹ * ‖etaE‖) ^ 2 := by rw [mul_pow, hetaNorm]
    _ ≤ ‖(A†) etaE‖ ^ 2 := by gcongr
    _ = _ := by simpa [dotProduct, pow_two] using EuclideanSpace.real_norm_sq_eq ((A†) etaE)


/-- The Jacobian weight of a `C¹` chart inverse is strictly positive on the
chart target.  This is the differential form of local invertibility used in
the compact-minimum argument below. -/
theorem inverseChartJacobianWeight_pos_on_target
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) :
    0 < inverseChartJacobianWeight (n := n) E y := by
  exact abs_pos.mpr (right_ne_zero_of_mul_eq_one (det_fderiv_mul_det_fderiv_symm E hE hSymm hy))


/-- On the chart target, the inverse-chart Jacobian weight is the reciprocal
of the absolute forward-chart Jacobian evaluated at the inverse point. -/
theorem inverseChartJacobianWeight_eq_forwardJacobianWeight_inv
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    {y : ℝ^n} (hy : y ∈ E.target) :
    inverseChartJacobianWeight (n := n) E y =
      |(fderiv ℝ (fun z ↦ E z) (E.symm y)).det|⁻¹ := by
  simp [inverseChartJacobianWeight, abs_inv,
    eq_inv_of_mul_eq_one_right (det_fderiv_mul_det_fderiv_symm E hE hSymm hy)]


/-- The inverse-chart Jacobian weight is `C¹` on the chart target when the
inverse chart is `C²`.  The absolute value is harmless there because the
derivative of a local inverse is nonsingular at every target point. -/
theorem contDiffOn_inverseChartJacobianWeight
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y)) :
    ContDiffOn ℝ 1 (inverseChartJacobianWeight (n := n) E) E.target := by
  refine (contDiff_det_fderiv (m := 1) _ hSymm).contDiffOn.abs fun y hy ↦ ?_
  exact abs_pos.mp (inverseChartJacobianWeight_pos_on_target E hE (hSymm.of_le (by norm_num)) hy)


/-- The inverse-chart Jacobian weight has the regularity `C^m` of the inverse chart, for every
finite order `m` (`m = 0` included), when the forward chart is `C^{m+1}` and the inverse chart is
also `C¹`. -/
theorem contDiffOn_inverseChartJacobianWeight_of_succ_of_contDiff_one
    {m : ℕ}
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ (m + 1) (fun x ↦ E x))
    (hSymm : ContDiff ℝ m (fun y ↦ E.symm y))
    (hSymmOne : ContDiff ℝ 1 (fun y ↦ E.symm y)) :
    ContDiffOn ℝ m (inverseChartJacobianWeight (n := n) E) E.target := by
  have hEone : ContDiff ℝ 1 (fun x ↦ E x) := hE.of_le (by simp)
  have hne (x : ℝ^n) (hx : x ∈ E.source) : (fderiv ℝ (fun z ↦ E z) x).det ≠ 0 :=
    abs_pos.mp (by simpa [inverseChartJacobianWeight] using
      inverseChartJacobianWeight_pos_on_target (n := n) E.symm hSymmOne (by simpa using hEone) hx)
  refine ((((contDiff_det_fderiv _ hE).contDiffOn.abs hne).inv fun x hx ↦
    abs_ne_zero.mpr (hne x hx)).comp hSymm.contDiffOn E.mapsTo_symm).congr fun y hy ↦ ?_
  exact inverseChartJacobianWeight_eq_forwardJacobianWeight_inv E hEone hSymmOne hy

/--
The inverse-chart Jacobian weight has the same positive finite regularity as
the inverse chart when the forward chart has one additional derivative.

Rewriting the weight as the reciprocal of the forward Jacobian avoids taking
one extra derivative of the inverse chart.
-/
theorem contDiffOn_inverseChartJacobianWeight_of_succ
    {m : ℕ}
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ (m + 1) (fun x ↦ E x))
    (hSymm : ContDiff ℝ m (fun y ↦ E.symm y))
    (hm : 0 < m) :
    ContDiffOn ℝ m (inverseChartJacobianWeight (n := n) E) E.target :=
  contDiffOn_inverseChartJacobianWeight_of_succ_of_contDiff_one E hE hSymm
    (hSymm.of_le (by exact_mod_cast hm))



/-- The inverse Jacobian has a uniform positive lower bound wherever the
canonical target cutoff is nonzero.  No numerical chart constant is part of
the domain structure: it is obtained from compactness of the cutoff support. -/
theorem exists_inverseChartJacobianWeight_lowerBound_on_cutoff
    [Fact (0 < n)] {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N) :
    ∃ Jzero : ℝ, 0 < Jzero ∧ ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (hΩ := hOmega.toC1ExtensionAtlas) i).toFun y ≠ 0 →
      Jzero ≤ inverseChartJacobianWeight
        (n := n) (hOmega.toC1ExtensionAtlas.chart i) y := by
  let K := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport
    (hΩ := hOmega.toC1ExtensionAtlas) i
  let J : ℝ^n → ℝ := inverseChartJacobianWeight (n := n) (hOmega.toC1ExtensionAtlas.chart i)
  have hJ : Continuous J := (ContinuousLinearMap.continuous_det.comp
    ((hOmega.toC1ExtensionAtlas.chart_symm_contDiff i).continuous_fderiv (by norm_num))).abs
  rcases K.eq_empty_or_nonempty with hK | hK
  · exact ⟨1, one_pos, fun y hy ↦
      (Set.eq_empty_iff_forall_notMem.1 hK y (subset_tsupport _ hy)).elim⟩
  obtain ⟨y0, hy0, hmin⟩ :=
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_targetCutoffSupport
      (hΩ := hOmega.toC1ExtensionAtlas) i).exists_isMinOn hK hJ.continuousOn
  refine ⟨J y0, inverseChartJacobianWeight_pos_on_target _
    ((hOmega.chart_contDiff_two i).of_le (by norm_num))
    ((hOmega.chart_symm_contDiff_two i).of_le (by norm_num))
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport_subset_target
      (hΩ := hOmega.toC1ExtensionAtlas) i hy0), fun y hy ↦ hmin (subset_tsupport _ hy)⟩


/-- The chart derivative has a uniform positive lower singular-value bound
wherever the canonical target cutoff is nonzero.  The constant is the inverse
of a compact upper bound for the inverse derivative's operator norm. -/
theorem exists_gradientLowerBound_on_cutoff
    [Fact (0 < n)] {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (i : Fin hOmega.toC1ExtensionAtlas.N) :
    ∃ m : ℝ, 0 < m ∧ ∀ y,
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (hΩ := hOmega.toC1ExtensionAtlas) i).toFun y ≠ 0 →
      HasGradientLowerBound
        (chartDerivativeMatrix (n := n) (hOmega.toC1ExtensionAtlas.chart i)
          ((hOmega.toC1ExtensionAtlas.chart i).symm y)) m := by
  let E := hOmega.toC1ExtensionAtlas.chart i
  have hB : Continuous fun y ↦ fderiv ℝ (fun z ↦ E.symm z) y :=
    (hOmega.toC1ExtensionAtlas.chart_symm_contDiff i).continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := (Boundary.C1ExtensionAtlas.DerivedCutoffs.isCompact_targetCutoffSupport
    (hΩ := hOmega.toC1ExtensionAtlas) i).exists_bound_of_continuousOn hB.continuousOn
  have hC1 : 0 < max C 1 := lt_max_of_lt_right one_pos
  refine ⟨(max C 1)⁻¹, inv_pos.mpr hC1, fun y hy ↦ ?_⟩
  exact hasGradientLowerBound_of_inverseDerivative_norm_le E
    ((hOmega.chart_contDiff_two i).of_le (by norm_num))
    ((hOmega.chart_symm_contDiff_two i).of_le (by norm_num))
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetCutoffSupport_subset_target
      (hΩ := hOmega.toC1ExtensionAtlas) i (subset_tsupport _ hy)) hC1
    ((hC y (subset_tsupport _ hy)).trans (le_max_left _ _))


/-- Componentwise `C^m` chart data imply `C^m` regularity of every transformed
principal coefficient.  The Jacobian assumption is local because the
absolute determinant is smooth precisely where the chart derivative is
nonsingular. -/
theorem contDiffOn_flattenedPrincipalCoefficientAt_of_components
    {m : ℕ∞} (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (a : ℝ^n → Fin n → Fin n → ℝ) {U : Set (ℝ^n)}
    (hJ : ContDiffOn ℝ m
      (inverseChartJacobianWeight (n := n) E) U)
    (hD : ∀ r k, ContDiffOn ℝ m
      (fun y ↦ chartDerivativeMatrix (n := n) E (E.symm y) r k) U)
    (hSymm : ContDiff ℝ m (fun y ↦ E.symm y))
    (ha : ∀ r s, ContDiff ℝ m (fun x ↦ a x r s))
    (k l : Fin n) :
    ContDiffOn ℝ m
      (fun y ↦ flattenedPrincipalCoefficientAt (n := n) E a y k l) U := by
  simpa [flattenedPrincipalCoefficientAt, flattenedPrincipalCoefficient] using
    hJ.mul (ContDiffOn.sum fun r _ ↦ ContDiffOn.sum fun s _ ↦
      ((hD r k).mul ((ha r s).comp hSymm).contDiffOn).mul (hD s l))


/-- On a `C²` domain, a globally `C¹` physical coefficient field has `C¹`
flattened coefficients on every boundary-chart target. Thus the regularity
hypothesis of the half-space theorem follows from `C¹` coefficients and a
`C²` boundary, as at the end of step 9 of Evans's proof of §6.3.2, Theorem 4. -/
theorem contDiffOn_flattenedPrincipalCoefficientAt_of_c2BoundaryAtlas
    [Fact (0 < n)] {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ r s, ContDiff ℝ 1 (fun x ↦ a x r s))
    (i : Fin hOmega.toC1ExtensionAtlas.N) (k l : Fin n) :
    ContDiffOn ℝ 1
      (fun y ↦ flattenedPrincipalCoefficientAt
        (n := n) (hOmega.toC1ExtensionAtlas.chart i) a y k l)
      (hOmega.toC1ExtensionAtlas.chart i).target := by
  apply contDiffOn_flattenedPrincipalCoefficientAt_of_components
    (hJ := contDiffOn_inverseChartJacobianWeight
      (hOmega.toC1ExtensionAtlas.chart i)
      ((hOmega.chart_contDiff_two i).of_le (by norm_num))
      (hOmega.chart_symm_contDiff_two i))
    (hD := fun r k ↦
      (contDiff_chartDerivativeMatrix_comp_symm
        (hOmega.toC1ExtensionAtlas.chart i)
        (hOmega.chart_contDiff_two i)
        ((hOmega.chart_symm_contDiff_two i).of_le (by norm_num)) r k).contDiffOn)
    (hSymm := (hOmega.chart_symm_contDiff_two i).of_le (by norm_num))
    (ha := ha)

/-- A `C^{m+1}` forward chart, `C^m` inverse chart, and `C^m` physical
coefficient field give `C^m` transformed principal coefficients for every
finite order. -/
theorem contDiffOn_flattenedPrincipalCoefficientAt_of_chartRegularity
    [Fact (0 < n)] {m : ℕ} {Omega : Set (ℝ^n)}
    (hOmega : Boundary.C1ExtensionAtlas n Omega)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ r s, ContDiff ℝ m (fun x ↦ a x r s))
    (i : Fin hOmega.N)
    (hChart : ContDiff ℝ (m + 1) (fun x ↦ hOmega.chart i x))
    (hChartSymm : ContDiff ℝ m (fun y ↦ (hOmega.chart i).symm y))
    (k l : Fin n) :
    ContDiffOn ℝ m
      (fun y ↦ flattenedPrincipalCoefficientAt
        (n := n) (hOmega.chart i) a y k l)
      (hOmega.chart i).target := by
  apply contDiffOn_flattenedPrincipalCoefficientAt_of_components
    (hJ := contDiffOn_inverseChartJacobianWeight_of_succ_of_contDiff_one
      (hOmega.chart i) hChart hChartSymm (hOmega.chart_symm_contDiff i))
    (hD := fun r j ↦
      (contDiff_chartDerivativeMatrix_comp_symm
        (hOmega.chart i) hChart hChartSymm r j).contDiffOn)
    (hSymm := hChartSymm)
    (ha := ha)

/-- Local `C^m` regularity of a transformed coefficient on the chart target
implies global `C^m` regularity of its smooth extension by `beta I`. The
extension replaces the restriction to a half-ball in step 7 of Evans's proof
of §6.3.2, Theorem 4. -/
theorem contDiff_extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {m : ℕ∞} {Omega : Set (ℝ^n)}
    (hOmega : Boundary.C1ExtensionAtlas n Omega) (i : Fin hOmega.N)
    (beta : ℝ) (a : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hlocal : ContDiffOn ℝ m
      (fun y ↦ flattenedPrincipalCoefficientAt
        (n := n) (hOmega.chart i) a y k l)
      (hOmega.chart i).target) :
    ContDiff ℝ m (fun y ↦
      extendedFlattenedPrincipalCoefficientAt
        (n := n) hOmega i beta a y k l) := by
  let eta := Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff (n := n) (Ω := Omega) i
  let c : ℝ := scalarIdentityMatrix (n := n) beta k l
  convert (contDiff_const (c := c)).add (contDiff_mul_testFunction_of_contDiffOn eta
    (hOmega.chart i).open_target
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.tsupport_targetSupportCutoff_subset_target
      (n := n) (Ω := Omega) i) _ (hlocal.sub (contDiffOn_const (c := c)))) using 1
  funext y
  simp only [extendedFlattenedPrincipalCoefficientAt, glueCoefficientField, glueToScalarIdentity,
    eta, c]
  ring


/-- The smoothly glued transformed coefficient retains every finite order of the physical
coefficients and the chart pair. -/
theorem contDiff_extendedFlattenedPrincipalCoefficientAt_of_chartRegularity
    [Fact (0 < n)] {m : ℕ} {Omega : Set (ℝ^n)}
    (hOmega : Boundary.C1ExtensionAtlas n Omega)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ r s, ContDiff ℝ m (fun x ↦ a x r s))
    (i : Fin hOmega.N)
    (hChart : ContDiff ℝ (m + 1) (fun x ↦ hOmega.chart i x))
    (hChartSymm : ContDiff ℝ m (fun y ↦ (hOmega.chart i).symm y))
    (beta : ℝ) (k l : Fin n) :
    ContDiff ℝ m (fun y ↦
      extendedFlattenedPrincipalCoefficientAt
        (n := n) hOmega i beta a y k l) := by
  apply contDiff_extendedFlattenedPrincipalCoefficientAt
  exact contDiffOn_flattenedPrincipalCoefficientAt_of_chartRegularity
    hOmega a ha i hChart hChartSymm k l

/-- The compactly supported perturbation of the constant matrix entry used
outside a boundary chart. -/
def extendedFlattenedPrincipalCoefficientDeviation
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (k l : Fin n) (y : ℝ^n) : ℝ :=
  extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l -
    scalarIdentityMatrix (n := n) β k l

/-- The perturbation of the constant matrix entry is supported wherever the
target cutoff is supported. -/
theorem support_extendedFlattenedPrincipalCoefficientDeviation_subset
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n) :
    Function.support (extendedFlattenedPrincipalCoefficientDeviation
      (n := n) hΩ i β A k l) ⊆
      tsupport
        (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
          (n := n) (Ω := Ω) i).toFun := by
  intro y hy
  apply subset_closure
  intro hη
  apply hy
  simp [extendedFlattenedPrincipalCoefficientDeviation,
    extendedFlattenedPrincipalCoefficientAt, glueCoefficientField,
    glueToScalarIdentity, hη, scalarIdentityMatrix]

/-- The perturbation of the constant matrix entry has compact support. -/
theorem hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n) :
    HasCompactSupport
      (extendedFlattenedPrincipalCoefficientDeviation
        (n := n) hΩ i β A k l) := by
  exact HasCompactSupport.of_support_subset_isCompact
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := n) (Ω := Ω) i).hasCompactSupport
    (support_extendedFlattenedPrincipalCoefficientDeviation_subset
      (n := n) hΩ i β A k l)

/-- A `C¹` scalar entry of the extended chart coefficient is globally
Lipschitz.  The proof subtracts its constant value at infinity, applies the
compact-support `C¹` Lipschitz theorem, and adds the constant back. -/
theorem exists_lipschitzWith_extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l)) :
    ∃ C : NNReal, LipschitzWith C (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation (n := n) hΩ i β A k l)
    (hC1.sub contDiff_const) (by norm_num)
  refine ⟨C, ?_⟩
  simpa [extendedFlattenedPrincipalCoefficientDeviation] using
    hC.add (LipschitzWith.const (scalarIdentityMatrix (n := n) β k l))


/-- A canonical global Lipschitz constant for a `C¹` extended scalar entry. -/
noncomputable def extendedFlattenedPrincipalCoefficientLipConst
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l)) :
    NNReal :=
  Classical.choose
    (exists_lipschitzWith_extendedFlattenedPrincipalCoefficientAt
      (n := n) hΩ i β A k l hC1)

/-- The canonical constant bounds the corresponding extended scalar entry. -/
theorem lipschitzWith_extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l)) :
    LipschitzWith
      (extendedFlattenedPrincipalCoefficientLipConst
        (n := n) hΩ i β A k l hC1)
      (fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hΩ i β A y k l) :=
  Classical.choose_spec
    (exists_lipschitzWith_extendedFlattenedPrincipalCoefficientAt
      (n := n) hΩ i β A k l hC1)

/-- A `C¹` scalar entry of the extended chart coefficient belongs to
`L∞` on every measurable domain, in particular on the upper half-space. -/
theorem memLp_top_extendedFlattenedPrincipalCoefficientAt
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (U : Set (ℝ^n)) :
    MemLp (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l)
      ∞ (domainMeasure n U) := by
  convert ((hC1.sub contDiff_const).continuous.memLp_top_of_hasCompactSupport
    (hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation (n := n) hΩ i β A k l)
    (domainMeasure n U)).add (memLp_top_const (scalarIdentityMatrix (n := n) β k l)) using 1
  funext y
  simp


/-- Canonical `L∞` coefficient represented by one extended scalar entry. -/
noncomputable def extendedFlattenedPrincipalCoefficientLpTop
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (U : Set (ℝ^n)) : DerivLp n ∞ U :=
  (memLp_top_extendedFlattenedPrincipalCoefficientAt
    (n := n) hΩ i β A k l hC1 U).toLp
      (fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hΩ i β A y k l)

/-- The `L∞` element `extendedFlattenedPrincipalCoefficientLpTop` is represented almost everywhere
on `U` by the classical extended scalar entry it was built from. -/
@[simp]
theorem extendedFlattenedPrincipalCoefficientLpTop_coe_ae
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ) (k l : Fin n)
    (hC1 : ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (U : Set (ℝ^n)) :
    (extendedFlattenedPrincipalCoefficientLpTop
      (n := n) hΩ i β A k l hC1 U : ℝ^n → ℝ) =ᵐ[domainMeasure n U]
      fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hΩ i β A y k l := by
  exact (memLp_top_extendedFlattenedPrincipalCoefficientAt
    (n := n) hΩ i β A k l hC1 U).coeFn_toLp

/-- A globally `C^m` transformed coefficient which is constant off a compact
set defines a `W^{m,∞}` coefficient on every domain. -/
noncomputable def extendedFlattenedPrincipalCoefficientWkTop
    [Fact (0 < n)] {m : ℕ} {Omega : Set (ℝ^n)}
    (hOmega : Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (beta : ℝ) (a : ℝ^n → Fin n → Fin n → ℝ)
    (k l : Fin n)
    (hCoeff : ContDiff ℝ m (fun y ↦
      extendedFlattenedPrincipalCoefficientAt
        (n := n) hOmega i beta a y k l))
    (U : Set (ℝ^n)) :
    W^{m,∞}(U) := by
  let f : ℝ^n → ℝ := fun y ↦
    extendedFlattenedPrincipalCoefficientAt
      (n := n) hOmega i beta a y k l
  let c : ℝ := scalarIdentityMatrix (n := n) beta k l
  have hcompact : HasCompactSupport (fun y ↦ f y - c) := by
    change HasCompactSupport
      (extendedFlattenedPrincipalCoefficientDeviation
        (n := n) hOmega i beta a k l)
    exact
      hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation
        (n := n) hOmega i beta a k l
  exact mkWkpSpaceOnOfContDiffMemLpFinite
    (n := n) (k := m) (p := ∞) (Ω := U) f (by simpa [f] using hCoeff)
    (fun d ↦
      memLp_top_iteratedPartialDeriv_of_contDiff_sub_const
        f c (by simpa [f] using hCoeff) hcompact U d)

/-- The base coordinate of the arbitrary-order Sobolev field is the transformed
coefficient almost everywhere. -/
theorem extendedFlattenedPrincipalCoefficientWkTop_base_ae
    [Fact (0 < n)] {m : ℕ} {Omega : Set (ℝ^n)}
    (hOmega : Boundary.C1ExtensionAtlas n Omega)
    (i : Fin hOmega.N)
    (beta : ℝ) (a : ℝ^n → Fin n → Fin n → ℝ)
    (k l : Fin n)
    (hCoeff : ContDiff ℝ m (fun y ↦
      extendedFlattenedPrincipalCoefficientAt
        (n := n) hOmega i beta a y k l))
    (U : Set (ℝ^n)) :
    ((((extendedFlattenedPrincipalCoefficientWkTop
        (n := n) hOmega i beta a k l hCoeff U :
          WkpAmbientOn n m ∞ U)
      (baseIndex n m) : DerivLp n ∞ U) : ℝ^n → ℝ)) =ᵐ[domainMeasure n U]
      fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hOmega i beta a y k l := by
  let f : ℝ^n → ℝ := fun y ↦
    extendedFlattenedPrincipalCoefficientAt (n := n) hOmega i beta a y k l
  have hcompact : HasCompactSupport (fun y ↦ f y - scalarIdentityMatrix (n := n) beta k l) :=
    hasCompactSupport_extendedFlattenedPrincipalCoefficientDeviation (n := n) hOmega i beta a k l
  simpa [extendedFlattenedPrincipalCoefficientWkTop, f, baseIndex_toList, iteratedPartialDeriv]
    using mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae (n := n) (k := m) (p := ∞) (Ω := U) f hCoeff
      (fun d ↦ memLp_top_iteratedPartialDeriv_of_contDiff_sub_const f _ hCoeff hcompact U d)
      (baseIndex n m)


/-- Entrywise `L∞` matrix of extended flattened coefficients. -/
noncomputable def extendedFlattenedPrincipalCoefficientsLpTop
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (hC1 : ∀ k l, ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (U : Set (ℝ^n)) : Fin n → Fin n → DerivLp n ∞ U :=
  fun k l ↦ extendedFlattenedPrincipalCoefficientLpTop
    (n := n) hΩ i β A k l (hC1 k l) U

/-- Every entry of the `L∞` matrix represents the corresponding
classical extended coefficient. -/
theorem extendedFlattenedPrincipalCoefficientsLpTop_coe_ae
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (hC1 : ∀ k l, ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (U : Set (ℝ^n)) (k l : Fin n) :
    (extendedFlattenedPrincipalCoefficientsLpTop
      (n := n) hΩ i β A hC1 U k l : ℝ^n → ℝ) =ᵐ[domainMeasure n U]
      fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hΩ i β A y k l := by
  exact extendedFlattenedPrincipalCoefficientLpTop_coe_ae
    (n := n) hΩ i β A k l (hC1 k l) U

/-- Entrywise global Lipschitz constants for the transformed coefficient
matrix.  Together with `extendedFlattenedPrincipalCoefficientsLpTop`, this is
the coefficient data expected by the flattened half-space regularity theorem. -/
noncomputable def extendedFlattenedPrincipalCoefficientLipConsts
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (hC1 : ∀ k l, ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l)) :
    Fin n → Fin n → NNReal :=
  fun k l ↦ extendedFlattenedPrincipalCoefficientLipConst
    (n := n) hΩ i β A k l (hC1 k l)

/-- Every transformed matrix entry satisfies its global Lipschitz
bound. -/
theorem lipschitzWith_extendedFlattenedPrincipalCoefficient_entries
    [Fact (0 < n)] {Ω : Set (ℝ^n)}
    (hΩ : Boundary.C1ExtensionAtlas n Ω) (i : Fin hΩ.N)
    (β : ℝ) (A : ℝ^n → Fin n → Fin n → ℝ)
    (hC1 : ∀ k l, ContDiff ℝ 1 (fun y ↦
      extendedFlattenedPrincipalCoefficientAt (n := n) hΩ i β A y k l))
    (k l : Fin n) :
    LipschitzWith
      (extendedFlattenedPrincipalCoefficientLipConsts
        (n := n) hΩ i β A hC1 k l)
      (fun y ↦ extendedFlattenedPrincipalCoefficientAt
        (n := n) hΩ i β A y k l) := by
  exact lipschitzWith_extendedFlattenedPrincipalCoefficientAt
    (n := n) hΩ i β A k l (hC1 k l)

end SobolevSpace.GraphSpace.BoundaryRegularity
