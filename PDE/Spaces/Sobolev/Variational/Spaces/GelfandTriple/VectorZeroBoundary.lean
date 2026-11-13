/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.FiniteProduct
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Vector.FirstOrder
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2

/-!
# The finite-vector zero-boundary Sobolev Gelfand triple

The energy space is the finite Hilbert product of the closure-defined scalar
`H¹₀` spaces. Its value is a Euclidean-valued `L²` class and its gradient is the
full weak matrix gradient. The squared norm splits exactly into the squared `L²`
norm of the value and the squared Frobenius norm of the gradient, which is the sum
of the squared `L²` norms of all matrix entries. Compact inclusion on bounded open
sets follows from the scalar zero-extension theorem, without a boundary regularity
assumption.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory PDE.Analysis.Evolution
open scoped ENNReal Sobolev

/-- Finite-vector `H¹₀`, with the full Hilbert Sobolev norm on its scalar coordinates. -/
abbrev ZeroBoundaryVectorSpace (n m : ℕ) (Ω : Set (ℝ^n)) :=
  PiLp 2 (fun _ : Fin m ↦ H¹₀(Ω))

/-- The first-order vector Sobolev space with zero boundary values. Activate
with `open scoped Sobolev`. The spatial dimension is inferred
from the domain, and `m` is the number of components. -/
scoped[Sobolev] notation "H¹₀(" Ω "; " "ℝ^" m ")" =>
  SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace _ m Ω

/-- The same space on a bundled domain, such as `TopologicalSpace.Opens`.
Taking its underlying set first lets the notation infer the spatial dimension. -/
scoped[Sobolev] notation "H¹₀(" Ω "; " "ℝ^" m ")" =>
  SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace _ m (SetLike.coe Ω)

namespace ZeroBoundaryVectorSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- Forget zero boundary data and the Hilbert product presentation to the graph tuple. -/
def toSobolev : H¹₀(Ω; ℝ^m) →L[ℝ] (Fin m → H¹(Ω)) :=
  (ContinuousLinearMap.piMap fun _ : Fin m ↦ h10SubtypeL (n := n) (Ω := Ω)).comp
    (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap

/-- The Euclidean-valued `L²` inclusion of finite-vector `H¹₀`. -/
def toLp : H¹₀(Ω; ℝ^m) →L[ℝ] Lp (ℝ^m) 2 μ :=
  Lp.euclideanTuple.comp
    ((ContinuousLinearMap.piMap fun _ : Fin m ↦ baseCoordCLM (n := n) (Ω := Ω)).comp
      (PiLp.continuousLinearEquiv 2 ℝ _).toContinuousLinearMap)

/-- The full weak matrix gradient of a finite-vector zero-boundary field. -/
def gradient : H¹₀(Ω; ℝ^m) →L[ℝ] Lp (ℝ^(m * n)) 2 μ :=
  vectorWkpGradientCLM.comp toSobolev

/-- The same weak matrix gradient as a Hilbert tuple of scalar `L²` coordinates.
This presentation pairs directly with independently supplied Lebesgue coefficients. -/
def gradientCoordinates : H¹₀(Ω; ℝ^m) →L[ℝ]
    PiLp 2 (fun _ : Fin m × Fin n ↦ DerivLp n 2 Ω) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m × Fin n ↦ DerivLp n 2 Ω)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun ki ↦ (derivCoordCLM ki.2).comp
        ((ContinuousLinearMap.proj ki.1).comp
          (PiLp.continuousLinearEquiv 2 ℝ
            (fun _ : Fin m ↦ H¹₀(Ω))).toContinuousLinearMap))

/-- Each coordinate is the corresponding scalar weak derivative. -/
@[simp]
theorem gradientCoordinates_apply (v : H¹₀(Ω; ℝ^m)) (k : Fin m × Fin n) :
    gradientCoordinates v k = derivCoordCLM k.2 (v k.1) :=
  rfl

/-- The weak matrix gradient in the shared `Sobolev` scope.
The norm of `∇ u` is the full Frobenius gradient norm. With Mathlib's
`Gradient` scope also open, annotate the weak `Lp` result type. -/
scoped[Sobolev] notation "∇" =>
  SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace.gradient

/-- The value inclusion retains all scalar zero-boundary coordinates almost everywhere. -/
theorem toLp_apply_ae (v : H¹₀(Ω; ℝ^m)) :
    ∀ᵐ x ∂μ, ∀ i, toLp v x i = baseCoordCLM (v i) x :=
  Lp.euclideanTuple_apply_ae _

/-- The graph value and the Hilbert-product value are the same `L²` class. -/
theorem value_toSobolev (v : H¹₀(Ω; ℝ^m)) :
    vectorWkpValueCLM (toSobolev v) = toLp v := by
  apply Lp.ext
  filter_upwards [vectorWkpValueCLM_apply_ae (toSobolev v),
    toLp_apply_ae v] with x hx hy
  exact PiLp.ext fun i ↦ (hx i).trans (hy i).symm

/-- Each matrix entry is the corresponding scalar weak derivative, on one full-measure set. -/
theorem gradient_apply_ae (v : H¹₀(Ω; ℝ^m)) :
    ∀ᵐ x ∂μ, ∀ i j, (∇ v) x (finProdFinEquiv (i, j)) =
      derivCoordCLM j (v i) x := by
  have hscalar : ∀ᵐ x ∂μ, ∀ i : Fin m, ∀ j : Fin n,
      (∇ (v i : H¹(Ω))) x j = derivCoordCLM j (v i) x :=
    ae_all_iff.mpr fun i ↦ gradientCLM_apply_ae (v i)
  filter_upwards [vectorWkpGradientCLM_apply_ae (toSobolev v), hscalar]
    with x hx hy
  exact fun i j ↦ (hx i j).trans (hy i j)

/-- The assembled matrix entries are distributional derivatives of the vector value. -/
theorem hasWeakDerivativeOn_gradient (v : H¹₀(Ω; ℝ^m)) (i : Fin m) (j : Fin n) :
    HasWeakDerivativeOn Ω [j] (fun x ↦ toLp v x i)
      (fun x ↦ (∇ v) x (finProdFinEquiv (i, j))) := by
  simpa only [gradient, ContinuousLinearMap.comp_apply,
    value_toSobolev] using
    hasWeakDerivativeOn_vectorWkpGradientCLM (toSobolev v) i j

/-- Flattening the scalar derivative coordinates gives the full matrix gradient. -/
theorem gradient_eq_euclideanTuple (v : H¹₀(Ω; ℝ^m)) :
    ∇ v =
      Lp.euclideanTuple (fun k : Fin (m * n) ↦
        derivCoordCLM (finProdFinEquiv.symm k).2 (v (finProdFinEquiv.symm k).1)) := by
  let d : Fin (m * n) → DerivLp n 2 Ω := fun k ↦
    derivCoordCLM (finProdFinEquiv.symm k).2 (v (finProdFinEquiv.symm k).1)
  change ∇ v = Lp.euclideanTuple d
  apply Lp.ext
  filter_upwards [gradient_apply_ae v, Lp.euclideanTuple_apply_ae d] with x hx hy
  apply PiLp.ext
  intro k
  rw [hy k]
  obtain ⟨ij, hij⟩ := (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).surjective k
  subst k
  simpa only [d, Equiv.symm_apply_apply] using hx ij.1 ij.2

/-- The vector value's squared `L²` norm is the sum of the scalar value norms. -/
theorem norm_toLp_sq (v : H¹₀(Ω; ℝ^m)) :
    ‖toLp v‖ ^ 2 = ∑ i, ‖baseCoordCLM (v i)‖ ^ 2 :=
  Lp.norm_euclideanTuple_sq _

/-- The squared Frobenius gradient norm sums every component and spatial derivative. -/
theorem norm_gradient_sq (v : H¹₀(Ω; ℝ^m)) :
    ‖∇ v‖ ^ 2 = ∑ i, ∑ j, ‖derivCoordCLM j (v i)‖ ^ 2 := by
  rw [gradient_eq_euclideanTuple, Lp.norm_euclideanTuple_sq,
    ← Equiv.sum_comp finProdFinEquiv]
  simp [Fintype.sum_prod_type]

/-- The coordinate presentation preserves the full Frobenius gradient norm. -/
theorem norm_gradientCoordinates (v : H¹₀(Ω; ℝ^m)) :
    ‖gradientCoordinates v‖ = ‖∇ v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, norm_gradient_sq, Fintype.sum_prod_type]
  rfl

/-- The full Hilbert Sobolev norm splits into the value and full matrix gradient. -/
theorem norm_sq (v : H¹₀(Ω; ℝ^m)) :
    ‖v‖ ^ 2 = ‖toLp v‖ ^ 2 + ‖∇ v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, norm_toLp_sq, norm_gradient_sq,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ norm_sq_eq_base_sq_add_sum_deriv_sq (v i)

/-- The value inclusion has norm at most one. -/
theorem norm_toLp_le (v : H¹₀(Ω; ℝ^m)) : ‖toLp v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The full gradient map has norm at most one. -/
theorem norm_gradient_le (v : H¹₀(Ω; ℝ^m)) : ‖∇ v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

/-- Compactly supported smooth scalar tuples, as finite-vector zero-boundary fields. -/
def ofTestFunction : (Fin m → TestFunctionOn n Ω) →ₗ[ℝ] H¹₀(Ω; ℝ^m) :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i ↦
      (testFunctionToH10Linear (n := n) (Ω := Ω)).comp (LinearMap.proj i))

/-- The vector zero-boundary space is generated densely by compactly supported smooth tuples. -/
theorem denseRange_ofTestFunction :
    DenseRange (ofTestFunction (n := n) (m := m) (Ω := Ω)) := by
  exact (PiLp.continuousLinearEquiv 2 ℝ _).symm.surjective.denseRange.comp
    (DenseRange.piMap fun _ : Fin m ↦
      denseRange_testFunctionToH10Linear (n := n) (Ω := Ω))
    (PiLp.continuousLinearEquiv 2 ℝ _).symm.continuous

/-- Smooth vector test tuples have their prescribed pointwise values almost everywhere. -/
theorem toLp_ofTestFunction_apply_ae
    (φ : Fin m → TestFunctionOn n Ω) :
    ∀ᵐ x ∂μ, ∀ i, toLp (ofTestFunction φ) x i = (φ i).1 x := by
  have hφ : ∀ᵐ x ∂μ, ∀ i, baseCoordCLM (testFunctionToH10 (φ i)) x = (φ i).1 x :=
    ae_all_iff.mpr fun i ↦ baseCoordCLM_testFunction_apply_ae (φ i)
  filter_upwards [toLp_apply_ae (ofTestFunction φ), hφ] with x hx hy
  exact fun i ↦ (hx i).trans (hy i)

/-- The gradient of a smooth vector test tuple consists of its classical partial derivatives. -/
theorem gradient_ofTestFunction_apply_ae
    (φ : Fin m → TestFunctionOn n Ω) :
    ∀ᵐ x ∂μ, ∀ i j, (∇ (ofTestFunction φ)) x
      (finProdFinEquiv (i, j)) = (∂[j] (φ i).1.toFun) x := by
  have hφ : ∀ᵐ x ∂μ, ∀ i j, derivCoordCLM j (testFunctionToH10 (φ i)) x =
      (∂[j] (φ i).1.toFun) x :=
    ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ derivCoordCLM_testFunction_apply_ae j (φ i)
  filter_upwards [gradient_apply_ae (ofTestFunction φ), hφ] with x hx hy
  exact fun i j ↦ (hx i j).trans (hy i j)

/-- The finite-vector Sobolev Gelfand triple with its Euclidean-valued `L²` pivot. -/
def gelfandTriple (hΩopen : IsOpen Ω) :
    GelfandTriple (V := H¹₀(Ω; ℝ^m)) (H := Lp (ℝ^m) 2 μ) where
  inclusion := toLp
  injective := by
    exact Lp.euclideanTupleIsometry.injective.comp
      (GelfandTriple.finiteProduct fun _ : Fin m ↦ h10L2GelfandTriple hΩopen).injective
  denseRange := by
    exact Lp.euclideanTupleIsometry.surjective.denseRange.comp
      (GelfandTriple.finiteProduct fun _ : Fin m ↦ h10L2GelfandTriple hΩopen).denseRange
      Lp.euclideanTupleIsometry.continuous

/-- The Gelfand inclusion is the vector value map. -/
@[simp]
theorem gelfandTriple_inclusion_apply (hΩopen : IsOpen Ω) (v : H¹₀(Ω; ℝ^m)) :
    (gelfandTriple (m := m) hΩopen).inclusion v = toLp v :=
  rfl

/-- Bounded open sets have compact vector zero-boundary inclusion, without boundary charts. -/
theorem isCompactOperator_inclusion
    (hΩopen : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (gelfandTriple (m := m) hΩopen).inclusion := by
  exact (GelfandTriple.finiteProduct_inclusion_isCompactOperator
    (fun _ : Fin m ↦ h10L2GelfandTriple hΩopen)
    (fun _ ↦ h10L2GelfandTriple_inclusion_isCompactOperator hΩopen hΩbounded)).clm_comp
      Lp.euclideanTupleIsometry.toContinuousLinearEquiv.toContinuousLinearMap

end ZeroBoundaryVectorSpace

end SobolevSpace.GraphSpace

public meta section

namespace Sobolev

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display the finite Hilbert product with its independent number of components. -/
@[scoped app_delab SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace]
def delabZeroBoundaryVectorSpace : Delab := (do
  guardSpaceNotation 3
  let m ← withNaryArg 1 delab
  let Ω ← withNaryArg 2 delabSpaceDomain
  return selectSpaceNotation (← `(H¹₀($Ω; ℝ^$m)))) <|> delabSpaceApp

end Sobolev

end
