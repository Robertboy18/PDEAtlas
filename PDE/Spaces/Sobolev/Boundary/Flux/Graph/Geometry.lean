/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Coordinates
public import PDE.Analysis.InnerProductSpace.CodimensionOne
import PDE.Analysis.LinearAlgebra.Determinant.RankOne

/-!
# Tangent area and conormal of a graph in linear coordinates

The graph derivative and its inward conormal are computed from the height
and the coordinate map. Their area relation retains the volume determinant
of the possibly nonorthogonal coordinates. The calculation also applies
when the tangent space has dimension zero.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set Trace.HalfSpace

variable {m : ℕ}

/-- Height above the graph, positive on the chosen epigraph. -/
def linearGraphHeight (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ)
    (x : ℝ^(m + 1)) : ℝ :=
  (A x) (Fin.last m) - g (splitTangentialNormal (A x)).1

/-- Tangential derivative of the physical graph parametrization. -/
def linearGraphTangent (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ)
    (y : ℝ^m) : ℝ^m →L[ℝ] ℝ^(m + 1) :=
  A.symm.toContinuousLinearMap.comp
    (tangentialNormalContinuousLinearEquiv.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ _).prod (fderiv ℝ g y)))

/-- The inward normal covector of a graph in physical coordinates. -/
def linearGraphCovector (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ)
    (y : ℝ^m) : ℝ^(m + 1) →L[ℝ] ℝ :=
  ((EuclideanSpace.proj (Fin.last m)) -
    (fderiv ℝ g y).comp
      ((ContinuousLinearMap.fst ℝ (ℝ^m) ℝ).comp
        tangentialNormalContinuousLinearEquiv.toContinuousLinearMap)).comp
    A.toContinuousLinearMap

/-- The Riesz vector of the graph height derivative. -/
def linearGraphConormal (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ)
    (y : ℝ^m) : ℝ^(m + 1) :=
  (InnerProductSpace.toDual ℝ (ℝ^(m + 1))).symm (linearGraphCovector A g y)

@[simp]
theorem linearGraphTangent_apply
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y v : ℝ^m) :
    linearGraphTangent A g y v =
      A.symm (joinTangentialNormal (v, fderiv ℝ g y v)) := rfl

@[simp]
theorem linearGraphCovector_apply
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ)
    (y : ℝ^m) (v : ℝ^(m + 1)) :
    linearGraphCovector A g y v =
      (A v) (Fin.last m) - fderiv ℝ g y (splitTangentialNormal (A v)).1 := rfl

/-- The graph derivative is the derivative of the parametrization. -/
theorem hasFDerivAt_linearGraphParametrization
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ}
    (hg : ContDiff ℝ 1 g) (y : ℝ^m) :
    HasFDerivAt (linearGraphParametrization A g) (linearGraphTangent A g y) y := by
  exact A.symm.hasFDerivAt.comp y
    (tangentialNormalContinuousLinearEquiv.symm.hasFDerivAt.comp y
      ((hasFDerivAt_id y).prodMk ((hg.differentiable one_ne_zero y).hasFDerivAt)))

/-- The height derivative is the stated physical conormal covector. -/
theorem hasFDerivAt_linearGraphHeight
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ}
    (hg : ContDiff ℝ 1 g) (x : ℝ^(m + 1)) :
    HasFDerivAt (linearGraphHeight A g)
      (linearGraphCovector A g (splitTangentialNormal (A x)).1) x := by
  exact ((EuclideanSpace.proj (Fin.last m)).hasFDerivAt.sub
    (((hg.differentiable one_ne_zero _).hasFDerivAt.comp (A x)
      ((ContinuousLinearMap.fst ℝ (ℝ^m) ℝ).hasFDerivAt.comp (A x)
        tangentialNormalContinuousLinearEquiv.hasFDerivAt)))).comp x A.hasFDerivAt

/-- The graph parametrization is C¹ whenever its height is C¹. -/
theorem contDiff_linearGraphParametrization
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (linearGraphParametrization A g) :=
  A.symm.contDiff.comp
    (tangentialNormalContinuousLinearEquiv.symm.contDiff.comp (contDiff_id.prodMk hg))

/-- Tangential projection is a left inverse of graph parametrization. -/
theorem linearGraphParametrization_injective
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) :
    Function.Injective (linearGraphParametrization A g) := by
  intro y z h
  have h' := congrArg (fun x ↦ (splitTangentialNormal (A x)).1) h
  simpa [linearGraphParametrization] using h'

/-- Tangential projection also gives injectivity of the graph derivative. -/
theorem linearGraphTangent_injective
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) :
    Function.Injective (linearGraphTangent A g y) := by
  intro v w h
  have h' := congrArg (fun x ↦ (splitTangentialNormal (A x)).1) h
  simpa using h'

/-- The graph height derivative cannot vanish: it takes value one on the
physical image of the final coordinate vector. -/
theorem linearGraphCovector_ne_zero
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) :
    linearGraphCovector A g y ≠ 0 := by
  intro h
  have he := congrArg (fun q : ℝ^(m + 1) →L[ℝ] ℝ ↦
    q (A.symm (joinTangentialNormal (0, 1)))) h
  simp at he

/-- The graph conormal is nonzero in every positive ambient dimension. -/
theorem linearGraphConormal_ne_zero
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) :
    linearGraphConormal A g y ≠ 0 := by
  intro h
  have he := congrArg (InnerProductSpace.toDual ℝ (ℝ^(m + 1))) h
  exact linearGraphCovector_ne_zero A g y (by simpa [linearGraphConormal] using he)

/-- The area factor of a graph is the coordinate volume factor times its
unnormalized conormal length. No orthogonality of the coordinates is used. -/
theorem normDet_linearGraphTangent
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (y : ℝ^m) :
    (linearGraphTangent A g y).toLinearMap.normDet =
      |A.symm.toLinearMap.det| * ‖linearGraphConormal A g y‖ := by
  let S := tangentialNormalContinuousLinearEquiv (n := m)
  let ℓ := (fderiv ℝ g y).comp ((ContinuousLinearMap.fst ℝ (ℝ^m) ℝ).comp
    S.toContinuousLinearMap)
  let b : ℝ^(m + 1) := joinTangentialNormal (0, 1)
  let D : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1) := .id ℝ _ + ℓ.smulRight b
  let E : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1) := .id ℝ _ - ℓ.smulRight b
  have hℓb : ℓ b = 0 := by simp [ℓ, b, S]
  have hDE : D.comp E = .id ℝ _ := by
    ext x : 1
    simp [D, E, hℓb]
  let M := A.symm.toContinuousLinearMap.comp D
  let C := E.comp A.toContinuousLinearMap
  have hMC : M.comp C = .id ℝ _ := by
    ext x : 1
    have h := congrArg (fun T : ℝ^(m + 1) →L[ℝ] ℝ^(m + 1) ↦ T (A x)) hDE
    change A.symm (D (E (A x))) = x
    rw [show D (E (A x)) = A x from h, A.symm_apply_apply]
  have hT (i : Fin m) :
      linearGraphTangent A g y (EuclideanSpace.basisFun (Fin m) ℝ i) =
        M (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i.castSucc) := by
    change A.symm _ = A.symm _
    congr 1
    ext j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · have hsingle : (EuclideanSpace.single i 1 : ℝ^m) =
          WithLp.toLp 2 (fun k : Fin m ↦ if k = i then 1 else 0) := by
        ext k
        simp [PiLp.single_apply]
      simpa [D, ℓ, b, S, EuclideanSpace.basisFun_apply, splitTangentialNormal] using
        congrArg (fderiv ℝ g y) hsingle
    · simp [D, b, EuclideanSpace.basisFun_apply]
  have hc (x : ℝ^(m + 1)) :
      inner ℝ (linearGraphConormal A g y) x = C x (Fin.last m) := by
    rw [linearGraphConormal, InnerProductSpace.toDual_symm_apply]
    simp [C, E, ℓ, b, S]
  have hdetD : D.toLinearMap.det = 1 := by
    exact LinearMap.det_id_add_smulRight_eq_one hℓb
  have hdetM : M.toLinearMap.det = A.symm.toLinearMap.det := by
    change (A.symm.toLinearMap.comp D.toLinearMap).det = _
    rw [LinearMap.det_comp, hdetD, mul_one]
  rw [ContinuousLinearMap.normDet_eq_abs_det_mul_norm_of_normal_covector
    M C hMC _ hT _ hc, hdetM]

end SobolevSpace.Boundary.Flux.Graph
