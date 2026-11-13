/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.AffineInterface.Geometry
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.FDeriv.PartialDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PDE.DistributionTheory.TestFunction
import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Boundary integrals across affine interfaces

For a speed `s`, the open set `leftHalfSpace s` is the region `x < s t`, and
`interface s` parametrizes its boundary by `t ↦ (t, s t)`. The main theorem evaluates a
linear combination of the time and space derivatives of a compactly supported test function
over this half-space:

`∫_{x < s t} (a φ_t + b φ_x) = (b - a s) ∫ φ(t, s t) dt`.

The proof reduces the moving half-space to `x < 0` by a volume-preserving shear and then uses
Fubini together with the one-dimensional fundamental theorem of calculus.

## Main results

* `setIntegral_linearCombination_partialDeriv_leftHalfSpace`: for a compactly supported `C¹`
  test function `φ` and constants `a, b`,
  `∫_{x < s t} (a φ_t + b φ_x) = (b - a s) ∫ φ(t, s t) dt`.

This is the divergence theorem on the half-plane `{x < s t}` for the constant vector
field `(a, b)`. The outward normal is proportional to `(-s, 1)`, and `(b - a s) dt` is
the flux of `(a, b)` through the boundary line in the parametrization `t ↦ (t, s t)`.
Evans states the Gauss–Green theorem for bounded domains with `C¹` boundary (Appendix C.2,
Theorem 1); our half-plane is unbounded, but the test function has compact support.
The identity computes weak integrals of piecewise-smooth profiles: `Scalar.PlanarShock`
obtains the Rankine–Hugoniot jump condition and `AffineFan` the matching-trace condition
for fans.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix C.2, Theorem 1 (Gauss–Green theorem).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE.Analysis (planeEquiv measurePreserving_planeEquiv planeEquiv_symm_apply)

namespace PDE.Hyperbolic.ConservationLaw.AffineInterface

noncomputable section

open scoped Distributions Topology

open MeasureTheory
open PDE.Common
open TopologicalSpace

open scoped Interval

private def stationaryLeftHalfSpace : Set ℝ^2 := {x : ℝ^2 | x 1 < 0}

/-! ## Slice maps for coordinate derivatives -/

private def sliceBase (c : ℝ) (i : Fin 2) : ℝ^2 :=
  WithLp.toLp 2 (fun j : Fin 2 ↦ if j = i then 0 else c)

private def slice (c : ℝ) (i : Fin 2) : ℝ → ℝ^2 :=
  coordinateLine i (sliceBase c i)

private theorem hasCompactSupport_slice (ψ : ℝ^2 → ℝ) (hψ : HasCompactSupport ψ) (c : ℝ)
    (i : Fin 2) :
    HasCompactSupport (fun z : ℝ ↦ ψ (slice c i z)) := by
  refine .intro (hψ.isCompact.image (EuclideanSpace.proj i).continuous) fun z hz ↦ ?_
  by_contra hne
  exact hz ⟨slice c i z, subset_closure hne, by simp [slice, sliceBase, coordinateLine]⟩

private theorem deriv_comp_slice_eq_partialDeriv (ψ : ℝ^2 → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (c : ℝ) (i : Fin 2) (z : ℝ) :
    deriv (fun r : ℝ ↦ ψ (slice c i r)) z = (∂[i] ψ) (slice c i z) := by
  have hψ' : DifferentiableAt ℝ ψ (slice c i z) := hψ.contDiffAt.differentiableAt_one
  have hderiv := hψ'.hasFDerivAt.comp_hasDerivAt z (hasDerivAt_coordinateLine i (sliceBase c i) z)
  simpa [slice, partialDeriv, Function.comp_def] using hderiv.deriv

/-! ## The coordinates of `planeEquiv` -/

private theorem planeEquiv_symm_snd (p : ℝ × ℝ) : (planeEquiv.symm p : ℝ^2) 1 = p.2 := by
  simp [planeEquiv_symm_apply]

/-! ## Half-space set integrals (`x < 0`) -/

private theorem preimage_stationaryLeftHalfSpace :
    (fun p : ℝ × ℝ ↦ (planeEquiv.symm p : ℝ^2)) ⁻¹' stationaryLeftHalfSpace = {p : ℝ × ℝ |
      p.2 < 0} := by
  classical
  ext p
  simp [stationaryLeftHalfSpace, planeEquiv_symm_snd]

private theorem planeEquiv_symm_eq_slice_one (t x : ℝ) :
    (planeEquiv.symm (t, x) : ℝ^2) = slice t 1 x := by
  ext i; fin_cases i <;> simp [planeEquiv_symm_apply, slice, sliceBase, coordinateLine]

private theorem planeEquiv_symm_eq_slice_zero (t x : ℝ) :
    (planeEquiv.symm (t, x) : ℝ^2) = slice x 0 t := by
  ext i; fin_cases i <;> simp [planeEquiv_symm_apply, slice, sliceBase, coordinateLine]

private theorem setIntegral_partialDeriv1_stationaryLeftHalfSpace (ψ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ x in stationaryLeftHalfSpace, (∂[(1 : Fin 2)] (ψ : ℝ^2 → ℝ)) x ∂volume) =
      ∫ t : ℝ, ψ !₂[t, 0] ∂volume := by
  have hpres : MeasurePreserving (fun p : ℝ × ℝ ↦ (planeEquiv.symm p : ℝ^2)) :=
    measurePreserving_planeEquiv.symm
  have hS0 : {p : ℝ × ℝ | p.2 < 0} = Set.univ ×ˢ Set.Iio 0 := by ext; simp
  have hint : Integrable fun p : ℝ × ℝ ↦ (∂[(1 : Fin 2)] (ψ : ℝ^2 → ℝ)) (planeEquiv.symm p) :=
    hpres.integrable_comp_of_integrable (ψ.integrable_partialDeriv 1)
  rw [← hpres.setIntegral_preimage_emb planeEquiv.symm.measurableEmbedding,
    preimage_stationaryLeftHalfSpace, hS0, Measure.volume_eq_prod,
    setIntegral_prod _ hint.integrableOn, Measure.restrict_univ]
  refine integral_congr_ae (.of_forall fun t ↦ ?_)
  simp only [planeEquiv_symm_eq_slice_one, ← deriv_comp_slice_eq_partialDeriv _ ψ.contDiff]
  rw [← integral_Iic_eq_integral_Iio, HasCompactSupport.integral_Iic_deriv_eq
    (f := fun r ↦ ψ (slice t 1 r))
    (ψ.contDiff.comp ((contDiff_coordinateLine 1 (sliceBase t 1)).of_le (by norm_num)))
    (hasCompactSupport_slice _ ψ.hasCompactSupport t 1)]
  congr 1
  ext i; fin_cases i <;> simp [slice, sliceBase, coordinateLine]

private theorem setIntegral_partialDeriv0_stationaryLeftHalfSpace (ψ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) :
    (∫ x in stationaryLeftHalfSpace, (∂[(0 : Fin 2)] (ψ : ℝ^2 → ℝ)) x ∂volume) = 0 := by
  have hpres : MeasurePreserving (fun p : ℝ × ℝ ↦ (planeEquiv.symm p : ℝ^2)) :=
    measurePreserving_planeEquiv.symm
  have hS0 : MeasurableSet {p : ℝ × ℝ | p.2 < 0} := measurableSet_lt measurable_snd measurable_const
  have hint : Integrable fun p : ℝ × ℝ ↦ (∂[(0 : Fin 2)] (ψ : ℝ^2 → ℝ)) (planeEquiv.symm p) :=
    hpres.integrable_comp_of_integrable (ψ.integrable_partialDeriv 0)
  rw [← hpres.setIntegral_preimage_emb planeEquiv.symm.measurableEmbedding,
    preimage_stationaryLeftHalfSpace, ← integral_indicator hS0, Measure.volume_eq_prod,
    integral_prod_symm _ (hint.indicator hS0)]
  refine integral_eq_zero_of_ae (.of_forall fun x ↦ ?_)
  by_cases hx : x < 0
  · have hg := ψ.contDiff.comp ((contDiff_coordinateLine 0 (sliceBase x 0)).of_le (by norm_num))
    have hgc := hasCompactSupport_slice _ ψ.hasCompactSupport x 0
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte,
      planeEquiv_symm_eq_slice_zero, ← deriv_comp_slice_eq_partialDeriv _ ψ.contDiff, Pi.zero_apply]
    exact integral_eq_zero_of_hasDerivAt_of_integrable
      (fun t ↦ (hg.differentiable one_ne_zero t).hasDerivAt)
      ((hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv)
      (hg.continuous.integrable_of_hasCompactSupport hgc)
  · simp [hx]

/-! ## Shear and the boundary-term identity for `x < s*t` -/

private def shearMat (s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.transvection (1 : Fin 2) (0 : Fin 2) s

private def shearPiLin (s : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  (shearMat s).mulVecLin

private def shearPiCLM (s : ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (shearPiLin s)

private def shearCLM (s : ℝ) : ℝ^2 →L[ℝ] ℝ^2 :=
  ((EuclideanSpace.equiv (Fin 2) ℝ).symm :
      (Fin 2 → ℝ) →L[ℝ] ℝ^2).comp
    ((shearPiCLM s).comp
      (EuclideanSpace.equiv (Fin 2) ℝ : ℝ^2 →L[ℝ] (Fin 2 → ℝ)))

private def shearFun (s : ℝ) : ℝ^2 → ℝ^2 := fun x ↦ shearCLM s x

private theorem shearPiLin_apply (s : ℝ) (x : Fin 2 → ℝ) :
    shearPiLin s x = ![x 0, x 1 + s * x 0] := by
  classical
  ext i; fin_cases i
  · simp [shearPiLin, shearMat, Matrix.transvection, Matrix.single_mulVec]
  · simp [shearPiLin, shearMat, Matrix.transvection, Matrix.single_mulVec, add_comm]

private theorem shearFun_apply (s : ℝ) (x : ℝ^2) :
    shearFun s x = !₂[x 0, x 1 + s * x 0] := by
  ext i; fin_cases i <;> simp [shearFun, shearCLM, shearPiCLM, shearPiLin_apply, add_comm]

private theorem preimage_leftHalfSpace (s : ℝ) :
    shearFun s ⁻¹' leftHalfSpace s = stationaryLeftHalfSpace := by
  classical
  ext x
  simp [leftHalfSpace, stationaryLeftHalfSpace, shearFun_apply (s := s) (x := x)]

private theorem measurePreserving_shearFun (s : ℝ) :
    MeasurePreserving (shearFun s) := by
  -- conjugate the transvection lemma on `Fin 2 → ℝ` by the coordinate equivalence
  let e : ℝ^2 ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
  have he : MeasurePreserving (e : ℝ^2 → (Fin 2 → ℝ)) := PiLp.volume_preserving_ofLp (Fin 2)
  convert he.symm.comp
    ((Real.volume_preserving_transvectionStruct (ι := Fin 2) ⟨1, 0, by decide, s⟩).comp he) using 1
  funext x
  ext i; fin_cases i <;> simp [shearFun_apply, e, Function.update,
    Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.toLin'_apply,
    Matrix.single_mulVec, add_comm]

/-- The shear as a homeomorphism; its inverse is the shear of the opposite speed. -/
private def shearHomeomorph (s : ℝ) : ℝ^2 ≃ₜ ℝ^2 where
  toFun := shearFun s
  invFun := shearFun (-s)
  left_inv x := by ext i; fin_cases i <;> simp [shearFun_apply]
  right_inv x := by ext i; fin_cases i <;> simp [shearFun_apply]
  continuous_toFun := (shearCLM s).continuous
  continuous_invFun := (shearCLM (-s)).continuous

private theorem measurableEmbedding_shearFun (s : ℝ) : MeasurableEmbedding (shearFun s) :=
  (shearHomeomorph s).toMeasurableEquiv.measurableEmbedding

/-- Affine derivative integrals over a left region reduce to the boundary line. -/
theorem setIntegral_linearCombination_partialDeriv_leftHalfSpace
    (φ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ)) (s a b : ℝ) :
    (∫ x in leftHalfSpace s, (a * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) x + b *
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) x) ∂volume) = (b - a * s) * ∫ t : ℝ,
      φ (interface s t) ∂volume := by
  let ψ : 𝓓^{1}((⊤ : Opens ℝ^2), ℝ) :=
    { toFun := fun x ↦ φ (shearFun s x)
      contDiff' := φ.contDiff.comp (shearCLM s).contDiff
      hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (shearHomeomorph s)
      tsupport_subset' := fun _ _ ↦ trivial }
  have hpd (i : Fin 2) (x : ℝ^2) : (∂[i] (ψ : ℝ^2 → ℝ)) x =
      fderiv ℝ φ (shearFun s x) (shearFun s (EuclideanSpace.single i 1)) :=
    congrArg (· (EuclideanSpace.single i 1)) ((φ.contDiff.differentiable one_ne_zero
      (shearFun s x)).hasFDerivAt.comp x (shearCLM s).hasFDerivAt).fderiv
  have he1 : shearFun s (EuclideanSpace.single 1 1) = EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [shearFun_apply]
  have he0 : shearFun s (EuclideanSpace.single 0 1) =
      EuclideanSpace.single 0 1 + s • EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp [shearFun_apply]
  have hpd1 (x : ℝ^2) : (∂[(1 : Fin 2)] (ψ : ℝ^2 → ℝ)) x =
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) (shearFun s x) := by
    rw [hpd, he1]
    rfl
  have hpd0 (x : ℝ^2) : (∂[(0 : Fin 2)] (ψ : ℝ^2 → ℝ)) x =
      (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) (shearFun s x) +
        s * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) (shearFun s x) := by
    rw [hpd, he0, map_add, map_smul]
    rfl
  rw [← (measurePreserving_shearFun s).setIntegral_preimage_emb (measurableEmbedding_shearFun s),
    preimage_leftHalfSpace]
  calc
    _ = ∫ x in stationaryLeftHalfSpace, (a * (∂[(0 : Fin 2)] (ψ : ℝ^2 → ℝ)) x +
            (b - a * s) * (∂[(1 : Fin 2)] (ψ : ℝ^2 → ℝ)) x) ∂volume :=
      integral_congr_ae (.of_forall fun x ↦ by simp only [hpd0, hpd1]; ring)
    _ = _ := by
      rw [integral_add ((ψ.integrable_partialDeriv 0).restrict.const_mul a)
        ((ψ.integrable_partialDeriv 1).restrict.const_mul _), integral_const_mul,
        integral_const_mul, setIntegral_partialDeriv0_stationaryLeftHalfSpace,
        setIntegral_partialDeriv1_stationaryLeftHalfSpace, mul_zero, zero_add]
      simp [ψ, interface, shearFun_apply]

end

end PDE.Hyperbolic.ConservationLaw.AffineInterface
