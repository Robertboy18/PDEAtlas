/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.Convolution
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVector
public import PDE.Fluid.Incompressible.LerayProjection.Convolution
public import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation
public import PDE.Fluid.Incompressible.LerayProjection.OrderLowering

/-!
# Heat evolution commutes with the Leray projection

The scalar Fourier heat operator is Gaussian Bochner convolution. Transporting each
real scalar component connects that convolution to the vector `L²` field, and
translation invariance of the Leray projection gives heat/Leray commutation, including
for the integer Sobolev gaining operators. Dilation also commutes with the projection,
so the free self-similar evolution and its gaining realization preserve distributional
divergence freedom. Forgetting the top Sobolev order commutes with the projection, and
forgetting the gained derivative recovers the free evolution.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open IncompressibleFlow PDE.Analysis
open SobolevSpace.GraphSpace.Rellich SobolevSpace.GraphSpace.DifferenceQuotient
open scoped ENNReal NNReal Sobolev Topology

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- A physical scalar component in ordinary real Lebesgue L². -/
def volumeCoordinate (j : Fin n) : WholeSpaceL2 n →L[ℝ]
    Lp ℝ 2 (volume : Measure (ℝ^n)) :=
  wholeSpaceL2Equiv.toContinuousLinearEquiv.toContinuousLinearMap.comp (l2Coordinate j)

private theorem wholeSpaceL2Equiv_translate (y : ℝ^n) (u : DerivLp n 2 Set.univ) :
    wholeSpaceL2Equiv (translateLp 2 (-y) u) = translateL2 ℝ y (wholeSpaceL2Equiv u) := by
  apply Lp.ext
  have htrans : (translateLp 2 (-y) u : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ u (x - y) := by
    simpa only [domainMeasure, Measure.restrict_univ, sub_eq_add_neg] using
      translateLp_apply_ae 2 (-y) u
  have hshift : (fun x ↦ wholeSpaceL2Equiv u (x - y)) =ᵐ[volume]
      fun x ↦ u (x - y) := by
    simpa only [Function.comp_def, sub_eq_add_neg, add_comm] using
      (measurePreserving_add_left (volume : Measure (ℝ^n)) (-y)).quasiMeasurePreserving.ae_eq_comp
        (wholeSpaceL2Equiv_ae u)
  filter_upwards [wholeSpaceL2Equiv_ae (translateLp 2 (-y) u), htrans,
    translateL2_ae_eq ℝ y (wholeSpaceL2Equiv u), hshift] with x he ht hT hs
  exact (he.trans ht).trans (hT.trans hs).symm

/-- The component transport respects the actual translation sign convention. -/
theorem volumeCoordinate_translate (j : Fin n) (y : ℝ^n) (u : WholeSpaceL2 n) :
    volumeCoordinate j (l2Translate (-y) u) = translateL2 ℝ y (volumeCoordinate j u) := by
  change wholeSpaceL2Equiv (l2Coordinate j (l2Translate (-y) u)) = _
  rw [l2Coordinate_translate, wholeSpaceL2Equiv_translate]
  rfl

/-- Scalar coordinates commute with actual vector Bochner convolution. -/
theorem volumeCoordinate_l2Convolution (j : Fin n) (q : ℝ^n → ℝ)
    (hq : Integrable q volume) (u : WholeSpaceL2 n) :
    volumeCoordinate j (l2Convolution q hq u) =
      convolutionL2CLM q hq (volumeCoordinate j u) := by
  rw [l2Convolution_apply, convolutionL2CLM_apply,
    ← (volumeCoordinate j).integral_comp_comm (integrable_smul_l2Translate hq u)]
  apply integral_congr_ae
  filter_upwards with y
  rw [map_smul, volumeCoordinate_translate]

/-- The actual vector L² heat operator is the Gaussian average of translations. -/
def l2HeatConvolution (n : ℕ) (t : ℝ) (ht : 0 < t) :
    WholeSpaceL2 n →L[ℝ] WholeSpaceL2 n :=
  l2Convolution (fun x ↦ fundamentalSolutionHeat (n := n) x t)
    (fundamentalSolutionHeat_integrable t ht)

/-- Physical vector heat has exactly the scalar Gaussian Fourier multiplier in each component. -/
theorem complexify_volumeCoordinate_l2HeatConvolution (j : Fin n) (t : ℝ≥0)
    (ht : 0 < (t : ℝ)) (u : WholeSpaceL2 n) :
    complexifyRealL2 n (volumeCoordinate j (l2HeatConvolution n (t : ℝ) ht u)) =
      heatL2 n t (complexifyRealL2 n (volumeCoordinate j u)) := by
  rw [l2HeatConvolution, volumeCoordinate_l2Convolution]
  exact (heatL2_complexify_eq_convolution t ht (volumeCoordinate j u)).symm

/-- The actual vector heat convolution commutes with the actual L² Leray projector. -/
theorem lerayProjection_l2HeatConvolution (t : ℝ) (ht : 0 < t) (u : WholeSpaceL2 n) :
    lerayProjection n (l2HeatConvolution n t ht u) =
      l2HeatConvolution n t ht (lerayProjection n u) :=
  lerayProjection_l2Convolution _ _ u

private theorem complexifyRealL2_injective : Function.Injective (complexifyRealL2 n) := by
  intro u v huv
  apply Lp.ext
  filter_upwards [Lp.ext_iff.mp huv, Complex.ofRealCLM.coeFn_compLpL u,
    Complex.ofRealCLM.coeFn_compLpL v] with x he hu hv
  exact Complex.ofReal_injective (hu.symm.trans (he.trans hv))

/-- The complexified physical components jointly determine the actual vector L² field. -/
theorem ext_of_complexify_volumeCoordinate {u v : WholeSpaceL2 n}
    (h : ∀ j, complexifyRealL2 n (volumeCoordinate j u) =
      complexifyRealL2 n (volumeCoordinate j v)) : u = v := by
  have hcoord (j : Fin n) : l2Coordinate j u = l2Coordinate j v :=
    wholeSpaceL2Equiv.injective (complexifyRealL2_injective (h j))
  have he : (fun j ↦ l2Coordinate j u) = (fun j ↦ l2Coordinate j v) := funext hcoord
  simp only [l2Coordinate] at he
  have htuple := congrArg (fun f : Fin n → DerivLp n 2 Set.univ ↦ Lp.euclideanTuple f) he
  simpa only [Lp.euclideanTuple_coordinates] using htuple

/-- Complexified coordinates of the physical base row are the established graph base functions. -/
theorem complexify_volumeCoordinate_baseRow (u : VectorH n k) (j : Fin n) :
    complexifyRealL2 n (volumeCoordinate j (l2SobolevRow (baseIndex n k) u)) = baseL2 (u j) := by
  change complexifyL2CLM n (l2Coordinate j (l2SobolevRow (baseIndex n k) u)) = _
  rw [l2SobolevRow_apply, l2Coordinate_euclideanTuple]
  exact complexifyL2CLM_base (u j)

/-- The vector graph gaining operator is the actual Gaussian vector heat evolution. -/
theorem l2SobolevRow_vectorHeatGain (t : ℝ≥0) (ht : 0 < (t : ℝ)) (u : VectorH n k) :
    l2SobolevRow (baseIndex n (k + 1)) (vectorHeatGain n k (t : ℝ) ht u) =
      l2HeatConvolution n (t : ℝ) ht (l2SobolevRow (baseIndex n k) u) := by
  apply ext_of_complexify_volumeCoordinate
  intro j
  rw [complexify_volumeCoordinate_baseRow, baseL2_vectorHeatGain,
    complexify_volumeCoordinate_l2HeatConvolution, complexify_volumeCoordinate_baseRow]

/-- Actual Leray projection commutes with the actual vector Sobolev heat gain. -/
theorem leraySobolev_vectorHeatGain (t : ℝ≥0) (ht : 0 < (t : ℝ)) (u : VectorH n k) :
    leraySobolev n (k + 1) (vectorHeatGain n k (t : ℝ) ht u) =
      vectorHeatGain n k (t : ℝ) ht (leraySobolev n k u) := by
  have hrow : l2SobolevRow (baseIndex n (k + 1))
        (leraySobolev n (k + 1) (vectorHeatGain n k (t : ℝ) ht u)) =
      l2SobolevRow (baseIndex n (k + 1))
        (vectorHeatGain n k (t : ℝ) ht (leraySobolev n k u)) := by
    rw [l2SobolevRow_leraySobolev, l2SobolevRow_vectorHeatGain,
      lerayProjection_l2HeatConvolution, l2SobolevRow_vectorHeatGain,
      l2SobolevRow_leraySobolev]
  apply PiLp.ext
  intro j
  apply baseL2_injective
  have h := congrArg (fun v ↦ complexifyRealL2 n (volumeCoordinate j v)) hrow
  simpa only [complexify_volumeCoordinate_baseRow] using h

/-- The gaining and order-preserving operators represent the same physical vector field. -/
theorem l2SobolevRow_vectorSelfsimilarHeatGain (τ : ℝ≥0) (hτ : 0 < τ) (u : VectorH n k) :
    l2SobolevRow (baseIndex n (k + 1)) (vectorSelfsimilarHeatGain n k τ hτ u) =
      l2SobolevRow (baseIndex n k) (vectorSelfsimilarHeat n k τ u) := by
  apply ext_of_complexify_volumeCoordinate
  intro j
  rw [complexify_volumeCoordinate_baseRow, complexify_volumeCoordinate_baseRow,
    vectorSelfsimilarHeatGain_apply, vectorSelfsimilarHeat_apply, baseL2_selfsimilarHeatGain_eq]

/-- Forgetting the gained derivative recovers the free evolution. -/
theorem vectorLower_vectorSelfsimilarHeatGain (τ : ℝ≥0) (hτ : 0 < τ) (u : VectorH n k) :
    vectorLower n k (vectorSelfsimilarHeatGain n k τ hτ u) = vectorSelfsimilarHeat n k τ u := by
  apply l2SobolevRow_base_injective
  rw [l2SobolevRow_base_vectorLower, l2SobolevRow_vectorSelfsimilarHeatGain]

/-- Forgetting the top Sobolev order commutes with the Leray projection. -/
theorem vectorLower_leraySobolev (u : VectorH n (k + 1)) :
    vectorLower n k (leraySobolev n (k + 1) u) = leraySobolev n k (vectorLower n k u) :=
  vectorLowerOrderCLM_leraySobolev (Nat.le_succ k) u

/-- Actual Leray projection commutes with self-similar heat gain between Sobolev orders. -/
theorem leraySobolev_vectorSelfsimilarHeatGain (τ : ℝ≥0) (hτ : 0 < τ) (u : VectorH n k) :
    leraySobolev n (k + 1) (vectorSelfsimilarHeatGain n k τ hτ u) =
      vectorSelfsimilarHeatGain n k τ hτ (leraySobolev n k u) := by
  rw [vectorSelfsimilarHeatGain_eq_dilation, map_smul, leraySobolev_vectorDilation,
    leraySobolev_vectorHeatGain (selfsimilarHeatTime τ) (selfsimilarHeatTime_pos hτ),
    vectorSelfsimilarHeatGain_eq_dilation]

/-- The actual Sobolev Leray projector commutes with the vector free semigroup. -/
theorem leraySobolev_vectorSelfsimilarHeat (τ : ℝ≥0) (u : VectorH n k) :
    leraySobolev n k (vectorSelfsimilarHeat n k τ u) =
      vectorSelfsimilarHeat n k τ (leraySobolev n k u) := by
  rcases eq_or_lt_of_le τ.property with hτ | hτ
  · have hzero : τ = 0 := NNReal.coe_injective hτ.symm
    subst τ
    simp only [vectorSelfsimilarHeat_zero]
  · have hpos : 0 < τ := hτ
    apply l2SobolevRow_base_injective
    rw [l2SobolevRow_leraySobolev,
      ← l2SobolevRow_vectorSelfsimilarHeatGain τ hpos,
      ← l2SobolevRow_leraySobolev, leraySobolev_vectorSelfsimilarHeatGain,
      l2SobolevRow_vectorSelfsimilarHeatGain]

/-- Free self-similar evolution preserves the actual distributionally solenoidal subspace. -/
theorem vectorSelfsimilarHeat_base_mem_solenoidal (τ : ℝ≥0) (u : VectorH n k)
    (hu : l2SobolevRow (baseIndex n k) u ∈ l2Solenoidal n) :
    l2SobolevRow (baseIndex n k) (vectorSelfsimilarHeat n k τ u) ∈ l2Solenoidal n := by
  have hfix : leraySobolev n k u = u := by
    apply l2SobolevRow_base_injective
    rw [l2SobolevRow_leraySobolev, lerayProjection_eq_self hu]
  have h := lerayProjection_mem n
    (l2SobolevRow (baseIndex n k) (vectorSelfsimilarHeat n k τ u))
  rwa [← l2SobolevRow_leraySobolev, leraySobolev_vectorSelfsimilarHeat, hfix] at h

/-- The physical gaining field is distributionally solenoidal whenever its input is. -/
theorem vectorSelfsimilarHeatGain_base_mem_solenoidal (τ : ℝ≥0) (hτ : 0 < τ) (u : VectorH n k)
    (hu : l2SobolevRow (baseIndex n k) u ∈ l2Solenoidal n) :
    l2SobolevRow (baseIndex n (k + 1)) (vectorSelfsimilarHeatGain n k τ hτ u) ∈ l2Solenoidal n := by
  rw [l2SobolevRow_vectorSelfsimilarHeatGain]
  exact vectorSelfsimilarHeat_base_mem_solenoidal τ u hu

end HeatEquation.WholeSpace
