/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Translation
public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.StrongDerivative
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Weak derivatives of the actual Leray projection

An `H¹` vector has a strongly differentiable `L²` translation orbit. Translation
commutation lets the bounded Leray operator pass through this derivative.
Applying scalar coordinate maps and the difference-quotient weak-derivative
theorem proves the literal distributional derivative identity for the projected
field. No Sobolev boundedness of the projection is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.Rellich SobolevSpace.GraphSpace.DifferenceQuotient
open scoped Sobolev

namespace IncompressibleFlow

variable {n : ℕ}

/-- The scalar `L²` component of a fluid vector. -/
def l2Coordinate (j : Fin n) : WholeSpaceL2 n →L[ℝ] DerivLp n 2 Set.univ :=
  (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).compLpL 2 (domainMeasure n Set.univ)

/-- Scalar coordinates agree with the physical vector coordinates almost everywhere. -/
theorem l2Coordinate_ae (j : Fin n) (u : WholeSpaceL2 n) :
    l2Coordinate j u =ᵐ[domainMeasure n Set.univ] fun x ↦ u x j :=
  (EuclideanSpace.proj j : ℝ^n →L[ℝ] ℝ).coeFn_compLpL u

/-- Each scalar coordinate of an assembled Euclidean tuple is the corresponding entry. -/
theorem l2Coordinate_euclideanTuple (j : Fin n) (f : Fin n → DerivLp n 2 Set.univ) :
    l2Coordinate j (Lp.euclideanTuple f) = f j := by
  apply Lp.ext
  filter_upwards [l2Coordinate_ae j (Lp.euclideanTuple f), Lp.euclideanTuple_apply_ae f]
    with x hcoord htuple
  exact hcoord.trans (htuple j)

/-- Taking a scalar component commutes with spatial translation. -/
theorem l2Coordinate_translate (j : Fin n) (y : ℝ^n) (u : WholeSpaceL2 n) :
    l2Coordinate j (l2Translate y u) = translateLp 2 y (l2Coordinate j u) := by
  apply Lp.ext
  have hs := (wholeSpace_translation_measurePreserving y).quasiMeasurePreserving.ae
    (l2Coordinate_ae j u)
  filter_upwards [l2Coordinate_ae j (l2Translate y u), l2Translate_ae y u,
    translateLp_apply_ae 2 y (l2Coordinate j u), hs] with x hcoord htrans hscalar hs
  rw [hcoord, htrans, hscalar, hs]

/-- Assembling scalar coordinates commutes with spatial translation. -/
theorem l2Translate_euclideanTuple (y : ℝ^n) (f : Fin n → DerivLp n 2 Set.univ) :
    l2Translate y (Lp.euclideanTuple f) =
      Lp.euclideanTuple (fun j ↦ translateLp 2 y (f j)) := by
  apply Lp.ext
  have hs := (wholeSpace_translation_measurePreserving y).quasiMeasurePreserving.ae
    (Lp.euclideanTuple_apply_ae f)
  filter_upwards [l2Translate_ae y (Lp.euclideanTuple f), hs,
    Lp.euclideanTuple_apply_ae (fun j ↦ translateLp 2 y (f j)),
    ae_all_iff.mpr (fun j ↦ translateLp_apply_ae 2 y (f j))]
    with x htrans hs htuple hscalar
  apply PiLp.ext
  intro j
  rw [htrans, hs j, htuple j, hscalar j]

/-- The vector translation derivative is the vector of actual weak partials. -/
theorem hasDerivAt_l2Translate_H1 (i : Fin n) (U : Fin n → H¹(ℝ^n)) :
    HasDerivAt (fun t : ℝ ↦ l2Translate (t • EuclideanSpace.single i 1)
      (Lp.euclideanTuple (fun j ↦ wkpBaseCoordinateCLM (U j))))
      (Lp.euclideanTuple (fun j ↦ wkpCoordinateCLM (singleDerivIndex n i) (U j))) 0 := by
  have hpi : HasDerivAt
      (fun t : ℝ ↦ fun j : Fin n ↦ translateLp 2 (t • EuclideanSpace.single i 1)
        (wkpBaseCoordinateCLM (U j)))
      (fun j ↦ wkpCoordinateCLM (singleDerivIndex n i) (U j)) 0 :=
    hasDerivAt_pi.mpr (fun j ↦ hasDerivAt_translateLp_base i (U j))
  have h := Lp.euclideanTuple.hasFDerivAt.comp_hasDerivAt 0 hpi
  simpa only [Function.comp_def, ← l2Translate_euclideanTuple] using h

/-- Each projected weak derivative is the actual Leray projection of the
corresponding derivative vector, tested in scalar coordinates. -/
theorem hasWeakDerivativeOn_lerayProjection_H1 (i j : Fin n)
    (U : Fin n → H¹(ℝ^n)) :
    HasWeakDerivativeOn Set.univ [i]
      (l2Coordinate j (lerayProjection n
        (Lp.euclideanTuple (fun l ↦ wkpBaseCoordinateCLM (U l)))))
      (l2Coordinate j (lerayProjection n
        (Lp.euclideanTuple (fun l ↦ wkpCoordinateCLM (singleDerivIndex n i) (U l))))) := by
  have h := (lerayProjection n).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_l2Translate_H1 i U)
  have hc := (l2Coordinate j).hasFDerivAt.comp_hasDerivAt 0 h
  apply hasWeakDerivativeOn_of_hasDerivAt_translateLp i
  simpa only [Function.comp_def, lerayProjection_l2Translate, l2Coordinate_translate] using hc

end IncompressibleFlow
