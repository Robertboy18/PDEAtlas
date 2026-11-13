/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TemperedDistribution.Sobolev.LinearMap
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# Linear maps and finite tuples of fractional Sobolev data

Postcomposition acts on the Bessel distribution and its weighted
`Lp` representative. Finite scalar families therefore assemble into Euclidean
vector data at the same real Sobolev order, including the empty family.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BesselPotentialSpace SchwartzMap ENNReal

namespace BesselPotentialSpace

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
  {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Apply a continuous linear map to a fractional Sobolev datum. -/
def postcomp (L : F →L[ℂ] G) (f : H^{s, p}(E, F)) : H^{s, p}(E, G) where
  toDistr := PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L f.toDistr
  toLp := L.compLpL p volume f.toLp
  bessel_toDistr_eq_toLp := by
    rw [← TemperedDistribution.postcomp_besselPotential,
      f.bessel_toDistr_eq_toLp, TemperedDistribution.postcomp_toTemperedDistribution]

/-- Testing the mapped datum applies the same linear map to its values. -/
@[simp]
theorem toDistr_postcomp_apply (L : F →L[ℂ] G) (f : H^{s, p}(E, F))
    (φ : 𝓢(E, ℂ)) :
    (postcomp L f).toDistr φ = L (f.toDistr φ) := rfl

/-- The underlying distribution of a finite sum is the sum of the underlying
distributions, evaluated on each test function. -/
@[simp]
theorem toDistr_sum_apply {ι : Type*} (I : Finset ι) (f : ι → H^{s, p}(E, F))
    (φ : 𝓢(E, ℂ)) :
    (∑ i ∈ I, f i).toDistr φ = ∑ i ∈ I, (f i).toDistr φ := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih => simp [Finset.sum_insert hi, ih]

/-- Assemble scalar Sobolev data into a Euclidean vector at the same real order. -/
def euclideanTuple {m : ℕ} (f : Fin m → H^{s, p}(E)) :
    H^{s, p}(E, EuclideanSpace ℂ (Fin m)) :=
  ∑ i, postcomp (ContinuousLinearMap.toSpanSingleton ℂ
    (EuclideanSpace.single i (1 : ℂ))) (f i)

/-- Each distributional coordinate of the assembled datum is the original
scalar datum. -/
@[simp]
theorem toDistr_euclideanTuple_apply {m : ℕ} (f : Fin m → H^{s, p}(E))
    (φ : 𝓢(E, ℂ)) (i : Fin m) :
    (euclideanTuple f).toDistr φ i = (f i).toDistr φ := by
  classical
  simp [euclideanTuple, toDistr_sum_apply, Pi.single_apply, mul_ite]

end BesselPotentialSpace
