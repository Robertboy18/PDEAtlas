/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarSmoothing
public import PDE.Parabolic.Heat.WholeSpace.Vector

/-!
# Free self-similar heat evolution on vector fields

The scalar physical evolution acts componentwise on vector Sobolev graphs and forms a
strongly continuous semigroup. Its one-derivative gain is the physical vector heat
gain followed by similarity dilation, and it commutes with the free evolution at
earlier and later times.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Componentwise free self-similar evolution on physical vector Sobolev graphs. -/
def vectorSelfsimilarHeat (n k : ℕ) (τ : ℝ≥0) : VectorH n k →L[ℝ] VectorH n k :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ selfsimilarHeatSobolev n k τ)

@[simp]
theorem vectorSelfsimilarHeat_apply (τ : ℝ≥0) (u : VectorH n k) (j : Fin n) :
    vectorSelfsimilarHeat n k τ u j = selfsimilarHeatSobolev n k τ (u j) := by
  simp only [vectorSelfsimilarHeat, ContinuousLinearMap.piLpMap_apply]

@[simp]
theorem vectorSelfsimilarHeat_zero (u : VectorH n k) :
    vectorSelfsimilarHeat n k 0 u = u := by
  apply PiLp.ext
  intro j
  simp only [vectorSelfsimilarHeat_apply, selfsimilarHeatSobolev_zero]

/-- The vector free evolution satisfies the semigroup law at all nonnegative times. -/
theorem vectorSelfsimilarHeat_add (s t : ℝ≥0) (u : VectorH n k) :
    vectorSelfsimilarHeat n k (s + t) u =
      vectorSelfsimilarHeat n k s (vectorSelfsimilarHeat n k t u) := by
  apply PiLp.ext
  intro j
  simp only [vectorSelfsimilarHeat_apply, selfsimilarHeatSobolev_add]

/-- Vector free evolution has continuous Sobolev orbits, including time zero. -/
theorem continuous_vectorSelfsimilarHeat (u : VectorH n k) :
    Continuous (fun τ : ℝ≥0 ↦ vectorSelfsimilarHeat n k τ u) := by
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi (fun j ↦ continuous_selfsimilarHeatSobolev (u j)))

/-- The actual vector free evolution as a strongly continuous semigroup. -/
def vectorSelfsimilarHeatSemigroup (n k : ℕ) : StronglyContinuousSemigroup (VectorH n k) where
  toMonoidHom :=
    { toFun := fun τ ↦ vectorSelfsimilarHeat n k τ.toAdd
      map_one' := by
        apply ContinuousLinearMap.ext
        exact vectorSelfsimilarHeat_zero
      map_mul' := by
        intro s t
        apply ContinuousLinearMap.ext
        exact vectorSelfsimilarHeat_add s.toAdd t.toAdd }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    exact continuous_vectorSelfsimilarHeat

/-- The vector free semigroup acts by the free evolution. -/
@[simp]
theorem vectorSelfsimilarHeatSemigroup_apply (τ : ℝ≥0) (u : VectorH n k) :
    vectorSelfsimilarHeatSemigroup n k τ u = vectorSelfsimilarHeat n k τ u := by
  simp only [vectorSelfsimilarHeatSemigroup, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]

/-- One derivative of actual free self-similar smoothing on vector fields. -/
def vectorSelfsimilarHeatGain (n k : ℕ) (τ : ℝ≥0) (hτ : 0 < τ) :
    VectorH n k →L[ℝ] VectorH n (k + 1) :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ selfsimilarHeatGain n k τ hτ)

@[simp]
theorem vectorSelfsimilarHeatGain_apply (τ : ℝ≥0) (hτ : 0 < τ)
    (u : VectorH n k) (j : Fin n) :
    vectorSelfsimilarHeatGain n k τ hτ u j = selfsimilarHeatGain n k τ hτ (u j) := by
  simp only [vectorSelfsimilarHeatGain, ContinuousLinearMap.piLpMap_apply]

/-- The gaining operator depends only on the time, not on the proof of positivity. -/
theorem vectorSelfsimilarHeatGain_congr {τ τ' : ℝ≥0} (h : τ = τ') (hτ : 0 < τ) (hτ' : 0 < τ') :
    vectorSelfsimilarHeatGain n k τ hτ = vectorSelfsimilarHeatGain n k τ' hτ' := by
  subst h
  rfl

/-- The gaining vector field is physical heat gain followed by similarity dilation. -/
theorem vectorSelfsimilarHeatGain_eq_dilation (τ : ℝ≥0) (hτ : 0 < τ) (u : VectorH n k) :
    vectorSelfsimilarHeatGain n k τ hτ u =
      selfsimilarFactor τ • vectorDilation n (k + 1) (selfsimilarFactor τ)
        (selfsimilarFactor_pos τ).ne'
        (vectorHeatGain n k (selfsimilarHeatTime τ) (selfsimilarHeatTime_pos hτ) u) := by
  apply PiLp.ext
  intro j
  simp only [vectorSelfsimilarHeatGain_apply, selfsimilarHeatGain_apply,
    PiLp.smul_apply, vectorDilation_apply, vectorHeatGain_apply]

/-- Gaining one derivative commutes with later free evolution. -/
theorem vectorSelfsimilarHeatGain_add (s t : ℝ≥0) (ht : 0 < t) (u : VectorH n k) :
    vectorSelfsimilarHeatGain n k (s + t) (by positivity) u =
      vectorSelfsimilarHeat n (k + 1) s (vectorSelfsimilarHeatGain n k t ht u) := by
  apply PiLp.ext
  intro j
  simp only [vectorSelfsimilarHeatGain_apply, vectorSelfsimilarHeat_apply]
  exact selfsimilarHeatGain_add s t ht (u j)

/-- Gaining one derivative also commutes with earlier free evolution. -/
theorem vectorSelfsimilarHeatGain_add_of_pos_left (s t : ℝ≥0) (hs : 0 < s)
    (u : VectorH n k) :
    vectorSelfsimilarHeatGain n k (s + t) (by positivity) u =
      vectorSelfsimilarHeatGain n k s hs (vectorSelfsimilarHeat n k t u) := by
  apply PiLp.ext
  intro j
  simp only [vectorSelfsimilarHeatGain_apply, vectorSelfsimilarHeat_apply]
  exact selfsimilarHeatGain_add_of_pos_left s t hs (u j)

end HeatEquation.WholeSpace
