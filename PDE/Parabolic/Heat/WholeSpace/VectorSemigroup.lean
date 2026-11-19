/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVector
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple

/-!
# The heat semigroup on vector Sobolev fields and parabolic dilations

`vectorHeat n k t` is the heat evolution `e^{tΔ}` acting componentwise on vector `Hᵏ(ℝⁿ)`. It is
a strongly continuous semigroup, it commutes with forgetting the top order, and it is covariant
under spatial dilations `(δ_a u)(x) = u(a x)`: `e^{tΔ} δ_a = δ_a e^{a² t Δ}`. The free
self-similar evolution is the heat evolution followed by a dilation,
`S₀(τ) = e^{τ/2} δ_{e^{τ/2}} e^{(e^τ - 1) Δ}`. Vector dilations compose multiplicatively and are
jointly continuous in the field and in factors bounded away from zero.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional
open PDE.Analysis.Evolution
open scoped ENNReal NNReal Sobolev

namespace HeatEquation.WholeSpace

set_option linter.missingDocs true

variable {n k : ℕ}

/-- The heat evolution `e^{tΔ}` on vector `Hᵏ(ℝⁿ)`, component by component. -/
def vectorHeat (n k : ℕ) (t : ℝ≥0) : VectorH n k →L[ℝ] VectorH n k :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ heatSobolev n k t)

/-- Each component of the vector heat evolution is the scalar heat evolution. -/
@[simp]
theorem vectorHeat_apply (t : ℝ≥0) (u : VectorH n k) (j : Fin n) :
    vectorHeat n k t u j = heatSobolev n k t (u j) := by
  simp only [vectorHeat, ContinuousLinearMap.piLpMap_apply]

/-- The vector heat evolution at time zero is the identity. -/
@[simp]
theorem vectorHeat_zero (u : VectorH n k) : vectorHeat n k 0 u = u :=
  PiLp.ext fun j ↦ by rw [vectorHeat_apply, heatSobolev_zero]

/-- The vector heat evolution satisfies the semigroup law. -/
theorem vectorHeat_add (s t : ℝ≥0) (u : VectorH n k) :
    vectorHeat n k (s + t) u = vectorHeat n k s (vectorHeat n k t u) :=
  PiLp.ext fun j ↦ by simp only [vectorHeat_apply, heatSobolev_add]

/-- The vector heat evolution has continuous orbits. -/
theorem continuous_vectorHeat (u : VectorH n k) :
    Continuous (fun t : ℝ≥0 ↦ vectorHeat n k t u) := by
  have h : Continuous (fun t : ℝ≥0 ↦ WithLp.toLp 2 fun j ↦ heatSobolev n k t (u j)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ continuous_heatSobolev (u j))
  refine h.congr fun t ↦ ?_
  exact PiLp.ext fun j ↦ (vectorHeat_apply t u j).symm

/-- The vector heat evolution as a strongly continuous semigroup. -/
def vectorHeatSemigroup (n k : ℕ) : StronglyContinuousSemigroup (VectorH n k) where
  toMonoidHom :=
    { toFun := fun t ↦ vectorHeat n k t.toAdd
      map_one' := by
        apply ContinuousLinearMap.ext
        exact vectorHeat_zero
      map_mul' := by
        intro s t
        apply ContinuousLinearMap.ext
        exact vectorHeat_add s.toAdd t.toAdd }
  continuous_toPointwise := by
    apply PointwiseConvergenceCLM.continuous_of_continuous_eval
    exact continuous_vectorHeat

/-- The vector heat semigroup acts by the vector heat evolution. -/
@[simp]
theorem vectorHeatSemigroup_apply (t : ℝ≥0) (u : VectorH n k) :
    vectorHeatSemigroup n k t u = vectorHeat n k t u :=
  rfl

/-- Forgetting the top order commutes with the vector heat evolution. -/
theorem vectorLower_vectorHeat (t : ℝ≥0) (u : VectorH n (k + 1)) :
    vectorLower n k (vectorHeat n (k + 1) t u) = vectorHeat n k t (vectorLower n k u) := by
  refine PiLp.ext fun j ↦ baseL2_injective ?_
  rw [vectorLower_apply, baseL2_lowerOrderCLM, vectorHeat_apply, vectorHeat_apply,
    baseL2_heatSobolev, baseL2_heatSobolev, vectorLower_apply, baseL2_lowerOrderCLM]

/-- Forgetting derivative orders commutes with the vector heat evolution. -/
theorem vectorLowerOrderCLM_vectorHeat {r : ℕ} (hrk : r ≤ k) (t : ℝ≥0) (u : VectorH n k) :
    vectorLowerOrderCLM hrk (vectorHeat n k t u) =
      vectorHeat n r t (vectorLowerOrderCLM hrk u) := by
  refine PiLp.ext fun j ↦ baseL2_injective ?_
  change baseL2 (lowerOrderCLM hrk (vectorHeat n k t u j)) =
    baseL2 (vectorHeat n r t (vectorLowerOrderCLM hrk u) j)
  rw [baseL2_lowerOrderCLM, vectorHeat_apply, vectorHeat_apply, baseL2_heatSobolev,
    baseL2_heatSobolev]
  change heatL2 n t (baseL2 (u j)) = heatL2 n t (baseL2 (lowerOrderCLM hrk (u j)))
  rw [baseL2_lowerOrderCLM]

/-! ### Dilations -/

/-- Equal factors give equal vector dilations. -/
theorem vectorDilation_congr {a b : ℝ} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) :
    vectorDilation n k a ha = vectorDilation n k b hb := by
  subst h
  rfl

/-- Vector dilations compose multiplicatively. -/
theorem vectorDilation_mul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (u : VectorH n k) :
    vectorDilation n k (a * b) (mul_ne_zero ha hb) u =
      vectorDilation n k a ha (vectorDilation n k b hb u) :=
  PiLp.ext fun j ↦ by
    simp only [vectorDilation_apply]
    exact dilationWkpCLM_mul _ a b ha hb (u j)

/-- Forgetting the top order commutes with vector dilations. -/
theorem vectorLower_vectorDilation (a : ℝ) (ha : a ≠ 0) (u : VectorH n (k + 1)) :
    vectorLower n k (vectorDilation n (k + 1) a ha u) =
      vectorDilation n k a ha (vectorLower n k u) := by
  refine PiLp.ext fun j ↦ baseL2_injective ?_
  change baseL2 (lowerOrderCLM (Nat.le_succ k) (vectorDilation n (k + 1) a ha u j)) =
    baseL2 (vectorDilation n k a ha (vectorLower n k u) j)
  rw [baseL2_lowerOrderCLM, vectorDilation_apply, vectorDilation_apply, vectorLower_apply,
    baseL2_dilationWkpCLM, baseL2_dilationWkpCLM, baseL2_lowerOrderCLM]

/-- Parabolic covariance of the vector heat evolution: `e^{tΔ} δ_a = δ_a e^{a² t Δ}`. -/
theorem vectorHeat_vectorDilation (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0) (u : VectorH n k) :
    vectorHeat n k t (vectorDilation n k a ha u) =
      vectorDilation n k a ha (vectorHeat n k (parabolicHeatTime a t) u) :=
  PiLp.ext fun j ↦ by
    simp only [vectorHeat_apply, vectorDilation_apply, heatSobolev_dilationWkpCLM]

/-- The free self-similar evolution is the heat evolution for the time `e^τ - 1` followed by
the dilation `e^{τ/2} δ_{e^{τ/2}}`. -/
theorem vectorSelfsimilarHeat_eq_vectorDilation (τ : ℝ≥0) (u : VectorH n k) :
    vectorSelfsimilarHeat n k τ u = selfsimilarFactor τ • vectorDilation n k (selfsimilarFactor τ)
      (selfsimilarFactor_pos τ).ne' (vectorHeat n k (selfsimilarHeatTime τ) u) :=
  PiLp.ext fun j ↦ by
    simp only [vectorSelfsimilarHeat_apply, selfsimilarHeatSobolev_apply, PiLp.smul_apply,
      vectorDilation_apply, vectorHeat_apply]

/-- Vector dilation is jointly continuous in the field and in factors at least `δ > 0`. -/
theorem continuous_vectorDilation_Ici {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun ua : VectorH n k × Ici δ ↦
      vectorDilation n k ua.2.val (hδ.trans_le ua.2.property).ne' ua.1) := by
  have hj : ∀ j : Fin n, Continuous (fun ua : VectorH n k × Ici δ ↦
      dilationWkpCLM (by norm_num) ua.2.val (hδ.trans_le ua.2.property).ne' (ua.1 j)) := by
    intro j
    have hc := continuous_dilationWkpCLM_Ici (n := n) (k := k) hδ
    have hp : Continuous (fun ua : VectorH n k × Ici δ ↦ (ua.1 j, ua.2)) :=
      ((PiLp.continuous_apply 2 _ j).comp continuous_fst).prodMk continuous_snd
    have h := hc.comp hp
    dsimp only [Function.comp_def] at h
    exact h
  have h : Continuous (fun ua : VectorH n k × Ici δ ↦ WithLp.toLp 2 fun j ↦
      dilationWkpCLM (by norm_num) ua.2.val (hδ.trans_le ua.2.property).ne' (ua.1 j)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi hj)
  refine h.congr fun ua ↦ ?_
  exact PiLp.ext fun j ↦ (vectorDilation_apply _ _ ua.1 j).symm

end HeatEquation.WholeSpace
