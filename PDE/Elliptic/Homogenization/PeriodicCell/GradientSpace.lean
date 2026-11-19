/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Torus

/-!
# The closed space of periodic gradients

The cell problem is first solved for its gradient in this closed subspace of `L²`.
Its generators are derivatives of periodic potentials on Mathlib's torus.
Every element has zero mean and admits approximation by these generators.
Reconstruction of a periodic Sobolev potential uses a Poincaré estimate
(`PeriodicCell.Potential`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace

namespace PDE.Elliptic.Homogenization.PeriodicCell

/-- Constant vector fields embed isometrically into the periodic cell Hilbert space. -/
def constantField (n : ℕ) : (ℝ^n) →ₗᵢ[ℝ] Lp (ℝ^n) 2 (cellMeasure n) where
  toLinearMap := Lp.constₗ 2 (cellMeasure n) ℝ
  norm_map' ξ := by
    change ‖Lp.const 2 (cellMeasure n) ξ‖ = ‖ξ‖
    simp [Lp.norm_const 2]

/-- The subspace of continuous gradients of periodic differentiable potentials. -/
def continuousGradientSpace (n : ℕ) : Submodule ℝ (Lp (ℝ^n) 2 (cellMeasure n)) where
  carrier := {v | ∃ (u : C(UnitAddTorus (Fin n), ℝ))
    (g : C(UnitAddTorus (Fin n), ℝ^n)),
    (∀ (x : UnitAddTorus (Fin n)) (i : Fin n) (t : ℝ),
      HasDerivAt (fun s ↦ u (x + coordinateShift i s))
        (g (x + coordinateShift i t) i) t) ∧
    v = ContinuousMap.toLp 2 (cellMeasure n) ℝ g}
  zero_mem' := by
    refine ⟨0, 0, fun x i t ↦ ?_, ?_⟩
    · simpa using hasDerivAt_const t (0 : ℝ)
    · exact (map_zero _).symm
  add_mem' := by
    rintro v w ⟨u, g, hg, rfl⟩ ⟨u', g', hg', rfl⟩
    refine ⟨u + u', g + g', fun x i t ↦ ?_, (map_add _ _ _).symm⟩
    exact (hg x i t).add (hg' x i t)
  smul_mem' := by
    rintro c v ⟨u, g, hg, rfl⟩
    refine ⟨c • u, c • g, fun x i t ↦ ?_, (map_smul _ _ _).symm⟩
    exact (hg x i t).const_smul c

/-- The closure in `L²` of gradients of periodic potentials. -/
def gradientSpace (n : ℕ) : Submodule ℝ (Lp (ℝ^n) 2 (cellMeasure n)) :=
  (continuousGradientSpace n).topologicalClosure

/-- The closed gradient subspace is a Hilbert space. -/
instance gradientSpace_complete (n : ℕ) : CompleteSpace (gradientSpace n) :=
  (continuousGradientSpace n).isClosed_topologicalClosure.completeSpace_coe

/-- A continuous periodic gradient has zero vector mean. -/
theorem integral_gradient_eq_zero {n : ℕ}
    (u : C(UnitAddTorus (Fin n), ℝ)) (g : C(UnitAddTorus (Fin n), ℝ^n))
    (hd : ∀ (x : UnitAddTorus (Fin n)) (i : Fin n) (t : ℝ),
      HasDerivAt (fun s ↦ u (x + coordinateShift i s))
        (g (x + coordinateShift i t) i) t) :
    (∫ x, g x ∂cellMeasure n) = 0 := by
  ext i
  have hint : Integrable g (cellMeasure n) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
  change (∫ x, g x i ∂cellMeasure n) = (∫ x, g x ∂cellMeasure n) i at he
  rw [← he, integral_gradient_coordinate_eq_zero u g hd]
  rfl

/-- Constants are orthogonal to the closed periodic gradient subspace. -/
theorem constantField_orthogonal_gradientSpace {n : ℕ} (ξ : ℝ^n) (g : gradientSpace n) :
    ⟪constantField n ξ, (g : Lp (ℝ^n) 2 (cellMeasure n))⟫_ℝ = 0 := by
  let L := innerSL ℝ (constantField n ξ)
  have hle : gradientSpace n ≤ L.ker := by
    apply Submodule.topologicalClosure_minimal _ _ L.isClosed_ker
    rintro v ⟨u, g, hg, rfl⟩
    change ⟪constantField n ξ, ContinuousMap.toLp 2 (cellMeasure n) ℝ g⟫_ℝ = 0
    rw [L2.inner_def]
    calc
      _ = ∫ x, ⟪ξ, g x⟫_ℝ ∂cellMeasure n := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_const 2 (cellMeasure n) ξ,
          ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) g] with x hx hy
        exact congrArg₂ (fun v w : ℝ^n ↦ ⟪v, w⟫_ℝ) hx hy
      _ = ⟪ξ, ∫ x, g x ∂cellMeasure n⟫_ℝ :=
        integral_inner
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) ξ
      _ = 0 := by rw [integral_gradient_eq_zero u g hg, inner_zero_right]
  exact hle g.property

/-- Every element of the closed gradient space is a limit of periodic gradients. -/
theorem exists_gradient_approximation {n : ℕ} (g : gradientSpace n) :
    ∃ v : ℕ → Lp (ℝ^n) 2 (cellMeasure n),
      (∀ k, v k ∈ continuousGradientSpace n) ∧
      Tendsto v atTop (𝓝 (g : Lp (ℝ^n) 2 (cellMeasure n))) := by
  exact mem_closure_iff_seq_limit.mp g.property

end PDE.Elliptic.Homogenization.PeriodicCell
