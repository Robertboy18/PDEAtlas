/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.FirstJet
public import PDE.Analysis.Matrix.Euclidean
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Euclidean values and matrix gradients of finite Sobolev systems

The state is the finite product of scalar Sobolev graph spaces.
Projecting its first jet gives the Euclidean value and flattened
matrix gradient. No new weak graph or choice of derivative is introduced.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {m n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The Euclidean value projection of a finite first jet. -/
def firstJetValueCLM : (Fin m → ℝ × ℝ^n) →L[ℝ] ℝ^m :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i ↦
        (ContinuousLinearMap.fst ℝ ℝ (ℝ^n)).comp (ContinuousLinearMap.proj i))

/-- The full matrix projection of a finite first jet, in Euclidean coordinates. -/
def firstJetGradientCLM : (Fin m → ℝ × ℝ^n) →L[ℝ] ℝ^(m * n) :=
    (EuclideanSpace.equiv (Fin (m * n)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k ↦
        (EuclideanSpace.proj (finProdFinEquiv.symm k).2).comp
          ((ContinuousLinearMap.snd ℝ ℝ (ℝ^n)).comp
            (ContinuousLinearMap.proj (finProdFinEquiv.symm k).1)))

/-- Euclidean values, obtained by projecting the finite first jet. -/
def vectorWkpValueCLM : (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (ℝ^m) p μ :=
  (firstJetValueCLM.compLpL p μ).comp vectorWkpFirstJetCLM

/-- The full weak derivative matrix as a Euclidean field, with Frobenius norm. -/
def vectorWkpGradientCLM : (Fin m → W^{1,p}(Ω)) →L[ℝ] Lp (ℝ^(m * n)) p μ :=
  (firstJetGradientCLM.compLpL p μ).comp vectorWkpFirstJetCLM

/-- The weak matrix gradient of a finite Sobolev family, with its Frobenius field norm.
Use `open scoped Sobolev` and write `∇ u`. With Mathlib's `Gradient` scope also open,
an `Lp` result type distinguishes the weak gradient from a classical gradient. -/
scoped[Sobolev] notation (name := vectorGradient) "∇" =>
  SobolevSpace.GraphSpace.vectorWkpGradientCLM

/-- The value map retains every scalar representative simultaneously. -/
theorem vectorWkpValueCLM_apply_ae (u : Fin m → W^{1,p}(Ω)) :
    ∀ᵐ x ∂μ, ∀ i, vectorWkpValueCLM u x i = wkpBaseCoordinateCLM (u i) x := by
  unfold vectorWkpValueCLM
  filter_upwards [firstJetValueCLM.coeFn_compLpL (vectorWkpFirstJetCLM u),
    vectorWkpFirstJetCLM_apply_ae u] with x hx hj
  intro i
  rw [ContinuousLinearMap.comp_apply, hx, hj]
  rfl

/-- Each matrix entry is exactly the corresponding weak partial derivative. -/
theorem vectorWkpGradientCLM_apply_ae (u : Fin m → W^{1,p}(Ω)) :
    ∀ᵐ x ∂μ, ∀ i j, ∇ u x (finProdFinEquiv (i, j)) =
      ∇ (u i) x j := by
  unfold vectorWkpGradientCLM
  filter_upwards [firstJetGradientCLM.coeFn_compLpL (vectorWkpFirstJetCLM u),
    vectorWkpFirstJetCLM_apply_ae u] with x hx hj
  intro i j
  rw [ContinuousLinearMap.comp_apply, hx, hj]
  change ∇ (u (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1) x
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

/-- Every scalar value norm is controlled by the coupled Euclidean value norm. -/
theorem norm_baseCoordinate_le_vectorWkpValueCLM (u : Fin m → W^{1,p}(Ω)) (i : Fin m) :
    ‖wkpBaseCoordinateCLM (u i)‖ ≤ ‖vectorWkpValueCLM u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [vectorWkpValueCLM_apply_ae u] with x hx
  rw [← hx i]
  exact PiLp.norm_apply_le _ i

/-- Every weak partial derivative is controlled by the full Frobenius field. -/
theorem norm_derivCoordinate_le_vectorWkpGradientCLM
    (u : Fin m → W^{1,p}(Ω)) (i : Fin m) (j : Fin n) :
    ‖(u i : WkpAmbientOn n 1 p Ω) (singleDerivIndex n j)‖ ≤
      ‖∇ u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [vectorWkpGradientCLM_apply_ae u, wkpGradientCLM_apply_ae (u i)]
    with x hx hy
  rw [← hy j, ← hx i j]
  exact PiLp.norm_apply_le _ _

/-- A component gradient is bounded by the full matrix gradient in `Lᵖ`. -/
theorem norm_wkpGradientCLM_le_vectorWkpGradientCLM (u : Fin m → W^{1,p}(Ω)) (i : Fin m) :
    ‖∇ (u i)‖ ≤ n * ‖∇ u‖ := by
  apply (wkpGradientCLM_norm_le_sum (u i)).trans
  calc
    _ ≤ ∑ _j : Fin n, ‖∇ u‖ :=
      Finset.sum_le_sum fun j _ ↦ norm_derivCoordinate_le_vectorWkpGradientCLM u i j
    _ = _ := by simp

/-- Values and the matrix gradient control the product Sobolev norm.
Together with continuity of the two maps, this is a norm equivalence. -/
theorem norm_le_vectorWkpValueCLM_add_gradient (u : Fin m → W^{1,p}(Ω)) :
    ‖u‖ ≤ ‖vectorWkpValueCLM u‖ + n * ‖∇ u‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  apply (ambient_norm_le_base_add_sum_deriv (u i : WkpAmbientOn n 1 p Ω)).trans
  apply add_le_add (norm_baseCoordinate_le_vectorWkpValueCLM u i)
  calc
    _ ≤ ∑ _j : Fin n, ‖∇ u‖ :=
      Finset.sum_le_sum fun j _ ↦ norm_derivCoordinate_le_vectorWkpGradientCLM u i j
    _ = _ := by simp

end SobolevSpace.GraphSpace
