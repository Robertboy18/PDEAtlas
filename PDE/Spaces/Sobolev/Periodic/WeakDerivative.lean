/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.Definitions

/-!
# Weak derivatives of periodic Sobolev functions

Integration by parts passes from the continuous graph to its closure because
pairing two `L²` functions is continuous. Tests are actual periodic functions
with continuous derivatives along the chosen coordinate.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace

namespace SobolevSpace.Periodic

/-- The gradient coordinate is a distributional derivative on the torus. -/
theorem integral_value_mul_derivative {n : ℕ} (u : h1Space n)
    (φ ψ : C(UnitAddTorus (Fin n), ℝ)) (i : Fin n)
    (hφ : ∀ x t, HasDerivAt (fun s ↦ φ (x + coordinateShift i s))
      (ψ (x + coordinateShift i t)) t) :
    (∫ x, valueCLM n u x * ψ x ∂cellMeasure n) =
      -(∫ x, gradientCLM n u x i * φ x ∂cellMeasure n) := by
  let D := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (cellMeasure n)
  let L : AmbientSpace n →L[ℝ] ℝ :=
    (innerSL ℝ (ContinuousMap.toLp 2 (cellMeasure n) ℝ ψ)).comp (WithLp.fstL 2 ℝ _ _) +
      (innerSL ℝ (ContinuousMap.toLp 2 (cellMeasure n) ℝ φ)).comp
        (D.comp (WithLp.sndL 2 ℝ _ _))
  have he (v : AmbientSpace n) :
      L v = (∫ x, v.fst x * ψ x ∂cellMeasure n) +
        ∫ x, v.snd x i * φ x ∂cellMeasure n := by
    change ⟪ContinuousMap.toLp 2 (cellMeasure n) ℝ ψ, v.fst⟫_ℝ +
      ⟪ContinuousMap.toLp 2 (cellMeasure n) ℝ φ, D v.snd⟫_ℝ = _
    rw [L2.inner_def, L2.inner_def]
    congr 1
    · apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) ψ]
        with x hx
      change v.fst x * ContinuousMap.toLp 2 (cellMeasure n) ℝ ψ x = _
      rw [hx]
    · apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) φ,
        (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL v.snd] with x hx hy
      change D v.snd x * ContinuousMap.toLp 2 (cellMeasure n) ℝ φ x = _
      rw [hx, hy]
      rfl
  have hker : continuousGraph n ≤ L.ker := by
    rintro v ⟨a, g, hg, rfl⟩
    change L (WithLp.toLp 2
      (ContinuousMap.toLp 2 (cellMeasure n) ℝ a,
        ContinuousMap.toLp 2 (cellMeasure n) ℝ g)) = 0
    rw [he]
    let gi : C(UnitAddTorus (Fin n), ℝ) :=
      ⟨fun x ↦ g x i, (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp g.continuous⟩
    have hb := integral_mul_coordinate_derivative a gi φ ψ i (fun x t ↦ hg x i t) hφ
    have h₁ :
        (∫ x, ContinuousMap.toLp 2 (cellMeasure n) ℝ a x * ψ x ∂cellMeasure n) =
          ∫ x, a x * ψ x ∂cellMeasure n := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) a]
        with x hx
      rw [hx]
    have h₂ :
        (∫ x, ContinuousMap.toLp 2 (cellMeasure n) ℝ g x i * φ x ∂cellMeasure n) =
          ∫ x, gi x * φ x ∂cellMeasure n := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (μ := cellMeasure n) (p := 2) (𝕜 := ℝ) g]
        with x hx
      rw [hx]
      rfl
    change (∫ x, ContinuousMap.toLp 2 (cellMeasure n) ℝ a x * ψ x ∂cellMeasure n) +
      (∫ x, ContinuousMap.toLp 2 (cellMeasure n) ℝ g x i * φ x ∂cellMeasure n) = 0
    rw [h₁, h₂, hb, neg_add_cancel]
  have hz : L u.val = 0 :=
    (continuousGraph n).topologicalClosure_minimal hker L.isClosed_ker u.property
  rw [he] at hz
  exact eq_neg_of_add_eq_zero_left hz

end SobolevSpace.Periodic
