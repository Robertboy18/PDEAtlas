/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Characterization
public import PDE.Analysis.Evolution.ODE.InvariantGraph.TimeTranslation
public import PDE.Analysis.Evolution.ODE.Linear.Diagonal.CenterProjection

/-!
# Time-shift invariance of the constructed paths

The center coordinates of the constructed path at zero equal its prescribed
center seed. A time shift is again exponentially bounded and solves the same
autonomous equation. Its new seed is the center projection of the value at the
shift time, so the differential characterization identifies it with the
corresponding constructed path.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ} {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- The constructed path has exactly the specified center data at time zero. -/
theorem perronPath_zero_apply_of_rate_eq_zero (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (ξ : ι → ℝ) (i : ι) (hi : rate i = 0) :
    perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ) 0 i =
      ξ i := by
  have heq := congrArg (fun u : ℝ →ᵇ (ι → ℝ) ↦ u 0 i)
    (perronPath_eq η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ))
  change _ = centerSeed hη.le ξ 0 i + _ at heq
  rw [diagonalGreen_zero_apply_of_rate_eq_zero hη rate hgap _ i hi, add_zero] at heq
  have hs := congrArg (fun x : ι → ℝ ↦ x i) (exponentialLift_centerSeed hη.le ξ 0)
  exact heq.trans (by simpa only [exponentialLift_zero] using hs)

/-- The new center data of a shifted path are the center projection of its
value at the shift time. -/
theorem translateWeightedPath_perronPath (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (ξ : ι → ℝ) (hξ : ∀ i, rate i * ξ i = 0) (τ : ℝ) :
    let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ)
    translateWeightedPath hη.le τ u =
      perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
        (centerSeed hη.le (diagonalCenterProjection rate (exponentialLift η u τ))) := by
  let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ)
  apply eq_perronPath_of_hasDerivAt hη rate hgap hN hN0 hsmall _
    (rate_mul_diagonalCenterProjection rate _)
  · intro t
    change HasDerivAt (fun s ↦ exponentialLift η (translateWeightedPath hη.le τ u) s) _ t
    simp only [exponentialLift_translateWeightedPath]
    have hd := (hasDerivAt_perronPath hη rate hgap hN hN0 hsmall ξ hξ (t + τ)).scomp t
      ((hasDerivAt_id t).add_const τ)
    simpa only [u, one_smul, Function.comp_def, id_eq] using hd
  · intro i hi
    have ht := congrArg (fun x : ι → ℝ ↦ x i)
      (exponentialLift_translateWeightedPath hη.le τ u 0)
    simpa only [exponentialLift_zero, zero_add, diagonalCenterProjection_apply, ite_eq_left hi]
      using ht

end PDE.Analysis.Evolution
