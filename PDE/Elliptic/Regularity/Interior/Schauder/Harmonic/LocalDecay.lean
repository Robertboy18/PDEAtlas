/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Harmonic.HolderDecay
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.ExtensionByZero

/-!
# Restricting the Poisson oscillation estimate to interior balls

Zero extension of an `H¹₀` test from an interior ball makes it a legitimate
test in the original open domain. The restriction and zero-extension
pairing identity transports both sides of the weak equation. Consequently
the one-step estimate holds on every interior ball for the original gradient
representatives.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped Sobolev InnerProductSpace NNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

private theorem dirichlet_eq_divergence_restrict
    {Ω V : Set ℝ^n} (hΩ : IsOpen Ω) (hV : IsOpen V) (hsub : V ⊆ Ω)
    (U : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪F j, derivCoordCLM j t⟫_ℝ) (t : H¹₀(V)) :
    (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j)
      (restrictCLM hV.measurableSet hsub U), derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪restrictDerivLp hsub (F j), derivCoordCLM j t⟫_ℝ := by
  have hpair (q : DerivLp n 2 Ω) (j : Fin n) :
      ⟪q, derivCoordCLM j (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hsub t)⟫_ℝ =
        ⟪restrictDerivLp hsub q, derivCoordCLM j t⟫_ℝ :=
    ZeroTrace.inner_zeroExtendH10ToSuperset_coordinate_eq_inner_restrict
      hV hΩ hsub q t (singleDerivIndex n j)
  have hcoord (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) (restrictCLM hV.measurableSet hsub U) =
        restrictDerivLp hsub (wkpCoordinateCLM (singleDerivIndex n j) U) := by
    apply Lp.ext
    simp [wkpCoordinateCLM]
  simpa only [hpair, hcoord] using
    hweak (ZeroTrace.zeroExtendH10ToSuperset hV hΩ hsub t)

variable [Fact (0 < n)]

/-- A weak equation on one open domain gives the Hölder-forcing oscillation
estimate at every interior centre and pair of radii. The averages use the
original weak derivative representatives, so the estimate can be iterated
without making new choices of representatives. -/
theorem meanSquare_gradient_oscillation_le_on_interior_ball
    {Ω : Set ℝ^n} (hΩ : IsOpen Ω) (U : H¹(Ω))
    (F : Fin n → DerivLp n 2 Ω) (f : Fin n → ℝ^n → ℝ) {M γ : ℝ≥0}
    (hf : ∀ j, HolderOnWith M γ (f j) Ω)
    (hF : ∀ j, (F j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f j)
    (hweak : ∀ t : H¹₀(Ω),
      (∑ j, ⟪wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM j t⟫_ℝ) =
        ∑ j, ⟪F j, derivCoordCLM j t⟫_ℝ)
    {z : ℝ^n} {R r : ℝ} (hsub : ball z R ⊆ Ω)
    (hr : 0 < r) (hrR : r ≤ R / 2) (i : Fin n) :
    (⨍ x in ball z r, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
      ⨍ y in ball z r, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) ≤
      4 * (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2 *
        (⨍ x in ball z R, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
          ⨍ y in ball z R, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2) +
      (2 * (R / r) ^ n + 4 * (((2 : ℝ) ^ (2 * n + 3) * n) * (r / R)) ^ 2) *
        ((n : ℝ) * (M * R ^ (γ : ℝ)) ^ 2) := by
  have hR : 0 < R := by linarith
  let V : H¹(ball z R) := restrictCLM isOpen_ball.measurableSet hsub U
  let G (j : Fin n) : DerivLp n 2 (ball z R) := restrictDerivLp hsub (F j)
  have hG (j : Fin n) : (G j : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball z R)] f j :=
    (restrictDerivLp_apply_ae hsub (F j)).trans
      ((hF j).filter_mono (ae_mono (domainMeasure_le hsub)))
  have hV := dirichlet_eq_divergence_restrict hΩ isOpen_ball hsub U F hweak
  have h := meanSquare_gradient_oscillation_le_of_holder_divergence
    V G f (fun j ↦ (hf j).mono hsub) hG hV hr hrR i
  have hrep : (wkpCoordinateCLM (singleDerivIndex n i) V : ℝ^n → ℝ)
      =ᵐ[domainMeasure n (ball z R)] wkpCoordinateCLM (singleDerivIndex n i) U :=
    restrictCLM_apply_ae isOpen_ball.measurableSet hsub U (singleDerivIndex n i)
  have hav (s : ℝ) (hs : s ≤ R) :
      (⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) V x -
        ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) V y‖ ^ 2) =
      ⨍ x in ball z s, ‖wkpCoordinateCLM (singleDerivIndex n i) U x -
        ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2 := by
    have hsrep := hrep.filter_mono
      (ae_mono (Measure.restrict_mono (ball_subset_ball hs) le_rfl))
    rw [average_congr hsrep]
    exact average_congr (hsrep.fun_comp (fun t ↦ ‖t -
      ⨍ y in ball z s, wkpCoordinateCLM (singleDerivIndex n i) U y‖ ^ 2))
  rwa [hav r (hrR.trans (by linarith)), hav R le_rfl] at h

end SobolevSpace.GraphSpace
