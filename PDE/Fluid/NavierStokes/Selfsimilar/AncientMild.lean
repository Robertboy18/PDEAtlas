/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.Sobolev
public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarAncient
public import PDE.Analysis.Evolution.Semigroup.Semilinear.AncientAffine

/-!
# Forced free ancient Navier--Stokes in Sobolev spaces

The actual convection `H³ × H³ → H²` and the actual projected free Green
operator give a unique small ancient mild path from explicit contraction
budgets. Decoding retains the physical weak convection, external forcing and
time-dependent coefficient. Solenoidal prescribed paths give solenoidal
solutions. Uniform budgets close at sufficiently early terminal times.

This is the forced free equation. The evolution linearized about a stationary
profile and its unstable modes are not constructed here.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution HeatEquation.WholeSpace NavierStokes.SobolevConvection
open scoped Sobolev BoundedContinuousFunction

namespace NavierStokes.Selfsimilar

/-- The free smoothing mass for forcing in weight `2η` and solution in weight `η`. -/
def ancientMildConstant (η : ℝ) : ℝ :=
  singularSelfsimilarConstant 3 2 0 * smoothingMass (1 / 2) (2 * η)

theorem ancientMildConstant_nonneg {η : ℝ} (hη : 0 < η) :
    0 ≤ ancientMildConstant η :=
  mul_nonneg (singularSelfsimilarConstant_nonneg 3 2 0)
    (smoothingMass_nonneg (by norm_num) (by positivity))

/-- The actual free projected Green operator from vector `H²` to vector `H³` paths. -/
def ancientMildOperator (a η : ℝ) (hη : 0 < η) :
    (Iic a →ᵇ VectorH 3 2) →L[ℝ] (Iic a →ᵇ VectorH 3 3) :=
  ancientSelfsimilarDuhamelOperator 3 2 a η (2 * η) 0
    (by norm_num) (by positivity) (by positivity) (by linarith)

/-- The gain in time weights makes the actual Green norm small at early times. -/
theorem norm_ancientMildOperator_le (a η : ℝ) (hη : 0 < η) :
    ‖ancientMildOperator a η hη‖ ≤ ancientMildConstant η * Real.exp (η * a) := by
  simpa only [ancientMildOperator, ancientMildConstant, sub_zero,
    show 2 * η - η = η by ring] using
    norm_ancientSelfsimilarDuhamelOperator_le (n := 3) (k := 2) a η (2 * η) 0
      (by norm_num) (by positivity) (by positivity) (by linarith)

/-- External and coefficient forcing together with the actual negative weak convection. -/
def mildForcing {a : ℝ}
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2) (u : Iic a →ᵇ VectorH 3 3) :
    Iic a →ᵇ VectorH 3 2 :=
  fullPathForcing (E := VectorH 3 3) (F := VectorH 3 2)
    L (-convection) f u

/-- Actual Sobolev convection and free smoothing give the unique mild path in a ball. -/
theorem existsUnique_ancientMild_of_bounds {a η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    (b : Iic a →ᵇ VectorH 3 3)
    (hsource : ‖b‖ + (ancientMildConstant η * Real.exp (η * a)) *
      (‖f‖ + ‖L‖ * R + ‖convection‖ * R ^ 2) ≤ R)
    (hsmall : (ancientMildConstant η * Real.exp (η * a)) *
      (‖L‖ + 2 * ‖convection‖ * R) < 1) :
    ∃! u : Iic a →ᵇ VectorH 3 3, ‖u‖ ≤ R ∧
      u = b + ancientMildOperator a η hη (mildForcing L f u) := by
  apply existsUnique_fullPath_fixedPoint
    (E := VectorH 3 3) (F := VectorH 3 2)
    (ancientMildOperator a η hη)
    (mul_nonneg (ancientMildConstant_nonneg hη) (Real.exp_nonneg _)) hR
    (norm_ancientMildOperator_le a η hη) L (-convection) f b
  · rw [norm_neg convection]
    exact hsource
  · rw [norm_neg convection]
    exact hsmall

/-- The decoded forcing contains the actual negative weak convection. -/
theorem ancientLift_mildForcing {a : ℝ} (η : ℝ)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    (u : Iic a →ᵇ VectorH 3 3) (t : ℝ) :
    ancientLift (2 * η) (mildForcing L f u) t =
      ancientLift (2 * η) f t +
        ancientLift (F := VectorH 3 3 →L[ℝ] VectorH 3 2)
          η L t (ancientLift η u t) -
        convection (ancientLift η u t) (ancientLift η u t) := by
  simpa only [mildForcing, neg_apply, sub_eq_add_neg] using
    ancientLift_fullPathForcing
      (E := VectorH 3 3) (F := VectorH 3 2) η L (-convection) f u t

/-- The physical forcing in the mild equation has an integrable past kernel. -/
theorem integrableOn_ancientMildForcing {a η : ℝ} (hη : 0 < η)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    (u : Iic a →ᵇ VectorH 3 3) (t : ℝ) :
    IntegrableOn (fun r ↦ projectedSelfsimilarHeatGainKernel 3 2 r
      (ancientLift (2 * η) f (t - r) +
        ancientLift (F := VectorH 3 3 →L[ℝ] VectorH 3 2)
          η L (t - r) (ancientLift η u (t - r)) -
        convection (ancientLift η u (t - r)) (ancientLift η u (t - r)))) (Ioi 0) := by
  simpa only [ancientLift_mildForcing] using
    integrableOn_selfsimilarAncientLift (n := 3) (k := 2) (ω := 0) (β := 2 * η)
      (by norm_num) (by positivity) (mildForcing L f u) t

/-- A fixed point decodes to the literal forced free ancient Navier--Stokes integral. -/
theorem ancientLift_ancientMild_fixedPoint {a η : ℝ} (hη : 0 < η)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    {b u : Iic a →ᵇ VectorH 3 3}
    (hu : u = b + ancientMildOperator a η hη (mildForcing L f u))
    {t : ℝ} (ht : t ≤ a) :
    ancientLift η u t = ancientLift η b t +
      ∫ r in Ioi (0 : ℝ), projectedSelfsimilarHeatGainKernel 3 2 r
        (ancientLift (2 * η) f (t - r) +
          ancientLift (F := VectorH 3 3 →L[ℝ] VectorH 3 2)
            η L (t - r) (ancientLift η u (t - r)) -
          convection (ancientLift η u (t - r)) (ancientLift η u (t - r))) := by
  have hdecode := ancientLift_ancientSelfsimilarDuhamelOperator (n := 3) (k := 2)
    a η (2 * η) 0 (by norm_num) (by positivity) (by positivity) (by linarith)
    (mildForcing L f u) ht
  simp only [ancientLift_mildForcing] at hdecode
  have hv := congrArg (fun w : Iic a →ᵇ VectorH 3 3 ↦ ancientLift η w t) hu
  have hlift : ancientLift η u t = ancientLift η b t +
      ancientLift η (ancientMildOperator a η hη (mildForcing L f u)) t := by
    simpa only [ancientLift, ContinuousMap.coe_mk, BoundedContinuousFunction.add_apply,
      smul_add] using hv
  exact hlift.trans (congrArg (fun x : VectorH 3 3 ↦ ancientLift η b t + x) hdecode)

/-- Solenoidal prescribed paths give solenoidal represented fixed points. -/
theorem leraySobolev_ancientMild_fixedPoint {a η : ℝ} (hη : 0 < η)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    {b u : Iic a →ᵇ VectorH 3 3}
    (hu : u = b + ancientMildOperator a η hη (mildForcing L f u))
    (hb : ∀ t : Iic a, leraySobolev 3 3 (b t) = b t) (t : Iic a) :
    leraySobolev 3 3 (u t) = u t := by
  have hv := congrArg (fun w : Iic a →ᵇ VectorH 3 3 ↦ w t) hu
  simp only [BoundedContinuousFunction.add_apply] at hv
  rw [hv, map_add, hb, ancientMildOperator,
    leraySobolev_ancientSelfsimilarDuhamelOperator]

/-- The physical base field of the decoded fixed point is distributionally solenoidal. -/
theorem ancientMild_fixedPoint_base_mem_solenoidal {a η : ℝ} (hη : 0 < η)
    (L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2))
    (f : Iic a →ᵇ VectorH 3 2)
    {b u : Iic a →ᵇ VectorH 3 3}
    (hu : u = b + ancientMildOperator a η hη (mildForcing L f u))
    (hb : ∀ t : Iic a, leraySobolev 3 3 (b t) = b t) (t : ℝ) :
    l2SobolevRow (baseIndex 3 3) (ancientLift η u t) ∈ l2Solenoidal 3 := by
  have hP : leraySobolev 3 3 (ancientLift η u t) = ancientLift η u t := by
    change leraySobolev 3 3 (Real.exp (η * t) • u ⟨min t a, min_le_right _ _⟩) = _
    rw [map_smul, leraySobolev_ancientMild_fixedPoint hη L f hu hb]
    rfl
  have h := lerayProjection_mem 3 (l2SobolevRow (baseIndex 3 3) (ancientLift η u t))
  rwa [← l2SobolevRow_leraySobolev, hP] at h

/-- Uniform source bounds give a unique actual mild path at every sufficiently early time. -/
theorem exists_early_ancientMild {η R S F₀ L₀ : ℝ}
    (hη : 0 < η) (hR : 0 ≤ R) (hmargin : S < R) :
    ∃ a₀ : ℝ, ∀ a ≤ a₀,
      ∀ L : Iic a →ᵇ (VectorH 3 3 →L[ℝ] VectorH 3 2), ‖L‖ ≤ L₀ →
      ∀ f : Iic a →ᵇ VectorH 3 2, ‖f‖ ≤ F₀ →
      ∀ b : Iic a →ᵇ VectorH 3 3, ‖b‖ ≤ S →
        ∃! u : Iic a →ᵇ VectorH 3 3, ‖u‖ ≤ R ∧
          u = b + ancientMildOperator a η hη (mildForcing L f u) := by
  have hC := ancientMildConstant_nonneg hη
  obtain ⟨a₀, ha₀⟩ := exists_early_fullPath_budgets (C := ancientMildConstant η)
    (P := F₀ + L₀ * R + ‖convection‖ * R ^ 2) (Q := L₀ + 2 * ‖convection‖ * R) hη hmargin
  refine ⟨a₀, fun a ha L hL f hf b hb ↦ ?_⟩
  obtain ⟨hsource, hsmall⟩ := ha₀ a ha
  apply existsUnique_ancientMild_of_bounds hη hR L f b
  · calc
      _ ≤ S + (ancientMildConstant η * Real.exp (η * a)) *
          (F₀ + L₀ * R + ‖convection‖ * R ^ 2) := by gcongr
      _ ≤ R := hsource
  · calc
      _ ≤ (ancientMildConstant η * Real.exp (η * a)) *
          (L₀ + 2 * ‖convection‖ * R) := by gcongr
      _ < 1 := hsmall

end NavierStokes.Selfsimilar
