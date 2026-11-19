/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientMixed
public import PDE.Analysis.Evolution.Semigroup.Semilinear.AncientAffine

/-!
# Mixed stable and unstable ancient affine-quadratic evolution

The mixed Green operator integrates the stable forcing from the infinite past and
subtracts the unstable forcing integrated backward from the terminal time. With
external forcing, a linear coefficient and a bounded bilinear term in weight `2η`
and the solution in weight `η`, its explicit bound turns source and coefficient
budgets into a unique solution on a closed ball. The fixed point decodes to the
localized ancient equation of Hou--Wang--Yang, Section 2.2, equations
(2.11)--(2.15), and a projection annihilating the stable kernel keeps the
prescribed unstable terminal coordinate.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α ω κ η Ms Mu a : ℝ} {Ks Ku : ℝ → F →L[ℝ] E}

/-- The represented fixed point solves the localized ancient integral equation
with external, linear and quadratic forcing, stable past integral and unstable
future integral. -/
theorem ancientLift_full_fixedPoint_ofJoint
    (hα : α < 1) (hgap : ω < 2 * η) (hη : 0 < η)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (L : Iic a →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F) (f : Iic a →ᵇ F)
    {b u : Iic a →ᵇ E}
    (hu : u = b + mixedDuhamelOperatorOfJoint hα hgap (by linarith : η < 2 * η)
      (by positivity : 0 ≤ 2 * η) hκ hMs hMu hKsjoint hKucont hKs hKu
        (fullPathForcing L B f u)) {t : ℝ} (ht : t ≤ a) :
    ancientLift η u t = ancientLift η b t +
      (ancientDuhamel Ks (fun s ↦ ancientLift (2 * η) f s +
        ancientLift η L s (ancientLift η u s) + B (ancientLift η u s) (ancientLift η u s)) t -
      backwardDuhamel Ku (fun s ↦ ancientLift (2 * η) f s +
        ancientLift η L s (ancientLift η u s) +
        B (ancientLift η u s) (ancientLift η u s)) a t) := by
  have hforcing : (ancientLift (2 * η) (fullPathForcing L B f u) : ℝ → F) =
      fun s ↦ ancientLift (2 * η) f s + ancientLift η L s (ancientLift η u s) +
        B (ancientLift η u s) (ancientLift η u s) :=
    funext (ancientLift_fullPathForcing η L B f u)
  rw [← hforcing]
  exact ancientLift_mixed_fixedPoint_of_joint hα hgap _ _ hκ hMs hMu hKsjoint hKucont
    hKs hKu hu ht

variable [CompleteSpace E]

/-- The mixed Green operator and a bounded linear path operator construct a
solution of the localized ancient affine-quadratic equation from explicit budgets. -/
theorem existsUnique_mixed_affinePath_fixedPoint_of_joint
    {R ℓ : ℝ} (hα : α < 1) (hgap : ω < 2 * η) (hη : 0 < η)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu) (hR : 0 ≤ R)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (T : (Iic a →ᵇ E) →L[ℝ] (Iic a →ᵇ F)) (hT : ‖T‖ ≤ ℓ) (B : E →L[ℝ] E →L[ℝ] F)
    (f : Iic a →ᵇ F) (b : Iic a →ᵇ E)
    (hsource : ‖b‖ +
      ((Ms * smoothingMass α (2 * η - ω) + Mu / η) * Real.exp (η * a)) *
        (‖f‖ + ℓ * R + ‖B‖ * R ^ 2) ≤ R)
    (hsmall : ((Ms * smoothingMass α (2 * η - ω) + Mu / η) * Real.exp (η * a)) *
      (ℓ + 2 * ‖B‖ * R) < 1) :
    ∃! u : Iic a →ᵇ E, ‖u‖ ≤ R ∧
      u = b + mixedDuhamelOperatorOfJoint hα hgap (by linarith : η < 2 * η)
        (by positivity : 0 ≤ 2 * η) hκ hMs hMu hKsjoint hKucont hKs hKu
          (affinePathForcing T B f u) := by
  have hA := (norm_mixedDuhamelOperatorOfJoint_le (a := a) hα hgap (by linarith : η < 2 * η)
    (by positivity : 0 ≤ 2 * η) hκ hMs hMu hKsjoint hKucont hKs hKu).trans_eq
      (by rw [show 2 * η - η = η by ring])
  exact existsUnique_affinePath_fixedPoint _
    (mul_nonneg (add_nonneg (mul_nonneg hMs (smoothingMass_nonneg hα (sub_pos.mpr hgap)))
      (div_nonneg hMu hη.le)) (Real.exp_nonneg _)) hR hA T hT B f b hsource hsmall

/-- The mixed Green operator constructs a solution of the localized ancient
equation with a bounded continuous coefficient path from explicit
external-forcing, coefficient and bilinear budgets. -/
theorem existsUnique_mixedAncientAffine_of_bounds_ofJoint
    {R : ℝ} (hα : α < 1) (hgap : ω < 2 * η) (hη : 0 < η)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu) (hR : 0 ≤ R)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (L : Iic a →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F)
    (f : Iic a →ᵇ F) (b : Iic a →ᵇ E)
    (hsource : ‖b‖ +
      ((Ms * smoothingMass α (2 * η - ω) + Mu / η) * Real.exp (η * a)) *
        (‖f‖ + ‖L‖ * R + ‖B‖ * R ^ 2) ≤ R)
    (hsmall : ((Ms * smoothingMass α (2 * η - ω) + Mu / η) * Real.exp (η * a)) *
      (‖L‖ + 2 * ‖B‖ * R) < 1) :
    ∃! u : Iic a →ᵇ E, ‖u‖ ≤ R ∧
      u = b + mixedDuhamelOperatorOfJoint hα hgap (by linarith : η < 2 * η)
        (by positivity : 0 ≤ 2 * η) hκ hMs hMu hKsjoint hKucont hKs hKu
          (fullPathForcing L B f u) :=
  existsUnique_mixed_affinePath_fixedPoint_of_joint hα hgap hη hκ hMs hMu hR
    hKsjoint hKucont hKs hKu (linearPathOperator L) (norm_linearPathOperator_le L) B f b
    hsource hsmall

/-- The full external, linear and quadratic forcing leaves the prescribed
unstable terminal coordinate unchanged when the stable kernel is annihilated. -/
theorem mixed_fullFixedPoint_terminal_projection_ofJoint
    (hα : α < 1) (hgap : ω < 2 * η) (hη : 0 < η)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (L : Iic a →ᵇ (E →L[ℝ] F)) (B : E →L[ℝ] E →L[ℝ] F) (f : Iic a →ᵇ F)
    (P : E →L[ℝ] E) (hP : ∀ r, 0 < r → ∀ x, P (Ks r x) = 0) {b u : Iic a →ᵇ E}
    (hu : u = b + mixedDuhamelOperatorOfJoint hα hgap (by linarith : η < 2 * η)
      (by positivity : 0 ≤ 2 * η) hκ hMs hMu hKsjoint hKucont hKs hKu
        (fullPathForcing L B f u)) :
    P (u ⟨a, self_mem_Iic⟩) = P (b ⟨a, self_mem_Iic⟩) :=
  mixed_fixedPoint_terminal_projection_of_joint hα hgap _ _ hκ hMs hMu hKsjoint hKucont hKs
    hKu P hP hu

end PDE.Analysis.Evolution
