/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientBackward
public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientStrong

/-!
# Mixed stable and unstable ancient Duhamel operators

The stable forcing is integrated from the infinite past, and the unstable
forcing is integrated backward from the terminal time and subtracted. The stable
kernel need only act jointly continuously at positive lag, as kernels containing
a dilation do; the unstable kernel is continuous in operator norm, as on a
finite-dimensional unstable space. The operator norm is at most the sum of the
two weighted bounds.

Decoding gives the physical past integral minus the physical future integral.
At the terminal time the future integral vanishes, so a map annihilating the
stable kernel annihilates the output there. This fixes the unstable terminal
coordinate of every mixed fixed point.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {α ω κ η β Ms Mu a : ℝ} {Ks Ku : ℝ → F →L[ℝ] E}

/-- Stable past forcing minus unstable future forcing, in bounded weighted
representatives. The stable kernel need only act jointly continuously at positive
lag; the unstable kernel is continuous in operator norm. -/
def mixedDuhamelOperatorOfJoint
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r))) :
    (Iic a →ᵇ F) →L[ℝ] (Iic a →ᵇ E) :=
  ancientDuhamelOperatorOfJoint hα hgap hweight.le hβ hMs hKsjoint hKs -
    backwardDuhamelOperator hκ hweight hMu hKucont hKu

/-- The mixed operator is the normalized difference of the stable past and the
unstable future integrals. -/
@[simp]
theorem mixedDuhamelOperatorOfJoint_apply
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (u : Iic a →ᵇ F) (t : Iic a) :
    mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu u t =
      Real.exp (-(η * (t : ℝ))) •
        (ancientDuhamel Ks (ancientLift β u) t - backwardDuhamel Ku (ancientLift β u) a t) := by
  simp only [mixedDuhamelOperatorOfJoint, _root_.sub_apply,
    BoundedContinuousFunction.sub_apply, ancientDuhamelOperatorOfJoint_apply,
    backwardDuhamelOperator_apply, smul_sub]

/-- The mixed bound is the sum of the stable Gamma bound and the unstable bound. -/
theorem norm_mixedDuhamelOperatorOfJoint_le
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r))) :
    ‖mixedDuhamelOperatorOfJoint (a := a) hα hgap hweight hβ hκ hMs hMu
      hKsjoint hKucont hKs hKu‖ ≤
      (Ms * smoothingMass α (β - ω) + Mu / (β - η)) * Real.exp ((β - η) * a) := by
  calc
    _ ≤ ‖ancientDuhamelOperatorOfJoint (a := a) hα hgap hweight.le hβ hMs hKsjoint hKs‖ +
        ‖backwardDuhamelOperator (a := a) hκ hweight hMu hKucont hKu‖ := norm_sub_le _ _
    _ ≤ Ms * smoothingMass α (β - ω) * Real.exp ((β - η) * a) +
        Mu / (β - η) * Real.exp ((β - η) * a) :=
      add_le_add (norm_ancientDuhamelOperatorOfJoint_le hα hgap hweight.le hβ hMs hKsjoint hKs)
        (norm_backwardDuhamelOperator_le hκ hweight hMu hKucont hKu)
    _ = _ := by ring

/-- Up to the terminal time, the decoded output is the physical past integral
minus the physical future integral of the decoded forcing. -/
theorem ancientLift_mixedDuhamelOperatorOfJoint
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (u : Iic a →ᵇ F) {t : ℝ} (ht : t ≤ a) :
    ancientLift η
        (mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu u)
        t =
      ancientDuhamel Ks (ancientLift β u) t - backwardDuhamel Ku (ancientLift β u) a t := by
  change Real.exp (η * t) •
    mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu u
      ⟨min t a, min_le_right t a⟩ = _
  rw [mixedDuhamelOperatorOfJoint_apply]
  simp only [min_eq_left ht, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    one_smul]

/-- A path fixed by the mixed operator plus a prescribed path decodes to the
past-minus-future integral equation for its forcing. -/
theorem ancientLift_mixed_fixedPoint_of_joint
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    {g : Iic a →ᵇ F} {b u : Iic a →ᵇ E}
    (hu : u = b +
      mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu g)
    {t : ℝ} (ht : t ≤ a) :
    ancientLift η u t = ancientLift η b t +
      (ancientDuhamel Ks (ancientLift β g) t - backwardDuhamel Ku (ancientLift β g) a t) := by
  rw [← ancientLift_mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint
    hKucont hKs hKu g ht]
  have hv := congrArg (fun w : Iic a →ᵇ E ↦ ancientLift η w t) hu
  simpa only [ancientLift, ContinuousMap.coe_mk, BoundedContinuousFunction.add_apply,
    smul_add] using hv

variable [CompleteSpace E]

/-- At the terminal time the future integral vanishes, so a map annihilating the
stable kernel annihilates the mixed output there. -/
theorem map_mixedDuhamelOperatorOfJoint_terminal
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (P : E →L[ℝ] E) (hP : ∀ r, 0 < r → ∀ x, P (Ks r x) = 0) (u : Iic a →ᵇ F) :
    P (mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu u
      ⟨a, self_mem_Iic⟩) = 0 := by
  rw [mixedDuhamelOperatorOfJoint_apply, backwardDuhamel_self, sub_zero, map_smul,
    map_ancientDuhamel_eq_zero P
      (integrableOn_ancientLift_of_joint hα hgap hMs hKsjoint hKs u a) hP, smul_zero]

/-- A path fixed by the mixed operator plus a prescribed path has the prescribed
terminal coordinate for every forcing, when the stable kernel is annihilated. -/
theorem mixed_fixedPoint_terminal_projection_of_joint
    (hα : α < 1) (hgap : ω < β) (hweight : η < β) (hβ : 0 ≤ β)
    (hκ : η ≤ κ) (hMs : 0 ≤ Ms) (hMu : 0 ≤ Mu)
    (hKsjoint : ContinuousOn (fun p : ℝ × F ↦ Ks p.1 p.2) (Ioi 0 ×ˢ univ))
    (hKucont : Continuous Ku)
    (hKs : ∀ r, 0 < r → ‖Ks r‖ ≤ Ms * r ^ (-α) * Real.exp (ω * r))
    (hKu : ∀ r, 0 ≤ r → ‖Ku r‖ ≤ Mu * Real.exp (-(κ * r)))
    (P : E →L[ℝ] E) (hP : ∀ r, 0 < r → ∀ x, P (Ks r x) = 0)
    {g : Iic a →ᵇ F} {b u : Iic a →ᵇ E}
    (hu : u = b +
      mixedDuhamelOperatorOfJoint hα hgap hweight hβ hκ hMs hMu hKsjoint hKucont hKs hKu g) :
    P (u ⟨a, self_mem_Iic⟩) = P (b ⟨a, self_mem_Iic⟩) := by
  rw [hu, BoundedContinuousFunction.add_apply, map_add,
    map_mixedDuhamelOperatorOfJoint_terminal _ _ _ _ _ _ _ _ _ _ _ P hP, add_zero]

end PDE.Analysis.Evolution
