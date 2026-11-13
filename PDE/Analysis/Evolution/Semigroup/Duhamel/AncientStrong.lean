/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientWeighted

/-!
# Ancient smoothing with a jointly continuous kernel action

The weighted Green operator on ancient paths needs continuity of `(r, u) ↦ K r u`
at positive lag. Operator-norm continuity of `K` is unnecessary, so the operator
applies to free self-similar evolution, whose physical dilation is only strongly
continuous. A kernel continuous in operator norm acts jointly continuously.

The Gamma majorant and weighted estimates are those of `AncientSmoothing`.
Only the continuity and assembly of the bounded path operator are supplied here.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction MeasureTheory Set
open scoped BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint continuity of the action suffices for continuous past integrands. -/
theorem continuousOn_ancientIntegrand_of_joint
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {t : ℝ}
    (hK : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hf : ContinuousOn f (Iic t)) :
    ContinuousOn (fun r ↦ K r (f (t - r))) (Ioi 0) := by
  apply hK.comp
    (continuous_id.continuousOn.prodMk
      (hf.comp (continuous_const.sub continuous_id).continuousOn
        (fun r hr ↦ sub_le_self t hr.le)))
  exact fun r hr ↦ ⟨hr, mem_univ _⟩

/-- Dominated convergence requires joint strong continuity, without an
operator-norm continuity hypothesis. -/
theorem continuousOn_ancientDuhamel_of_joint
    {K : ℝ → F →L[ℝ] E} {f : ℝ → F} {α ω β M D a : ℝ}
    (hα : α < 1) (hgap : ω < β) (hβ : 0 ≤ β) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hKcont : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (hfcont : ContinuousOn f (Iic a))
    (hf : ∀ s, s ≤ a → ‖f s‖ ≤ D * Real.exp (β * s)) :
    ContinuousOn (ancientDuhamel K f) (Iic a) := by
  apply continuousOn_of_dominated
    (bound := fun r ↦ (M * D * Real.exp (β * a)) * smoothingWeight α (β - ω) r)
  · intro t ht
    exact (continuousOn_ancientIntegrand_of_joint hKcont
      (hfcont.mono (Iic_subset_Iic.mpr ht))).aestronglyMeasurable measurableSet_Ioi
  · intro t ht
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    calc
      _ ≤ (M * D * Real.exp (β * t)) * smoothingWeight α (β - ω) r :=
        norm_ancientIntegrand_le hM (hK r hr) hr
          (hf (t - r) ((sub_le_self t hr.le).trans ht))
      _ ≤ (M * D * Real.exp (β * a)) * smoothingWeight α (β - ω) r := by
        apply mul_le_mul_of_nonneg_right _ (by
          unfold smoothingWeight
          exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_nonneg _))
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hβ)) (mul_nonneg hM hD)
  · exact (integrableOn_smoothingWeight hα (sub_pos.mpr hgap)).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (K r).continuous.comp_continuousOn
      (hfcont.comp (continuous_id.sub continuous_const).continuousOn
        (fun t ht ↦ (sub_le_self t hr.le).trans ht))

variable {α ω β η M a : ℝ} {K : ℝ → F →L[ℝ] E}

/-- The lifted forcing has a genuine integrable past under joint strong continuity. -/
theorem integrableOn_ancientLift_of_joint
    (hα : α < 1) (hgap : ω < β) (hM : 0 ≤ M)
    (hKcont : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (u : Iic a →ᵇ F) (t : ℝ) :
    IntegrableOn (fun r ↦ K r (ancientLift β u (t - r))) (Ioi 0) :=
  integrableOn_ancientIntegrand hα hgap hM hK
    (fun s _ ↦ norm_ancientLift_le β u s)
    ((continuousOn_ancientIntegrand_of_joint hKcont
      (ancientLift β u).continuous.continuousOn).aestronglyMeasurable measurableSet_Ioi)

/-- The weighted past operator for a jointly continuous kernel action. -/
def ancientDuhamelOperatorOfJoint
    (hα : α < 1) (hgap : ω < β) (hweight : η ≤ β) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hKcont : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r)) :
    (Iic a →ᵇ F) →L[ℝ] (Iic a →ᵇ E) := by
  let C := M * smoothingMass α (β - ω) * Real.exp ((β - η) * a)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg hM (smoothingMass_nonneg hα (sub_pos.mpr hgap))) (Real.exp_nonneg _)
  let I (u : Iic a →ᵇ F) : C(Iic a, E) :=
    { toFun t := Real.exp (-(η * (t : ℝ))) • ancientDuhamel K (ancientLift β u) t
      continuous_toFun := by
        apply (Real.continuous_exp.comp
          (continuous_const.mul continuous_subtype_val).neg).smul
        exact (continuousOn_ancientDuhamel_of_joint hα hgap hβ hM (norm_nonneg u) hKcont hK
          (ancientLift β u).continuous.continuousOn
          (fun s _ ↦ norm_ancientLift_le β u s)).comp_continuous
            continuous_subtype_val (fun t ↦ t.property) }
  have hI (u : Iic a →ᵇ F) (t : Iic a) : ‖I u t‖ ≤ C * ‖u‖ :=
    norm_weighted_ancientDuhamel_le hα hgap hweight hM (norm_nonneg u) t.property hK
      (fun s _ ↦ norm_ancientLift_le β u s)
  let T : (Iic a →ᵇ F) →ₗ[ℝ] (Iic a →ᵇ E) :=
    { toFun u := ofNormedAddCommGroup (I u) (I u).continuous (C * ‖u‖) (hI u)
      map_add' u v := by
        ext t
        change Real.exp (-(η * (t : ℝ))) •
            ancientDuhamel K (ancientLift β (u + v)) t =
          Real.exp (-(η * (t : ℝ))) • ancientDuhamel K (ancientLift β u) t +
            Real.exp (-(η * (t : ℝ))) • ancientDuhamel K (ancientLift β v) t
        have hlift : (ancientLift β (u + v) : ℝ → F) =
            fun s ↦ ancientLift β u s + ancientLift β v s := by
          funext s
          change Real.exp (β * s) • (u _ + v _) =
            Real.exp (β * s) • u _ + Real.exp (β * s) • v _
          exact smul_add _ _ _
        rw [hlift]
        simp only [ancientDuhamel, map_add]
        rw [integral_add (integrableOn_ancientLift_of_joint hα hgap hM hKcont hK u t)
          (integrableOn_ancientLift_of_joint hα hgap hM hKcont hK v t), smul_add]
      map_smul' c u := by
        ext t
        change Real.exp (-(η * (t : ℝ))) •
            (∫ r in Ioi (0 : ℝ), K r
              (Real.exp (β * ((t : ℝ) - r)) • (c • u _))) =
          c • (Real.exp (-(η * (t : ℝ))) •
            (∫ r in Ioi (0 : ℝ), K r
              (Real.exp (β * ((t : ℝ) - r)) • u _)))
        simp_rw [smul_comm (Real.exp _) c, map_smul]
        rw [integral_smul, smul_comm] }
  exact T.mkContinuous C (fun u ↦ norm_ofNormedAddCommGroup_le (I u).continuous
    (mul_nonneg hC (norm_nonneg u)) (hI u))

/-- The weighted operator evaluates to the normalized physical integral. -/
@[simp]
theorem ancientDuhamelOperatorOfJoint_apply
    (hα : α < 1) (hgap : ω < β) (hweight : η ≤ β) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hKcont : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r))
    (u : Iic a →ᵇ F) (t : Iic a) :
    ancientDuhamelOperatorOfJoint hα hgap hweight hβ hM hKcont hK u t =
      Real.exp (-(η * (t : ℝ))) • ancientDuhamel K (ancientLift β u) t :=
  rfl

/-- The operator norm retains the exact Gamma mass and terminal-time weight gain. -/
theorem norm_ancientDuhamelOperatorOfJoint_le
    (hα : α < 1) (hgap : ω < β) (hweight : η ≤ β) (hβ : 0 ≤ β) (hM : 0 ≤ M)
    (hKcont : ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ))
    (hK : ∀ r, 0 < r → ‖K r‖ ≤ M * r ^ (-α) * Real.exp (ω * r)) :
    ‖ancientDuhamelOperatorOfJoint (a := a) hα hgap hweight hβ hM hKcont hK‖ ≤
      M * smoothingMass α (β - ω) * Real.exp ((β - η) * a) := by
  unfold ancientDuhamelOperatorOfJoint
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg (mul_nonneg hM (smoothingMass_nonneg hα (sub_pos.mpr hgap)))
    (Real.exp_nonneg _)

end PDE.Analysis.Evolution
