/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.InitialPrimitive
public import PDE.Analysis.Evolution.LionsMagenes.Basic.Primitives

/-!
# Lifting a time primitive through a bounded coordinate map

If two velocities represent the same curve in a common space, their primitives
with matching initial values also agree there. A uniform bound on the lifted
velocity controls the lifted primitive by its initial norm and the interval
length. This identifies a higher spatial representative of the same trajectory.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {V X H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {a b : ℝ}

/-- Construct a stronger primitive of the same curve from a stronger velocity
and a matching initial value. The estimate contains no norm of the original curve. -/
theorem exists_lifted_primitive_L2
    (hab : a < b) (J : V →L[ℝ] H) (K : X →L[ℝ] H)
    (u v : Lp V 2 (volume.restrict (Ioc a b)))
    (dU : Lp X 2 (volume.restrict (Ioc a b)))
    (q : V) (Q : X) (hq : J q = K Q)
    (hu : ∀ᵐ t ∂volume.restrict (Ioc a b), u t = q + ∫ s in a..t, v s)
    (hv : ∀ᵐ t ∂volume.restrict (Ioc a b), J (v t) = K (dU t))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖dU t‖ ≤ C) :
    ∃ U : Lp X 2 (volume.restrict (Ioc a b)),
      (∀ᵐ t ∂volume.restrict (Ioc a b), K (U t) = J (u t)) ∧
      HasWeakTimeDerivativeOn (Ioo a b) U dU ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), ‖U t‖ ≤ ‖Q‖ + (b - a) * C := by
  obtain ⟨R, hR, _, hRint, _, _, hRweak⟩ := exists_initial_primitive_L2 dU Q
  have hmem : MemLp R 2 (volume.restrict (Ioc a b)) :=
    memLp_restrict_Ioc_of_continuousOn hR.continuousOn
  let U := hmem.toLp R
  have hU : (U : ℝ → X) =ᵐ[volume.restrict (Ioc a b)] R := hmem.coeFn_toLp
  refine ⟨U, ?_, ?_, ?_⟩
  · filter_upwards [hU, hu, ae_restrict_mem measurableSet_Ioc] with t hUt hut ht
    have htI := Ioc_subset_Icc_self ht
    have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc_left (Icc_subset_uIcc htI)
    have hdint := (intervalIntegrable_coeFn_L2_restrict_Ioc dU hab.le).mono_set hsub
    have hvint := (intervalIntegrable_coeFn_L2_restrict_Ioc v hab.le).mono_set hsub
    have heq : (∫ s in a..t, K (dU s)) = ∫ s in a..t, J (v s) := by
      rw [intervalIntegral.integral_of_le ht.1.le]
      rw [intervalIntegral.integral_of_le ht.1.le]
      apply integral_congr_ae
      exact (hv.mono (fun _ h ↦ h.symm)).filter_mono
        (ae_mono (volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2)))
    rw [hUt, hRint t htI, hut, map_add, map_add, hq,
      ← K.intervalIntegral_comp_comm hdint, ← J.intervalIntegral_comp_comm hvint, heq]
  · exact hRweak.congr_ae_restrict measurableSet_Ioo
      (hU.symm.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      Filter.EventuallyEq.rfl
  · filter_upwards [hU, ae_restrict_mem measurableSet_Ioc] with t hUt ht
    have hi : ‖∫ s in a..t, dU s‖ ≤ C * |t - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const_ae
      rw [uIoc_of_le ht.1.le]
      exact (ae_restrict_iff' measurableSet_Ioc).mp (hbound.filter_mono
        (ae_mono (volume.restrict_mono_set (Ioc_subset_Ioc_right ht.2))))
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1.le)] at hi
    rw [hUt, hRint t (Ioc_subset_Icc_self ht)]
    exact (norm_add_le _ _).trans (add_le_add le_rfl
      (hi.trans (by nlinarith only [ht.2, hC])))

end PDE.Analysis.Evolution
