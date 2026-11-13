/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.IntegratedTrajectory
public import PDE.Analysis.Evolution.Time.WeakDerivative.IntegralIdentity

/-!
# Continuous classical trajectories as weak waves

The two distributional time links and continuity on the closed interval give
both integrated wave identities, including their initial terms. Extending the trajectory by its
endpoint values lets the continuous integral construction be used.
-/

@[expose] public noncomputable section

namespace Hyperbolic.Variational

open Filter MeasureTheory Set PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Continuous energy curves with the two weak time links determine a
weak wave with exactly their initial values and prescribed continuous load. -/
theorem exists_weakWave_of_continuousOn_weak_derivatives (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a < b) {q : ℝ → V} {p : ℝ → H}
    {ell : ℝ → StrongDual ℝ V} (hq : ContinuousOn q (Icc a b)) (hp : ContinuousOn p (Icc a b))
    (hell : ContinuousOn ell (Icc a b))
    (hdq : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.inclusion (q t)) p)
    (hdp :
      HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.pivotToDual (p t)) (fun t ↦ ell t - B (q t))) :
    ∃ (ellLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b)))
      (qLp : Lp V 2 (volume.restrict (Ioc a b)))
      (pLp : Lp H 2 (volume.restrict (Ioc a b)))
      (accLp : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))),
      (ellLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)] ell ∧
      (qLp : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] q ∧
      (pLp : ℝ → H) =ᵐ[volume.restrict (Ioc a b)] p ∧
      (accLp : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
        (fun t ↦ ell t - B (q t)) ∧
      IsGelfandWeakWaveSolution T (fun _ ↦ B) ellLp qLp pLp accLp (q a) (p a) := by
  let trajectory : ℝ → V × H := fun t ↦ (q (projIcc a b hab.le t), p (projIcc a b hab.le t))
  let load : ℝ → StrongDual ℝ V := fun t ↦ ell (projIcc a b hab.le t)
  have htrajectory : Continuous trajectory :=
    ((continuousOn_iff_continuous_domRestrict.mp hq).comp continuous_projIcc).prodMk
      ((continuousOn_iff_continuous_domRestrict.mp hp).comp continuous_projIcc)
  have hload : Continuous load :=
    (continuousOn_iff_continuous_domRestrict.mp hell).comp continuous_projIcc
  have heq {t : ℝ} (ht : t ∈ Icc a b) : trajectory t = (q t, p t) := by
    dsimp only [trajectory]
    rw [projIcc_of_mem hab.le ht]
  have hleq {t : ℝ} (ht : t ∈ Icc a b) : load t = ell t := by
    dsimp only [load]
    rw [projIcc_of_mem hab.le ht]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hacc : ContinuousOn (fun t ↦ ell t - B (q t)) (Icc a b) :=
    hell.sub (B.continuous.comp_continuousOn hq)
  obtain ⟨ellLp, qLp, pLp, accLp, hl, hqt, hpt, hat, hw⟩ :=
    exists_weakWave_of_continuous_integral_equations T B hload htrajectory (q a, p a) hab
      (fun t ht ↦ by
        rw [heq ht]
        calc
          (∫ s in a..t, (trajectory s).2) = ∫ s in a..t, p s := by
            apply intervalIntegral.integral_congr
            intro s hs
            exact congrArg Prod.snd (heq (uIcc_subset_Icc ha ht hs))
          _ = _ := hdq.integral_eq_sub_of_continuousOn hab
            (T.inclusion.continuous.comp_continuousOn hq)
            (hp.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ha ht)
      (fun t ht ↦ by
        rw [heq ht]
        calc
          (∫ s in a..t, load s - B (trajectory s).1) =
              ∫ s in a..t, ell s - B (q s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            change load s - B (trajectory s).1 = ell s - B (q s)
            rw [hleq (uIcc_subset_Icc ha ht hs), heq (uIcc_subset_Icc ha ht hs)]
          _ = _ := hdp.integral_eq_sub_of_continuousOn hab
            (T.pivotToDual.continuous.comp_continuousOn hp)
            (hacc.integrableOn_Icc.mono_set Ioo_subset_Icc_self) ha ht)
  refine ⟨ellLp, qLp, pLp, accLp, ?_, ?_, ?_, ?_, hw⟩
  · filter_upwards [hl, ae_restrict_mem measurableSet_Ioc] with t ht hti
    exact ht.trans (hleq (Ioc_subset_Icc_self hti))
  · filter_upwards [hqt, ae_restrict_mem measurableSet_Ioc] with t ht hti
    exact ht.trans (congrArg Prod.fst (heq (Ioc_subset_Icc_self hti)))
  · filter_upwards [hpt, ae_restrict_mem measurableSet_Ioc] with t ht hti
    exact ht.trans (congrArg Prod.snd (heq (Ioc_subset_Icc_self hti)))
  · filter_upwards [hat, ae_restrict_mem measurableSet_Ioc] with t ht hti
    rw [ht, hleq (Ioc_subset_Icc_self hti), heq (Ioc_subset_Icc_self hti)]

end Hyperbolic.Variational
