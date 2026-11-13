/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Representative

/-!
# Continuous representatives of finite weak derivative families

An integrable family of successive weak derivatives gives compatible continuous
representatives at every level except the last. The fundamental theorem retains
the final integrable derivative, and all earlier links are classical derivatives
on the closed interval. The averaging estimate controls each representative
without selecting an initial value.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A finite integrable weak derivative family has compatible continuous
representatives, endpoint derivatives, and uniform integral bounds.
The final integrable component requires no further weak derivative. -/
theorem exists_finite_continuous_representatives_Icc
    {a b : ℝ} (hab : a < b) {k : ℕ} (y : Fin (k + 2) → ℝ → X)
    (hy : ∀ j, IntegrableOn (y j) (Ioo a b))
    (hweak : ∀ j : Fin (k + 1),
      HasWeakTimeDerivativeOn (Ioo a b) (y j.castSucc) (y j.succ)) :
    ∃ R : Fin (k + 1) → ℝ → X,
      (∀ j, Continuous (R j)) ∧
      (∀ j, y j.castSucc =ᵐ[volume.restrict (Ioo a b)] R j) ∧
      (∀ j, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
        R j t - R j s = ∫ r in s..t, y j.succ r) ∧
      (∀ j : Fin k, HasWeakTimeDerivativeOn (Ioo a b) (R j.castSucc) (R j.succ)) ∧
      (∀ j : Fin k, ∀ t ∈ Icc a b,
        HasDerivWithinAt (R j.castSucc) (R j.succ t) (Icc a b) t) ∧
      ∀ j, ∀ t ∈ Icc a b,
        ‖R j t‖ ≤ (b - a)⁻¹ * (∫ r in Ioo a b, ‖y j.castSucc r‖) +
          ∫ r in Ioo a b, ‖y j.succ r‖ := by
  have hrep (j : Fin (k + 1)) :=
    (hweak j).exists_continuous_representative_Icc hab (hy j.succ)
  choose R hcontinuous hae hFTC using hrep
  have hRweak (j : Fin k) :
      HasWeakTimeDerivativeOn (Ioo a b) (R j.castSucc) (R j.succ) :=
    (hweak j.castSucc).congr_ae_restrict measurableSet_Ioo
      (hae j.castSucc) (hae j.succ)
  refine ⟨R, hcontinuous, hae, hFTC, hRweak, ?_, ?_⟩
  · intro j t ht
    exact (hRweak j).hasDerivWithinAt_of_continuousOn hab
      (hcontinuous j.castSucc).continuousOn (hcontinuous j.succ).continuousOn ht
  · intro j t ht
    exact norm_le_average_add_integral_of_intervalIntegral hab
      (hy j.castSucc) (hy j.succ) (hae j) (hFTC j) ht

end PDE.Analysis.Evolution
