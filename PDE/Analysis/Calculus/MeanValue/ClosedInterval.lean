/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Constancy up to the endpoints of an interval

The mean value theorem gives constancy in the open interval. Continuity extends
that equality to both endpoints, without differentiating an exterior continuation.
-/

@[expose] public section

open Set

namespace PDE

/-- A continuous curve with zero derivative in the open interval is constant on
the closed interval. No derivative at either endpoint is required. -/
theorem constantOn_Icc_of_hasDerivAt_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f 0 t) :
    ∀ t ∈ Icc a b, f t = f a := by
  obtain ⟨c, hconst⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv)
  have heq : EqOn f (fun _ ↦ c) (closure (Ioo a b)) :=
    Set.EqOn.of_subset_closure hconst (by simpa only [closure_Ioo hab.ne] using hc)
      continuousOn_const subset_closure Subset.rfl
  rw [closure_Ioo hab.ne] at heq
  exact fun t ht ↦ (heq ht).trans (heq ⟨le_rfl, hab.le⟩).symm

end PDE
