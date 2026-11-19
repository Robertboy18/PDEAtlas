/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.HigherEstimates

/-!
# Time integrals of smooth families

For a smooth family `G ρ` of order `m` on `[a, b]` (`PDE.Analysis.IsSmoothFamilyOn`) and
`t, r ∈ [a, b]`, the map `y ↦ ∫ₜʳ G ρ y dρ` is `C^m`; its derivatives are the integrals of the
derivatives (`PDE.Analysis.ODE.iteratedFDeriv_integral_of_isSmoothFamilyOn`).

## Main results

* `IsSmoothFamilyOn.continuous_integral`: the time integral of a jointly continuous family is
  continuous.
* `IsSmoothFamilyOn.contDiff_integral`: the time integral `y ↦ ∫ₜʳ G ρ y dρ` of a smooth family
  of order `m` is `C^m`.
-/

@[expose] public section

open Set MeasureTheory

namespace PDE.Analysis.IsSmoothFamilyOn

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {G : ℝ → E → F} {a b t r : ℝ}

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- The time integral of a jointly continuous family is continuous. -/
theorem continuous_integral (hG : IsSmoothFamilyOn 0 G (Icc a b)) (ht : t ∈ Icc a b)
    (hr : r ∈ Icc a b) : Continuous fun y ↦ ∫ ρ in t..r, G ρ y := by
  have hab : a ≤ b := ht.1.trans ht.2
  have hc : Continuous fun p : E × ℝ ↦ G (projIcc a b hab p.2) p.1 :=
    (isSmoothFamilyOn_zero_iff.mp hG).comp_continuous
      ((continuous_subtype_val.comp ((continuous_projIcc (h := hab)).comp continuous_snd)).prodMk
        continuous_fst) fun p ↦ ⟨(projIcc a b hab p.2).2, mem_univ _⟩
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y ρ ↦ G (projIcc a b hab ρ) y) hc t r (μ := volume)
  refine hi.congr fun y ↦ intervalIntegral.integral_congr fun ρ hρ ↦ ?_
  simp only [projIcc_of_mem hab (uIcc_subset_Icc ht hr hρ)]

/-- **The time integral of a smooth family of order `m` is `C^m`.** -/
theorem contDiff_integral {m : ℕ} (hG : IsSmoothFamilyOn m G (Icc a b)) (ht : t ∈ Icc a b)
    (hr : r ∈ Icc a b) : ContDiff ℝ m fun y ↦ ∫ ρ in t..r, G ρ y := by
  induction m generalizing F with
  | zero => exact contDiff_zero.mpr (hG.continuous_integral ht hr)
  | succ m ih =>
    have hD : IsSmoothFamilyOn m (fun ρ y ↦ fderiv ℝ (G ρ) y) (Icc a b) :=
      (isSmoothFamilyOn_succ_iff.mp hG).2.2
    have hd (y : E) := ODE.hasFDerivAt_integral_of_isSmoothFamilyOn (hG.mono (by omega)) ht hr y
    have hfd : fderiv ℝ (fun z ↦ ∫ ρ in t..r, G ρ z) =
        fun y ↦ ∫ ρ in t..r, fderiv ℝ (G ρ) y := funext fun y ↦ (hd y).fderiv
    push_cast
    refine contDiff_succ_iff_fderiv.mpr ⟨fun y ↦ (hd y).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih hD

end PDE.Analysis.IsSmoothFamilyOn
