/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Base
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Variation

import PDE.Analysis.Evolution.ODE.Linear.Scalar.Parametric

/-!
# Smooth dependence of the fixed gate and scalar candidate

The denominator belongs to the reference clock and stays fixed as the signed
coefficients vary. Writing the gate as a linear combination of three fixed
smooth gates gives joint smoothness without repeating the extension argument.
The candidate then uses the parameterized integrating-factor theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open PDE.Analysis.Evolution

/-- The base-normalized gate is jointly smooth in every signed coefficient and
the spatial variable. The fixed-gate theorem supplies each basis function, with its own moments. -/
theorem contDiff_prescribed_clock_gate (L Bhit : ℝ × ℝ → ℝ) (β : Fin 3 → ℝ → ℝ)
    (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j)) (hβcompact : ∀ j, HasCompactSupport (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint : let D0 := parameterizedClockPassageData L Bhit (0, 0); ∀ j i : Fin 3,
      Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i)) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0); ContDiff ℝ ∞
      (fun p : (Fin 3 → ℝ) × ℝ ↦ (Ioo (205 : ℝ) (2051 / 10)).indicator
      (fun y ↦ (∑ j, p.1 j * β j y) / D0.wMinus y) p.2) := by
  classical
  dsimp only
  let D0 := parameterizedClockPassageData L Bhit (0, 0)
  let U : Set ℝ := Ioo (205 : ℝ) (2051 / 10)
  let B : Fin 3 → ℝ → ℝ := fun j ↦ U.indicator (fun y ↦ β j y / D0.wMinus y)
  have hB (j : Fin 3) : ContDiff ℝ ∞ (B j) := by
    let c : Fin 3 → ℝ := fun k ↦ if k = j then 1 else 0
    let v : Fin 3 → ℝ := fun i ↦ ∫ y, (∑ k, c k * β k y) * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i
    have hselected := fixed_base_clock_gate_of_selected_moments
      205 (Bhit (0, 0)) (L (0, 0)) (prescribedSpeedAnchorConstant L Bhit)
      β c v hβsmooth hβcompact hβsupport
      (by simpa only [parameterizedClockPassageData_zero] using hβint)
      (by
        dsimp only [v, D0]
        rw [parameterizedClockPassageData_zero])
    rw [← parameterizedClockPassageData_zero L Bhit] at hselected
    simpa [B, U, c, D0, ite_mul] using hselected.1
  have heq : (fun p : (Fin 3 → ℝ) × ℝ ↦
        U.indicator (fun y ↦ (∑ j, p.1 j * β j y) / D0.wMinus y) p.2) =
      (fun p : (Fin 3 → ℝ) × ℝ ↦ ∑ j, p.1 j * B j p.2) := by
    funext p
    by_cases hp : p.2 ∈ U
    · simp only [B, Set.indicator_of_mem hp, Finset.sum_div, mul_div_assoc]
    · simp only [B, Set.indicator_of_notMem hp, mul_zero, Finset.sum_const_zero]
  change ContDiff ℝ ∞ (fun p : (Fin 3 → ℝ) × ℝ ↦
      U.indicator (fun y ↦ (∑ j, p.1 j * β j y) / D0.wMinus y) p.2)
  rw [heq]
  exact ContDiff.sum (fun j _ ↦
    ((contDiff_apply ℝ (fun _ ↦ ℝ) j).comp contDiff_fst).mul ((hB j).comp contDiff_snd))

/-- The scalar candidate depends smoothly on time, speed, initial displacement,
and signed gate coefficients. This is regularity of the explicit candidate;
agreement with a coupled trajectory requires the separate field calculation. -/
theorem contDiff_prescribed_clock_scalar_candidate {F : ℝ × (ℝ × ℝ) → ℝ × ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun p : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) ↦ (F (p.1, p.2.1)).2 *
      scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (p.2.2, (F (s, p.2.1)).1)) 0 0 p.1) := by
  have hfamily : ContDiff ℝ ∞ (fun p : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) ↦ F (p.1, p.2.1)) :=
    hF.comp (contDiff_fst.prodMk contDiff_snd.fst)
  have hforcing : ContDiff ℝ ∞ (fun p : ℝ × ((ℝ × ℝ) × (Fin 3 → ℝ)) ↦
        b (p.2.2, (F (p.1, p.2.1)).1)) := hb.comp (contDiff_snd.snd.prodMk hfamily.fst)
  exact hfamily.snd.mul
    (contDiff_scalarLinearSolution_uncurry contDiff_const hforcing contDiff_const 0)

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
