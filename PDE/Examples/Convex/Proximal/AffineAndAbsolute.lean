/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.Resolvent.ConvexGradient.Subdifferential
import CAS.ExactTactic

/-!
# Affine and nonsmooth scalar proximal examples

Affine energies need not be bounded below, but their quadratic perturbations have the
constructed resolvent. A shifted absolute value is finite and nonsmooth, with a whole interval
of subgradients at zero.
-/

@[expose] public section

noncomputable section

open PDE.Analysis.Convex

namespace PDE.Examples.ConvexProximal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A signed affine potential on an arbitrary real inner-product space. -/
def affinePotential (a : H) (c : ℝ) (u : H) : ℝ := inner ℝ a u + c

/-- Convexity of the affine example. -/
theorem affinePotential_convex (a : H) (c : ℝ) :
    ConvexOn ℝ Set.univ (affinePotential a c) := by
  refine ⟨convex_univ, fun x _ y _ s t _ _ hst ↦ ?_⟩
  simp only [affinePotential, inner_add_right, real_inner_smul_right, smul_eq_mul]
  nlinarith [congrArg (fun r : ℝ ↦ r * c) hst]

/-- Lower semicontinuity of the signed extended affine example. -/
theorem affinePotential_lowerSemicontinuous (a : H) (c : ℝ) :
    LowerSemicontinuous (fun u ↦ (affinePotential a c u : EReal)) := by
  have hc : Continuous (affinePotential a c) := by unfold affinePotential; fun_prop
  exact (continuous_coe_real_ereal.comp hc).lowerSemicontinuous

/-- The affine slope is an actual subgradient at every point. -/
theorem affinePotential_mem_subdifferential (a u : H) (c : ℝ) :
    a ∈ subdifferential (fun x ↦ (affinePotential a c x : EReal)) u := by
  intro w
  rw [← EReal.coe_add]
  apply EReal.coe_le_coe_iff.2
  simp only [affinePotential, inner_sub_right]
  linarith

variable [CompleteSpace H]

/-- The general resolvent of an affine energy is translation by its negative scaled slope. -/
theorem affinePotential_resolvent (a w : H) (c : ℝ) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    resolvent (fun u ↦ (affinePotential a c u : EReal))
        (isProper_coeReal (affinePotential a c))
        (convex_realEpigraph_coeReal (affinePotential_convex a c))
        (affinePotential_lowerSemicontinuous a c) lambda hlambda w =
      w - lambda • a := by
  apply resolvent_eq_of_mem_subdifferential
    (isProper_coeReal (affinePotential a c))
    (convex_realEpigraph_coeReal (affinePotential_convex a c))
    (affinePotential_lowerSemicontinuous a c) hlambda
    (affinePotential_mem_subdifferential a (w - lambda • a) c)
  exact sub_add_cancel _ _

/-- A nonsmooth real convex energy with negative minimum. -/
def absoluteEnergy (x : ℝ) : EReal := ((|x| - 2 : ℝ) : EReal)

/-- The shifted absolute value is a proper signed energy. -/
theorem absoluteEnergy_isProper : IsProper absoluteEnergy :=
  isProper_coeReal (fun x : ℝ ↦ |x| - 2)

/-- Convexity of the shifted absolute value. -/
theorem absoluteEnergy_convex : Convex ℝ (realEpigraph absoluteEnergy) := by
  apply convex_realEpigraph_coeReal
  change ConvexOn ℝ Set.univ (fun x : ℝ ↦ ‖x‖ + (-2))
  exact convexOn_univ_norm.add_const (-2)

/-- Lower semicontinuity follows from continuity of the absolute value. -/
theorem absoluteEnergy_lowerSemicontinuous : LowerSemicontinuous absoluteEnergy := by
  have hc : Continuous (fun x : ℝ ↦ |x| - 2) := by fun_prop
  exact (continuous_coe_real_ereal.comp hc).lowerSemicontinuous

/-- The subdifferential at the corner is the interval `[-1,1]`. -/
theorem absoluteEnergy_subdifferential_zero :
    subdifferential absoluteEnergy 0 = Set.Icc (-1 : ℝ) 1 := by
  ext v
  constructor
  · intro hv
    have hreal := (mem_subdifferential_iff absoluteEnergy_isProper).1 hv
    have hp := hreal.2 1 (EReal.coe_ne_top _)
    have hn := hreal.2 (-1) (EReal.coe_ne_top _)
    norm_num [absoluteEnergy, Real.inner_apply] at hp hn
    constructor <;> linarith
  · rintro ⟨hvlo, hvhi⟩ w
    have hvabs : |v| ≤ 1 := abs_le.2 ⟨hvlo, hvhi⟩
    have hmul : v * w ≤ |w| :=
      (le_abs_self (v * w)).trans (by
        rw [abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hvabs (abs_nonneg w))
    change absoluteEnergy 0 + (inner ℝ v (w - 0) : EReal) ≤ absoluteEnergy w
    simp only [absoluteEnergy, abs_zero, zero_sub, sub_zero, Real.inner_apply,
      ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

/-- At a positive input, the supporting slope `1` gives the explicit scalar resolvent. -/
theorem absoluteEnergy_resolvent_three :
    resolvent absoluteEnergy absoluteEnergy_isProper absoluteEnergy_convex
      absoluteEnergy_lowerSemicontinuous 1 (by norm_num) 3 = 2 := by
  apply resolvent_eq_of_mem_subdifferential absoluteEnergy_isProper absoluteEnergy_convex
    absoluteEnergy_lowerSemicontinuous (by norm_num : (0 : ℝ) < 1) (v := 1)
  · intro w
    simp only [absoluteEnergy, Real.inner_apply]
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    norm_num
    linarith [le_abs_self w]
  · norm_num

end PDE.Examples.ConvexProximal
