/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Superposition
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# First variation of an integral along an Lp line

A density with a derivative of conjugate power growth can be differentiated along
`u + t • v` for `u, v ∈ Lᵖ`, provided its value at `u` is integrable. The same Hölder
bound used for power-growth fluxes bounds the line derivative uniformly for `-1 ≤ t ≤ 1`.
The mean value theorem then controls the change in density by an integrable function,
giving integrability throughout this segment and differentiation under the integral at
`t = 0`. A separate upper-growth bound on the density is unnecessary.

The measure is arbitrary and `1 ≤ p < ∞`; the endpoint `p = 1` uses `q = ∞`.
The derivative need not be continuous. Differentiability and growth hold at every
state outside one fixed null set. Only evaluation of the derivative is required to be
measurable, avoiding a measurable structure on the space of continuous linear maps.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]

/-- An integrable base density and conjugate growth of its derivative give
integrability along `u + t • v` for `-1 ≤ t ≤ 1` and the derivative of its integral
at `t = 0`. Differentiability and growth hold at every state outside a fixed null set;
joint measurability of the density and of the evaluated derivative supplies measurability
along the line.

The conclusion is a derivative along each fixed `Lᵖ` direction, including `p = 1, q = ∞`.
The measure is arbitrary; no continuity of the derivative or upper-growth bound on the
density is required. -/
theorem MemLp.hasDerivAt_integral_of_deriv_growth
    {u v : α → E} (hu : MemLp u p μ) (hv : MemLp v p μ) (hp_top : p ≠ ∞)
    {F : α → E → ℝ} {dF : α → E → E →L[ℝ] ℝ} {h : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hdF : Measurable (fun z : α × E × E ↦ dF z.1 z.2.1 z.2.2))
    (hderiv : ∀ᵐ x ∂μ, ∀ z, HasFDerivAt (F x) (dF x z) z)
    (hh : MemLp h q μ)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ (p.toReal - 1))
    (hbase : Integrable (fun x ↦ F x (u x)) μ) :
    (∀ t ∈ Icc (-1 : ℝ) 1, Integrable (fun x ↦ F x (u x + t • v x)) μ) ∧
      Integrable (fun x ↦ dF x (u x) (v x)) μ ∧
      HasDerivAt (fun t : ℝ ↦ ∫ x, F x (u x + t • v x) ∂μ)
        (∫ x, dF x (u x) (v x) ∂μ) 0 := by
  let M (x : α) :=
    (‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1)) * ‖v x‖
  have hM : Integrable M μ := hu.integrable_rpow_growth_bound hv hp_top hh C
  have hpexp : 0 ≤ p.toReal - 1 := by
    simpa only [
      ENNReal.toReal_sub_of_le (ENNReal.HolderConjugate.one_le p q) hp_top,
      ENNReal.toReal_one] using (ENNReal.toReal_nonneg : 0 ≤ (p - 1).toReal)
  have hline (t : ℝ) : MemLp (fun x ↦ u x + t • v x) p μ :=
    hu.add (hv.const_smul t)
  have hmeas (t : ℝ) : AEStronglyMeasurable (fun x ↦ F x (u x + t • v x)) μ :=
    (hF.comp_aemeasurable
      (aemeasurable_id.prodMk (hline t).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hdiff : ∀ᵐ x ∂μ, ∀ t : ℝ,
      HasDerivAt (fun s : ℝ ↦ F x (u x + s • v x))
        (dF x (u x + t • v x) (v x)) t := by
    filter_upwards [hderiv] with x hx
    intro t
    have hl : HasDerivAt (fun s : ℝ ↦ u x + s • v x) (v x) t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (v x)).const_add (u x)
    simpa only [Function.comp_def] using (hx (u x + t • v x)).comp_hasDerivAt t hl
  have hbound : ∀ᵐ x ∂μ, ∀ t ∈ Icc (-1 : ℝ) 1,
      ‖dF x (u x + t • v x) (v x)‖ ≤ M x := by
    filter_upwards [hgrowth] with x hx
    intro t ht
    have htabs : |t| ≤ 1 := abs_le.mpr ht
    have hnorm : ‖u x + t • v x‖ ≤ ‖u x‖ + ‖v x‖ := by
      calc
        ‖u x + t • v x‖ ≤ ‖u x‖ + ‖t • v x‖ := norm_add_le _ _
        _ ≤ ‖u x‖ + ‖v x‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          nlinarith [norm_nonneg (v x)]
    have hoperator : ‖dF x (u x + t • v x)‖ ≤
        ‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1) := by
      calc
        ‖dF x (u x + t • v x)‖ ≤
            h x + C * ‖u x + t • v x‖ ^ (p.toReal - 1) := hx _
        _ ≤ ‖h x‖ + |C| * ‖u x + t • v x‖ ^ (p.toReal - 1) :=
          add_le_add (by simpa only [Real.norm_eq_abs] using le_abs_self (h x))
            (mul_le_mul_of_nonneg_right (le_abs_self C)
              (Real.rpow_nonneg (norm_nonneg _) _))
        _ ≤ ‖h x‖ + |C| * (‖u x‖ + ‖v x‖) ^ (p.toReal - 1) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hnorm hpexp) (abs_nonneg C))
    exact ((dF x (u x + t • v x)).le_opNorm (v x)).trans
      (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hnear : ∀ t ∈ Icc (-1 : ℝ) 1,
      Integrable (fun x ↦ F x (u x + t • v x)) μ := by
    intro t ht
    apply integrable_of_norm_sub_le (hmeas t) hbase (hM.mul_const ‖t‖)
    filter_upwards [hdiff, hbound] with x hdx hbx
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s (_ : s ∈ Icc (-1 : ℝ) 1) ↦ (hdx s).hasDerivWithinAt) hbx
      (convex_Icc (-1 : ℝ) 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1) ht
    simpa only [zero_smul, add_zero, sub_zero, norm_sub_rev] using hm
  have hdmeas : AEStronglyMeasurable (fun x ↦ dF x (u x) (v x)) μ :=
    (hdF.comp_aemeasurable (aemeasurable_id.prodMk
      (hu.aestronglyMeasurable.aemeasurable.prodMk
        hv.aestronglyMeasurable.aemeasurable))).aestronglyMeasurable
  refine ⟨hnear, ?_⟩
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x ↦ F x (u x + t • v x))
    (F' := fun t x ↦ dF x (u x + t • v x) (v x))
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hmeas) (by simpa only [zero_smul, add_zero] using hbase)
    (by simpa only [zero_smul, add_zero] using hdmeas) hbound hM
    (hdiff.mono fun x hx t _ ↦ hx t)
  simpa only [zero_smul, add_zero] using hint

end MeasureTheory
