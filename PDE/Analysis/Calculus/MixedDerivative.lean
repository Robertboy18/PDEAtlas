/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MeanValue.ClosedInterval
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Mixed derivatives from closed time traces

Integrate the time derivative first, then differentiate its spatial
parameter. Joint continuity of the derivative of the time rate
supplies the local integral bound. The resulting derivative equation includes
both one-sided time endpoints and requires no second time derivative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

private theorem hasDerivAt_intervalIntegral_of_continuous_spatial_deriv
    {r d : ℝ → ℝ → ℝ}
    (hr : Continuous (Function.uncurry r)) (hd : Continuous (Function.uncurry d))
    (hrd : ∀ x t, HasDerivAt (fun y ↦ r y t) (d x t) x) (x t : ℝ) :
    HasDerivAt (fun y ↦ ∫ s in 0..t, r y s) (∫ s in 0..t, d x s) x := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc).exists_bound_of_continuousOn
    (s := Icc (x - 1) (x + 1) ×ˢ uIcc 0 t) hd.continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := r) (F' := d) (bound := fun _ ↦ C)
    (Icc_mem_nhds (by linarith : x - 1 < x) (by linarith : x < x + 1))
    (.of_forall fun y ↦
      (hr.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hr.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t)
    ((hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (.of_forall fun s hs y hy ↦ hC (y, s) ⟨hy, uIoc_subset_uIcc hs⟩)
    intervalIntegrable_const (.of_forall fun s _ y _ ↦ hrd y s)).2

/-- Continuous closed transport values with continuous spatial derivatives
give the mixed derivative, including both one-sided time endpoints.
No joint C² assumption or extension outside the closed interval is used. -/
theorem hasDerivWithinAt_spatial_deriv_of_continuous_transport
    {g r d : ℝ → ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hg : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ g p.1 p.2))
    (hr : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ r p.1 p.2))
    (hd : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ d p.1 p.2))
    (hspace : ∀ t ∈ Icc 0 T, Differentiable ℝ (fun x ↦ g x t))
    (hrd : ∀ x t, t ∈ Icc 0 T → HasDerivAt (fun y ↦ r y t) (d x t) x)
    (htime : ∀ x t, t ∈ Ioo 0 T → HasDerivAt (g x) (r x t) t)
    (x : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s ↦ deriv (fun y ↦ g y s) x) (d x t) (Icc 0 T) t := by
  let R : ℝ → ℝ → ℝ := fun y s ↦ r y (projIcc 0 T hT.le s)
  let D : ℝ → ℝ → ℝ := fun y s ↦ d y (projIcc 0 T hT.le s)
  have hR : Continuous (Function.uncurry R) :=
    hr.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT.le)).comp continuous_snd))
  have hD : Continuous (Function.uncurry D) :=
    hd.comp (continuous_fst.prodMk ((continuous_projIcc (h := hT.le)).comp continuous_snd))
  have hRD (y s : ℝ) : HasDerivAt (fun z ↦ R z s) (D y s) y :=
    hrd y _ (projIcc 0 T hT.le s).property
  have hprimitive (y s : ℝ) : HasDerivAt (fun a ↦ ∫ b in 0..a, R y b) (R y s) s :=
    ((hR.comp (continuous_const.prodMk continuous_id)).integral_hasStrictDerivAt 0 s).hasDerivAt
  have hformula (y s : ℝ) (hs : s ∈ Icc 0 T) :
      g y s = g y 0 + ∫ b in 0..s, R y b := by
    have hc : ContinuousOn (fun a ↦ g y a - ∫ b in 0..a, R y b) (Icc 0 T) := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      exact (hg.comp (continuous_const.prodMk continuous_id)).sub
        ((Differentiable.continuous fun a ↦ (hprimitive y a).differentiableAt).comp
          continuous_subtype_val)
    have hz (a : ℝ) (ha : a ∈ Ioo 0 T) :
        HasDerivAt (fun s ↦ g y s - ∫ b in 0..s, R y b) 0 a := by
      have hp := (htime y a ha).fun_sub (hprimitive y a)
      simpa only [R, projIcc_of_mem hT.le (Ioo_subset_Icc_self ha),
        sub_self] using hp
    have heq := constantOn_Icc_of_hasDerivAt_zero hT hc hz s hs
    rw [intervalIntegral.integral_same, sub_zero] at heq
    linarith
  have hderiv (s : ℝ) (hs : s ∈ Icc 0 T) :
      deriv (fun y ↦ g y s) x = deriv (fun y ↦ g y 0) x + ∫ b in 0..s, D x b := by
    have hp := ((hspace 0 ⟨le_rfl, hT.le⟩ x).hasDerivAt).fun_add
      (hasDerivAt_intervalIntegral_of_continuous_spatial_deriv hR hD hRD x s)
    have heq : (fun y ↦ g y 0 + ∫ b in 0..s, R y b) = fun y ↦ g y s :=
      funext fun y ↦ (hformula y s hs).symm
    rw [heq] at hp
    exact hp.deriv
  have hp : HasDerivWithinAt
      (fun s ↦ deriv (fun y ↦ g y 0) x + ∫ b in 0..s, D x b) (D x t) (Icc 0 T) t :=
    (((hD.comp ((continuous_const (y := x)).prodMk continuous_id)).integral_hasStrictDerivAt
      0 t).hasDerivAt.const_add (deriv (fun y ↦ g y 0) x)).hasDerivWithinAt
  have heq := hp.congr_of_mem hderiv ht
  simpa only [D, projIcc_of_mem hT.le ht] using heq

/-- The transport term `(c + u') g - (c y + u) g'` of two `C²` profiles has derivative
`g u'' - (c x + u) g''`; the two products of first derivatives cancel. -/
theorem hasDerivAt_transport_rhs
    {g u : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hu : ContDiff ℝ 2 u) (c x : ℝ) :
    HasDerivAt (fun y ↦ (c + deriv u y) * g y - (c * y + u y) * deriv g y)
      (g x * deriv (deriv u) x - (c * x + u x) * deriv (deriv g) x) x := by
  have hgd := (hg.differentiable two_ne_zero x).hasDerivAt
  have hud := (hu.differentiable two_ne_zero x).hasDerivAt
  have hgdd := (hg.differentiable_deriv_two x).hasDerivAt
  have hudd := (hu.differentiable_deriv_two x).hasDerivAt
  convert ((hudd.const_add c).fun_mul hgd).fun_sub
    ((((hasDerivAt_id x).const_mul c).fun_add hud).fun_mul hgdd) using 1
  · rfl
  · simp only [id_eq]
    ring

end PDE.Analysis
