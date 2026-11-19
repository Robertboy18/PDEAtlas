/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralEnergy.Trace
public import PDE.Analysis.Evolution.Time.GronwallInterior
public import PDE.Fluid.DeGregorio.Uniqueness.Rescaled.WeakEnergy
import CAS.ExactTactic

/-!
# Support preservation by exterior energy on an open slab

The fields are jointly C¹ on the open slab `ℝ × (a, b)`. If the boundary fluxes
`(U + cl x) ω²` vanish at `l` and `r`, the energy `∫ₗʳ ω²` obeys a linear differential
inequality with a uniform coefficient. Pointwise time traces and bounded amplitudes
supply continuity at the endpoints `a` and `b`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Analysis.Evolution

namespace DeGregorio

/-- If `ω(·, a)` vanishes on `(l, r)` and the fluxes `(U + cl x) ω²` vanish at `l` and
`r` for `t ∈ (a, b)`, then `ω` vanishes on `[l, r] × [a, b]`. The equation is assumed
only for `t ∈ (a, b)`. -/
theorem IsClassicalRescaledSolutionOn.eq_zero_on_interval_of_zero_flux
    {fields : Fields} {cl cw : ℝ → ℝ} {a b l r C : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Ioo a b))
    (hω : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ 1 (Function.uncurry fields.velocity) (univ ×ˢ Ioo a b))
    (hlr : l < r)
    (hcl : ContinuousOn cl (Icc a b)) (hcw : ContinuousOn cw (Icc a b))
    (hspace : ∀ t ∈ Icc a b, Continuous (fun x ↦ fields.vorticity x t))
    (htrace : ∀ x, ContinuousOn (fields.vorticity x) (Icc a b))
    (hvalue : ∀ t ∈ Icc a b, ∀ x, |fields.vorticity x t| ≤ C)
    (hgradient : ∀ t ∈ Ioo a b, ∀ x, |deriv (fun y ↦ fields.velocity y t) x| ≤ C)
    (hleft : ∀ t ∈ Ioo a b,
      (fields.velocity l t + cl t * l) * fields.vorticity l t ^ 2 = 0)
    (hright : ∀ t ∈ Ioo a b,
      (fields.velocity r t + cl t * r) * fields.vorticity r t ^ 2 = 0)
    (hinitial : ∀ x ∈ Ioo l r, fields.vorticity x a = 0) :
    ∀ t ∈ Icc a b, ∀ x ∈ Icc l r, fields.vorticity x t = 0 := by
  let E (t : ℝ) := ∫ x in Icc l r, fields.vorticity x t ^ 2
  have hcont : ContinuousOn E (Icc a b) :=
    continuousOn_integral_sq_Icc_of_traces hspace htrace hvalue l r
  have hnonneg (t : ℝ) : 0 ≤ E t := integral_nonneg fun _ ↦ sq_nonneg _
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun t ↦ 2 * cw t + cl t)
    ((continuousOn_const.mul hcw).add hcl)
  have henergy : ∀ t ∈ Icc a b, E t = 0 := by
    apply eq_zero_on_Icc_of_deriv_le_mul hcont (fun t _ ↦ hnonneg t)
      (K := 3 * C + K)
    · intro t ht
      exact (hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder hω ht l r).differentiableAt
    · intro t ht
      have hωt := contDiff_slice_of_contDiffOn_cylinder hω ht
      have hut := contDiff_slice_of_contDiffOn_cylinder hu ht
      have hpde (x : ℝ) : deriv (fields.vorticity x) t =
          (cw t + deriv (fun y ↦ fields.velocity y t) x) * fields.vorticity x t -
            (fields.velocity x t + cl t * x) *
              deriv (fun y ↦ fields.vorticity y t) x := by
        have h := hsol.transport (x := x) ht
        simp only [one_mul] at h
        cas
      rw [(hasDerivAt_integral_sq_Icc_of_contDiffOn_cylinder hω ht l r).deriv]
      simp_rw [hpde]
      rw [integral_rescaled_square_energy hωt hut hlr.le (cl t) (cw t)
        (hleft t ht) (hright t ht)]
      have hU := hut.continuous_deriv le_rfl
      have hbase : Continuous (fun x ↦
          (2 * cw t + 3 * deriv (fun y ↦ fields.velocity y t) x + cl t) *
            fields.vorticity x t ^ 2) := by fun_prop
      have hmajor : Continuous (fun x ↦ (3 * C + K) * fields.vorticity x t ^ 2) := by
        fun_prop
      calc
        _ ≤ ∫ x in Icc l r, (3 * C + K) * fields.vorticity x t ^ 2 := by
          apply integral_mono_ae hbase.integrableOn_Icc hmajor.integrableOn_Icc
          filter_upwards with x
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          have hg := (le_abs_self _).trans (hgradient t ht x)
          have hk := (le_abs_self _).trans (hK t (Ioo_subset_Icc_self ht))
          linarith
        _ = _ := integral_const_mul _ _
    · change (∫ x in Icc l r, fields.vorticity x a ^ 2) = 0
      rw [integral_Icc_eq_integral_Ioo]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hinitial x hx, zero_pow (by decide : 2 ≠ 0)]
  intro t ht
  exact eq_zero_on_Icc_of_integral_sq_eq_zero hlr (hspace t ht) (henergy t ht)

/-- Fixed zero-velocity boundaries preserve the initial support interval on
the whole closed time interval. A finite common enclosure is needed only on
the open slab; the endpoint conclusions follow from the traces. -/
theorem IsClassicalRescaledSolutionOn.support_on_closed_slab_of_initialData
    {fields : Fields} {cl cw : ℝ → ℝ} {a b L R C : ℝ}
    (hsol : IsClassicalRescaledSolutionOn 1 fields cl cw (Ioo a b))
    (hω : ContDiffOn ℝ 1 (Function.uncurry fields.vorticity) (univ ×ˢ Ioo a b))
    (hu : ContDiffOn ℝ 1 (Function.uncurry fields.velocity) (univ ×ˢ Ioo a b))
    (hab : a < b) (hL : 0 < L) (hR : 0 ≤ R)
    (hcl : ContinuousOn cl (Icc a b)) (hcw : ContinuousOn cw (Icc a b))
    (hspace : ∀ t ∈ Icc a b, Continuous (fun x ↦ fields.vorticity x t))
    (htrace : ∀ x, ContinuousOn (fields.vorticity x) (Icc a b))
    (hvalue : ∀ t ∈ Icc a b, ∀ x, |fields.vorticity x t| ≤ C)
    (hgradient : ∀ t ∈ Ioo a b, ∀ x, |deriv (fun y ↦ fields.velocity y t) x| ≤ C)
    (henclosure : ∀ t ∈ Ioo a b, ∀ x, x ∉ Ioo (-R) R → fields.vorticity x t = 0)
    (hleft : ∀ t ∈ Ioo a b, fields.velocity (-L) t + cl t * (-L) = 0)
    (hright : ∀ t ∈ Ioo a b, fields.velocity L t + cl t * L = 0)
    (hinitial : Function.support (fun x ↦ fields.vorticity x a) ⊆ Icc (-L) L) :
    ∀ t ∈ Icc a b, ∀ x ∉ Icc (-L) L, fields.vorticity x t = 0 := by
  let S := R + L + 1
  have hLS : L < S := by dsimp [S]; linarith
  have hRS : R ≤ S := by dsimp [S]; linarith
  have hz (t : ℝ) (ht : t ∈ Ioo a b) (x : ℝ) (hx : x ∉ Ioo (-R) R) :=
    henclosure t ht x hx
  have hinit (x : ℝ) (hx : x ∉ Icc (-L) L) : fields.vorticity x a = 0 := by
    by_contra hne
    exact hx (hinitial hne)
  have hrightZero := hsol.eq_zero_on_interval_of_zero_flux hω hu hLS hcl hcw
    hspace htrace hvalue hgradient
    (fun t ht ↦ by rw [hright t ht, zero_mul])
    (fun t ht ↦ by
      rw [hz t ht S (fun hx ↦ (not_lt_of_ge hRS) hx.2),
        zero_pow (by decide : 2 ≠ 0), mul_zero])
    (fun x hx ↦ hinit x (fun h ↦ (not_lt_of_ge h.2) hx.1))
  have hleftZero := hsol.eq_zero_on_interval_of_zero_flux hω hu (neg_lt_neg hLS)
    hcl hcw hspace htrace hvalue hgradient
    (fun t ht ↦ by
      rw [hz t ht (-S) (fun hx ↦ (not_lt_of_ge (neg_le_neg hRS)) hx.1),
        zero_pow (by decide : 2 ≠ 0), mul_zero])
    (fun t ht ↦ by rw [hleft t ht, zero_mul])
    (fun x hx ↦ hinit x (fun h ↦ (not_lt_of_ge h.1) hx.2))
  intro t ht x hx
  apply eqOn_Icc_of_eqOn_Ioo_of_continuousOn hab (htrace x) continuousOn_const
    (fun s hs ↦ ?_) ht
  by_cases hxS : x ∈ Ioo (-S) S
  · rcases not_and_or.mp hx with hxleft | hxright
    · exact hleftZero s (Ioo_subset_Icc_self hs) x ⟨hxS.1.le, (lt_of_not_ge hxleft).le⟩
    · exact hrightZero s (Ioo_subset_Icc_self hs) x ⟨(lt_of_not_ge hxright).le, hxS.2.le⟩
  · exact hz s hs x (fun hxR ↦ hxS
      ⟨(neg_le_neg hRS).trans_lt hxR.1, hxR.2.trans_le hRS⟩)

end DeGregorio
