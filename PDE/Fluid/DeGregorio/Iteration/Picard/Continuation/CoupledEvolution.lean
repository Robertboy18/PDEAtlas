/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.SobolevEnergy
public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.CoupledEnergy
public import Mathlib.Analysis.ODE.Gronwall

/-!
# H² propagation from H¹ for the coupled rescaled equation

The H² production estimate and the smooth energy identity of `SobolevEnergy` yield an
exponential estimate with a coefficient depending only on H¹ and the common
rescaling rate.

The joint C³ hypothesis is used to differentiate the energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- Equal rescaling rates preserve the coupled transport form after adding
an affine term to the velocity. The resulting H² differential estimate needs
only the H¹ size of the vorticity and the magnitude of the common rate. -/
theorem norm_deriv_sobolevEnergyTwo_le_of_coupled_rescaled_transport
    {w u : ℝ → ℝ → ℝ} {L t ρ : ℝ}
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hu : ContDiff ℝ 3 (fun y ↦ u y t))
    (hpair : IsHilbertPair (fun x ↦ w x t) (deriv (fun y ↦ u y t)))
    (htransport : ∀ x, deriv (w x) t + (ρ * x + u x t) * deriv (fun y ↦ w y t) x =
      (ρ + deriv (fun y ↦ u y t) x) * w x t)
    (hL : 0 ≤ L) (hsupp : tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L) :
    ‖deriv (sobolevEnergyTwo w L) t‖ ≤
      (3 * |ρ| + 8 * (lpNorm (fun x ↦ w x t) 2 volume +
        lpNorm (deriv (fun x ↦ w x t)) 2 volume)) * sobolevEnergyTwo w L t := by
  let V := fun x s ↦ ρ * x + u x s
  have hV : ContDiff ℝ 3 (fun x ↦ V x t) := (contDiff_const.mul contDiff_id).add hu
  have hV₁ : deriv (fun x ↦ V x t) = fun x ↦ ρ + deriv (fun y ↦ u y t) x := by
    funext x
    exact (((hasDerivAt_id x).const_mul ρ).add
      ((hu.differentiable (by norm_num)) x).hasDerivAt).deriv.trans (by simp)
  have htransportV : ∀ x, deriv (w x) t + V x t * deriv (fun y ↦ w y t) x =
      deriv (fun y ↦ V y t) x * w x t := by
    simpa only [hV₁] using htransport
  let v := fun x ↦ w x t
  have hq : tsupport (deriv v) ⊆ Ioo (-L) L :=
    tsupport_deriv_subset.trans hsupp
  have hr : tsupport (deriv (deriv v)) ⊆ Ioo (-L) L :=
    tsupport_deriv_subset.trans hq
  have hzero (x : ℝ) (hx : x ∉ Ioo (-L) L) :
      v x = 0 ∧ deriv v x = 0 ∧ deriv (deriv v) x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupp h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hq h)),
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hr h))⟩
  have hcompact : HasCompactSupport v :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport v)
      (hsupp.trans Ioo_subset_Icc_self)
  have hv : ContDiff ℝ 3 v :=
    hw.comp (contDiff_id.prodMk contDiff_const)
  have hleft : -L ∉ Ioo (-L) L := by simp
  have hright : L ∉ Ioo (-L) L := by simp
  have hE := hasDerivAt_sobolevEnergyTwo_of_frozen_transport hw hV htransportV hL
    (hzero (-L) hleft) (hzero L hright)
  rw [hE.deriv]
  simp only [hV₁, deriv_const_add']
  have hproduction :=
    norm_integral_coupled_rescaled_sobolev_production_le ρ hv hcompact hu hpair
  have hout (x : ℝ) (hx : x ∉ Icc (-L) L) :
      v x = 0 ∧ deriv v x = 0 ∧ deriv (deriv v) x = 0 :=
    hzero x fun h ↦ hx (Ioo_subset_Icc_self h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by
      have hxzero := hout x hx
      change 3 * (ρ + deriv (fun y ↦ u y t) x) * v x ^ 2 +
          (ρ + deriv (fun y ↦ u y t) x) * deriv v x ^ 2 -
          (ρ + deriv (fun y ↦ u y t) x) * deriv (deriv v) x ^ 2 +
          2 * deriv (deriv (fun y ↦ u y t)) x * v x * deriv v x +
          2 * deriv (deriv (deriv (fun y ↦ u y t))) x * v x * deriv (deriv v) x +
          2 * deriv (deriv (fun y ↦ u y t)) x * deriv v x * deriv (deriv v) x = 0
      simp only [hxzero.1, hxzero.2.1, hxzero.2.2, zero_pow (by decide : 2 ≠ 0),
        mul_zero, add_zero, sub_zero])]
  have hglobal₀ : (∫ x in Icc (-L) L, v x ^ 2) = ∫ x, v x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).1, zero_pow (by decide : 2 ≠ 0)]
  have hglobal₁ : (∫ x in Icc (-L) L, deriv v x ^ 2) = ∫ x, deriv v x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).2.1, zero_pow (by decide : 2 ≠ 0)]
  have hglobal₂ : (∫ x in Icc (-L) L, deriv (deriv v) x ^ 2) =
      ∫ x, deriv (deriv v) x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp only [(hout x hx).2.2, zero_pow (by decide : 2 ≠ 0)]
  simpa only [sobolevEnergyTwo, ← hglobal₀, ← hglobal₁, ← hglobal₂] using hproduction

/-- Uniform H¹ and common-rate bounds propagate H² exponentially on each
finite time interval for a smooth coupled rescaled trajectory. -/
theorem sobolevEnergyTwo_le_exp_of_coupled_rescaled_transport
    {w u : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {L B D t₀ T : ℝ}
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hu : ∀ t ∈ Icc t₀ T, ContDiff ℝ 3 (fun x ↦ u x t))
    (hpair : ∀ t ∈ Icc t₀ T,
      IsHilbertPair (fun x ↦ w x t) (deriv (fun x ↦ u x t)))
    (htransport : ∀ t ∈ Icc t₀ T, ∀ x,
      deriv (w x) t + (ρ t * x + u x t) * deriv (fun y ↦ w y t) x =
        (ρ t + deriv (fun y ↦ u y t) x) * w x t)
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Icc t₀ T, tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L)
    (hinput : ∀ t ∈ Icc t₀ T,
      lpNorm (fun x ↦ w x t) 2 volume + lpNorm (deriv (fun x ↦ w x t)) 2 volume ≤ B)
    (hrate : ∀ t ∈ Icc t₀ T, |ρ t| ≤ D) :
    ∀ t ∈ Icc t₀ T, sobolevEnergyTwo w L t ≤
      sobolevEnergyTwo w L t₀ * Real.exp ((3 * D + 8 * B) * (t - t₀)) := by
  have hq : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ deriv (fun x ↦ w x p.2) p.1) :=
    Calculus.contDiff_spatial_deriv hw
  have hr := Calculus.contDiff_spatial_deriv (w := fun x s ↦ deriv (fun y ↦ w y s) x) hq
  have hdiff : Differentiable ℝ (sobolevEnergyTwo w L) := by
    intro t
    exact (((hasDerivAt_integral_sq_Icc_of_contDiff
      (hw.of_le (by norm_num)) (-L) L t).add
        (hasDerivAt_integral_sq_Icc_of_contDiff (hq.of_le (by norm_num)) (-L) L t)).add
          (hasDerivAt_integral_sq_Icc_of_contDiff
            (f := fun x s ↦ deriv (deriv (fun y ↦ w y s)) x) hr (-L) L t)).differentiableAt
  have hestimate := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := sobolevEnergyTwo w L) (f' := deriv (sobolevEnergyTwo w L))
    (δ := sobolevEnergyTwo w L t₀) (K := 3 * D + 8 * B) (ε := 0) (a := t₀) (b := T)
    hdiff.continuous.continuousOn
    (fun t _ ↦ (hdiff t).hasDerivAt.hasDerivWithinAt)
    (by rw [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t₀)])
    (by
      intro t ht
      have htc : t ∈ Icc t₀ T := ⟨ht.1, ht.2.le⟩
      rw [add_zero, Real.norm_eq_abs (sobolevEnergyTwo w L t),
        abs_of_nonneg (sobolevEnergyTwo_nonneg w L t)]
      exact (norm_deriv_sobolevEnergyTwo_le_of_coupled_rescaled_transport
        hw (hu t htc) (hpair t htc)
        (htransport t htc) hL (hsupp t htc)).trans
        (mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left (hrate t htc) (by norm_num))
            (mul_le_mul_of_nonneg_left (hinput t htc) (by norm_num)))
          (sobolevEnergyTwo_nonneg w L t)))
  intro t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t),
    gronwallBound_ε0] using hestimate t ht

end DeGregorio
