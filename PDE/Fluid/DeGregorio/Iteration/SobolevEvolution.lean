/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.SobolevEnergy
public import PDE.Fluid.DeGregorio.Iteration.SobolevBound
public import Mathlib.Analysis.ODE.Gronwall

/-!
# The H² differential estimate for frozen Hilbert transport

The PDE-derived energy identity and the concrete Hilbert estimate combine into a
differential inequality. A strict compact support enclosure, assumed as a hypothesis,
gives all boundary traces and identifies interval energies with whole-line energies.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- A frozen transport step obeys an H² energy differential estimate
with coefficient determined only by input H² norms. Its support enclosure
derives the endpoint conditions, including those of the derivatives. -/
theorem norm_deriv_sobolevEnergyTwo_le_of_frozen_transport
    {f : ℝ → ℝ} {w u : ℝ → ℝ → ℝ} {L t : ℝ}
    (hf : ContDiff ℝ 3 f) (hsuppf : HasCompactSupport f)
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hu : ContDiff ℝ 3 (fun y ↦ u y t))
    (hpair : IsHilbertPair f (deriv (fun y ↦ u y t)))
    (htransport : ∀ x, deriv (w x) t + u x t * deriv (fun y ↦ w y t) x =
      deriv (fun y ↦ u y t) x * w x t)
    (hsupp : tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L) :
    ‖deriv (sobolevEnergyTwo w L) t‖ ≤
      9 * (lpNorm f 2 volume + lpNorm (deriv f) 2 volume +
        lpNorm (deriv (deriv f)) 2 volume) * sobolevEnergyTwo w L t := by
  rcases lt_or_ge L 0 with hL | hL
  · have h0 : sobolevEnergyTwo w L = fun _ ↦ 0 := by
      funext s
      simp [sobolevEnergyTwo, Icc_eq_empty (by linarith : ¬-L ≤ L)]
    simp [h0]
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
  have hv : ContDiff ℝ 2 v :=
    (hw.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hleft : -L ∉ Ioo (-L) L := by simp
  have hright : L ∉ Ioo (-L) L := by simp
  have hE := hasDerivAt_sobolevEnergyTwo_of_frozen_transport hw hu htransport hL
    (hzero (-L) hleft) (hzero L hright)
  rw [hE.deriv]
  have hproduction :=
    norm_integral_hilbert_sobolev_production_le hf hsuppf hv hcompact hu hpair
  have hout (x : ℝ) (hx : x ∉ Icc (-L) L) :
      v x = 0 ∧ deriv v x = 0 ∧ deriv (deriv v) x = 0 :=
    hzero x fun h ↦ hx (Ioo_subset_Icc_self h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx ↦ by
      have hxzero := hout x hx
      change 3 * deriv (fun y ↦ u y t) x * v x ^ 2 +
          deriv (fun y ↦ u y t) x * deriv v x ^ 2 -
          deriv (fun y ↦ u y t) x * deriv (deriv v) x ^ 2 +
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

/-- A uniform input H² size gives an exponential output H² energy estimate
for transport solutions on a common support cylinder. -/
theorem sobolevEnergyTwo_le_exp_of_frozen_transport
    {f w u : ℝ → ℝ → ℝ} {L B t₀ T : ℝ}
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hf : ∀ t ∈ Icc t₀ T, ContDiff ℝ 3 (fun x ↦ f x t))
    (hsuppf : ∀ t ∈ Icc t₀ T, HasCompactSupport (fun x ↦ f x t))
    (hu : ∀ t ∈ Icc t₀ T, ContDiff ℝ 3 (fun x ↦ u x t))
    (hpair : ∀ t ∈ Icc t₀ T,
      IsHilbertPair (fun x ↦ f x t) (deriv (fun x ↦ u x t)))
    (htransport : ∀ t ∈ Icc t₀ T, ∀ x,
      deriv (w x) t + u x t * deriv (fun y ↦ w y t) x =
        deriv (fun y ↦ u y t) x * w x t)
    (hsupp : ∀ t ∈ Icc t₀ T, tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L)
    (hinput : ∀ t ∈ Icc t₀ T,
      lpNorm (fun x ↦ f x t) 2 volume +
        lpNorm (deriv (fun x ↦ f x t)) 2 volume +
        lpNorm (deriv (deriv (fun x ↦ f x t))) 2 volume ≤ B) :
    ∀ t ∈ Icc t₀ T, sobolevEnergyTwo w L t ≤
      sobolevEnergyTwo w L t₀ * Real.exp (9 * B * (t - t₀)) := by
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
    (δ := sobolevEnergyTwo w L t₀) (K := 9 * B) (ε := 0) (a := t₀) (b := T)
    hdiff.continuous.continuousOn
    (fun t _ ↦ (hdiff t).hasDerivAt.hasDerivWithinAt)
    (by rw [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t₀)])
    (by
      intro t ht
      have htc : t ∈ Icc t₀ T := ⟨ht.1, ht.2.le⟩
      rw [add_zero, Real.norm_eq_abs (sobolevEnergyTwo w L t),
        abs_of_nonneg (sobolevEnergyTwo_nonneg w L t)]
      exact (norm_deriv_sobolevEnergyTwo_le_of_frozen_transport
        (hf t htc) (hsuppf t htc) hw (hu t htc) (hpair t htc)
        (htransport t htc) (hsupp t htc)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hinput t htc) (by norm_num))
          (sobolevEnergyTwo_nonneg w L t)))
  intro t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t),
    gronwallBound_ε0] using hestimate t ht

end DeGregorio
