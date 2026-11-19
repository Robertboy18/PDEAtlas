/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.CoupledEvolution

/-!
# Localizing the smooth energy estimate in time

A smooth time cutoff extends a trajectory from an open time interval without
changing it near a chosen interior time. This allows the energy identity to be
used on a half-open trajectory that is smooth only before its terminal time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

namespace DeGregorio

/-- A C³ trajectory on an open convex time set has a global C³ representative
agreeing with every spatial slice near any chosen interior time. -/
theorem exists_contDiff_time_localization {w : ℝ → ℝ → ℝ} {J : Set ℝ} {t : ℝ}
    (hJ : IsOpen J) (hconv : Convex ℝ J)
    (hw : ContDiffOn ℝ 3 (Function.uncurry w) (univ ×ˢ J)) (ht : t ∈ J) :
    ∃ W : ℝ → ℝ → ℝ, ContDiff ℝ 3 (Function.uncurry W) ∧
      ∀ᶠ s in 𝓝 t, (fun x ↦ W x s) = fun x ↦ w x s := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hJ.mem_nhds ht)
  let b : ContDiffBump t :=
    { rIn := ε / 2
      rOut := ε
      rIn_pos := half_pos hε
      rIn_lt_rOut := half_lt_self hε }
  let g := fun s ↦ (1 - b s) * t + b s * s
  have hg : ContDiff ℝ 3 g :=
    ((contDiff_const.sub b.contDiff).mul contDiff_const).add (b.contDiff.mul contDiff_id)
  have hgJ (s : ℝ) : g s ∈ J := by
    by_cases hs : b s = 0
    · simpa only [g, hs, sub_zero, one_mul, zero_mul, add_zero] using ht
    · have hsJ : s ∈ J := hball (by
        change s ∈ Metric.ball t b.rOut
        rw [← b.support_eq]
        exact hs)
      simpa only [smul_eq_mul] using
        hconv ht hsJ (sub_nonneg.mpr b.le_one) b.nonneg (sub_add_cancel 1 (b s))
  refine ⟨fun x s ↦ w x (g s), ?_, ?_⟩
  · exact hw.comp_contDiff (contDiff_fst.prodMk (hg.comp contDiff_snd))
      (fun p ↦ ⟨mem_univ p.1, hgJ p.2⟩)
  · filter_upwards [b.eventuallyEq_one] with s hs
    funext x
    simp only [g, Pi.one_apply, hs, sub_self, zero_mul, one_mul, zero_add]

/-- Joint C³ regularity makes the classical H² energy differentiable. -/
theorem differentiable_sobolevEnergyTwo_of_contDiff {w : ℝ → ℝ → ℝ} (L : ℝ)
    (hw : ContDiff ℝ 3 (Function.uncurry w)) : Differentiable ℝ (sobolevEnergyTwo w L) := by
  have hq : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ deriv (fun x ↦ w x p.2) p.1) :=
    Calculus.contDiff_spatial_deriv hw
  have hr := Calculus.contDiff_spatial_deriv (w := fun x s ↦ deriv (fun y ↦ w y s) x) hq
  intro t
  exact (((hasDerivAt_integral_sq_Icc_of_contDiff
    (hw.of_le (by norm_num)) (-L) L t).add
      (hasDerivAt_integral_sq_Icc_of_contDiff (hq.of_le (by norm_num)) (-L) L t)).add
        (hasDerivAt_integral_sq_Icc_of_contDiff
          (f := fun x s ↦ deriv (deriv (fun y ↦ w y s)) x) hr (-L) L t)).differentiableAt

/-- Local C³ regularity on an open time interval suffices to differentiate H²
energy at every interior time. -/
theorem differentiableAt_sobolevEnergyTwo_of_contDiffOn
    {w : ℝ → ℝ → ℝ} {a T t : ℝ} (L : ℝ)
    (hw : ContDiffOn ℝ 3 (Function.uncurry w) (univ ×ˢ Ioo a T)) (ht : t ∈ Ioo a T) :
    DifferentiableAt ℝ (sobolevEnergyTwo w L) t := by
  obtain ⟨W, hW, heq⟩ := exists_contDiff_time_localization isOpen_Ioo (convex_Ioo a T) hw ht
  have henergy : sobolevEnergyTwo W L =ᶠ[𝓝 t] sobolevEnergyTwo w L := by
    filter_upwards [heq] with s hs
    simp only [sobolevEnergyTwo, congrFun hs]
  exact (differentiable_sobolevEnergyTwo_of_contDiff L hW t).congr_of_eventuallyEq henergy.symm

/-- The coupled rescaled H² differential estimate holds at interior times of
a C³ trajectory on `ℝ × (a, T)`. -/
theorem norm_deriv_sobolevEnergyTwo_le_of_coupled_rescaled_transportOn
    {w u : ℝ → ℝ → ℝ} {L a T t ρ : ℝ}
    (hw : ContDiffOn ℝ 3 (Function.uncurry w) (univ ×ˢ Ioo a T))
    (ht : t ∈ Ioo a T) (hu : ContDiff ℝ 3 (fun y ↦ u y t))
    (hpair : IsHilbertPair (fun x ↦ w x t) (deriv (fun y ↦ u y t)))
    (htransport : ∀ x, deriv (w x) t + (ρ * x + u x t) * deriv (fun y ↦ w y t) x =
      (ρ + deriv (fun y ↦ u y t) x) * w x t)
    (hL : 0 ≤ L) (hsupp : tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L) :
    ‖deriv (sobolevEnergyTwo w L) t‖ ≤
      (3 * |ρ| + 8 * (lpNorm (fun x ↦ w x t) 2 volume +
        lpNorm (deriv (fun x ↦ w x t)) 2 volume)) * sobolevEnergyTwo w L t := by
  obtain ⟨W, hW, heq⟩ := exists_contDiff_time_localization isOpen_Ioo (convex_Ioo a T) hw ht
  have hslice : (fun x ↦ W x t) = fun x ↦ w x t := heq.self_of_nhds
  have htime (x : ℝ) : deriv (W x) t = deriv (w x) t :=
    Filter.EventuallyEq.deriv_eq (heq.mono (fun _ hs ↦ congrFun hs x))
  have henergy : sobolevEnergyTwo W L =ᶠ[𝓝 t] sobolevEnergyTwo w L := by
    filter_upwards [heq] with s hs
    simp only [sobolevEnergyTwo, congrFun hs]
  have htransportW : ∀ x, deriv (W x) t + (ρ * x + u x t) * deriv (fun y ↦ W y t) x =
      (ρ + deriv (fun y ↦ u y t) x) * W x t := by
    simpa only [htime, hslice, congrFun hslice] using htransport
  have h := norm_deriv_sobolevEnergyTwo_le_of_coupled_rescaled_transport hW hu
    (by simpa only [hslice] using hpair) htransportW hL (by simpa only [hslice] using hsupp)
  simpa only [hslice, henergy.deriv_eq, henergy.self_of_nhds] using h

/-- Uniform H¹ and rate bounds propagate H² up to every interior time of an
open time interval. All regularity and equation hypotheses are on `(a, T)`. -/
theorem sobolevEnergyTwo_le_exp_of_coupled_rescaled_transportOn
    {w u : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {L B D a t₀ T : ℝ}
    (hw : ContDiffOn ℝ 3 (Function.uncurry w) (univ ×ˢ Ioo a T))
    (ht₀ : t₀ ∈ Ioo a T)
    (hu : ∀ t ∈ Ioo a T, ContDiff ℝ 3 (fun x ↦ u x t))
    (hpair : ∀ t ∈ Ioo a T,
      IsHilbertPair (fun x ↦ w x t) (deriv (fun x ↦ u x t)))
    (htransport : ∀ t ∈ Ioo a T, ∀ x,
      deriv (w x) t + (ρ t * x + u x t) * deriv (fun y ↦ w y t) x =
        (ρ t + deriv (fun y ↦ u y t) x) * w x t)
    (hL : 0 ≤ L)
    (hsupp : ∀ t ∈ Ioo a T, tsupport (fun x ↦ w x t) ⊆ Ioo (-L) L)
    (hinput : ∀ t ∈ Ioo a T,
      lpNorm (fun x ↦ w x t) 2 volume + lpNorm (deriv (fun x ↦ w x t)) 2 volume ≤ B)
    (hrate : ∀ t ∈ Ioo a T, |ρ t| ≤ D) :
    ∀ t ∈ Ico t₀ T, sobolevEnergyTwo w L t ≤
      sobolevEnergyTwo w L t₀ * Real.exp ((3 * D + 8 * B) * (t - t₀)) := by
  intro t ht
  have hsub : Icc t₀ t ⊆ Ioo a T := fun _ hs ↦
    ⟨ht₀.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
  have hdiff (s : ℝ) (hs : s ∈ Icc t₀ t) :
      DifferentiableAt ℝ (sobolevEnergyTwo w L) s :=
    differentiableAt_sobolevEnergyTwo_of_contDiffOn L hw (hsub hs)
  have hcont : ContinuousOn (sobolevEnergyTwo w L) (Icc t₀ t) :=
    fun s hs ↦ (hdiff s hs).continuousAt.continuousWithinAt
  have hestimate := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := sobolevEnergyTwo w L) (f' := deriv (sobolevEnergyTwo w L))
    (δ := sobolevEnergyTwo w L t₀) (K := 3 * D + 8 * B) (ε := 0) (a := t₀) (b := t)
    hcont
    (fun s hs ↦ (hdiff s ⟨hs.1, hs.2.le⟩).hasDerivAt.hasDerivWithinAt)
    (by rw [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t₀)])
    (by
      intro s hs
      have hst : s ∈ Ioo a T := hsub ⟨hs.1, hs.2.le⟩
      rw [add_zero, Real.norm_eq_abs (sobolevEnergyTwo w L s),
        abs_of_nonneg (sobolevEnergyTwo_nonneg w L s)]
      exact (norm_deriv_sobolevEnergyTwo_le_of_coupled_rescaled_transportOn
        hw hst (hu s hst) (hpair s hst) (htransport s hst) hL (hsupp s hst)).trans
        (mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left (hrate s hst) (by norm_num))
            (mul_le_mul_of_nonneg_left (hinput s hst) (by norm_num)))
          (sobolevEnergyTwo_nonneg w L s)))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sobolevEnergyTwo_nonneg w L t),
    gronwallBound_ε0] using hestimate t ⟨ht.1, le_rfl⟩

end DeGregorio
