/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/


module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flow.Variation.FirstOrder

import PDE.Analysis.Calculus.LocalSpectralFrame.Coordinates
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.State
import CAS.ExactTactic

/-!
# Retained selected-clock inputs for neutral corrections

The supplied positive-delta flow, terminal time, coefficient slice, speed
variation, selected time and index pair determine one smooth ordered
frame. Its base vectors are the selected normalized eigenvectors. The ordinary
closed-interval clock equation, all nonzero tangent coordinates and the two
signed determinants are derived with these same data.

The concrete flux is globally smooth, strictly hyperbolic and genuinely nonlinear
by the global scalar-law theorem and the feedback range. These
baseline facts are independent of the local frame construction.
-/

@[expose] public noncomputable section

open Set PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Extract the ordered frame and global baseline properties for the
retained selected flow. Every frame column and the joint dual evaluation are
smooth on one open neighborhood, and the base frame agrees with the selected
normalized vectors. The supplied physical speed variation is globally smooth.

No terminal ratio, projection, fundamental solution or correction is selected.
The two determinants and nonzero expansion are precisely the retained seed
inputs; the ordinary ODE converts them to the same flux tangent. -/
theorem exists_selected_clock_neutral_correction_inputs {δ A B H tStar : ℝ} {c : Fin 3 → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} (hδ : 0 < δ)
    (hδsmall : δ < 1 / 4) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hΨ : ContDiff ℝ ∞ Ψ)
    (hselected : ((δ, c), (0, 0)) ∈ N) (hinitial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H, HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 •
      Ψ (s, θ)) s)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) (i j : Fin 3) :
    let θ0 := ((δ, c), ((0 : ℝ), (0 : ℝ)))
    let e := T θ0
    let b0 : ℝ → ℝ := fun y ↦ b (c, y)
    let f := concreteGatedFlux δ (clockFeedback A B) b0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, θ0)
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let rStar := GatedFlux.rightEigenvector (fastLogCosh δ) MiddleClock.g cutoff
      (clockFeedback A B) b0 (γ tStar)
    tStar ∈ Ioo (0 : ℝ) e →
    205 < γ tStar 1 → 2 < γ tStar 2 → (γ tStar 2) ^ 2 < A ^ 2 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar i), ⇑(W tStar)] ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar j), ⇑(W tStar)] ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • rStar k) →
    ContDiff ℝ ∞ b0 ∧
    tsupport b0 ⊆ Icc (205 : ℝ) (2051 / 10) ∧
    ContDiff ℝ ∞ f ∧
    (∀ x, IsStrictlyHyperbolicAt f x) ∧
    (∀ k, IsGenuinelyNonlinearFamily f k) ∧
    ContDiff ℝ ∞ γ ∧ ContDiff ℝ ∞ W ∧
    (∀ t ∈ Icc (0 : ℝ) H, HasDerivAt γ (f (γ t)) t) ∧
    γ 0 = (!₂[0, 0, 1] : ℝ^3) ∧ e ∈ Ioo (0 : ℝ) H ∧ γ e 1 = 0 ∧
    1 ≤ A ^ 2 ∧
    ∃ (V : Set ℝ) (r : ℝ → Module.Basis (Fin 3) ℝ (ℝ^3)),
      IsOpen V ∧ tStar ∈ V ∧ (∀ k, r tStar k = rStar k) ∧
      (∀ k, ContDiffOn ℝ ∞ (fun t ↦ r t k) V ∧
        ContDiffOn ℝ ∞ (fun t ↦ characteristicSpeed f k (γ t)) V) ∧
      ContDiffOn ℝ ∞
        (fun p : ℝ × (ℝ^3) ↦ ((r p.1).repr p.2 : Fin 3 → ℝ)) (V ×ˢ univ) ∧
      (∀ t ∈ V, StrictMono (fun k ↦ characteristicSpeed f k (γ t)) ∧
        ∀ k, fderiv ℝ f (γ t) (r t k) = characteristicSpeed f k (γ t) • r t k ∧
          (r tStar).equivFun (r t k) k = 1) ∧
      (∀ k, (r tStar).repr (f (γ tStar)) k ≠ 0) ∧
      Matrix.det ![⇑(f (γ tStar)), ⇑(r tStar i), ⇑(W tStar)] ≠ 0 ∧
      Matrix.det ![⇑(f (γ tStar)), ⇑(r tStar j), ⇑(W tStar)] ≠ 0 := by
  classical
  intro θ0 e b0 f γ W rStar htStar hy hzInner hzOuter hi hj hexp
  have hb0 : ContDiff ℝ ∞ b0 := hb.comp (contDiff_const.prodMk contDiff_id)
  have hγSmooth : ContDiff ℝ ∞ γ := hΨ.comp (contDiff_id.prodMk contDiff_const)
  have hW : ContDiff ℝ ∞ W :=
    (contDiff_prescribedClockFullVariation hΨ (1, 0)).comp (contDiff_id.prodMk contDiff_const)
  obtain ⟨hf, hhyperOn, hgn⟩ := concreteGatedFlux_smooth_strictlyHyperbolic_genuinelyNonlinear
      hδ hδsmall (contDiff_clockFeedback A B) (fun z ↦ clockFeedback_mem_Icc A B z) hb0 hbsupport
  have hγODE (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : HasDerivAt γ (f (γ t)) t := by
    simpa only [γ, f, b0, θ0, zero_smul, sub_zero] using hode θ0 hselected t ht
  have he : e ∈ Ioo (0 : ℝ) H := (hevent θ0 hselected).1
  have hvelocity : deriv γ tStar = f (γ tStar) :=
    (hγODE tStar ⟨htStar.1.le, htStar.2.le.trans he.2.le⟩).deriv
  -- The shared gate-state theorem gives the middle speed at this selected point.
  have hmid := (concreteGatedFlux_upward_gate_state_general (δ := δ) (b := b0) (q := γ tStar)
    hAB (hb0.differentiable (by simp) (γ tStar 1)) hbsupport hy hzInner hzOuter).2.1
  have hδabs : |δ| < 1 / 4 := by simpa only [abs_of_pos hδ] using hδsmall
  have hfast := seven_fourths_lt_deriv_fastLogCosh hδabs
  have hslow := abs_le.mp (MiddleClock.abs_deriv_g_le (γ tStar 1))
  have hlow : -deriv (fastLogCosh δ) (γ tStar 0) <
      GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) (γ tStar) := by
    rw [hmid]; linarith [hfast (γ tStar 0), hslow.1]
  have hhigh : GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B)
      (γ tStar) < deriv (fastLogCosh δ) (γ tStar 2) := by
    rw [hmid]; linarith [hfast (γ tStar 2), hslow.2]
  have hk : Differentiable ℝ (fastLogCosh δ) :=
    (contDiff_fastLogCosh δ).differentiable (by simp)
  have hg : Differentiable ℝ MiddleClock.g := MiddleClock.contDiff_g.differentiable (by simp)
  have hC : Differentiable ℝ cutoff := contDiff_cutoff.differentiable (by simp)
  have hφ : Differentiable ℝ (clockFeedback A B) :=
    (contDiff_clockFeedback A B).differentiable (by simp)
  have hbDiff : Differentiable ℝ b0 := hb0.differentiable (by simp)
  have ha : (0 : ℝ) < 100 := by cas
  have had : (100 : ℝ) < 205 := by cas
  have hleft : ∀ y : ℝ, y ≤ 100 → cutoff y = 1 := fun _ ↦ cutoff_of_le
  have hright : ∀ y : ℝ, 205 ≤ y → cutoff y = 0 := fun _ ↦ cutoff_of_ge
  let r0 : Module.Basis (Fin 3) ℝ (ℝ^3) :=
    GatedFlux.eigenbasis (q := γ tStar) hk hg hC hφ hbDiff ha had hleft hright hbsupport hlow hhigh
  have hr0 (k : Fin 3) : r0 k = rStar k :=
    GatedFlux.eigenbasis_apply (q := γ tStar) hk hg hC hφ hbDiff ha had hleft hright
      hbsupport hlow hhigh k
  have hdiag (k : Fin 3) : fderiv ℝ f (γ tStar) (r0 k) =
      GatedFlux.speed (fastLogCosh δ) MiddleClock.g cutoff (clockFeedback A B) (γ tStar) k • r0 k :=
    GatedFlux.fderiv_flux_eigenbasis (q := γ tStar) hk hg hC hφ hbDiff ha had hleft hright
      hbsupport hlow hhigh k
  obtain ⟨V, hV, htV, _, r, eigenvalues, hrBase, _, hrSmooth, hdual, hspectral⟩ :=
    PDE.Analysis.Calculus.SimpleEigenpair.exists_contDiffOn_spectral_basis
      (I := univ) isOpen_univ (mem_univ tStar)
      ((hf.fderiv_right (by simp)).comp hγSmooth).contDiffOn r0
      (GatedFlux.speed (fastLogCosh δ) MiddleClock.g cutoff (clockFeedback A B)
        (γ tStar)) hdiag (GatedFlux.speed_strictMono hlow hhigh)
  have hrStar (k : Fin 3) : r tStar k = rStar k := by rw [hrBase]; exact hr0 k
  have hcanonical (t : ℝ) (ht : t ∈ V) : (fun k ↦ characteristicSpeed f k (γ t)) = eigenvalues t :=
    characteristicSpeed_eq_of_eigenbasis (r t)
      (hspectral t ht).1 (fun k ↦ ((hspectral t ht).2 k).1)
  have hsmooth (k : Fin 3) : ContDiffOn ℝ ∞ (fun t ↦ r t k) V ∧
      ContDiffOn ℝ ∞ (fun t ↦ characteristicSpeed f k (γ t)) V :=
    ⟨(hrSmooth k).1, (hrSmooth k).2.congr fun t ht ↦ congrFun (hcanonical t ht) k⟩
  have hspectral' (t : ℝ) (ht : t ∈ V) : StrictMono (fun k ↦ characteristicSpeed f k (γ t)) ∧
        ∀ k, fderiv ℝ f (γ t) (r t k) = characteristicSpeed f k (γ t) • r t k ∧
          (r tStar).equivFun (r t k) k = 1 := by
    refine ⟨by rw [hcanonical t ht]; exact (hspectral t ht).1, fun k ↦ ⟨?_, ?_⟩⟩
    · rw [congrFun (hcanonical t ht) k]; exact ((hspectral t ht).2 k).1
    · rw [hrBase]; exact ((hspectral t ht).2 k).2
  -- Coordinates follow from the selected expansion in the same concrete basis.
  obtain ⟨a, haNonzero, haExpansion⟩ := hexp
  have haBasis : f (γ tStar) = ∑ k, a k • r0 k := by
    rw [← hvelocity, haExpansion]; simp only [hr0]
  exact ⟨hb0, hbsupport.trans Ioo_subset_Icc_self, hf, fun x ↦ hhyperOn x (mem_univ x), hgn,
    hγSmooth, hW, hγODE, hinitial θ0, he, (hevent θ0 hselected).2, by nlinarith [hzInner, hzOuter],
    V, r, hV, htV, hrStar, hsmooth, hdual, hspectral',
    fun k ↦ by rw [hrBase, haBasis, congrFun (r0.repr_sum_self a) k]; exact haNonzero k,
    by simpa only [hrStar, hvelocity] using hi, by simpa only [hrStar, hvelocity] using hj⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
