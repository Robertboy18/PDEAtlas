/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.PhaseCore
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.RankConstruction
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.PhysicalAssembly

import CAS.ExactTactic

/-!
# Positive-speed profiles for one selected corrected flux

The selected second-jet construction fixes the first correction and retains the
branches, their events, and the strip rank. The phase-core construction
then fixes a second correction and constructs the matched finite cores. Both
corrections have support in the same isolating neighborhood of the seed orbit.

Their sum is fixed before the final speed radius. Closed-axis isolation and the
physical tail theorem extend these cores to full viscous profiles. The
result retains global strict hyperbolicity and genuine nonlinearity, together
with closed-axis support exclusion for later endpoint calculations.
-/

@[expose] public noncomputable section

open Set
open scoped BigOperators ContDiff Matrix

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The selected rank and cancellation hypotheses produce a single smooth compact
correction whose flux admits full profiles at every sufficiently small positive
speed. The correction is chosen once, before that common speed radius.

The hypotheses are those of the selected second-jet construction. Its
retained branches supply the phase cores and their two original section anchors;
no core, outer-avoidance condition, or nonzero-speed profile is an extra input.
Both complete closed tail segments avoid the total support, including their
limiting endpoints. Global hyperbolicity and all canonical genuinely nonlinear
families belong to this same corrected flux. -/
theorem exists_selected_fixed_flux_viscous_profiles {δ A B H tStar : ℝ} {c : Fin 3 → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} (hδ : 0 < δ)
    (hδsmall : δ < 1 / 4) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hΨ : ContDiff ℝ ∞ Ψ)
    (hN : IsOpen N) (hselected : ((δ, c), (0, 0)) ∈ N) (hT : ContDiffOn ℝ ∞ T N)
    (hinitial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H, HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 •
      Ψ (s, θ)) s)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) (i j : Fin 3) (hij : i ≠ j) :
    let θ0 := ((δ, c), ((0 : ℝ), (0 : ℝ)))
    let e := T θ0
    let b0 : ℝ → ℝ := fun y ↦ b (c, y)
    let f := concreteGatedFlux δ (clockFeedback A B) b0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, θ0)
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let rStar := GatedFlux.rightEigenvector (PDE.Analysis.fastLogCosh δ) MiddleClock.g cutoff
      (clockFeedback A B) b0 (γ tStar)
    let Q := retainedTerminalState Ψ T (δ, c)
    tStar ∈ Ioo (0 : ℝ) e →
    205 < γ tStar 1 → 2 < γ tStar 2 → (γ tStar 2) ^ 2 < A ^ 2 →
    0 < Q (0, 0) 2 → Q (0, 0) 0 / Q (0, 0) 2 = 1 →
    deriv (fun a ↦ Q (0, a) 0 / Q (0, a) 2) 0 = 0 →
    Q (0, 0) 2 * deriv (fun μ ↦ Q (μ, 0) 0 / Q (μ, 0) 2) 0 +
      2 * deriv (fun μ ↦ Q (μ, 0) 2) 0 +
      2000000 * deriv (fun a ↦ Q (0, a) 2) 0 = 0 →
    (f (γ e)) 1 ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar i), ⇑(W tStar)] ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar j), ⇑(W tStar)] ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • rStar k) →
    ∃ P : ℝ^3 → ℝ^3,
      ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
      (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
      (∀ k, IsGenuinelyNonlinearFamily (f + P) k) ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 40000 ∧ r < 1 / 20000 ∧
        (∀ s ∈ Icc (0 : ℝ) 1,
          (!₂[0, 0, s] : ℝ^3) ∉ tsupport P ∧ P !₂[0, 0, s] = 0 ∧
          (f + P) !₂[0, 0, s] = f !₂[0, 0, s]) ∧
        (∀ μ : ℝ, |μ| ≤ r → ∀ s ∈ Icc (0 : ℝ) 1,
          (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P ∧
          P !₂[s, 2000000 * μ, 0] = 0 ∧
          (f + P) !₂[s, 2000000 * μ, 0] = f !₂[s, 2000000 * μ, 0]) ∧
        ∀ μ : ℝ, 0 < μ → μ ≤ r → ∃ qμ : ℝ → ℝ^3,
          IsViscousProfile (f + P) 0 !₂[0, 2000000 * μ, 0] μ qμ := by
  intro θ0 e b0 f γ W rStar Q htStar hy hzInner hzOuter hz hρ hρa hres hmiddle hi hj hexp
  have hb0 : ContDiff ℝ ∞ b0 := hb.comp (contDiff_const.prodMk contDiff_id)
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb0
  have heSelected : e ∈ Ioo (0 : ℝ) H := (hevent θ0 hselected).1
  have hH : 0 ≤ H := heSelected.1.le.trans heSelected.2.le
  -- The gate inequalities already place A beyond the section-one tail scale.
  have hA1 : 1 ≤ A ^ 2 := by nlinarith [hzInner, hzOuter]
  -- This is the only selection call. Its orbit, support set and rank stay together.
  obtain ⟨_, _, _, _, q, J, Ω, _, _, _, _, _, _,
      hprofile, hqSmooth, hqODE, _, hFoutBase, hFinBase, _, hJinner,
      hΩ, hpre, hqinj, hgate, rGate, _, _, _, _, hcorrections⟩ :=
    exists_selected_second_jet_cancellation_with_rank
      hδ hδsmall hAB hb hbsupport hΨ hN hselected hT hinitial hode hevent i j hij
      htStar hy hzInner hzOuter hz hρ hρa hres hmiddle hi hj hexp
  -- Recover both seed anchors from the original retained sections.
  have hOldInitial := retained_branches_initial hinitial (δ, c) e (0 : ℝ)
  have hq0 : q 0 = !₂[0, 0, 1] := (hFoutBase ⟨le_rfl, hH⟩).symm.trans hOldInitial.1
  have hq2e : q (2 * e) = !₂[1, 0, 0] := by
    simpa only [two_mul, mul_zero] using
      (hFinBase ⟨sub_le_self (e + e) hH, le_rfl⟩).symm.trans hOldInitial.2
  obtain ⟨P₁, Gout, Gin, υout, υin, I,
      hP₁, hP₁c, hP₁Ω, _, _, hhyper₁, hgn₁, _, _, _, _, _, hI, h0I, _,
      hInitial, _, _, _, hυout, hυin, hυout0, hυin0, _, _, _, _, _, _, _, _, hRank⟩ :=
    hcorrections (1 : ℝ) one_pos
  -- The phase-core theorem chooses the second correction for f + P₁.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrealize⟩ :=
    exists_retained_selected_phase_core (hf.add hP₁) hhyper₁ hgn₁ hqSmooth.continuous hqinj hΩ hgate
      hJinner heSelected.1 hRank (hυout.continuousOn.continuousAt (hI.mem_nhds h0I))
      (hυin.continuousOn.continuousAt (hI.mem_nhds h0I)) hυout0 hυin0
  obtain ⟨P₂, _, rCore, _, core, hP₂, hP₂c, hP₂Ω, _, _, hhyper₂, hgn₂,
      _, _, hrCore, _, _, hcores⟩ := hrealize (1 : ℝ) one_pos (1 : ℝ) one_pos
  let P : ℝ^3 → ℝ^3 := P₁ + P₂
  have hP : ContDiff ℝ ∞ P := hP₁.add hP₂
  have hPc : HasCompactSupport P := hP₁c.add hP₂c
  have hflux : (fun x ↦ f x + P₁ x) + P₂ = f + P := add_assoc f P₁ P₂
  let loCore : ℝ → ℝ := fun μ ↦ -(υout μ - e)
  let hiCore : ℝ → ℝ := fun μ ↦ e + e - (υin μ - e)
  have hcore : ∀ μ : ℝ, 0 < μ → μ ≤ rCore → loCore μ < hiCore μ ∧ (∀ t ∈ Icc (loCore μ) (hiCore μ),
        HasDerivWithinAt (core μ) ((f + P) (core μ t) - μ • core μ t)
          (Icc (loCore μ) (hiCore μ)) t) ∧ core μ (loCore μ) = !₂[0, 0, 1] ∧
      core μ (hiCore μ) = !₂[1, 2000000 * μ, 0] := by
    intro μ hμ hμr
    obtain ⟨_, _, _, _, _, hlohi, _, _, _, hleft, hright, hodeCore⟩ :=
      hcores μ ((abs_of_pos hμ).trans_le hμr)
    refine ⟨hlohi, ?_, hleft.trans (hInitial μ).1, hright.trans (hInitial μ).2⟩
    simpa only [hflux] using hodeCore
  -- Both corrections are fixed before the compact-support translation radius.
  obtain ⟨r, hr, _, hrSmall, hrTail, hleftAxis, hrightAxis, hprofiles⟩ :=
    exists_viscousProfile_family_of_fixed_correction_and_core
      hδ.le hA1 hAB hb0 (hbsupport.trans Ioo_subset_Icc_self)
      hqODE hq0 hq2e hΩ hpre hJinner hP hPc
      ((tsupport_add P₁ P₂).trans (union_subset hP₁Ω hP₂Ω)) hrCore hcore
  exact ⟨P, hP, hPc, by simpa only [hflux] using hhyper₂, by simpa only [hflux] using hgn₂, r, hr,
    hrSmall, hrTail, hleftAxis, hrightAxis, fun μ hμ hμr ↦
      let ⟨qμ, hqμ, _⟩ := hprofiles μ hμ hμr; ⟨qμ, hqμ⟩⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
