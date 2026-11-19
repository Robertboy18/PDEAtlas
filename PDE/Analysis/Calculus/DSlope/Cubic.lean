/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.DSlope

/-!
# Smooth cubic factors from vanishing derivatives

If a smooth function and its first two derivatives vanish at zero, its third
iterated divided slope is a smooth cubic factor. Mathlib supplies the algebraic
factorization; the diagonal derivative formula converts the ordinary zero jets
into the required divided-slope values.

For a function smooth only near zero, a compactly supported representative
proves the result locally. The resulting factor is still the iterated divided
slope of the original function.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

universe u v

variable {P : Type u} {E : Type v} {G : Type (max u v)}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Three zero ordinary jets give an exact cubic factorization using the existing
iterated divided slope. Only two derivatives are needed for this algebraic identity. -/
theorem eq_cube_smul_iterate_dslope_of_zero
    {f : ℝ → E} (hf : ContDiff ℝ 2 f)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0) (hsecond : deriv (deriv f) 0 = 0)
    (s : ℝ) :
    f s = s ^ 3 • (Function.swap dslope 0)^[3] f s := by
  have hjets : ∀ k < 3, (Function.swap dslope 0)^[k] f 0 = 0 := by
    intro k hk
    interval_cases k
    · change f 0 = 0
      exact hzero
    · change dslope f 0 0 = 0
      simpa only [dslope_same] using hfirst
    · change dslope (dslope f 0) 0 0 = 0
      rw [dslope_same, deriv_dslope_same hf, hsecond, smul_zero]
  simpa only [sub_zero] using
    (pow_sub_smul_iterate_dslope_of_zero 3 hjets s).symm

/-- A jointly smooth family with three vanishing scalar jets has one jointly
smooth cubic factor. Its witness is the third iterated divided slope. -/
theorem exists_contDiff_cubic_factor_joint
    {F : P × ℝ → G} (hF : ContDiff ℝ ∞ F)
    (hzero : ∀ p, F (p, 0) = 0)
    (hfirst : ∀ p, deriv (fun s ↦ F (p, s)) 0 = 0)
    (hsecond : ∀ p, deriv (deriv (fun s ↦ F (p, s))) 0 = 0) :
    ∃ g : P × ℝ → G, ContDiff ℝ ∞ g ∧ ∀ p s, F (p, s) = s ^ 3 • g (p, s) := by
  refine ⟨fun q ↦ (Function.swap dslope 0)^[3] (fun s ↦ F (q.1, s)) q.2,
    contDiff_iterate_dslope_snd hF 0 3, ?_⟩
  intro p s
  have hslice : ContDiff ℝ 2 (fun t ↦ F (p, t)) :=
    (hF.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)
  exact eq_cube_smul_iterate_dslope_of_zero hslice (hzero p) (hfirst p) (hsecond p) s

/-- A smooth function on an open neighborhood of zero, with zero jets through
order two, has its canonical smooth cubic factor on a smaller open neighborhood.
No regularity of the original function outside the given neighborhood is assumed. -/
theorem exists_local_contDiff_cubic_factor
    {f : ℝ → E} {U : Set ℝ} (hU : IsOpen U) (hmem : (0 : ℝ) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0) (hsecond : deriv (deriv f) 0 = 0) :
    ∃ V : Set ℝ, IsOpen V ∧ (0 : ℝ) ∈ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ ((Function.swap dslope 0)^[3] f) V ∧
      ∀ s ∈ V, f s = s ^ 3 • (Function.swap dslope 0)^[3] f s := by
  classical
  let e : ℝ ≃L[ℝ] ℝ^(Module.finrank ℝ ℝ) :=
    (Module.finBasis ℝ ℝ).equivFunL.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ ℝ)) ℝ).symm
  have hlocal : ContDiffOn ℝ ∞ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ hx ↦ hx)
  have hezero : e 0 ∈ e.symm ⁻¹' U := by simpa using hmem
  obtain ⟨g, hg, _, heq⟩ := hlocal.exists_contDiff_compactSupport_eventuallyEq
    (hU.preimage e.symm.continuous) hezero
  let f₁ : ℝ → E := g ∘ e
  have hf₁ : ContDiff ℝ ∞ f₁ := hg.comp e.contDiff
  have hfg : f =ᶠ[𝓝 (0 : ℝ)] f₁ := by
    have h := heq.comp_tendsto e.continuous.continuousAt
    simpa only [f₁, Function.comp_def, e.symm_apply_apply] using h
  have hz : f₁ 0 = 0 := hfg.self_of_nhds.symm.trans hzero
  have h₁ : deriv f₁ 0 = 0 := hfg.deriv_eq.symm.trans hfirst
  have h₂ : deriv (deriv f₁) 0 = 0 := hfg.deriv.deriv_eq.symm.trans hsecond
  have hfactor := iterate_dslope_eventuallyEq_of_eventuallyEq hfg 3
  have hnear : {s | f s = f₁ s ∧
      (Function.swap dslope 0)^[3] f s = (Function.swap dslope 0)^[3] f₁ s ∧ s ∈ U}
      ∈ 𝓝 (0 : ℝ) := hfg.and (hfactor.and (hU.mem_nhds hmem))
  obtain ⟨V, hVsub, hVopen, hzeroV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V, hVopen, hzeroV, fun s hs ↦ (hVsub hs).2.2, ?_, ?_⟩
  · exact (contDiff_iterate_dslope hf₁ 0 3).contDiffOn.congr
      (fun s hs ↦ (hVsub hs).2.1)
  · intro s hs
    rw [(hVsub hs).1, (hVsub hs).2.1]
    exact eq_cube_smul_iterate_dslope_of_zero (hf₁.of_le (by simp)) hz h₁ h₂ s

end PDE.Analysis
