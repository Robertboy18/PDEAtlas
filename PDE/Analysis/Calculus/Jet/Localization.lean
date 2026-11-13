/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension

import PDE.Analysis.Calculus.LocalExtension.Cutoff.Hessian
import PDE.Analysis.Calculus.LocalExtension.Zero
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Compact localization preserving a vanishing lower jet

The cutoff is supplied by the existing compact test-function construction. Its
product with a map smooth on an open set has closed support inside that set, so
the existing extension-by-zero theorem gives global smoothness.

The product remains explicit. Where the original value and first derivative
vanish, its full second derivative is multiplied only by the cutoff value.
This preserves zero lower jets even where the cutoff is not equal to one.
-/

@[expose] public section

noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Multiplication preserves a zero value and first derivative. At such a point,
the full second derivative is the cutoff value times the original second derivative. -/
theorem second_jet_smul_of_lower_jet_eq_zero
    {χ : E → ℝ} {Q : E → F} {x : E}
    (hχ : ContDiffAt ℝ 2 χ x) (hQ : ContDiffAt ℝ 2 Q x)
    (hzero : Q x = 0) (hfirst : fderiv ℝ Q x = 0) :
    let R := fun y ↦ χ y • Q y
    R x = 0 ∧ fderiv ℝ R x = 0 ∧
      fderiv ℝ (fderiv ℝ R) x = χ x • fderiv ℝ (fderiv ℝ Q) x := by
  dsimp only
  refine ⟨by rw [hzero, smul_zero], ?_, ?_⟩
  · rw [fderiv_fun_smul (hχ.differentiableAt two_ne_zero)
      (hQ.differentiableAt two_ne_zero), hzero, hfirst]
    simp
  · have hbound := norm_fderiv_fderiv_smul_sub_le hχ hQ
    simp only [hzero, hfirst, norm_zero, mul_zero, zero_mul, add_zero] at hbound
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound
      (fderiv ℝ (fderiv ℝ (fun y ↦ χ y • Q y)) x -
        χ x • fderiv ℝ (fderiv ℝ Q) x).opNorm_nonneg))

/-- A compact subset of an open domain admits a scalar cutoff equal to one on
one open neighborhood of the whole subset. The displayed indicator product is
globally smooth and compactly supported inside the original domain.
No regularity of `Q` outside that domain is required. -/
theorem exists_smooth_cutoff_localization [FiniteDimensional ℝ E]
    {Q : E → F} {Ω K : Set E}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ (χ : E → ℝ) (U : Set E),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧ EqOn χ 1 U ∧
      let P := Ω.indicator (fun x ↦ χ x • Q x)
      ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ Ω ∧ EqOn P Q U := by
  obtain ⟨ψ, hψΩ, _, hψOne, hψRange⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional hΩ hK hKΩ
  let R : E → F := fun x ↦ ψ.toFun x • Q x
  have hRΩ : tsupport R ⊆ Ω :=
    (tsupport_smul_subset_left ψ.toFun Q).trans hψΩ
  have hindicator : Ω.indicator R = R :=
    indicator_eq_self.mpr ((subset_tsupport R).trans hRΩ)
  have hPΩ : tsupport (Ω.indicator R) ⊆ Ω := by rwa [hindicator]
  have hR : ContDiffOn ℝ ∞ R Ω := ψ.contDiff.contDiffOn.fun_smul hQ
  have hP := hR.indicator_of_tsupport_subset hΩ hPΩ
  have hnear : ∀ x ∈ K, Ω ∩ {y | ψ.toFun y = 1} ∈ 𝓝 x :=
    fun x hx ↦ inter_mem (hΩ.mem_nhds (hKΩ hx)) (hψOne x hx)
  obtain ⟨U, hKU, hU, hUχ⟩ := exists_open_set_nhds hnear
  refine ⟨ψ.toFun, U, ψ.contDiff, ψ.hasCompactSupport, hψΩ, hψRange,
    hU, hKU, (fun _ hx ↦ (hUχ hx).1), (fun _ hx ↦ (hUχ hx).2), ?_⟩
  change ContDiff ℝ ∞ (Ω.indicator R) ∧ HasCompactSupport (Ω.indicator R) ∧
    tsupport (Ω.indicator R) ⊆ Ω ∧ EqOn (Ω.indicator R) Q U
  refine ⟨hP, ?_, hPΩ, ?_⟩
  · rw [hindicator]
    exact ψ.hasCompactSupport.smul_right
  · intro x hx
    rw [indicator_of_mem (hUχ hx).1]
    change ψ.toFun x • Q x = Q x
    rw [(hUχ hx).2, one_smul]

/- The local quadratic-tube consumer keeps the whole supplied zero section.
The compact set need only contain the image of the time support of `B`.
There is no regularity, injectivity, or isolation premise on the remaining curve. -/
example [FiniteDimensional ℝ E]
    {γ : ℝ → E} {B : ℝ → E →L[ℝ] E →L[ℝ] F} {J : Set ℝ}
    {Q : E → F} {Ω K : Set E}
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hγ : MapsTo γ J Ω) (hBK : γ '' tsupport B ⊆ K)
    (hjet : ∀ s ∈ J, Q (γ s) = 0 ∧ fderiv ℝ Q (γ s) = 0 ∧
      fderiv ℝ (fderiv ℝ Q) (γ s) = B s) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧
      let P := Ω.indicator (fun x ↦ χ x • Q x)
      ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ Ω ∧
      ∀ s ∈ J, P (γ s) = 0 ∧ fderiv ℝ P (γ s) = 0 ∧
        fderiv ℝ (fderiv ℝ P) (γ s) = B s := by
  obtain ⟨χ, U, hχ, hχc, hχΩ, _, hU, hKU, _, _, hP, hPc, hPΩ, hPQ⟩ :=
    exists_smooth_cutoff_localization hQ hΩ hK hKΩ
  let P := Ω.indicator (fun x ↦ χ x • Q x)
  refine ⟨χ, hχ, hχc, hχΩ, hP, hPc, hPΩ, ?_⟩
  intro s hs
  obtain ⟨hzero, hfirst, hsecond⟩ := hjet s hs
  by_cases hsB : s ∈ tsupport B
  · have hmem : γ s ∈ U := hKU (hBK ⟨s, hsB, rfl⟩)
    have heq : P =ᶠ[𝓝 (γ s)] Q := by
      filter_upwards [hU.mem_nhds hmem] with x hx
      exact hPQ hx
    exact ⟨heq.self_of_nhds.trans hzero, (heq.fderiv_eq (𝕜 := ℝ)).trans hfirst,
      ((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)).trans hsecond⟩
  · have hBzero : B s = 0 := image_eq_zero_of_notMem_tsupport hsB
    have hmem : Ω ∈ 𝓝 (γ s) := hΩ.mem_nhds (hγ hs)
    have heq : P =ᶠ[𝓝 (γ s)] (fun x ↦ χ x • Q x) := by
      filter_upwards [hmem] with x hx
      exact indicator_of_mem hx _
    obtain ⟨hRzero, hRfirst, hRsecond⟩ := second_jet_smul_of_lower_jet_eq_zero
      (hχ.contDiffAt.of_le (by simp)) ((hQ.contDiffAt hmem).of_le (by simp))
      hzero hfirst
    refine ⟨heq.self_of_nhds.trans hRzero,
      (heq.fderiv_eq (𝕜 := ℝ)).trans hRfirst, ?_⟩
    rw [((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)), hRsecond, hsecond, hBzero,
      smul_zero]

end PDE.Analysis
