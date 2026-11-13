/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Radial

import PDE.Analysis.Calculus.Jet.QuadraticTube
import PDE.Analysis.Calculus.LocalExtension.Zero

/-!
# Compact zero extension with the actual logarithmic normal cutoff

The chart, bilinear family and isolating open set are supplied and remain fixed.
Compact time support gives one positive normal radius inside that chart and open
set. Every smaller logarithmic cutoff then has compact support there, so the
existing indicator extension theorem applies without another cutoff.

The extended function agrees locally with the actual cutoff product throughout
its open domain. The inner plateau preserves the quadratic jet on the zero
section; isolation gives the same prescribed jet on the complete supplied curve.
No quantitative derivative estimate is claimed here.
-/

@[expose] public noncomputable section

open Filter Function Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- For a fixed transverse chart and compactly supported bilinear family, choose
one pilot radius before the logarithmic parameters. The explicit extension uses
only the radial logarithmic cutoff and an indicator of the open chart domain.

The coordinate premises are outputs of the existing transverse-curve chart
owner, with `S = ell.ker`. The complete curve `q` agrees with `γ` on `J` and visits
`U` only at times in `J`. No smoothness or jet of the quadratic expression, and no
compactness or smoothness of its extension, is assumed. The target needs neither
finite dimension nor completeness. -/
theorem exists_logarithmic_tube_extension_radius
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Submodule ℝ E) (e : OpenPartialHomeomorph (ℝ × S) E)
    (γ : ℝ → E) (J : Set ℝ)
    (hγtarget : MapsTo γ J e.target)
    (htmap : MapsTo (fun x : E ↦ (e.symm x).1) e.target J)
    (ht : ContDiffOn ℝ ∞ (fun x : E ↦ (e.symm x).1) e.target)
    (hz : ContDiffOn ℝ ∞ (fun x : E ↦ ((e.symm x).2 : E)) e.target)
    (hcoord : ∀ s ∈ J, e.symm (γ s) = (s, (0 : S)))
    (hmod : ∀ s ∈ J, ∀ v : E,
      fderiv ℝ (fun x : E ↦ ((e.symm x).2 : E)) (γ s) v - v ∈
        Submodule.span ℝ ({deriv γ s} : Set E))
    (B : ℝ → E →L[ℝ] E →L[ℝ] F)
    (hB : ContDiff ℝ ∞ B) (hBcompact : HasCompactSupport B)
    (hBsupport : tsupport B ⊆ J)
    (hsym : ∀ s ∈ J, ∀ v w, B s v w = B s w v)
    (hker : ∀ s ∈ J, ∀ v, B s (deriv γ s) v = 0)
    (q : ℝ → E) (hq : EqOn q γ J)
    (U : Set E) (hU : IsOpen U) (hsupportU : γ '' tsupport B ⊆ U)
    (hisolate : q ⁻¹' U ⊆ J) :
    ∃ ρ : ℝ, 0 < ρ ∧
      tsupport B ×ˢ closedBall (0 : S) ρ ⊆ e.source ∩ e ⁻¹' U ∧
      ∀ δ L : ℝ, 0 < δ → δ < ρ → 1 ≤ L →
        let t : E → ℝ := fun x ↦ (e.symm x).1
        let z : E → E := fun x ↦ ((e.symm x).2 : E)
        let Q : E → F := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
        let Ω : Set E := e.target ∩ U
        let P : E → F := Ω.indicator (fun x ↦ radialLogarithmicCutoff δ L (z x) • Q x)
        ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
          tsupport P ⊆ e '' (tsupport B ×ˢ closedBall (0 : S) δ) ∧
          tsupport P ⊆ Ω ∧
          (∀ x ∈ Ω, P =ᶠ[𝓝 x] (fun y ↦ radialLogarithmicCutoff δ L (z y) • Q y)) ∧
          ∀ s : ℝ, P (q s) = 0 ∧ fderiv ℝ P (q s) = 0 ∧
            fderiv ℝ (fderiv ℝ P) (q s) = B s := by
  classical
  let t : E → ℝ := fun x ↦ (e.symm x).1
  let z : E → E := fun x ↦ ((e.symm x).2 : E)
  let Q : E → F := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
  let Ω : Set E := e.target ∩ U
  have hΩ : IsOpen Ω := e.open_target.inter hU
  have htime (s : ℝ) (hs : s ∈ J) : t (γ s) = s := congrArg Prod.fst (hcoord s hs)
  have hzero (s : ℝ) (hs : s ∈ J) : z (γ s) = 0 :=
    congrArg (fun p : ℝ × S ↦ (p.2 : E)) (hcoord s hs)
  obtain ⟨hQ, hjet⟩ := quadratic_tube_jet γ t z B J e.target
    e.open_target hγtarget htmap ht hz hB.contDiffOn htime hzero hmod hsym hker
  have haxisO : tsupport B ×ˢ ({0} : Set S) ⊆ e.source ∩ e ⁻¹' U := by
    rintro ⟨s, y⟩ ⟨hs, rfl⟩
    have hγ := hγtarget (hBsupport hs)
    rw [← hcoord s (hBsupport hs)]
    exact ⟨e.map_target hγ, show e (e.symm (γ s)) ∈ U from
      (e.right_inv hγ).symm ▸ hsupportU ⟨s, hs, rfl⟩⟩
  obtain ⟨V, W, _, hW, hBV, hzeroW, hVW⟩ := generalized_tube_lemma hBcompact.isCompact
    isCompact_singleton (e.continuousOn.isOpen_inter_preimage e.open_source hU) haxisO
  obtain ⟨ρ, hρ, hρW⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall (0 : S) ρ ⊆ W :=
    Metric.nhds_basis_closedBall.mem_iff.mp (hW.mem_nhds (hzeroW (mem_singleton 0)))
  have hpilot : tsupport B ×ˢ closedBall (0 : S) ρ ⊆ e.source ∩ e ⁻¹' U :=
    fun _ hp ↦ hVW ⟨hBV hp.1, hρW hp.2⟩
  refine ⟨ρ, hρ, hpilot, fun δ L hδ hδρ hL ↦ ?_⟩
  let χ : E → ℝ := fun x ↦ radialLogarithmicCutoff δ L (z x)
  let P : E → F := Ω.indicator (fun x ↦ χ x • Q x)
  let K : Set E := e '' (tsupport B ×ˢ closedBall (0 : S) δ)
  have hsmall : tsupport B ×ˢ closedBall (0 : S) δ ⊆ e.source ∩ e ⁻¹' U :=
    fun _ hp ↦ hpilot ⟨hp.1, closedBall_subset_closedBall hδρ.le hp.2⟩
  have hK : IsCompact K :=
    (hBcompact.isCompact.prod (isCompact_closedBall (0 : S) δ)).image_of_continuousOn
      (e.continuousOn.mono (fun _ hp ↦ (hsmall hp).1))
  have hKΩ : K ⊆ Ω := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨e.map_source (hsmall hp).1, (hsmall hp).2⟩
  obtain ⟨_, _, hradial⟩ := exists_pos_radialLogarithmicCutoff_bounds (E := E)
  obtain ⟨hcut, hone, _, _, hcutSupport, _⟩ := hradial δ L hδ hL
  have hsupport : Function.support P ⊆ K := by
    intro x hx
    have hxΩ : x ∈ Ω := mem_of_indicator_ne_zero hx
    have hnonzero : χ x • Q x ≠ 0 := by
      simpa only [P, indicator_of_mem hxΩ] using show P x ≠ 0 from hx
    have hxB : t x ∈ tsupport B := by
      by_contra hout
      exact hnonzero (by simp only [Q, image_eq_zero_of_notMem_tsupport hout, zero_apply,
        smul_zero])
    exact ⟨e.symm x, ⟨hxB, mem_closedBall_zero_iff.mpr (mem_closedBall_zero_iff.mp
      (hcutSupport (subset_tsupport _ (left_ne_zero_of_smul hnonzero))))⟩, e.right_inv hxΩ.1⟩
  have hPsupportK : tsupport P ⊆ K := closure_minimal hsupport hK.isClosed
  have hPsupportΩ : tsupport P ⊆ Ω := hPsupportK.trans hKΩ
  have hP : ContDiff ℝ ∞ P := ((hcut.fun_comp_contDiffOn (hz.mono fun _ hx ↦ hx.1)).fun_smul
    (hQ.mono fun _ hx ↦ hx.1)).indicator_of_tsupport_subset hΩ hPsupportΩ
  have hproductGerm (x : E) (hx : x ∈ Ω) : P =ᶠ[𝓝 x] (fun y ↦ χ y • Q y) :=
    eventually_of_mem (hΩ.mem_nhds hx) fun _ hy ↦ indicator_of_mem hy _
  refine ⟨hP, hK.of_isClosed_subset (isClosed_tsupport P) hPsupportK, hPsupportK, hPsupportΩ,
    hproductGerm, fun s ↦ ?_⟩
  by_cases hsΩ : q s ∈ Ω
  · have hsJ : s ∈ J := hisolate hsΩ.2
    have hqs : q s = γ s := hq hsJ
    -- near the zero section the cutoff is one, so `P` agrees with `Q`
    have hzq : z (q s) = 0 := hqs ▸ hzero s hsJ
    have hnear : z ⁻¹' ball (0 : E) (δ * Real.exp (-L)) ∈ 𝓝 (q s) :=
      (show ContinuousAt z (q s) from hz.continuousOn.continuousAt
        (e.open_target.mem_nhds hsΩ.1)).preimage_mem_nhds (hzq ▸ ball_mem_nhds _ (by positivity))
    have heq : P =ᶠ[𝓝 (q s)] Q := by
      filter_upwards [hproductGerm (q s) hsΩ, hnear] with x hx hnormal
      rw [hx]
      change radialLogarithmicCutoff δ L (z x) • Q x = Q x
      rw [hone (z x) (mem_ball_zero_iff.mp hnormal).le, one_smul]
    have hjetq := hqs ▸ hjet s hsJ
    exact ⟨heq.self_of_nhds.trans hjetq.1,
      (heq.fderiv_eq (𝕜 := ℝ)).trans hjetq.2.1,
      ((heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)).trans hjetq.2.2⟩
  · have hBzero : B s = 0 := image_eq_zero_of_notMem_tsupport fun hsB ↦ hsΩ <| by
      rw [hq (hBsupport hsB)]
      exact ⟨hγtarget (hBsupport hsB), hsupportU ⟨s, hsB, rfl⟩⟩
    have hPout : q s ∉ tsupport P := fun hx ↦ hsΩ (hPsupportΩ hx)
    refine ⟨image_eq_zero_of_notMem_tsupport hPout, fderiv_of_notMem_tsupport ℝ hPout, ?_⟩
    rw [hBzero]
    exact fderiv_of_notMem_tsupport ℝ fun hx ↦ hPout (tsupport_fderiv_subset ℝ (f := P) hx)

end PDE.Analysis
