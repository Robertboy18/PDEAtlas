/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Logarithmic.Tube
public import PDE.Analysis.Calculus.LocalExtension.Tube.ProductBounds

import PDE.Analysis.Calculus.Jet.QuadraticTube

/-!
# Uniform estimates for a compact logarithmic tube extension

The chart and bilinear family determine one compact pilot tube. Their derivatives
are bounded there before the cutoff radius and logarithmic width are chosen.
The actual zero extension therefore has globally small value and first
derivative, while its Hessian stays close to the cutoff multiple of the prescribed
quadratic jet. No second cutoff is inserted during extension.
-/

@[expose] public noncomputable section

open Filter Function Metric Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- Realize the prescribed quadratic jet on the complete curve by the actual
logarithmic tube extension. Its value and derivative are uniformly small with
the outer radius; the Hessian error is controlled by that radius and the inverse
logarithmic width. The pilot radius and common constant are chosen first.

The bilinear family need not be small. The Hessian is compared to its cutoff
multiple, which is the term preserved by the neutral-jet argument. -/
theorem exists_quantitative_logarithmic_tube_extension
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ell : E →L[ℝ] ℝ) (e : OpenPartialHomeomorph (ℝ × ell.ker) E)
    (γ : ℝ → E) (J : Set ℝ)
    (he : EqOn e (fun p ↦ γ p.1 + (p.2 : E)) e.source)
    (hγtarget : MapsTo γ J e.target)
    (htmap : MapsTo (fun x : E ↦ (e.symm x).1) e.target J)
    (ht : ContDiffOn ℝ ∞ (fun x : E ↦ (e.symm x).1) e.target)
    (hz : ContDiffOn ℝ ∞ (fun x : E ↦ ((e.symm x).2 : E)) e.target)
    (hcoord : ∀ s ∈ J, e.symm (γ s) = (s, (0 : ell.ker)))
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
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧
      tsupport B ×ˢ closedBall (0 : ell.ker) ρ ⊆ e.source ∩ e ⁻¹' U ∧
      ∀ δ L : ℝ, 0 < δ → δ < ρ → δ ≤ 1 → 1 ≤ L →
        let t : E → ℝ := fun x ↦ (e.symm x).1
        let z : E → E := fun x ↦ ((e.symm x).2 : E)
        let Q : E → F := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
        let Ω : Set E := e.target ∩ U
        let P : E → F := Ω.indicator (fun x ↦ radialLogarithmicCutoff δ L (z x) • Q x)
        ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧
          tsupport P ⊆ e '' (tsupport B ×ˢ closedBall (0 : ell.ker) δ) ∧
          tsupport P ⊆ Ω ∧
          (∀ s : ℝ, P (q s) = 0 ∧ fderiv ℝ P (q s) = 0 ∧
            fderiv ℝ (fderiv ℝ P) (q s) = B s) ∧
          ∀ x : E, ‖P x‖ ≤ C * δ ^ 2 ∧ ‖fderiv ℝ P x‖ ≤ C * δ ∧
            (x ∈ tsupport P → t x ∈ tsupport B ∧
              ‖fderiv ℝ (fderiv ℝ P) x -
                radialLogarithmicCutoff δ L (z x) • B (t x)‖ ≤ C * δ + C / L) := by
  classical
  let t : E → ℝ := fun x ↦ (e.symm x).1
  let z : E → E := fun x ↦ ((e.symm x).2 : E)
  let Q : E → F := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
  obtain ⟨ρ, hρ, hpilot, hbuild⟩ := exists_logarithmic_tube_extension_radius
    ell.ker e γ J hγtarget htmap ht hz hcoord hmod B hB hBcompact hBsupport
    hsym hker q hq U hU hsupportU hisolate
  have htime (s : ℝ) (hs : s ∈ J) : t (γ s) = s :=
    congrArg Prod.fst (hcoord s hs)
  have hzero (s : ℝ) (hs : s ∈ J) : z (γ s) = 0 :=
    congrArg (fun p : ℝ × ell.ker ↦ (p.2 : E)) (hcoord s hs)
  obtain ⟨hQ, hjet⟩ := quadratic_tube_jet γ t z B J e.target
    e.open_target hγtarget htmap ht hz hB.contDiffOn htime hzero hmod hsym hker
  have hsource : tsupport B ×ˢ closedBall (0 : ell.ker) ρ ⊆ e.source :=
    fun _ hp ↦ (hpilot hp).1
  have htarget : e '' (tsupport B ×ˢ closedBall (0 : ell.ker) ρ) ⊆ e.target :=
    fun _ ⟨_, hp, hpx⟩ ↦ hpx ▸ e.map_source (hsource hp)
  have hQlocal (x : E) (hx : x ∈ e '' (tsupport B ×ˢ closedBall (0 : ell.ker) ρ)) :
      ContDiffAt ℝ 3 Q x :=
    (hQ.contDiffAt (e.open_target.mem_nhds (htarget hx))).of_le (by simp)
  have hzlocal (x : E) (hx : x ∈ e '' (tsupport B ×ˢ closedBall (0 : ell.ker) ρ)) :
      ContDiffAt ℝ 3 z x :=
    (hz.contDiffAt (e.open_target.mem_nhds (htarget hx))).of_le (by simp)
  obtain ⟨C, hC, hbound⟩ := exists_pos_compact_tube_radial_product_bounds
    hBcompact.isCompact hρ he hsource hQlocal hzlocal
    (fun s hs ↦ (hjet s (hBsupport hs)).1)
    (fun s hs ↦ (hjet s (hBsupport hs)).2.1)
    (fun s hs ↦ (hjet s (hBsupport hs)).2.2)
  refine ⟨ρ, C, hρ, hC, hpilot, ?_⟩
  intro δ L hδ hδρ hδ₁ hL
  let Ω : Set E := e.target ∩ U
  let P : E → F := Ω.indicator (fun x ↦ radialLogarithmicCutoff δ L (z x) • Q x)
  obtain ⟨hP, hPcompact, hPK, hPΩ, hPgerm, hPjet⟩ := hbuild δ L hδ hδρ hL
  refine ⟨hP, hPcompact, hPK, hPΩ, hPjet, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport P
  · have hxK := hPK hx
    obtain ⟨hv, hd, hh⟩ := hbound δ L hδ (le_min hδρ.le hδ₁) hL x hxK
    have hgerm := hPgerm x (hPΩ hx)
    have hD := hgerm.fderiv_eq (𝕜 := ℝ)
    have hH := (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    refine ⟨?_, ?_, fun _ ↦ ⟨?_, ?_⟩⟩
    · simpa only [hgerm.self_of_nhds] using hv
    · simpa only [hD] using hd
    · obtain ⟨p, hp, rfl⟩ := hxK
      change (e.symm (e p)).1 ∈ tsupport B
      rw [e.left_inv (hsource ⟨hp.1, closedBall_subset_closedBall hδρ.le hp.2⟩)]
      exact hp.1
    · simpa only [hH] using hh
  · refine ⟨?_, ?_, fun h ↦ (hx h).elim⟩
    · change ‖P x‖ ≤ C * δ ^ 2
      rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact mul_nonneg hC.le (sq_nonneg δ)
    · change ‖fderiv ℝ P x‖ ≤ C * δ
      rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
      exact mul_nonneg hC.le hδ.le

end PDE.Analysis
