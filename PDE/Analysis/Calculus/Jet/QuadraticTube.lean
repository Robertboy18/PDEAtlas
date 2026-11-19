/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

import PDE.Analysis.Calculus.Composition
import PDE.Analysis.Calculus.Jet.Quadratic

/-!
# Ambient second jets from transverse coordinates

A varying quadratic form has a particularly simple second jet where its vector
argument vanishes. The calculation is a pullback of the existing fixed quadratic
polynomial on the product of a vector space and its space of linear maps.

For tube coordinates along a curve, the differential of the transverse coordinate
need only equal the identity modulo the tangent. A symmetric bilinear family
annihilating that tangent is then the full ambient Hessian of the explicit
quadratic expression. The tube and its coordinate identities are supplied data.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Topology

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a zero of the vector argument, derivatives of the bilinear family do not
contribute to the second jet. The two displayed terms retain both mixed slots;
no symmetry of the family is needed. -/
theorem quadratic_family_jet_of_eq_zero
    {B : E → E →L[ℝ] E →L[ℝ] F} {z : E → E} {x : E}
    (hB : ContDiffAt ℝ 2 B x) (hz : ContDiffAt ℝ 2 z x) (hzero : z x = 0) :
    let Q := fun y ↦ (1 / 2 : ℝ) • B y (z y) (z y)
    Q x = 0 ∧ fderiv ℝ Q x = 0 ∧
      ∀ v w, fderiv ℝ (fderiv ℝ Q) x v w =
        (1 / 2 : ℝ) •
          (B x (fderiv ℝ z x v) (fderiv ℝ z x w) +
            B x (fderiv ℝ z x w) (fderiv ℝ z x v)) := by
  let P := E × (E →L[ℝ] F)
  let C : P →L[ℝ] P →L[ℝ] F :=
    ((ContinuousLinearMap.compL ℝ P E F).flip
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] F))).comp
        (ContinuousLinearMap.snd ℝ E (E →L[ℝ] F))
  have hC (u v : P) : C u v = u.2 v.1 := rfl
  let g : E → P := fun y ↦ (z y, B y (z y))
  let q : P → F := quadraticJet 0 0 0 C
  have hg : ContDiffAt ℝ 2 g x := hz.prodMk (hB.clm_apply hz)
  have hq : ContDiff ℝ ∞ q := contDiff_quadraticJet 0 0 0 C
  have hq₂ : ContDiffAt ℝ 2 q (g x) := hq.contDiffAt.of_le (by simp)
  have hgzero : g x = 0 := by
    change (z x, B x (z x)) = (0, 0)
    simp [hzero]
  have hqzero : fderiv ℝ q (0 : P) = 0 := fderiv_quadraticJet_self 0 0 0 C
  have hqsecond : fderiv ℝ (fderiv ℝ q) (0 : P) =
      (1 / 2 : ℝ) • (C + C.flip) := fderiv_fderiv_quadraticJet 0 0 0 C 0
  have heq : (fun y ↦ (1 / 2 : ℝ) • B y (z y) (z y)) = q ∘ g := by
    funext y
    simp [q, quadraticJet, hC, g]
  have hBd := hB.differentiableAt two_ne_zero
  have hzd := hz.differentiableAt two_ne_zero
  have hDg (v : E) : fderiv ℝ g x v =
      (fderiv ℝ z x v, B x (fderiv ℝ z x v)) := by
    change fderiv ℝ (fun y ↦ (z y, B y (z y))) x v = _
    rw [(hzd.hasFDerivAt.prodMk (hBd.hasFDerivAt.clm_apply hzd.hasFDerivAt)).fderiv]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      hzero, map_zero, add_zero]
  dsimp only
  refine ⟨by simp [hzero], ?_, ?_⟩
  · rw [heq, fderiv_comp x (hq₂.differentiableAt two_ne_zero)
      (hg.differentiableAt two_ne_zero), hgzero, hqzero, ContinuousLinearMap.zero_comp]
  · intro v w
    rw [heq]
    have hcomp : ContDiffAt ℝ 2 (q ∘ g) x := hq₂.comp x hg
    have hD : DifferentiableAt ℝ (fderiv ℝ (q ∘ g)) x :=
      (hcomp.fderiv_right (m := 1) (by decide)).differentiableAt_one
    have heval : fderiv ℝ (fun y ↦ fderiv ℝ (q ∘ g) y w) x v =
        fderiv ℝ (fderiv ℝ (q ∘ g)) x v w := by
      rw [fderiv_clm_apply hD (differentiableAt_const w)]
      simp
    rw [← heval, fderiv_fderiv_comp_apply hq₂ hg v w, hgzero, hqzero, hqsecond]
    simp only [smul_apply, add_apply, ContinuousLinearMap.flip_apply,
      hC, hDg, zero_apply, add_zero]

/-- Smooth tube coordinates realize a tangent-annihilating symmetric family as
an ambient Hessian, with zero value and first derivative along the same curve.
The span condition states exactly that `Dz` is the identity modulo the actual
curve tangent. No invertible chart, extension, or cutoff is chosen here. -/
theorem quadratic_tube_jet
    (γ : ℝ → E) (t : E → ℝ) (z : E → E)
    (B : ℝ → E →L[ℝ] E →L[ℝ] F) (I : Set ℝ) (Ω : Set E)
    (hΩ : IsOpen Ω) (hγ : MapsTo γ I Ω) (htI : MapsTo t Ω I)
    (ht : ContDiffOn ℝ ∞ t Ω) (hz : ContDiffOn ℝ ∞ z Ω)
    (hB : ContDiffOn ℝ ∞ B I)
    (htime : ∀ s ∈ I, t (γ s) = s)
    (hzero : ∀ s ∈ I, z (γ s) = 0)
    (hmod : ∀ s ∈ I, ∀ v, fderiv ℝ z (γ s) v - v ∈
      Submodule.span ℝ ({deriv γ s} : Set E))
    (hsym : ∀ s ∈ I, ∀ v w, B s v w = B s w v)
    (hker : ∀ s ∈ I, ∀ v, B s (deriv γ s) v = 0) :
    let Q := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
    ContDiffOn ℝ ∞ Q Ω ∧
      ∀ s ∈ I, Q (γ s) = 0 ∧ fderiv ℝ Q (γ s) = 0 ∧
        fderiv ℝ (fderiv ℝ Q) (γ s) = B s := by
  let Q := fun x ↦ (1 / 2 : ℝ) • B (t x) (z x) (z x)
  have hBt : ContDiffOn ℝ ∞ (fun x ↦ B (t x)) Ω := hB.comp ht htI
  have hQ : ContDiffOn ℝ ∞ Q Ω :=
    ((hBt.clm_apply hz).clm_apply hz).const_smul (1 / 2 : ℝ)
  refine ⟨hQ, ?_⟩
  intro s hs
  have hmem : Ω ∈ 𝓝 (γ s) := hΩ.mem_nhds (hγ hs)
  obtain ⟨hvalue, hfirst, hsecond⟩ := quadratic_family_jet_of_eq_zero
    ((hBt.contDiffAt hmem).of_le (by simp))
    ((hz.contDiffAt hmem).of_le (by simp)) (hzero s hs)
  have hright (v : E) : B s v (deriv γ s) = 0 :=
    (hsym s hs v (deriv γ s)).trans (hker s hs v)
  have hpull (v w : E) :
      B s (fderiv ℝ z (γ s) v) (fderiv ℝ z (γ s) w) = B s v w := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hmod s hs v)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hmod s hs w)
    have hv : fderiv ℝ z (γ s) v = a • deriv γ s + v := by
      rw [ha, sub_add_cancel]
    have hw : fderiv ℝ z (γ s) w = b • deriv γ s + w := by
      rw [hb, sub_add_cancel]
    rw [hv, hw]
    simp [map_add, map_smul, hker s hs, hright]
  refine ⟨hvalue, hfirst, ?_⟩
  ext v w
  rw [hsecond v w, htime s hs, hpull v w, hpull w v, hsym s hs w v]
  rw [← two_smul ℝ (B s v w), one_div,
    inv_smul_smul₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

end PDE.Analysis
