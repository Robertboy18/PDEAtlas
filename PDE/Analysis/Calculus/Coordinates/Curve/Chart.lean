/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# A local transverse chart for a supplied smooth curve

The forward map is `φ(s, y) = γ s + y`, with `y` in the kernel of a fixed
transverse covector. Mathlib's right-inverse splitting supplies its invertible
derivative, and the inverse function theorem supplies the local chart.

The chart and its inverse are smooth on their open source and target. The normal
coordinate, viewed in the ambient space, has derivative `Id - γ' ⊗ Dt` throughout
the target. This is a local construction, with no global separation assertion.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PDE.Analysis

/-- A smooth local transverse chart through the supplied curve at `t₀`.

The common open time neighborhood `J` lies in the supplied smoothness domain `I`.
The curve maps `J` into the open target, and the inverse time coordinate maps the
whole target back into `J`. Both inverse coordinates are smooth there.

The normal coordinate is viewed in `E`. Its ordinary Fréchet derivative is
`Id - γ' ⊗ Dt` on the target, and hence equals the identity modulo the actual
curve tangent along `γ`. These are the coordinate hypotheses for a local
quadratic tube jet, without any hypothesis on a bilinear family.

No finite-dimensional coordinates or new curve are selected. -/
theorem exists_smooth_transverse_curve_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {γ : ℝ → E} {I : Set ℝ} {t₀ : ℝ}
    (ell : E →L[ℝ] ℝ) (hI : IsOpen I) (ht₀ : t₀ ∈ I)
    (hγ : ContDiffOn ℝ ∞ γ I) (htrans : ell (deriv γ t₀) ≠ 0) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ell.ker) E) (J : Set ℝ),
      let t : E → ℝ := fun x ↦ (e.symm x).1
      let z : E → E := fun x ↦ ((e.symm x).2 : E)
      IsOpen J ∧ t₀ ∈ J ∧ J ⊆ I ∧
      (e : (ℝ × ell.ker) → E) = (fun p ↦ γ p.1 + (p.2 : E)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      MapsTo γ J e.target ∧ MapsTo t e.target J ∧
      ContDiffOn ℝ ∞ t e.target ∧ ContDiffOn ℝ ∞ z e.target ∧
      (∀ s ∈ J, e.symm (γ s) = (s, (0 : ell.ker))) ∧
      (∀ s ∈ J, t (γ s) = s ∧ z (γ s) = 0) ∧
      (∀ x ∈ e.target,
        fderiv ℝ z x = ContinuousLinearMap.id ℝ E -
          (fderiv ℝ t x).smulRight (deriv γ (t x))) ∧
      ∀ s ∈ J, ∀ w, fderiv ℝ z (γ s) w - w ∈
        Submodule.span ℝ ({deriv γ s} : Set E) := by
  -- Normalizing the covector preserves its kernel and makes `r ↦ r • v` a right inverse.
  have hlin (v : E) (hv : ell v ≠ 0) :
      ∃ D : (ℝ × ell.ker) ≃L[ℝ] E, ∀ p, D p = p.1 • v + (p.2 : E) := by
    let α : E →L[ℝ] ℝ := (ell v)⁻¹ • ell
    let q : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
    have hαv : α v = 1 := inv_mul_cancel₀ hv
    have hq : Function.RightInverse q α := fun r ↦ by
      change α (r • v) = r
      rw [map_smul, hαv, smul_eq_mul, mul_one]
    have hker : α.ker = ell.ker := LinearMap.ker_smul ell.toLinearMap _ (inv_ne_zero hv)
    let k : α.ker ≃L[ℝ] ell.ker := ContinuousLinearEquiv.ofEq _ _ hker
    let S : E ≃L[ℝ] (ℝ × ell.ker) :=
      (ContinuousLinearEquiv.equivOfRightInverse α q hq).trans
        ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr k)
    exact ⟨S.symm, fun _ ↦ rfl⟩
  -- Keep one open region where both the supplied smoothness and transversality hold.
  have hden : ContinuousOn (fun s ↦ ell (deriv γ s)) I :=
    ell.continuous.comp_continuousOn
      (hγ.continuousOn_deriv_of_isOpen hI (by simp))
  let I₁ : Set ℝ := I ∩ (fun s ↦ ell (deriv γ s)) ⁻¹' ({0} : Set ℝ)ᶜ
  have hI₁ : IsOpen I₁ :=
    hden.isOpen_inter_preimage hI isClosed_singleton.isOpen_compl
  let V : Set (ℝ × ell.ker) := I₁ ×ˢ univ
  have hV : IsOpen V := hI₁.prod isOpen_univ
  have hbase : (t₀, (0 : ell.ker)) ∈ V :=
    ⟨⟨ht₀, htrans⟩, mem_univ _⟩
  let φ : (ℝ × ell.ker) → E := fun p ↦ γ p.1 + (p.2 : E)
  have hnormal : ContDiff ℝ ∞ (fun p : ℝ × ell.ker ↦ (p.2 : E)) :=
    ell.ker.subtypeL.contDiff.comp contDiff_snd
  have hφ : ContDiffOn ℝ ∞ φ V :=
    (hγ.comp contDiffOn_fst (fun p hp ↦ hp.1.1)).add hnormal.contDiffOn
  have hφd (p : ℝ × ell.ker) (hp : p ∈ V) :
      ∃ D : (ℝ × ell.ker) ≃L[ℝ] E,
        HasFDerivAt φ (D : (ℝ × ell.ker) →L[ℝ] E) p := by
    obtain ⟨D, hD⟩ := hlin (deriv γ p.1) hp.1.2
    have hgp : DifferentiableAt ℝ γ p.1 :=
      (hγ.contDiffAt (hI.mem_nhds hp.1.1)).differentiableAt (by simp)
    let A : (ℝ × ell.ker) →L[ℝ] E :=
      (fderiv ℝ γ p.1).comp (ContinuousLinearMap.fst ℝ ℝ ell.ker) +
        ell.ker.subtypeL.comp (ContinuousLinearMap.snd ℝ ℝ ell.ker)
    have hA : HasFDerivAt φ A p :=
      (hgp.hasFDerivAt.comp p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).add
        (ell.ker.subtypeL.hasFDerivAt.comp p (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
    have hAD : A = D.toContinuousLinearMap := ContinuousLinearMap.ext fun r ↦ by
      change fderiv ℝ γ p.1 r.1 + (r.2 : E) = D r
      rw [hD, fderiv_eq_smul_deriv]
    exact ⟨D, hAD ▸ hA⟩
  obtain ⟨D₀, hD₀⟩ := hφd (t₀, (0 : ell.ker)) hbase
  have hφ₀ : ContDiffAt ℝ ∞ φ (t₀, (0 : ell.ker)) :=
    hφ.contDiffAt (hV.mem_nhds hbase)
  let e₀ := hφ₀.toOpenPartialHomeomorph φ hD₀ (by simp)
  -- A product source ensures both inclusions needed by the quadratic tube calculation.
  have hbase₀ : (t₀, (0 : ell.ker)) ∈ e₀.source ∩ V :=
    ⟨hφ₀.mem_toOpenPartialHomeomorph_source hD₀ (by simp), hbase⟩
  obtain ⟨J, K, hJ, hK, htJ, hzeroK, hJK⟩ :=
    isOpen_prod_iff.mp (e₀.open_source.inter hV) t₀ (0 : ell.ker) hbase₀
  let e := e₀.restrOpen (J ×ˢ K) (hJ.prod hK)
  have he : (e : (ℝ × ell.ker) → E) = φ := rfl
  have hsource : e.source ⊆ V := fun p (hp : p ∈ e₀.source ∩ (J ×ˢ K)) ↦ (hJK hp.2).2
  have hJsub : J ⊆ I := fun s hs ↦ (hJK (show (s, (0 : ell.ker)) ∈ J ×ˢ K from ⟨hs, hzeroK⟩)).2.1.1
  have heSmooth : ContDiffOn ℝ ∞ e e.source := hφ.mono hsource
  -- Prove inverse smoothness pointwise on the whole target, including order infinity.
  have hiSmooth : ContDiffOn ℝ ∞ e.symm e.target := by
    apply e.open_target.contDiffOn_iff.mpr
    intro x hx
    obtain ⟨D, hD⟩ := hφd (e.symm x) (hsource (e.map_target hx))
    exact e.contDiffAt_symm hx
      (show HasFDerivAt e (D : (ℝ × ell.ker) →L[ℝ] E) (e.symm x) from hD)
      (heSmooth.contDiffAt (e.open_source.mem_nhds (e.map_target hx)))
  let T : E → ℝ := fun x ↦ (e.symm x).1
  let z : E → E := fun x ↦ ((e.symm x).2 : E)
  have hTmap : MapsTo T e.target J := fun x hx ↦
    (show e.symm x ∈ e₀.source ∩ (J ×ˢ K) from e.map_target hx).2.1
  have hTSmooth : ContDiffOn ℝ ∞ T e.target := hiSmooth.fst
  have hzSmooth : ContDiffOn ℝ ∞ z e.target :=
    ell.ker.subtypeL.contDiff.comp_contDiffOn hiSmooth.snd
  have hezero (s : ℝ) : e (s, (0 : ell.ker)) = γ s := add_zero (γ s)
  have hcurve (s : ℝ) (hs : s ∈ J) :
      γ s ∈ e.target ∧ e.symm (γ s) = (s, (0 : ell.ker)) := by
    have hp : (s, (0 : ell.ker)) ∈ J ×ˢ K := ⟨hs, hzeroK⟩
    have hs' : (s, (0 : ell.ker)) ∈ e.source := ⟨(hJK hp).1, hp⟩
    constructor
    · simpa only [hezero] using e.map_source hs'
    · simpa only [hezero] using e.left_inv hs'
  have hγmap : MapsTo γ J e.target := fun s hs ↦ (hcurve s hs).1
  have hcoord (s : ℝ) (hs : s ∈ J) : T (γ s) = s ∧ z (γ s) = 0 :=
    ⟨congrArg Prod.fst (hcurve s hs).2,
      congrArg (fun p : ℝ × ell.ker ↦ (p.2 : E)) (hcurve s hs).2⟩
  have hzD (x : E) (hx : x ∈ e.target) :
      fderiv ℝ z x = ContinuousLinearMap.id ℝ E -
        (fderiv ℝ T x).smulRight (deriv γ (T x)) := by
    have hT : DifferentiableAt ℝ T x :=
      (hTSmooth.contDiffAt (e.open_target.mem_nhds hx)).differentiableAt (by simp)
    have hγT : DifferentiableAt ℝ γ (T x) :=
      (hγ.contDiffAt (hI.mem_nhds (hJsub (hTmap hx)))).differentiableAt (by simp)
    have heq : z =ᶠ[𝓝 x] (fun y ↦ y - γ (T y)) := by
      filter_upwards [e.eventually_right_inverse hx] with y hy
      change γ (T y) + z y = y at hy
      exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans hy)
    have hdz : HasFDerivAt z
        (ContinuousLinearMap.id ℝ E - (fderiv ℝ γ (T x)).comp (fderiv ℝ T x)) x :=
      ((hasFDerivAt_id x).sub (hγT.hasFDerivAt.comp x hT.hasFDerivAt)).congr_of_eventuallyEq
        heq
    have hcomp : (fderiv ℝ γ (T x)).comp (fderiv ℝ T x) =
        (fderiv ℝ T x).smulRight (deriv γ (T x)) :=
      ContinuousLinearMap.ext fun w ↦ fderiv_eq_smul_deriv (fderiv ℝ T x w)
    exact hdz.fderiv.trans (congrArg (fun A ↦ ContinuousLinearMap.id ℝ E - A) hcomp)
  refine ⟨e, J, hJ, htJ, hJsub, he, heSmooth, hiSmooth, hγmap, hTmap,
    hTSmooth, hzSmooth, (fun s hs ↦ (hcurve s hs).2), hcoord, hzD, ?_⟩
  intro s hs w
  rw [hzD (γ s) (hγmap hs), (hcoord s hs).1]
  change (w - (fderiv ℝ T (γ s) w) • deriv γ s) - w ∈ _
  refine Submodule.mem_span_singleton.mpr ⟨-(fderiv ℝ T (γ s) w), ?_⟩
  rw [neg_smul, sub_sub_cancel_left]

end PDE.Analysis
