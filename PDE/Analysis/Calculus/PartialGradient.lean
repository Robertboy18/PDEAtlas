/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Partial gradients on product spaces

Restricting the full differential to a Hilbert-space factor and applying the
Riesz isomorphism gives its partial gradient. This identifies the contribution
of that factor to the full differential and preserves one less derivative
of local smoothness. No regularity outside the neighborhood is needed.
-/

@[expose] public section

open scoped Gradient

open Set
open scoped ContDiff RealInnerProductSpace

namespace PDE.Analysis

/-- A partial gradient has one less derivative of joint local smoothness. -/
theorem contDiffAt_gradient_fst
    {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {m : ℕ∞} {f : H × A → ℝ} {p : H × A}
    (hf : ContDiffAt ℝ ((m : ℕ∞ω) + 1) f p) :
    ContDiffAt ℝ m (fun q ↦ ∇ (fun x ↦ f (x, q.2)) q.1) p := by
  let R := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv
  have hd : ContDiffAt ℝ m (fun q ↦ fderiv ℝ (fun x ↦ f (x, q.2)) q.1) p :=
    (hf.comp (p, p.1) (contDiffAt_snd.prodMk contDiffAt_fst.snd)).fderiv
      contDiffAt_fst le_rfl
  exact R.contDiff.contDiffAt.comp p hd

/-- The full differential splits into the first partial gradient and the
differential in the other factor. -/
theorem fderiv_prod_apply_eq_gradient_fst_add
    {H A : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {f : H × A → ℝ} {p : H × A} (hf : DifferentiableAt ℝ f p) (v : H × A) :
    fderiv ℝ f p v =
      ⟪∇ (fun x ↦ f (x, p.2)) p.1, v.1⟫ +
        fderiv ℝ (fun t ↦ f (p.1, t)) p.2 v.2 := by
  have hleft :=
    (hf.hasFDerivAt.comp p.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) p.1 p.2)).fderiv
  have hright :=
    (hf.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  dsimp only [Function.comp_def] at hleft hright
  rw [inner_gradient_left, hleft, hright]
  change fderiv ℝ f p v = fderiv ℝ f p (v.1, 0) + fderiv ℝ f p (0, v.2)
  rw [← map_add]
  simp

/-- The second-variable gradient of a `C¹` function on an open product-space
region is continuous on that region. The first factor is an arbitrary real
normed space and the second is a real Hilbert space. -/
theorem continuousOn_gradient_snd
    {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : A × H → ℝ} {s : Set (A × H)}
    (hf : ContDiffOn ℝ 1 f s) (hs : IsOpen s) :
    ContinuousOn (fun p ↦ ∇ (fun z ↦ f (p.1, z)) p.2) s := by
  let R := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv
  have hc : ContinuousOn
      (fun p ↦ R ((fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ A H))) s :=
    R.continuous.comp_continuousOn
      ((hf.continuousOn_fderiv_of_isOpen hs le_rfl).clm_comp continuous_const.continuousOn)
  apply hc.congr
  intro p hp
  have hd := ((hf.differentiableOn (by decide)) p hp).differentiableAt (hs.mem_nhds hp)
  have hpart := hd.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  change R (fderiv ℝ (fun z ↦ f (p.1, z)) p.2) = _
  exact congrArg R hpart.fderiv

end PDE.Analysis
