/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smooth selection of nondegenerate stationary points

The parameter derivative of a jointly smooth function is jointly smooth with
one fewer derivative. An invertible parameter Hessian therefore gives a
locally unique C¹ stationary selector by Mathlib's implicit-function theorem.
The stationarity equation and regularity of the selector are conclusions.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

variable {E A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The parameter derivative is the full derivative restricted to parameter
directions. This is a chain rule for the slice. -/
theorem fderiv_snd_eq_comp_inr {f : E × A → B} {p : E × A}
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun a ↦ f (p.1, a)) p.2 =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ E A) :=
  (hf.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

/-- Differentiating in the parameter lowers joint local regularity by one. -/
theorem contDiffAt_fderiv_snd {f : E × A → B} {p : E × A} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1) f p) :
    ContDiffAt ℝ k (fun q : E × A ↦ fderiv ℝ (fun a ↦ f (q.1, a)) q.2) p := by
  have hD : ContDiffAt ℝ k
      (fun q : E × A ↦ (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ E A)) p :=
    (hf.fderiv_right (by simp)).clm_comp contDiffAt_const
  apply hD.congr_of_eventuallyEq
  filter_upwards [hf.eventually (by simp)] with q hq
  exact fderiv_snd_eq_comp_inr (hq.differentiableAt (by norm_num))

/-- Along a differentiable stationary selector, the envelope derivative is
the spatial derivative with the parameter held fixed. -/
theorem fderiv_stationary_envelope {f : E × A → B} {φ : E → A} {x : E}
    (hf : DifferentiableAt ℝ f (x, φ x)) (hφ : DifferentiableAt ℝ φ x)
    (hstationary : fderiv ℝ (fun a ↦ f (x, a)) (φ x) = 0) :
    fderiv ℝ (fun y ↦ f (y, φ y)) x = fderiv ℝ (fun y ↦ f (y, φ x)) x := by
  change fderiv ℝ (f ∘ fun y ↦ (id y, φ y)) x =
    fderiv ℝ (f ∘ fun y ↦ (y, φ x)) x
  rw [(hf.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk hφ.hasFDerivAt)).fderiv,
    (hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x (φ x))).fderiv]
  ext v
  have hz := congrArg (fun L : A →L[ℝ] B ↦ L (fderiv ℝ φ x v))
    ((fderiv_snd_eq_comp_inr hf).symm.trans hstationary)
  change fderiv ℝ f (x, φ x) (v, fderiv ℝ φ x v) = fderiv ℝ f (x, φ x) (v, 0)
  rw [show (v, fderiv ℝ φ x v) = (v, 0) + (0, fderiv ℝ φ x v) by simp, map_add]
  simpa using hz

variable [CompleteSpace E] [CompleteSpace A]

/-- A stationary point with invertible parameter Hessian continues to a
locally unique C¹ family of stationary points. Nondegeneracy is imposed on
the second derivative of the parameter slice. -/
theorem exists_stationary_selector {f : E × A → ℝ} {x : E} {a : A}
    (hf : ContDiffAt ℝ 2 f (x, a))
    (hstationary : fderiv ℝ (fun b ↦ f (x, b)) a = 0)
    (hessian : (fderiv ℝ (fun b ↦ fderiv ℝ (fun c ↦ f (x, c)) b) a).IsInvertible) :
    ∃ φ : E → A, φ x = a ∧ ContDiffAt ℝ 1 φ x ∧
      (∀ᶠ y in 𝓝 x, fderiv ℝ (fun b ↦ f (y, b)) (φ y) = 0) ∧
      (∀ᶠ q : E × A in 𝓝 (x, a),
        fderiv ℝ (fun b ↦ f (q.1, b)) q.2 = 0 ↔ φ q.1 = q.2) := by
  let G : E × A → A →L[ℝ] ℝ := fun q ↦ fderiv ℝ (fun b ↦ f (q.1, b)) q.2
  have hG : ContDiffAt ℝ 1 G (x, a) := contDiffAt_fderiv_snd hf
  have hinv : ((fderiv ℝ G (x, a)).comp (ContinuousLinearMap.inr ℝ E A)).IsInvertible := by
    rw [← fderiv_snd_eq_comp_inr hG.differentiableAt_one]
    exact hessian
  let φ := hG.implicitFunction one_ne_zero hinv
  refine ⟨φ, hG.implicitFunction_apply_self one_ne_zero hinv,
    hG.contDiffAt_implicitFunction one_ne_zero hinv, ?_, ?_⟩
  · simpa only [G, hstationary] using hG.eventually_apply_implicitFunction one_ne_zero hinv
  · simpa only [G, hstationary] using hG.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv

end PDE.Analysis
