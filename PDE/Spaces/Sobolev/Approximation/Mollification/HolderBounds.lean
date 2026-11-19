/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.FiniteJets
public import PDE.FDeriv.PartialDeriv.WordBounds

/-!
# Uniform and Hölder bounds of mollifications

Mollification by a kernel of mass one does not increase uniform bounds
(`norm_mollify_le_of_ae_bound`), and it commutes with translations. A difference
`mollify f (y + h) - mollify f y` is therefore the mollification of `f (· + h) - f`, so an
`α`-Hölder bound `|f y - f z| ≤ M ‖y - z‖^α` of a continuous `f` passes to the mollification with
the same constant; for `α = 1` this is a Lipschitz bound.

For a compactly supported `C^m` function the coordinate derivative words of order `j ≤ m`
commute with mollification, so the words of `Dʲ (mollify f)` are bounded by the bound of `Dʲ f`;
applied to `f (· + h) - f`, this turns a Hölder bound of `Dʲ f` into one of `Dʲ (mollify f)`.

## Main results

* `mollify_comp_add_right`: mollification commutes with translations.
* `abs_mollify_sub_le_rpow`: an `α`-Hölder bound with constant `M` passes to the mollification
  with the same constant.
* `norm_iteratedFDeriv_mollify_le`: `‖Dʲ (mollify f)‖ ≤ nʲ N` when `‖Dʲ f‖ ≤ N`, for a compactly
  supported `C^m` function and `j ≤ m`.
* `norm_iteratedFDeriv_mollify_sub_le_rpow`: a Hölder bound of `Dʲ f` with constant `M` gives the
  Hölder constant `nʲ M` of `Dʲ (mollify f)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set

namespace SobolevSpace.Approximation

variable {n : ℕ}

/-- Mollification commutes with translations. -/
theorem mollify_comp_add_right (μ : Mollifier n) (ε : ℝ) (f : ℝ^n → ℝ) (h x : ℝ^n) :
    mollify μ ε (fun y ↦ f (y + h)) x = mollify μ ε f (x + h) := by
  simp only [mollify, convolution_def]
  congr 1
  funext t
  rw [sub_add_eq_add_sub]

/-- **Hölder bounds pass to mollifications** with the same constant. -/
theorem abs_mollify_sub_le_rpow (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) {f : ℝ^n → ℝ}
    (hf : Continuous f) {M α : ℝ} (hM : ∀ y z, |f y - f z| ≤ M * ‖y - z‖ ^ α) (x y : ℝ^n) :
    |mollify μ ε f x - mollify μ ε f y| ≤ M * ‖x - y‖ ^ α := by
  set h := x - y with hh
  have hx : mollify μ ε f x = mollify μ ε (fun z ↦ f (z + h)) y := by
    rw [mollify_comp_add_right, hh, add_sub_cancel]
  have hτ : Continuous fun z ↦ f (z + h) := hf.comp (continuous_id.add continuous_const)
  rw [hx, ← Pi.sub_apply (mollify μ ε (fun z ↦ f (z + h))),
    ← mollify_sub_of_pos μ hε _ _ hτ.locallyIntegrable hf.locallyIntegrable]
  rw [← Real.norm_eq_abs]
  refine norm_mollify_le_of_ae_bound μ hε (Eventually.of_forall fun z ↦ ?_) y
  have := hM (z + h) z
  simpa only [Pi.sub_apply, add_sub_cancel_left, Real.norm_eq_abs] using this

/-- **Derivatives of mollifications**: for a compactly supported `C^m` function and `j ≤ m`,
`‖Dʲ (mollify f)‖ ≤ nʲ N` when `‖Dʲ f‖ ≤ N`. -/
theorem norm_iteratedFDeriv_mollify_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) {m j : ℕ}
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f) (hj : j ≤ m) {N : ℝ}
    (hN : ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ N) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ j (mollify μ ε f) x‖ ≤ (n : ℝ) ^ j * N := by
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (mollify μ ε f) :=
    mollify_contDiff_of_pos μ hε f hf.continuous.locallyIntegrable
  refine PDE.norm_iteratedFDeriv_le_of_forall_word j
    ((hsm.of_le (by exact_mod_cast le_top)).contDiffAt) fun w hw ↦ ?_
  rw [iteratedPartialDeriv_mollify_of_contDiff μ (ε := ε) hf hfc w (hw ▸ hj)]
  refine norm_mollify_le_of_ae_bound μ hε (Eventually.of_forall fun z ↦ ?_) x
  have hz := PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv w
    ((hf.of_le (by exact_mod_cast hw ▸ hj)).contDiffAt (x := z))
  rw [hw] at hz
  exact hz.trans (hN z)

/-- **Hölder bounds of derivatives pass to mollifications**: for a compactly supported `C^m`
function, `j ≤ m`, a Hölder bound of `Dʲ f` with constant `M` gives the Hölder constant `nʲ M`
of `Dʲ (mollify f)`. -/
theorem norm_iteratedFDeriv_mollify_sub_le_rpow (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    {m j : ℕ} {f : ℝ^n → ℝ} (hf : ContDiff ℝ m f) (hfc : HasCompactSupport f) (hj : j ≤ m)
    {M α : ℝ} (hM : ∀ y z, ‖iteratedFDeriv ℝ j f y - iteratedFDeriv ℝ j f z‖ ≤ M * ‖y - z‖ ^ α)
    (x y : ℝ^n) :
    ‖iteratedFDeriv ℝ j (mollify μ ε f) x - iteratedFDeriv ℝ j (mollify μ ε f) y‖ ≤
      (n : ℝ) ^ j * (M * ‖x - y‖ ^ α) := by
  set h := x - y with hh
  set τ : ℝ^n → ℝ := fun z ↦ f (z + h) with hτdef
  have hτ : ContDiff ℝ m τ := hf.comp (contDiff_id.add contDiff_const)
  have hτc : HasCompactSupport τ := hfc.comp_homeomorph (Homeomorph.addRight h)
  have hsm : ∀ φ : ℝ^n → ℝ, Continuous φ → ContDiff ℝ (⊤ : ℕ∞) (mollify μ ε φ) :=
    fun φ hφ ↦ mollify_contDiff_of_pos μ hε φ hφ.locallyIntegrable
  have hcj : ∀ φ : ℝ^n → ℝ, Continuous φ → ∀ z, ContDiffAt ℝ j (mollify μ ε φ) z :=
    fun φ hφ z ↦ ((hsm φ hφ).of_le (by exact_mod_cast le_top)).contDiffAt
  have htrans : iteratedFDeriv ℝ j (mollify μ ε f) x =
      iteratedFDeriv ℝ j (mollify μ ε τ) y := by
    have hfun : mollify μ ε τ = fun z ↦ mollify μ ε f (z + h) :=
      funext fun z ↦ mollify_comp_add_right μ ε f h z
    rw [hfun, iteratedFDeriv_comp_add_right, hh, add_sub_cancel]
  have hdiff : iteratedFDeriv ℝ j (mollify μ ε τ) y - iteratedFDeriv ℝ j (mollify μ ε f) y =
      iteratedFDeriv ℝ j (mollify μ ε (τ - f)) y := by
    rw [mollify_sub_of_pos μ hε _ _ hτ.continuous.locallyIntegrable
      hf.continuous.locallyIntegrable,
      iteratedFDeriv_sub_apply (hcj τ hτ.continuous y) (hcj f hf.continuous y)]
  rw [htrans, hdiff]
  refine norm_iteratedFDeriv_mollify_le μ hε (hτ.sub hf) (hτc.sub hfc) hj (fun z ↦ ?_) y
  have hτj : iteratedFDeriv ℝ j τ z = iteratedFDeriv ℝ j f (z + h) := by
    rw [hτdef, iteratedFDeriv_comp_add_right]
  change ‖iteratedFDeriv ℝ j (τ - f) z‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((hτ.of_le (by exact_mod_cast hj)).contDiffAt)
    ((hf.of_le (by exact_mod_cast hj)).contDiffAt), hτj]
  have := hM (z + h) z
  rwa [add_sub_cancel_left] at this

end SobolevSpace.Approximation
