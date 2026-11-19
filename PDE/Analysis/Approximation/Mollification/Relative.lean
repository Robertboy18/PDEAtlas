/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Mollification.Real
public import PDE.Analysis.Approximation.EndpointFlattening
import CAS.ExactTactic

/-!
# Smooth odd approximation relative to an origin germ

Subtract a compact smooth copy of the origin germ, convolve the remainder, and
add the copy back. This gives smooth compact odd approximations with uniform
control of values and first derivatives, exact agreement on a fixed origin interval,
and a common outer support bound.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PDE.Analysis.Calculus

/-- Relative smoothing of a compact `C¹` odd function with a smooth odd origin germ.
The two preserved collars have sizes independent of the requested error tolerance. -/
theorem exists_smooth_odd_relative_approximation {f p : ℝ → ℝ} {r R s ε : ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hp : ContDiff ℝ ∞ p) (hfodd : ∀ x, f (-x) = -f x)
    (hpodd : ∀ x, p (-x) = -p x)
    (hr : 0 < r) (hrR : r < R) (hs : 0 < s) (hε : 0 < ε)
    (hfp : ∀ x, |x| < r → f x = p x)
    (hfzero : ∀ x, R ≤ |x| → f x = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ x, g (-x) = -g x) ∧
      (∀ x, |x| ≤ r / 4 → g x = f x) ∧
      (∀ x, R + s ≤ |x| → g x = 0) ∧
      (∀ x, |g x - f x| ≤ ε) ∧
      (∀ x, |deriv g x - deriv f x| ≤ ε) := by
  let P := flattenedProfile p r (r / 4)
  have hquarter : 0 < r / 4 := by positivity
  have hP : ContDiff ℝ ∞ P := contDiff_flattenedProfile hquarter hp.contDiffOn
  have hPc : HasCompactSupport P := hasCompactSupport_flattenedProfile hquarter
  have hPodd : ∀ x, P (-x) = -P x := flattenedProfile_neg hpodd r (r / 4)
  let F := fun x ↦ f x - P x
  have hF : ContDiff ℝ 1 F := hf.sub (hP.of_le (by simp))
  have hFc : HasCompactSupport F := hfc.sub hPc
  have hFodd : ∀ x, F (-x) = -F x := by
    intro x
    dsimp only [F]
    rw [hfodd, hPodd]
    cas
  have hFinner : ∀ x, |x| < r / 2 → F x = 0 := by
    intro x hx
    have hp' : P x = p x := flattenedProfile_eq_self hquarter (by cas)
    dsimp only [F]
    rw [hp', hfp x (by cas), sub_self]
  have hPouter : ∀ x, R ≤ |x| → P x = 0 := by
    intro x hx
    exact flattenedProfile_eq_zero hquarter (by cas)
  have hFouter : ∀ x, R ≤ |x| → F x = 0 := by
    intro x hx
    dsimp only [F]
    rw [hfzero x hx, hPouter x hx, sub_self]
  obtain ⟨d, hd, happrox⟩ := exists_realMollify_uniform_jet_radius hF hFc hε
  let ρ := min d (min (r / 4) s)
  have hρ : 0 < ρ := lt_min hd (lt_min hquarter hs)
  let φ : ContDiffBump (0 : ℝ) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  have hφd : φ.rOut ≤ d := min_le_left _ _
  have hφr : φ.rOut ≤ r / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hφs : φ.rOut ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hvalue, hderiv⟩ := happrox φ hφd
  let g := fun x ↦ P x + realMollify φ F x
  have hg : ContDiff ℝ ∞ g := hP.add (contDiff_realMollify φ hF.continuous)
  refine ⟨g, hg, hPc.add (hasCompactSupport_realMollify φ hFc), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp only [g]
    rw [hPodd, realMollify_neg φ hFodd]
    cas
  · intro x hx
    have hzero : realMollify φ F x = 0 :=
      realMollify_eq_zero_of_inner hFinner (by cas)
    have hFx : F x = 0 := hFinner x (by cas)
    dsimp only [F] at hFx
    dsimp only [g]
    rw [hzero, add_zero]
    exact (sub_eq_zero.mp hFx).symm
  · intro x hx
    have hzero : realMollify φ F x = 0 :=
      realMollify_eq_zero_of_outer hFouter (by cas)
    dsimp only [g]
    rw [hzero, hPouter x (by cas), add_zero]
  · intro x
    convert hvalue x using 1
    congr 1
    dsimp only [g, F]
    cas
  · intro x
    have hPd := (hP.differentiable (by simp)) x
    have hfd := hf.differentiable one_ne_zero x
    have hMd := ((contDiff_realMollify φ hF.continuous (n := ⊤)).differentiable
      (by simp)) x
    have hFderiv : deriv F x = deriv f x - deriv P x := deriv_sub hfd hPd
    have hgderiv : deriv g x = deriv P x + deriv (realMollify φ F) x :=
      deriv_add hPd hMd
    rw [hgderiv]
    convert hderiv x using 1
    rw [hFderiv]
    congr 1
    cas

/-- Agreement on an origin interval gives agreement of the derivatives, including
zero derivative for the perturbation. -/
theorem origin_deriv_eq_of_eq_on_ball {f g : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (heq : ∀ x, |x| < r → g x = f x) :
    g =ᶠ[𝓝 0] f ∧ deriv g 0 = deriv f 0 ∧
      deriv (fun x ↦ g x - f x) 0 = 0 := by
  have hlocal : g =ᶠ[𝓝 0] f := by
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with x hx
    exact heq x (abs_lt.mpr hx)
  refine ⟨hlocal, hlocal.deriv_eq, ?_⟩
  have hzero : (fun x ↦ g x - f x) =ᶠ[𝓝 0] (fun _ ↦ 0) := by
    filter_upwards [hlocal] with x hx
    exact sub_eq_zero.mpr hx
  rw [hzero.deriv_eq, deriv_const]

end PDE.Analysis.Calculus
