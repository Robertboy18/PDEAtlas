/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AveragedFDeriv
public import PDE.Analysis.Calculus.SecondDifference.Local

/-!
# Midpoint asymptotics for functions of averaged derivatives

At a collapsed segment, a differentiable scalar function of the averaged derivative
has half the derivative of its diagonal restriction. With one more derivative,
its difference from the arithmetic mean of the two diagonal values is quadratic
in the displacement. All regularity assumptions concern germs.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter
open scoped Topology

universe u v

variable {X : Type u} {Y : Type (max u v)} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The half-derivative identity requires only a `C²` germ of the original map. -/
theorem hasFDerivAt_comp_averagedFDeriv_self_of_contDiffAt
    {f : X → Y} {a : (X →L[ℝ] Y) → ℝ} {x₀ : X}
    (hf : ContDiffAt ℝ 2 f x₀) (ha : DifferentiableAt ℝ a (fderiv ℝ f x₀)) :
    HasFDerivAt (fun x ↦ a (averagedFDeriv f x₀ x))
      ((1 / 2 : ℝ) • fderiv ℝ (fun x ↦ a (fderiv ℝ f x)) x₀) x₀ := by
  obtain ⟨g, hg, _hcompact, heq⟩ :=
    hf.exists_contDiff_compactSupport_eventuallyEq
  have hD : fderiv ℝ f =ᶠ[𝓝 x₀] fderiv ℝ g := heq.fderiv
  have ha' : DifferentiableAt ℝ a (fderiv ℝ g x₀) := by
    rw [← hD.self_of_nhds]
    exact ha
  have hdiag : (fun x ↦ a (fderiv ℝ f x)) =ᶠ[𝓝 x₀] fun x ↦ a (fderiv ℝ g x) :=
    hD.fun_comp a
  have havg : (fun x ↦ a (averagedFDeriv f x₀ x)) =ᶠ[𝓝 x₀]
      fun x ↦ a (averagedFDeriv g x₀ x) :=
    (averagedFDeriv_eventuallyEq_of_eventuallyEq heq).fun_comp a
  rw [hdiag.fderiv_eq]
  exact (hasFDerivAt_comp_averagedFDeriv_self hg ha').congr_of_eventuallyEq havg

private theorem exists_abs_comp_averagedFDeriv_sub_mean_le_global
    {f : X → Y} {a : (X →L[ℝ] Y) → ℝ} {x₀ : X}
    (hf : ContDiff ℝ 3 f) (ha : ContDiffAt ℝ 2 a (fderiv ℝ f x₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀,
      |a (averagedFDeriv f x₀ x) - (a (fderiv ℝ f x) + a (fderiv ℝ f x₀)) / 2|
        ≤ C * ‖x - x₀‖ ^ 2 := by
  let d : X → ℝ := fun x ↦ a (fderiv ℝ f x)
  let H : X → ℝ := fun x ↦ a (averagedFDeriv f x₀ x) - (1 / 2 : ℝ) • (d x + d x₀)
  have hD : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd : ContDiffAt ℝ 2 d x₀ := ha.comp x₀ hD.contDiffAt
  have havg : ContDiff ℝ 2 (averagedFDeriv f x₀) :=
    contDiff_averagedFDeriv (n := 2) hf x₀
  have ha' : ContDiffAt ℝ 2 a (averagedFDeriv f x₀ x₀) := by simpa using ha
  have hH : ContDiffAt ℝ 2 H x₀ :=
    (ha'.comp x₀ havg.contDiffAt).sub ((hd.add contDiffAt_const).const_smul (1 / 2 : ℝ))
  have hhalf := hasFDerivAt_comp_averagedFDeriv_self
    (hf.of_le (by norm_num)) (ha.differentiableAt (by norm_num))
  have hmid := ((hd.differentiableAt (by norm_num)).hasFDerivAt.add_const (d x₀)).const_smul
    (1 / 2 : ℝ)
  have hzero : fderiv ℝ H x₀ = 0 := by
    simpa only [H, d, Pi.sub_def, Pi.smul_def, sub_self] using (hhalf.sub hmid).fderiv
  have hvalue : H x₀ = 0 := by simp [H, d]; ring
  obtain ⟨C, hC, hbound⟩ := hH.exists_norm_sub_sub_fderiv_le_mul_sq
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with x hx
  change ‖H x - H x₀ - fderiv ℝ H x₀ (x - x₀)‖ ≤ _ at hx
  rw [hvalue, hzero, zero_apply, sub_zero, sub_zero] at hx
  simpa only [
    H, d, smul_eq_mul, one_div, inv_mul_eq_div, Real.norm_eq_abs] using hx

/-- A `C³` germ and a `C²` scalar function on the derivative space give the
quadratic midpoint estimate. The bound uses the norm of the state displacement,
and its constant is obtained from local regularity rather than assumed. -/
theorem exists_abs_comp_averagedFDeriv_sub_mean_le
    {f : X → Y} {a : (X →L[ℝ] Y) → ℝ} {x₀ : X}
    (hf : ContDiffAt ℝ 3 f x₀) (ha : ContDiffAt ℝ 2 a (fderiv ℝ f x₀)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x in 𝓝 x₀,
      |a (averagedFDeriv f x₀ x) - (a (fderiv ℝ f x) + a (fderiv ℝ f x₀)) / 2|
        ≤ C * ‖x - x₀‖ ^ 2 := by
  obtain ⟨g, hg, _hcompact, heq⟩ :=
    hf.exists_contDiff_compactSupport_eventuallyEq
  have hD : fderiv ℝ f =ᶠ[𝓝 x₀] fderiv ℝ g := heq.fderiv
  have ha' : ContDiffAt ℝ 2 a (fderiv ℝ g x₀) := by
    rw [← hD.self_of_nhds]
    exact ha
  obtain ⟨C, hC, hbound⟩ := exists_abs_comp_averagedFDeriv_sub_mean_le_global hg ha'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hD, averagedFDeriv_eventuallyEq_of_eventuallyEq heq]
    with x hx hxD hxavg
  simpa only [hxD, hxavg, hD.self_of_nhds] using hx

end PDE.Analysis
