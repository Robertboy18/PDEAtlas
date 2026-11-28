/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Ladyzhenskaya.WholeSpace
public import PDE.Spaces.Sobolev.Calculus.IsolatedPoint.Membership
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus

/-!
# `|x| g` is in `L⁴(ℝ³)` when `g`, `|x| g` and `|x| ∇g` are square integrable

If a `C¹` function `g` on `ℝ³` is square integrable, and so are `|x| g` and `|x| ∇g`, then
`|x| g` lies in `L⁴`. Hou, Wang and Yang need this for the derivatives of their near-field
profile, where they bound `‖ |ξ|² g² ‖_{L²}` by the Gagliardo–Nirenberg inequality. Only the
membership is stated here. The inequality with its constant,
`‖f‖₄² ≤ C ‖f‖₂^{1/2} ‖∇f‖₂^{3/2}` for `f = |x| g`, is not.

## Main results

* `SobolevSpace.Inequalities.memLp_four_norm_mul`: `|x| g ∈ L⁴` for every real `C¹` function `g`
  on `ℝ³` with `g`, `|x| g` and `|x| ∇g` in `L²`.
* `SobolevSpace.Inequalities.memLp_four_norm_smul`: the same for `C¹` vector fields on `ℝ³`,
  component by component.

## How it works

`f = |x| g` is `C¹` away from the origin, and `∇f = (x/|x|) g + |x| ∇g` there, so
`|∇f| ≤ |g| + |x| |∇g|`. Hence `f` and its classical gradient are square integrable. A point is
removable for `W^{1,2}` (`SobolevSpace.exists_wkpSpace_of_contDiffAt_off_zero`), so `f` is an
element of `H¹(ℝ³)`, and `H¹(ℝ³) ⊂ L⁴(ℝ³)` by Ladyzhenskaya's inequality (`memLp_four_H1`).

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, the bound before
  (2.21). <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace.GraphSpace
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Inequalities

/-- **`|x| g ∈ L⁴(ℝ³)`** for a real `C¹` function `g` with `g`, `|x| g` and `|x| ∇g` square
integrable: `|x| g` is an element of `H¹(ℝ³)`, because a point is removable, and
`H¹(ℝ³) ⊂ L⁴(ℝ³)`. -/
theorem memLp_four_norm_mul {g : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g) (h0 : MemLp g 2 volume)
    (h1 : MemLp (fun x ↦ ‖x‖ * g x) 2 volume)
    (h2 : MemLp (fun x ↦ ‖x‖ • fderiv ℝ g x) 2 volume) :
    MemLp (fun x ↦ ‖x‖ * g x) 4 volume := by
  have hf : ∀ x : ℝ^3, x ≠ 0 → ContDiffAt ℝ 1 (fun y ↦ ‖y‖ * g y) x := fun x hx ↦
    (contDiffAt_norm ℝ hx).mul hg.contDiffAt
  -- Away from the origin, `|∇(|x| g)| ≤ |x| |∇g| + |g|`.
  have hD : ∀ x : ℝ^3, x ≠ 0 → ‖fderiv ℝ (fun y ↦ ‖y‖ * g y) x‖ ≤
      ‖‖x‖ • fderiv ℝ g x‖ + ‖g x‖ := fun x hx ↦ by
    have hn : DifferentiableAt ℝ (fun y : ℝ^3 ↦ ‖y‖) x :=
      (contDiffAt_norm ℝ hx).differentiableAt one_ne_zero
    have hgd : DifferentiableAt ℝ g x := hg.differentiable one_ne_zero x
    have hlip : ‖fderiv ℝ (fun y : ℝ^3 ↦ ‖y‖) x‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := ℝ^3)) (x₀ := x)
    rw [fderiv_fun_mul hn hgd]
    calc ‖‖x‖ • fderiv ℝ g x + g x • fderiv ℝ (fun y : ℝ^3 ↦ ‖y‖) x‖
        ≤ ‖‖x‖ • fderiv ℝ g x‖ + ‖g x • fderiv ℝ (fun y : ℝ^3 ↦ ‖y‖) x‖ := norm_add_le _ _
      _ ≤ ‖‖x‖ • fderiv ℝ g x‖ + ‖g x‖ := by
          rw [norm_smul (g x)]
          nlinarith [norm_nonneg (g x), norm_nonneg (fderiv ℝ (fun y : ℝ^3 ↦ ‖y‖) x)]
  have hgp : ∀ i : Fin 3, MemLp (PDE.partialDeriv i fun y : ℝ^3 ↦ ‖y‖ * g y) 2 volume :=
    fun i ↦ by
      have hmeas : AEStronglyMeasurable (PDE.partialDeriv i fun y : ℝ^3 ↦ ‖y‖ * g y) volume :=
        (measurable_fderiv_apply_const ℝ (fun y : ℝ^3 ↦ ‖y‖ * g y)
          (EuclideanSpace.single i (1 : ℝ))).aestronglyMeasurable
      have hsum : MemLp (fun x : ℝ^3 ↦ ‖‖x‖ • fderiv ℝ g x‖ + ‖g x‖) 2 volume :=
        h2.norm.add h0.norm
      refine hsum.mono' hmeas ?_
      filter_upwards [(volume : Measure (ℝ^3)).ae_ne 0] with x hx
      exact (PDE.norm_partialDeriv_le_norm_fderiv i _ x).trans (hD x hx)
  obtain ⟨U, hU, -⟩ := exists_wkpSpace_of_contDiffAt_off_zero (n := 2) (p := 2) hf h1 hgp
  exact (memLp_four_H1 U).ae_eq hU

/-- **`|x| v ∈ L⁴(ℝ³)`** for a `C¹` vector field `v` with `v`, `|x| v` and `|x| ∇v` square
integrable. This is `memLp_four_norm_mul` for each component. -/
theorem memLp_four_norm_smul {v : ℝ^3 → ℝ^3} (hv : ContDiff ℝ 1 v) (h0 : MemLp v 2 volume)
    (h1 : MemLp (fun x ↦ ‖x‖ • v x) 2 volume)
    (h2 : MemLp (fun x ↦ ‖x‖ • fderiv ℝ v x) 2 volume) :
    MemLp (fun x ↦ ‖x‖ • v x) 4 volume := by
  refine MemLp.of_eval_piLp fun i ↦ ?_
  have hgi : ContDiff ℝ 1 (fun x ↦ v x i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv
  have hD : ∀ x, fderiv ℝ (fun y ↦ v y i) x = (EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (fderiv ℝ v x) := fun x ↦
    ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
      (hv.differentiable one_ne_zero x).hasFDerivAt).fderiv
  have hc : Continuous fun x ↦ ‖x‖ • fderiv ℝ (fun y ↦ v y i) x :=
    continuous_norm.smul (hgi.continuous_fderiv one_ne_zero)
  have h2i : MemLp (fun x ↦ ‖x‖ • fderiv ℝ (fun y ↦ v y i) x) 2 volume := by
    refine h2.of_le hc.aestronglyMeasurable (.of_forall fun x ↦ ?_)
    rw [norm_smul, norm_smul, hD x]
    refine mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_) (norm_nonneg _)
    exact (PiLp.norm_apply_le (fderiv ℝ v x y) i).trans ((fderiv ℝ v x).le_opNorm y)
  exact memLp_four_norm_mul hgi (h0.eval_piLp i) (h1.eval_piLp i) h2i

end SobolevSpace.Inequalities
