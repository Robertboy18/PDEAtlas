/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Local second coordinate rules for sums and products

The first derivative rules hold on a neighborhood supplied by local `C²` regularity.
-/

@[expose] public section

open scoped Topology

namespace PDE

/-- The second coordinate derivative distributes over sums under local `C²` assumptions. -/
theorem secondPartialDeriv_add_at {n : ℕ} {f g : ℝ^n → ℝ} {x : ℝ^n}
    (i j : Fin n) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[i] (∂[j] (fun y ↦ f y + g y))) x =
      (∂[i] (∂[j] f)) x + (∂[i] (∂[j] g)) x := by
  have heq : (∂[j] (fun y ↦ f y + g y)) =ᶠ[𝓝 x]
      fun y ↦ (∂[j] f) y + (∂[j] g) y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact partialDeriv_add (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))
  rw [partialDeriv_congr_nhds i heq,
    partialDeriv_add
      ((contDiffAt_partialDeriv 1 hf j).differentiableAt (by norm_num))
      ((contDiffAt_partialDeriv 1 hg j).differentiableAt (by norm_num))]

/-- The second coordinate product rule under local `C²` assumptions. -/
theorem secondPartialDeriv_mul_at {n : ℕ} {f g : ℝ^n → ℝ} {x : ℝ^n}
    (i j : Fin n) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    (∂[i] (∂[j] (fun y ↦ f y * g y))) x =
      (∂[i] (∂[j] f)) x * g x + (∂[j] f) x * (∂[i] g) x +
        ((∂[i] f) x * (∂[j] g) x + f x * (∂[i] (∂[j] g)) x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  have hfj := (contDiffAt_partialDeriv 1 hf j).differentiableAt (by norm_num)
  have hgj := (contDiffAt_partialDeriv 1 hg j).differentiableAt (by norm_num)
  have heq : (∂[j] (fun y ↦ f y * g y)) =ᶠ[𝓝 x]
      fun y ↦ (∂[j] f) y * g y + f y * (∂[j] g) y := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hyf hyg
    exact partialDeriv_mul (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))
  rw [partialDeriv_congr_nhds i heq,
    partialDeriv_add (hfj.fun_mul hgd) (hfd.fun_mul hgj),
    partialDeriv_mul hfj hgd, partialDeriv_mul hfd hgj]

end PDE
