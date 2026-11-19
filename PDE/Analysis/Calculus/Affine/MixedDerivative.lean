/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Affine.IteratedDerivative
public import PDE.Analysis.Calculus.SpaceTime.MixedDerivative

/-!
# Mixed derivatives under independent affine dilations

The multilinear chain rule retains the two scales separately. In particular,
parabolic dilation gives one spatial weight and two temporal weights, without
estimating by the norm of the entire block map.
-/

@[expose] public section

open Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- The mixed derivative of an affine pullback is bounded by the joint jet
times the exact spatial and temporal scale factors. Neither scale needs to
be nonzero, and the spatial space may be trivial. -/
theorem norm_spaceTimeMixedFDerivWithin_comp_prod_affine_le
    (k l : ℕ) {f : E × ℝ → F} (hf : ContDiff ℝ ∞ f)
    (x : E) (t r s : ℝ) (p : E × ℝ) :
    ‖spaceTimeMixedFDerivWithin k l
      (fun q : E × ℝ ↦ f (r • (q.1 - x), s * (q.2 - t))) univ p‖ ≤
      (|s| ^ l * |r| ^ k) *
        ‖iteratedFDeriv ℝ (l + k) f (r • (p.1 - x), s * (p.2 - t))‖ := by
  let L : E × ℝ →L[ℝ] E × ℝ :=
    (r • ContinuousLinearMap.id ℝ E).prodMap (s • ContinuousLinearMap.id ℝ ℝ)
  let g : E × ℝ →ᴬ[ℝ] E × ℝ :=
    ContinuousAffineMap.const ℝ (E × ℝ) (-(r • x), -(s * t)) + L.toContinuousAffineMap
  have hg (q : E × ℝ) : g q = (r • (q.1 - x), s * (q.2 - t)) := by
    change (-(r • x) + r • q.1, -(s * t) + s * q.2) = _
    rw [smul_sub, mul_sub]
    simp only [sub_eq_add_neg, add_comm]
  have hL : g.contLinear = L := by simp [g]
  have hjet :
      iteratedFDerivWithin ℝ (l + k)
          (fun q : E × ℝ ↦ f (r • (q.1 - x), s * (q.2 - t))) univ p =
        (iteratedFDeriv ℝ (l + k) f (g p)).compContinuousLinearMap (fun _ ↦ L) := by
    simpa only [preimage_univ, iteratedFDerivWithin_univ, hL, Function.comp_def, hg] using
      g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ
        uniqueDiffOn_univ (mem_univ (g p)) (show (l + k : ℕ) ≤ (∞ : ℕ∞ω) by simp)
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  rw [spaceTimeMixedFDerivWithin_apply, hjet,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hargs :
      (fun i ↦ L (Fin.append (fun _ : Fin l ↦ (0, 1))
        (fun i : Fin k ↦ (v i, 0)) i)) =
      Fin.append (fun _ : Fin l ↦ (0, s)) (fun i : Fin k ↦ (r • v i, 0)) := by
    funext i
    cases i using Fin.addCases <;> simp [L]
  rw [hargs]
  calc
    _ ≤ ‖iteratedFDeriv ℝ (l + k) f (g p)‖ *
        ∏ i, ‖Fin.append (fun _ : Fin l ↦ (0, s))
          (fun i : Fin k ↦ (r • v i, 0)) i‖ :=
      (iteratedFDeriv ℝ (l + k) f (g p)).le_opNorm _
    _ = _ := by
      have hn (y : E) : max (|r| * ‖y‖) 0 = |r| * ‖y‖ :=
        max_eq_left (mul_nonneg (abs_nonneg r) (norm_nonneg y))
      simp [Fin.prod_univ_add, Prod.norm_def, norm_smul, Finset.prod_mul_distrib,
        hn, hg, mul_comm, mul_left_comm, mul_assoc]

end PDE
