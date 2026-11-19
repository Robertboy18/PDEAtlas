/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Continuous fields of line derivatives

A continuous field of bounded linear maps representing every line derivative
is the strict Fréchet derivative. The mean-value estimate along affine segments
works in arbitrary real normed spaces.
-/

@[expose] public section

open Asymptotics Filter Metric Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A line derivative at a point of an affine line differentiates that line
at its corresponding parameter. -/
theorem HasLineDerivAt.hasDerivAt_affineLine
    {f : E → F} {f' : F} {x v : E} {t : ℝ}
    (h : HasLineDerivAt ℝ f f' (x + t • v) v) :
    HasDerivAt (fun s : ℝ ↦ f (x + s • v)) f' t := by
  have hh : HasDerivAt (fun r : ℝ ↦ f (x + t • v + r • v)) f' (t - t) := by
    simpa only [sub_self, HasLineDerivAt] using h
  have hs := hh.comp_sub_const t t
  convert hs using 1
  ext s
  congr 1
  simp only [sub_smul]
  abel

namespace PDE

/-- A continuous field of bounded linear maps giving all line derivatives is
the strict Fréchet derivative, with no finite-dimensional assumption. -/
theorem hasStrictFDerivAt_of_hasLineDerivAt_of_continuousAt
    {f : E → F} {D : E → E →L[ℝ] F} {x : E}
    (hline : ∀ y v, HasLineDerivAt ℝ f (D y v) y v)
    (hD : ContinuousAt D x) :
    HasStrictFDerivAt f (D x) x := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  apply Metric.eventually_nhds_iff_ball.mpr
  obtain ⟨r, hr, hDr⟩ := Metric.mem_nhds_iff.mp (hD (ball_mem_nhds _ hc))
  refine ⟨r, hr, ?_⟩
  rintro ⟨a, b⟩ hab
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at hab
  let v := a - b
  let q : ℝ → F := fun t ↦ f (b + t • v) - t • D x v
  let q' : ℝ → F := fun t ↦ (D (b + t • v) - D x) v
  have hq : ∀ t, HasDerivAt q (q' t) t := by
    intro t
    simpa only [q, q', sub_apply, Pi.sub_def, one_smul, id_eq] using
      (hline (b + t • v) v).hasDerivAt_affineLine.sub
        ((hasDerivAt_id t).smul_const (D x v))
  have hq' : ∀ t ∈ Icc (0 : ℝ) 1, ‖q' t‖ ≤ c * ‖v‖ := by
    intro t ht
    have hmem := (convex_ball x r).add_smul_sub_mem hab.2 hab.1 ht
    have hd : ‖D (b + t • v) - D x‖ ≤ c := by
      rw [← dist_eq_norm]
      exact (show dist (D (b + t • v)) (D x) < c from hDr hmem).le
    exact (D (b + t • v) - D x).le_opNorm v |>.trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg v))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ ↦ (hq t).hasDerivWithinAt) hq' (convex_Icc (0 : ℝ) 1)
    (by simp : (0 : ℝ) ∈ Icc 0 1) (by simp : (1 : ℝ) ∈ Icc 0 1)
  simpa [q, v, sub_right_comm] using h

end PDE
