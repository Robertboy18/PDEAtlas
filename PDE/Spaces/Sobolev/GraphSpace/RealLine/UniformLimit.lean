/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.WeakProductBound

/-!
# Uniform limits of `H¹` functions on the line

On the real line an `H¹` function obeys `|U(x)|² ≤ ‖U‖₂ ‖U‖_{H¹}`. Strong `L²` convergence
of a family whose distances to the limit stay bounded in `H¹` is therefore uniform
convergence of the continuous representatives on the whole line; no convergence of the
derivatives is needed.

## Main results

* `sq_realLineRepresentative_le`: `|U(x)|² ≤ ‖U‖₂ ‖U‖_{H¹}`.
* `tendstoUniformly_realLineRepresentative`: `L²` convergence with eventually bounded `H¹`
  distances is uniform convergence.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev ENNReal

namespace SobolevSpace.GraphSpace

/-- The one-dimensional interpolation inequality `|U(x)|² ≤ ‖U‖₂ ‖U‖_{H¹}` for the
continuous representative of an `H¹` graph. -/
theorem sq_realLineRepresentative_le (U : W^{1,2}(ℝ^1)) (x : ℝ) :
    realLineRepresentative U x ^ 2 ≤
      (eLpNorm (realLineRepresentative U) 2 volume).toReal * ‖U‖ := by
  have h := (hasWeakTimeDerivativeOn_realLineRepresentative U).sq_apply_le_l2_mul_l2
    (continuous_realLineRepresentative U) (memLp_realLineRepresentative U)
    (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) U)) x
  rw [← Lp.norm_def] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_realLineCoordinateCLM_le _ U)
    ENNReal.toReal_nonneg)

/-- Strong `L²` convergence of continuous representatives, with an eventual `H¹` bound
on the distances to the limit, is uniform convergence on the whole line. -/
theorem tendstoUniformly_realLineRepresentative {ι : Type*} {l : Filter ι}
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {B : ℝ}
    (hbound : ∀ᶠ i in l, ‖u i - U‖ ≤ B)
    (hL2 : Tendsto (fun i ↦ eLpNorm
      (fun x ↦ realLineRepresentative (u i) x - realLineRepresentative U x) 2 volume)
      l (𝓝 0)) :
    TendstoUniformly (fun i ↦ realLineRepresentative (u i)) (realLineRepresentative U) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  set C : ℝ := max B 1 with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL2
  rw [ENNReal.toReal_zero] at hreal
  filter_upwards [hbound, hreal.eventually (gt_mem_nhds (div_pos (pow_pos hε 2) hCpos))]
    with i hi hs x
  have hsq := sq_realLineRepresentative_le (u i - U) x
  rw [realLineRepresentative_sub] at hsq
  have hle : (eLpNorm (realLineRepresentative (u i) - realLineRepresentative U) 2
      volume).toReal * ‖u i - U‖ < ε ^ 2 := by
    calc
      _ ≤ (eLpNorm (realLineRepresentative (u i) - realLineRepresentative U) 2
          volume).toReal * C :=
        mul_le_mul_of_nonneg_left (hi.trans (le_max_left _ _)) ENNReal.toReal_nonneg
      _ < ε ^ 2 / C * C := mul_lt_mul_of_pos_right hs hCpos
      _ = ε ^ 2 := div_mul_cancel₀ _ hCpos.ne'
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_lt_of_sq_lt_sq' (hsq.trans_lt hle) hε.le |>.elim
    (fun h1 h2 ↦ abs_lt.mpr ⟨h1, h2⟩)

end SobolevSpace.GraphSpace
