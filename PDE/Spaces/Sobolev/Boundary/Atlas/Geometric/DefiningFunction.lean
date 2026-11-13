/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Regular C1 defining functions and inward translations

`HasC1Boundary` describes a C1 boundary by local defining functions with nonzero derivative.
The shared graph predicate supplies these functions by subtracting the graph height
from the normal coordinate.

Strict differentiability controls the difference between two nearby points uniformly.
Choosing a direction on which the derivative is positive then gives room for a ball
of radius `ε` after translating inward by `ε v`. This is the geometric step in
Evans §5.3.3 and uses no higher derivatives of the boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.1, pp. 710-711, for `C^k` boundaries as local graphs,
  and §5.3.3, Theorem 3, pp. 266-268, whose proof translates inward in each boundary chart.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SobolevSpace.Boundary

variable {n : ℕ}

/-- A C¹ boundary, described locally as the positive side of a regular C¹ level set.
The defining functions are required to be C¹ only near their respective boundary points. -/
def HasC1Boundary (Ω : Set (ℝ^n)) : Prop :=
  ∀ x ∈ frontier Ω, ∃ f : ℝ^n → ℝ,
    ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      ∀ᶠ y in 𝓝 x, (y ∈ Ω ↔ 0 < f y)

/-- The local graph description of a C¹ boundary supplies regular defining functions.
The coordinate change may be any continuous linear equivalence, so orthogonal changes
of coordinates in Evans's definition (App. C.1) are included. -/
theorem hasC1Boundary_of_local_graph {Ω : Set (ℝ^n)}
    (hgraph : HasC1GraphBoundary Ω) :
    HasC1Boundary Ω := by
  intro x hx
  obtain ⟨e, γ, hγ, heq, hside⟩ := hgraph x hx
  let f (y : ℝ^n) := (e y).2 - γ (e y).1
  have hf : ContDiffAt ℝ 1 f x :=
    e.contDiff.contDiffAt.snd.sub (hγ.comp x e.contDiff.contDiffAt.fst)
  have hdf := e.hasFDerivAt.snd.sub
    ((hγ.differentiableAt one_ne_zero).hasFDerivAt.comp x e.hasFDerivAt.fst)
  refine ⟨f, hf, sub_eq_zero.mpr heq, ?_, ?_⟩
  · intro hzero
    have hz := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (e.symm (0, 1)))
      (hdf.fderiv.symm.trans hzero)
    change (e (e.symm (0, 1))).2 -
      fderiv ℝ γ (e x).1 (e (e.symm (0, 1))).1 = 0 at hz
    simp only [e.apply_symm_apply, map_zero, sub_zero, one_ne_zero] at hz
  · filter_upwards [hside] with y hy
    exact hy.trans sub_pos.symm

/-- A regular strictly differentiable defining function gives a uniform inward
translation on a neighborhood of the point. -/
theorem exists_inward_ball_of_hasStrictFDerivAt
    {Ω : Set (ℝ^n)} {x : ℝ^n} {f : ℝ^n → ℝ} {L : ℝ^n →L[ℝ] ℝ}
    (hf : HasStrictFDerivAt f L x) (hL : L ≠ 0)
    (hΩ : ∀ᶠ y in 𝓝 x, (y ∈ Ω ↔ 0 < f y)) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ x ∈ V ∧
      ∃ v : ℝ^n, ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∀ z ∈ V ∩ Ω,
        closedBall (z + ε • v) ε ⊆ Ω := by
  obtain ⟨u, hu⟩ : ∃ u, L u ≠ 0 := by
    by_contra! h
    exact hL (ContinuousLinearMap.ext h)
  let v := ((‖L‖ + 2) / L u) • u
  have hv : L v = ‖L‖ + 2 := by
    simp only [v, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu]
  have hvpos : 0 < ‖v‖ + 1 := by positivity
  have hc : 0 < (‖v‖ + 1)⁻¹ := inv_pos.mpr hvpos
  obtain ⟨S, hSo, hxS, hS⟩ := exists_nhds_square (hf.isLittleO.bound hc)
  obtain ⟨r, hr, hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem (hSo.mem_nhds hxS) hΩ)
  refine ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
    v, r / (2 * (‖v‖ + 1)), div_pos hr (by positivity), ?_⟩
  intro ε hε z hz y hy
  have hzsmall : dist z x < r / 2 := hz.1
  have hzbig : z ∈ ball x r := by
    change dist z x < r
    linarith
  have hyz : ‖y - z‖ ≤ ε * (‖v‖ + 1) := by
    have hn := norm_add_le (y - (z + ε • v)) (ε • v)
    have heq : y - (z + ε • v) + ε • v = y - z := by abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1] at hn
    have hball : ‖y - (z + ε • v)‖ ≤ ε := hy
    nlinarith
  have hεsmall : ε * (‖v‖ + 1) < r / 2 := by
    have := (lt_div_iff₀ (show 0 < 2 * (‖v‖ + 1) by positivity)).mp hε.2
    linarith
  have hybig : y ∈ ball x r := by
    have := dist_triangle y z x
    rw [dist_eq_norm y z] at this
    change dist y x < r
    linarith
  have herr : |f y - f z - L (y - z)| ≤ ε := by
    have h := hS (mk_mem_prod (hrS hybig).1 (hrS hzbig).1)
    change ‖f y - f z - L (y - z)‖ ≤ (‖v‖ + 1)⁻¹ * ‖y - z‖ at h
    have hb := mul_le_mul_of_nonneg_left hyz hc.le
    have heq : (‖v‖ + 1)⁻¹ * (ε * (‖v‖ + 1)) = ε := by
      rw [mul_left_comm, inv_mul_cancel₀ hvpos.ne', mul_one]
    rw [heq] at hb
    exact h.trans hb
  have hnoise : -(‖L‖ * ε) ≤ L (y - (z + ε • v)) := by
    have h := L.le_opNorm (y - (z + ε • v))
    have hb : ‖y - (z + ε • v)‖ ≤ ε := hy
    have hab : |L (y - (z + ε • v))| ≤ ‖L‖ * ε :=
      h.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    exact (abs_le.mp hab).1
  have hlin : L (y - z) = L (y - (z + ε • v)) + ε * (‖L‖ + 2) := by
    rw [← hv, ← smul_eq_mul, ← map_smul, ← map_add]
    congr 1
    abel
  apply (hrS hybig).2.mpr
  have hzpos := (hrS hzbig).2.mp hz.2
  have hlow := (abs_le.mp herr).1
  nlinarith [hε.1]

/-- Near each point of a C¹ boundary there is a fixed direction that allows
interior mollification after a sufficiently small translation. -/
theorem HasC1Boundary.exists_inward_ball {Ω : Set (ℝ^n)}
    (hΩ : HasC1Boundary Ω) {x : ℝ^n} (hx : x ∈ frontier Ω) :
    ∃ V : Set (ℝ^n), IsOpen V ∧ x ∈ V ∧
      ∃ v : ℝ^n, ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∀ z ∈ V ∩ Ω,
        closedBall (z + ε • v) ε ⊆ Ω := by
  obtain ⟨f, hf, _, hdf, hside⟩ := hΩ x hx
  exact exists_inward_ball_of_hasStrictFDerivAt (hf.hasStrictFDerivAt one_ne_zero) hdf hside

end SobolevSpace.Boundary
