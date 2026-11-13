/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Sobolev
public import PDE.Elliptic.Variational.Supersolution.SobolevTruncation
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Cone

/-!
# Truncated weak barriers at C¹ boundary points

The intrinsic normal puts nearby domain points in a slightly enlarged inward
half-space. The angular barrier is superharmonic there. Its positive radial
lower bound ensures that a sufficiently small sublevel lies entirely in that
neighbourhood. Truncation at this level therefore produces a global
`H¹` weak supersolution without imposing curvature or an exterior-ball condition.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Elliptic.BoundaryContinuity

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Trace.C1
open scoped ENNReal Topology InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
    [hΩ : SobolevSpace.Boundary.C1ExtensionAtlas n Ω]

/-- At a C¹ boundary point a positive sublevel of the explicit angular barrier
is contained in its region of classical superharmonicity. -/
theorem exists_superharmonic_angularPowerBarrier_sublevel
    (hn : 2 ≤ n) (z : frontier Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Ω,
      angularPowerBarrier (1 / (32 * (n : ℝ))) (-outwardUnitNormal (Ω := Ω) z) (x - z) < c →
      laplacian (fun y : ℝ^n ↦ angularPowerBarrier (1 / (32 * (n : ℝ)))
        (-outwardUnitNormal (Ω := Ω) z) (y - (z : ℝ^n))) x ≤ 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let a : ℝ := 1 / (32 * (n : ℝ))
  let N : ℝ^n := -outwardUnitNormal (Ω := Ω) z
  have ha : 0 < a := by dsimp [a]; positivity
  have hN : ‖N‖ = 1 := by simp only [N, norm_neg, norm_outwardUnitNormal]
  obtain ⟨r, hr, hcone⟩ := Metric.eventually_nhds_iff.mp
    (eventually_neg_normal_inner_ge (Ω := Ω) z
      (show (0 : ℝ) < 1 / (8 * (n : ℝ)) by positivity))
  refine ⟨(3 / 4) * r ^ a, mul_pos (by norm_num) (Real.rpow_pos_of_pos hr a), ?_⟩
  intro x hx hsub
  have hz : (z : ℝ^n) ∉ Ω := by
    intro hzΩ
    exact (mem_interior_iff_notMem_frontier hzΩ).mp
      (by simpa only [hΩ.isOpen.interior_eq] using hzΩ) z.property
  have hne : x - (z : ℝ^n) ≠ 0 := by
    intro heq
    exact hz (sub_eq_zero.mp heq ▸ hx)
  have hnear : ‖x - (z : ℝ^n)‖ < r := by
    by_contra h
    have hpow := Real.rpow_le_rpow hr.le (le_of_not_gt h) ha.le
    have hb := (angularPowerBarrier_bounds a hN hne).1
    have := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3 / 4)
    exact (not_lt_of_ge (this.trans hb)) hsub
  rw [laplacian_comp_sub_right _ _ _ (angularPowerBarrier_contDiffAt a N hne)]
  exact (laplacian_angularPowerBarrier_le hn hN hne
    (hcone (by simpa only [dist_eq_norm] using hnear) hx)).trans
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

/-- The explicit C¹ boundary barrier, truncated at a derived positive level,
is an `H¹` weak supersolution against every nonnegative `H¹₀` test. -/
theorem exists_truncated_angularPowerBarrier
    (hn : 2 ≤ n) (hbounded : Bornology.IsBounded Ω) (z : frontier Ω) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : W^{1,2}(Ω),
      (B.val (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        (fun x ↦ min c (angularPowerBarrier (1 / (32 * (n : ℝ)))
          (-outwardUnitNormal (Ω := Ω) z) (x - z))) ∧
      ∀ t : H¹₀(Ω),
        (∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x) →
        0 ≤ ∑ i : Fin n,
          inner ℝ (wkpCoordinateCLM (singleDerivIndex n i) B) (derivCoordCLM i t) := by
  let a : ℝ := 1 / (32 * (n : ℝ))
  let N : ℝ^n := -outwardUnitNormal (Ω := Ω) z
  let b : ℝ^n → ℝ := fun x ↦ angularPowerBarrier a N (x - z)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one (by positivity)]
    linarith
  have hN : ‖N‖ = 1 := by simp only [N, norm_neg, norm_outwardUnitNormal]
  have hz : (z : ℝ^n) ∉ Ω := by
    intro hzΩ
    exact (mem_interior_iff_notMem_frontier hzΩ).mp
      (by simpa only [hΩ.isOpen.interior_eq] using hzΩ) z.property
  have hne (x : ℝ^n) (hx : x ∈ Ω) : x - (z : ℝ^n) ≠ 0 := by
    intro heq
    exact hz (sub_eq_zero.mp heq ▸ hx)
  have hb0 (x : ℝ^n) (hx : x ∈ Ω) : 0 < b x :=
    (mul_pos (by norm_num) (Real.rpow_pos_of_pos (norm_pos_iff.mpr (hne x hx)) a)).trans_le
      (angularPowerBarrier_bounds a hN (hne x hx)).1
  have hb (x : ℝ^n) (hx : x ∈ Ω) : ContDiffAt ℝ 2 b x :=
    (angularPowerBarrier_contDiffAt a N (hne x hx)).comp x
      (contDiffAt_id.sub contDiffAt_const)
  obtain ⟨c, hc, hΔ⟩ := exists_superharmonic_angularPowerBarrier_sublevel hn z
  obtain ⟨U, hU, hdU⟩ := exists_angularPowerBarrier_h1 hn hΩ.isOpen hbounded ha ha1 hN hz
  let B := intervalTruncationOn (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hc.le U
  refine ⟨c, hc, B, ?_, ?_⟩
  · filter_upwards [intervalTruncationOn_base_ae (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hc.le U,
      hU, self_mem_ae_restrict hΩ.isOpen.measurableSet] with x hx hu hxΩ
    have hbx : 0 ≤ angularPowerBarrier a N (x - (z : ℝ^n)) := (hb0 x hxΩ).le
    simpa only [hu, PDE.Analysis.Calculus.intervalTruncation_eq_min_max hc.le,
      max_eq_right hbx] using hx
  · intro t ht
    exact intervalTruncationOn_dirichlet_nonneg U hU hdU hb hb0 hc.le hΔ t ht

end PDE.Elliptic.BoundaryContinuity
