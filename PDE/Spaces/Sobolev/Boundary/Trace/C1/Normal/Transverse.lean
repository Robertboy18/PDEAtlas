/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Continuity
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction

/-!
# Smooth transverse fields on bounded C¹ domains

The outward normal is continuous on the compact boundary, although it need
not be differentiable. On a sufficiently small patch, its value at the
center has positive pairing with every normal in the patch. A finite smooth
partition of unity combines these constant vectors into a smooth ambient
field. Bounded patches give compact support, hence a global derivative bound.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Set Filter
open scoped Manifold

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

private theorem exists_transverse_ball (x : frontier Ω) :
    ∃ r > 0, ∀ y : frontier Ω, (y : ℝ^n) ∈ Metric.ball (x : ℝ^n) r →
      (1 / 2 : ℝ) < inner ℝ (outwardUnitNormal x) (outwardUnitNormal y) := by
  have hc : Continuous (fun y : frontier Ω ↦
      inner ℝ (outwardUnitNormal x) (outwardUnitNormal y)) :=
    continuous_const.inner continuous_outwardUnitNormal
  have hx : (1 / 2 : ℝ) <
      inner ℝ (outwardUnitNormal x) (outwardUnitNormal x) := by
    rw [real_inner_self_eq_norm_sq, norm_outwardUnitNormal]
    norm_num
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.eventually (lt_mem_nhds hx))
  refine ⟨r, hr, fun y hy ↦ hball ?_⟩
  exact hy

/-- A bounded C¹ domain admits a compactly supported smooth ambient field
with uniform positive outward component. The field has norm at most one,
and its derivative has a derived global bound. No boundary smoothness
beyond continuity of the unit normal is used in the construction. -/
theorem exists_contDiff_transverse_outwardUnitNormal :
    ∃ X : ℝ^n → ℝ^n, ContDiff ℝ (⊤ : ℕ∞) X ∧ HasCompactSupport X ∧
      (∀ x, ‖X x‖ ≤ 1) ∧
      (∀ x : frontier Ω, (1 / 2 : ℝ) ≤ inner ℝ (X x) (outwardUnitNormal x)) ∧
      ∃ C > 0, ∀ x, ‖fderiv ℝ X x‖ ≤ C := by
  classical
  choose r hr hpair using exists_transverse_ball (Ω := Ω)
  have hcompact : IsCompact (frontier Ω) :=
    hΩ.bounded.isCompact_closure.of_isClosed_subset
      isClosed_frontier frontier_subset_closure
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover
    (fun x : frontier Ω ↦ Metric.ball (x : ℝ^n) (r x))
    (fun _ ↦ Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr _)⟩)
  let U (i : s) : Set (ℝ^n) := Metric.ball (i.val : ℝ^n) (r i.val)
  have hcover : frontier Ω ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, ℝ^n) isClosed_frontier U (fun _ ↦ Metric.isOpen_ball) hcover
  have hρcompact (i : s) : HasCompactSupport (fun x ↦ ρ i x) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (Metric.isBounded_ball.subset (hρ i))
  let X : ℝ^n → ℝ^n := fun x ↦ ∑ i : s, ρ i x • outwardUnitNormal i.val
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) X :=
    ContDiff.sum fun i _ ↦ (ρ i).contMDiff.contDiff.smul contDiff_const
  have hsupp : HasCompactSupport X := by
    convert
      HasCompactSupport.finset_sum (s := Finset.univ)
        (fun i _ ↦ (hρcompact i).smul_right
          (f' := fun _ ↦ outwardUnitNormal i.val)) using 1
    ext x
    simp [X]
  refine ⟨X, hsmooth, hsupp, ?_, ?_, ?_⟩
  · intro x
    calc
      ‖X x‖ ≤ ∑ i : s, ‖ρ i x • outwardUnitNormal i.val‖ :=
        norm_sum_le _ _
      _ = ∑ i : s, ρ i x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, norm_outwardUnitNormal, mul_one,
          Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
      _ ≤ 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x
  · intro x
    have hsum : ∑ i : s, ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one x.property
    calc
      (1 / 2 : ℝ) = ∑ i : s, ρ i x * (1 / 2) := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ i : s, ρ i x *
          inner ℝ (outwardUnitNormal i.val) (outwardUnitNormal x) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : ρ i x = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_left
            (hpair i.val x (hρ i (subset_tsupport _ (Function.mem_support.mpr hi)))).le
            (ρ.nonneg i x)
      _ = inner ℝ (X x) (outwardUnitNormal x) := by
        simp only [X, sum_inner, real_inner_smul_left]
  · obtain ⟨C, hC⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous
      (hsmooth.continuous_fderiv (by simp))
    exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun x ↦ (hC x).trans (le_max_left _ _)⟩

end SobolevSpace.Trace.C1

namespace SobolevSpace.Boundary

open Set

/-- Raw bounded open graph geometry supplies both the atlas and a smooth
uniformly transverse field. The positive normal component is the fixed
constant `1/2`; the field and derivative bounds are conclusions. -/
theorem HasC1GraphBoundary.exists_contDiff_transverse
    {n : ℕ} {Ω : Set (ℝ^(n + 1))} (hgraph : HasC1GraphBoundary Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    ∃ X : ℝ^(n + 1) → ℝ^(n + 1),
      ContDiff ℝ (⊤ : ℕ∞) X ∧ HasCompactSupport X ∧
      (∀ x, ‖X x‖ ≤ 1) ∧
      (∀ x : frontier Ω, (1 / 2 : ℝ) ≤ inner ℝ (X x)
        (Trace.C1.outwardUnitNormal (hΩ := hgraph.c1ExtensionAtlas hopen hbounded) x)) ∧
      ∃ C > 0, ∀ x, ‖fderiv ℝ X x‖ ≤ C :=
  @Trace.C1.exists_contDiff_transverse_outwardUnitNormal (n + 1) inferInstance Ω
    (hgraph.c1ExtensionAtlas hopen hbounded)

end SobolevSpace.Boundary
