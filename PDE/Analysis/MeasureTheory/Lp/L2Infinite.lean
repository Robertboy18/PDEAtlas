/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Infinite-dimensional scalar L² spaces

A locally finite measure with infinite support on a Hausdorff space has
infinite-dimensional real or complex `L²`. Finite collections of support points
have disjoint open neighborhoods of positive finite measure. Their indicators
are nonzero and orthogonal, giving arbitrarily large linearly independent families.

For a nonzero measure that vanishes on singletons, a conull support cannot be finite.
This gives a corollary on hereditarily Lindelöf spaces, including second-countable
spaces.
-/

@[expose] public section

noncomputable section

namespace MeasureTheory.Lp

open scoped ENNReal InnerProductSpace Topology

variable {X 𝕜 : Type*} [RCLike 𝕜]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- A locally finite measure with infinite support has infinite-dimensional scalar `L²`.
The measure may have atoms: distinct support points supply disjoint neighborhoods of
positive finite measure, whose indicators are nonzero and orthogonal. -/
theorem not_finiteDimensional_of_infinite_support
    (μ : Measure X) [IsLocallyFiniteMeasure μ] (hμ : μ.support.Infinite) :
    ¬FiniteDimensional 𝕜 (Lp 𝕜 2 μ) := by
  classical
  intro hfinite
  obtain ⟨t, ht, htcard⟩ :=
    hμ.exists_subset_card_eq (Module.finrank 𝕜 (Lp 𝕜 2 μ) + 1)
  obtain ⟨U, hU, hdisjoint⟩ := t.finite_toSet.t2_separation
  choose W hWmem hWopen hWfinite using
    (fun x : X ↦ μ.exists_isOpen_measure_lt_top x)
  let s (i : t) : Set X := U i ∩ W i
  have hsopen (i : t) : IsOpen (s i) := (hU i).2.inter (hWopen i)
  have hsmem (i : t) : (i : X) ∈ s i := ⟨(hU i).1, hWmem i⟩
  have hspos (i : t) : 0 < μ (s i) :=
    (Measure.mem_support_iff_forall (μ := μ) i).mp (ht i.property)
      (s i) ((hsopen i).mem_nhds (hsmem i))
  have hsfinite (i : t) : μ (s i) < ∞ :=
    (measure_mono Set.inter_subset_right).trans_lt (hWfinite i)
  have hsdisjoint : Pairwise (fun i j : t ↦ Disjoint (s i) (s j)) := by
    intro i j hij
    exact (hdisjoint i.property j.property (fun h ↦ hij (Subtype.ext h))).mono
      Set.inter_subset_left Set.inter_subset_left
  let v (i : t) : Lp 𝕜 2 μ :=
    indicatorConstLp 2 (hsopen i).measurableSet (hsfinite i).ne (1 : 𝕜)
  have hvne (i : t) : v i ≠ 0 := by
    intro hzero
    have heq :
        indicatorConstLp 2 (hsopen i).measurableSet (hsfinite i).ne (1 : 𝕜) =
          indicatorConstLp (μ := μ) 2 MeasurableSet.empty (by simp) (1 : 𝕜) := by
      simpa only [indicatorConstLp_empty] using hzero
    have hnull : μ (s i) = 0 :=
      ae_eq_empty.mp ((indicatorConstLp_inj
        (hsopen i).measurableSet (hsfinite i).ne MeasurableSet.empty
        (by simp) (one_ne_zero : (1 : 𝕜) ≠ 0)).mp heq)
    exact (hspos i).ne' hnull
  have hvorth : Pairwise (fun i j : t ↦ ⟪v i, v j⟫_𝕜 = 0) := by
    intro i j hij
    dsimp only [v]
    rw [L2.inner_indicatorConstLp_one_indicatorConstLp_one
      (hsopen i).measurableSet (hsopen j).measurableSet (hsfinite i).ne (hsfinite j).ne,
      Set.disjoint_iff_inter_eq_empty.mp (hsdisjoint hij)]
    simp
  have hlin : LinearIndependent 𝕜 v :=
    linearIndependent_of_ne_zero_of_inner_eq_zero hvne hvorth
  have hcard := hlin.fintype_card_le_finrank
  rw [Fintype.card_coe, htcard] at hcard
  exact Nat.not_succ_le_self _ hcard

/-- A nonzero locally finite measure that vanishes on singletons has
infinite-dimensional scalar `L²` on a hereditarily Lindelöf Hausdorff space.
Second-countable Hausdorff spaces satisfy the topological hypothesis.
The conull-support property is essential: null singletons alone on an arbitrary
measurable space do not imply this conclusion. -/
theorem not_finiteDimensional_of_nullSingleton
    [HereditarilyLindelofSpace X] (μ : Measure X)
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] (hμ : μ ≠ 0) :
    ¬FiniteDimensional 𝕜 (Lp 𝕜 2 μ) := by
  apply not_finiteDimensional_of_infinite_support μ
  intro hsupport
  apply hμ
  apply Measure.measure_univ_eq_zero.mp
  simpa only [Set.union_compl_self] using
    measure_union_null (hsupport.measure_zero μ) (Measure.measure_compl_support (μ := μ))

end MeasureTheory.Lp
