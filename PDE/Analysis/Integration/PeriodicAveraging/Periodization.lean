/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.FundamentalCell

/-!
# Periodizing compactly supported tests

Integer translates of a compactly supported function are locally finite. Their
sum descends to a continuous function on the unit torus, preserves smoothness,
and commutes with the Fréchet derivative. These tests connect periodic weak
identities with compactly supported Euclidean tests.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped Topology

namespace PDE.Analysis.PeriodicAveraging

/-- The integer lattice in Euclidean coordinates. -/
def integerVector (n : ℕ) : (Fin n → ℤ) →+ (ℝ^n) where
  toFun k := WithLp.toLp 2 fun i ↦ (k i : ℝ)
  map_zero' := by ext i; simp
  map_add' k l := by ext i; simp

/-- The Euclidean integer lattice is closed and discrete. -/
theorem isClosedEmbedding_integerVector (n : ℕ) :
    IsClosedEmbedding (integerVector n) :=
  (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).symm.isClosedEmbedding.comp
    (IsClosedEmbedding.piMap fun _ : Fin n ↦ Int.isClosedEmbedding_coe_real)

/-- Only finitely many integer translates of one compact set meet another. -/
theorem finite_integer_translates {n : ℕ} {s t : Set (ℝ^n)}
    (hs : IsCompact s) (ht : IsCompact t) :
    {k : Fin n → ℤ | ∃ x ∈ t, x + integerVector n k ∈ s}.Finite := by
  have hK := (hs.prod ht).image (continuous_fst.sub continuous_snd)
  have h := ((isClosedEmbedding_integerVector n).isCompact_preimage hK).finite_of_discrete
  apply h.subset
  rintro k ⟨x, hx, hxs⟩
  exact ⟨(x + integerVector n k, x), ⟨hxs, hx⟩, by dsimp; abel⟩

/-- Translates of a compactly supported function form a locally finite family. -/
theorem locallyFinite_integer_translates {n : ℕ} {E : Type*} [Zero E]
    {f : ℝ^n → E} (hf : HasCompactSupport f) :
    LocallyFinite fun k : Fin n → ℤ ↦ Function.support (fun x ↦ f (x + integerVector n k)) := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  apply (finite_integer_translates hf (isCompact_closedBall x 1)).subset
  rintro k ⟨y, hy, hyx⟩
  exact ⟨y, Metric.ball_subset_closedBall hyx, subset_tsupport f hy⟩

/-- The locally finite sum of all integer translates. -/
def periodize {n : ℕ} {E : Type*} [AddCommMonoid E] (f : ℝ^n → E) : ℝ^n → E :=
  fun x ↦ ∑ᶠ k : Fin n → ℤ, f (x + integerVector n k)

/-- A compactly supported continuous function has a continuous periodization. -/
theorem continuous_periodize {n : ℕ} {E : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [ContinuousAdd E] {f : ℝ^n → E}
    (hf : Continuous f) (hfc : HasCompactSupport f) : Continuous (periodize f) :=
  continuous_finsum
    (fun _ ↦ hf.comp (continuous_id.add continuous_const))
    (locallyFinite_integer_translates hfc)

/-- Periodization is invariant under all integer translations. -/
theorem periodize_add_integerVector {n : ℕ} {E : Type*} [AddCommMonoid E]
    (f : ℝ^n → E) (x : ℝ^n) (k : Fin n → ℤ) :
    periodize f (x + integerVector n k) = periodize f x := by
  simpa only [periodize, Equiv.coe_addLeft, map_add, add_assoc] using
    finsum_comp_equiv (Equiv.addLeft k) (f := fun l ↦ f (x + integerVector n l))

/-- Periodization preserves every finite or infinite differentiability order. -/
theorem contDiff_periodize {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : WithTop ℕ∞} {f : ℝ^n → E} (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f) :
    ContDiff ℝ r (periodize f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨s, hs⟩ := finsum_eventually_eq_sum (locallyFinite_integer_translates hfc) x
  apply ContDiffAt.congr_of_eventuallyEq _ hs
  exact (ContDiff.sum fun k _ ↦ hf.comp (contDiff_id.add contDiff_const)).contDiffAt

/-- The Euclidean projection to the unit torus is an open quotient map. -/
theorem isOpenQuotientMap_toTorus (n : ℕ) : IsOpenQuotientMap (toTorus n) := by
  exact (IsOpenQuotientMap.piMap fun _ : Fin n ↦
    (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))).comp
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isOpenQuotientMap

/-- Two lifts of the same torus point differ by an integer vector. -/
theorem exists_integerVector_of_toTorus_eq {n : ℕ} {x y : ℝ^n}
    (h : toTorus n x = toTorus n y) : ∃ k : Fin n → ℤ, y = x + integerVector n k := by
  have hi (i : Fin n) : ∃ k : ℤ, (k : ℝ) = y i - x i := by
    have hz : ((y i - x i : ℝ) : UnitAddCircle) = 0 := by
      change toTorus n y i - toTorus n x i = 0
      exact sub_eq_zero.mpr (congrFun h i).symm
    simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  choose k hk using hi
  refine ⟨k, ?_⟩
  ext i
  change y i = x i + (k i : ℝ)
  rw [hk]
  abel

/-- Periodization is constant on the fibers of the torus projection. -/
theorem periodize_factorsThrough {n : ℕ} {E : Type*} [AddCommMonoid E]
    (f : ℝ^n → E) : Function.FactorsThrough (periodize f) (toTorus n) := by
  intro x y h
  obtain ⟨k, rfl⟩ := exists_integerVector_of_toTorus_eq h
  exact (periodize_add_integerVector f x k).symm

/-- A compactly supported continuous function determines a continuous periodic test. -/
def periodizeTorus {n : ℕ} {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [ContinuousAdd E] (f : ℝ^n → E) (hf : Continuous f) (hfc : HasCompactSupport f) :
    C(UnitAddTorus (Fin n), E) :=
  (isOpenQuotientMap_toTorus n).isQuotientMap.lift
    ⟨periodize f, continuous_periodize hf hfc⟩ (periodize_factorsThrough f)

/-- Pulling the torus test back gives the locally finite sum of integer translates. -/
theorem periodizeTorus_toTorus {n : ℕ} {E : Type*} [TopologicalSpace E]
    [AddCommMonoid E] [ContinuousAdd E] (f : ℝ^n → E)
    (hf : Continuous f) (hfc : HasCompactSupport f) (x : ℝ^n) :
    periodizeTorus f hf hfc (toTorus n x) = periodize f x := by
  exact congrArg (fun g : C(ℝ^n, E) ↦ g x)
    ((isOpenQuotientMap_toTorus n).isQuotientMap.lift_comp
      ⟨periodize f, continuous_periodize hf hfc⟩ (periodize_factorsThrough f))

/-- The derivative of the periodization is the periodization of the derivative. -/
theorem hasFDerivAt_periodize {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ^n → E}
    (hf : Differentiable ℝ f) (hfc : HasCompactSupport f) (x : ℝ^n) :
    HasFDerivAt (periodize f) (periodize (fderiv ℝ f) x) x := by
  classical
  obtain ⟨s, hs⟩ := (locallyFinite_integer_translates hfc).exists_finset_support x
  have hd (k : Fin n → ℤ) :
      HasFDerivAt (fun y ↦ f (y + integerVector n k))
        (fderiv ℝ f (x + integerVector n k)) x := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      (hf (x + integerVector n k)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const _)
  have hg : periodize f =ᶠ[𝓝 x] fun y ↦ ∑ k ∈ s, f (y + integerVector n k) := by
    filter_upwards [hs] with y hy
    exact finsum_eq_sum_of_support_subset _ (fun k hk ↦ hy hk)
  have hz (k : Fin n → ℤ) (hk : k ∉ s) : fderiv ℝ f (x + integerVector n k) = 0 := by
    have he : (fun _ : ℝ^n ↦ (0 : E)) =ᶠ[𝓝 x] fun y ↦ f (y + integerVector n k) := by
      filter_upwards [hs] with y hy
      exact (not_not.mp (fun h ↦ hk (hy h))).symm
    exact ((hd k).congr_of_eventuallyEq he).unique (hasFDerivAt_const (0 : E) x)
  have he : periodize (fderiv ℝ f) x = ∑ k ∈ s, fderiv ℝ f (x + integerVector n k) := by
    apply finsum_eq_sum_of_support_subset
    intro k hk
    by_contra hks
    exact hk (hz k hks)
  rw [he]
  exact (HasFDerivAt.fun_sum fun k _ ↦ hd k).congr_of_eventuallyEq hg

end PDE.Analysis.PeriodicAveraging
