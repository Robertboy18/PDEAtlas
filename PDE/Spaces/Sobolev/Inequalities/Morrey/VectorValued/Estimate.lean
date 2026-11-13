/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FullEmbedding
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Function.LpSeminorm.Count

/-!
# Banach-valued Morrey estimates

A norming functional reduces pointwise and difference estimates to the scalar Morrey
inequality. The scalar graph identification is isometric, and applying a functional to
all derivative coordinates costs only its operator norm. In particular, no derivative
of the Banach norm is used. The estimate applies to every continuous representative,
including the smooth representatives supplied by mollification.

The constant depends only on dimension and exponent. In dimension zero volume is the
unit Dirac measure, and the constant is one.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A dimension- and exponent-dependent bound for Banach-valued Morrey estimates.
For positive dimension this is the scalar constant; in dimension zero it is one. -/
def morreyConstant (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hp : (n : ℝ≥0∞) < p) : ℝ :=
  if hn : 0 < n then (exists_morreyEmbeddingBound hn hp).choose else 1

/-- The Morrey constant is nonnegative. -/
theorem morreyConstant_nonneg (hp : (n : ℝ≥0∞) < p) : 0 ≤ morreyConstant n p hp := by
  unfold morreyConstant
  split
  · exact (exists_morreyEmbeddingBound _ hp).choose_spec.1
  · exact zero_le_one

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem scalar_representative_bound (hn : 0 < n) (hp : (n : ℝ≥0∞) < p)
    (U : W^{1,p}(ℝ^n; F)) {f : ℝ^n → F} (hf : Continuous f)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f)
    (L : F →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ∃ g : HolderSpace.C0GammaOn (ℝ^n) (morreyHolderExponent n p hn hp),
      (∀ x, g x = L (f x)) ∧ ‖g‖ ≤ morreyConstant n p hp * ‖U‖ := by
  obtain ⟨g, hg, hgnorm⟩ :=
    (exists_morreyEmbeddingBound hn hp).choose_spec.2 (scalarEquiv (mapCLM L U))
  have hmap : GraphSpace.baseRepresentative (scalarEquiv (mapCLM L U)) =ᵐ[volume]
      fun x ↦ L (f x) := by
    have h := mapCLM_apply_ae L U (baseIndex n 1)
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at h
    exact h.trans (hbase.fun_comp L)
  refine ⟨g, congrFun (Measure.eq_of_ae_eq (hg.trans hmap) g.continuous
    (L.continuous.comp hf)), ?_⟩
  have hnorm : ‖scalarEquiv (mapCLM L U)‖ ≤ ‖U‖ := by
    rw [LinearIsometryEquiv.norm_map]
    exact (norm_mapCLM_apply_le L U).trans
      ((mul_le_mul_of_nonneg_right hL (norm_nonneg U)).trans_eq (one_mul _))
  simpa only [morreyConstant, dite_eq_left hn] using hgnorm.trans
    (mul_le_mul_of_nonneg_left hnorm (exists_morreyEmbeddingBound hn hp).choose_spec.1)

/-- A continuous representative satisfies the global pointwise Morrey bound. This includes
smooth representatives without any support restriction and the one-point case `n = 0`. -/
theorem norm_apply_le_morreyConstant (hp : (n : ℝ≥0∞) < p)
    (U : W^{1,p}(ℝ^n; F)) {f : ℝ^n → F} (hf : Continuous f)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f) (x : ℝ^n) :
    ‖f x‖ ≤ morreyConstant n p hp * ‖U‖ := by
  by_cases hn : 0 < n
  · obtain ⟨L, hL, hx⟩ := exists_dual_vector'' ℝ (f x)
    obtain ⟨g, hg, hgnorm⟩ := scalar_representative_bound hn hp U hf hbase L hL
    calc
      ‖f x‖ = ‖g x‖ := by rw [hg, hx]; simp
      _ ≤ ‖g‖ := g.norm_apply_le x
      _ ≤ _ := hgnorm
  · have hn0 : n = 0 := by omega
    subst n
    have hnorm : ‖f x‖ = ‖coordinateCLM (baseIndex 0 1) U‖ := by
      rw [Lp.norm_def]
      change ‖f x‖ = (eLpNorm (U.val (baseIndex 0 1)) p
        (domainMeasure 0 (⊤ : Opens ℝ^0))).toReal
      simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
      rw [eLpNorm_congr_ae hbase, volume_euclideanSpace_eq_dirac]
      simp [eLpNorm_dirac, ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)),
        Subsingleton.elim (0 : ℝ^0) x]
    rw [hnorm]
    simpa [morreyConstant] using norm_coordinate_le (baseIndex 0 1) U

/-- The Hölder difference estimate for a continuous Banach-valued Sobolev representative.
Norming the difference uses one scalar functional, so the constant is independent of `F`. -/
theorem norm_sub_le_morreyConstant (hp : (n : ℝ≥0∞) < p)
    (U : W^{1,p}(ℝ^n; F)) {f : ℝ^n → F} (hf : Continuous f)
    (hbase : (U.val (baseIndex n 1) : ℝ^n → F) =ᵐ[volume] f) (x y : ℝ^n) :
    ‖f x - f y‖ ≤ morreyConstant n p hp * ‖U‖ * ‖x - y‖ ^ morreyExponent n p := by
  by_cases hn : 0 < n
  · obtain ⟨L, hL, hxy⟩ := exists_dual_vector'' ℝ (f x - f y)
    obtain ⟨g, hg, hgnorm⟩ := scalar_representative_bound hn hp U hf hbase L hL
    have h := g.holderWith.dist_le x y
    rw [morreyHolderExponent_coe_real] at h
    calc
      ‖f x - f y‖ = dist (g x) (g y) := by
        rw [dist_eq_norm, hg, hg, ← map_sub, hxy]; simp
      _ ≤ (g.holderSeminorm : ℝ) * dist x y ^ morreyExponent n p := h
      _ ≤ (morreyConstant n p hp * ‖U‖) * dist x y ^ morreyExponent n p :=
        mul_le_mul_of_nonneg_right (g.holderSeminorm_le_norm.trans hgnorm)
          (Real.rpow_nonneg (dist_nonneg) _)
      _ = _ := by rw [dist_eq_norm]
  · have hn0 : n = 0 := by omega
    subst n
    rw [Subsingleton.elim x y, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (morreyConstant_nonneg hp) (norm_nonneg U))
      (Real.rpow_nonneg (norm_nonneg _) _)

end SobolevSpace.VectorValued
