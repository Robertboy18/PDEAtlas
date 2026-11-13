/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.DerivativeBounds
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Representatives.FirstOrder

/-!
# The Banach-valued mollified extension as a Sobolev function

The interior formula is smooth, and its function and first derivatives have
finite `Lᵖ` norm. These facts place it in the weak-derivative graph.
The representative is unique, and the estimates for its coordinates give
one norm bound valid for all fractional boundary data in any real Banach space.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open Approximation Fractional GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Fractional boundary data have a unique Sobolev representative of
their mollified extension, with the classical first derivatives. -/
theorem existsUnique_mollifiedExtension (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    ∃! U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, HalfSpace.isOpen_upper (n + 1)⟩; F),
      (coordinateCLM (baseIndex (n + 1) 1) U : ℝ^(n + 1) → F)
          =ᵐ[volume.restrict ℝ^(n + 1)₊]
            mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) ∧
        ∀ i : Fin (n + 1),
          (coordinateCLM (singleDerivIndex (n + 1) i) U : ℝ^(n + 1) → F)
            =ᵐ[volume.restrict ℝ^(n + 1)₊]
              ∂[i] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)) := by
  obtain ⟨_, _, hderiv⟩ := exists_pos_partialDeriv_mollifiedExtension_bound (F := F) hp μ
  apply existsUnique_firstOrder_of_contDiffOn_memLp
  · exact (contDiffOn_mollifiedExtension μ
      ((boundary_memLp g).locallyIntegrable (Fact.out : 1 ≤ ENNReal.ofReal p))).of_le (by simp)
  · exact memLp_mollifiedExtension μ ENNReal.ofReal_ne_top (boundary_memLp g)
  · exact fun i ↦ (hderiv g i).1

/-- The cutoff mollified formula, represented in the first-order Sobolev space. -/
def mollifiedExtensionSobolev (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, HalfSpace.isOpen_upper (n + 1)⟩; F) :=
  (existsUnique_mollifiedExtension μ hp g).choose

/-- The function coordinate of the extension is its defining formula. -/
theorem mollifiedExtensionSobolev_base_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    (coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp g) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g) :=
  (existsUnique_mollifiedExtension μ hp g).choose_spec.1.1

/-- The stored weak partials agree with the classical partials of the interior formula. -/
theorem mollifiedExtensionSobolev_partialDeriv_ae (μ : Mollifier n) (hp : 1 < p)
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) (i : Fin (n + 1)) :
    (coordinateCLM (singleDerivIndex (n + 1) i) (mollifiedExtensionSobolev μ hp g) :
        ℝ^(n + 1) → F)
      =ᵐ[volume.restrict ℝ^(n + 1)₊]
        ∂[i] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)) :=
  (existsUnique_mollifiedExtension μ hp g).choose_spec.1.2 i

/-- The Sobolev norm of the extension is bounded by the fractional
boundary norm, with one positive constant independent of the datum. -/
theorem exists_pos_norm_mollifiedExtensionSobolev_bound (μ : Mollifier n) (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        ‖mollifiedExtensionSobolev μ hp g‖ ≤ C * ‖g‖ := by
  obtain ⟨D, hD, hderiv⟩ := exists_pos_partialDeriv_mollifiedExtension_bound (F := F) hp μ
  have hp₀ : 0 < p := zero_lt_one.trans hp
  refine ⟨(2 : ℝ) ^ (1 / p) + ∑ i, D i, ?_, fun g ↦ ?_⟩
  · exact add_pos_of_pos_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _)
      (Finset.sum_nonneg fun i _ ↦ (hD i).le)
  · have hboundary : eLpNorm (GagliardoSpace.toLp n (1 - 1 / p) univ g)
        (ENNReal.ofReal p) volume ≤ ‖g‖ₑ := by
      have h : ‖GagliardoSpace.toLp n (1 - 1 / p) univ g‖ₑ ≤ ‖g‖ₑ :=
        WithLp.enorm_fst_le _ g.val
      simpa only [Lp.enorm_def, Measure.restrict_univ] using h
    have hbase :
        ‖coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp g)‖ ≤
          (2 : ℝ) ^ (1 / p) * ‖g‖ := by
      rw [Lp.norm_def]
      change (eLpNorm _ _ (volume.restrict ℝ^(n + 1)₊)).toReal ≤ _
      rw [eLpNorm_congr_ae (mollifiedExtensionSobolev_base_ae μ hp g)]
      have hb := (eLpNorm_mollifiedExtension_le μ ENNReal.ofReal_ne_top
        (boundary_memLp g)).trans (mul_le_mul' le_rfl hboundary)
      have ht : (2 : ℝ≥0∞) ^ (1 / (ENNReal.ofReal p).toReal) * ‖g‖ₑ ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by norm_num)) enorm_ne_top
      have h := ENNReal.toReal_mono ht hb
      simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat,
        ENNReal.toReal_ofReal hp₀.le, toReal_enorm] using h
    have hrow (i : Fin (n + 1)) :
        ‖coordinateCLM (singleDerivIndex (n + 1) i)
          (mollifiedExtensionSobolev μ hp g)‖ ≤ D i * ‖g‖ := by
      rw [Lp.norm_def]
      change (eLpNorm _ _ (volume.restrict ℝ^(n + 1)₊)).toReal ≤ _
      rw [eLpNorm_congr_ae (mollifiedExtensionSobolev_partialDeriv_ae μ hp g i)]
      have h := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top) (hderiv g i).2
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hD i).le, toReal_enorm] using h
    calc
      ‖mollifiedExtensionSobolev μ hp g‖ ≤
          ‖coordinateCLM (baseIndex (n + 1) 1) (mollifiedExtensionSobolev μ hp g)‖ +
            ∑ i : Fin (n + 1), ‖coordinateCLM (singleDerivIndex (n + 1) i)
              (mollifiedExtensionSobolev μ hp g)‖ :=
        by
          simpa only [norm_partialDeriv_eq_coordinate, coordinateCLM_apply] using
            norm_le_base_add_sum_partialDeriv (mollifiedExtensionSobolev μ hp g)
      _ ≤ (2 : ℝ) ^ (1 / p) * ‖g‖ + ∑ i : Fin (n + 1), D i * ‖g‖ :=
        add_le_add hbase (Finset.sum_le_sum fun i _ ↦ hrow i)
      _ = _ := by rw [← Finset.sum_mul, ← add_mul]

end SobolevSpace.VectorValued.Trace.HalfSpace
