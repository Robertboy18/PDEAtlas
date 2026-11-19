/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.Truncation
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.Dirichlet.IntegralBound
public import PDE.Elliptic.Regularity.Interior.DeGiorgi.UniformSobolev

/-!
# Sobolev norm of the zero-boundary superlevel

Testing `-div(A Du) = f` with `(u-k)₊`, using ellipticity and the
zero-boundary Sobolev embedding, gives
`‖(u-k)₊‖q ≤ C ‖f‖∞ |{u>k}|^(1-1/q)`.
The coefficient and solution have only their usual measurable and `H¹`
regularity. The constant is uniform in both the load and the level.

This is the quantitative Sobolev step in Stampacchia's truncation argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal NNReal

namespace SobolevSpace.GraphSpace

open Approximation.UpToBoundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The Dirichlet equation bounds the improved norm of every
nonnegative superlevel by the corresponding support measure. -/
theorem exists_superlevelH10_eLpNorm_le
    (P : InwardPartition Ω) (hΩb : Bornology.IsBounded Ω)
    {q : ℝ≥0∞} (hq2 : 2 ≤ q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : Fin n → Fin n → DerivLp n ∞ Ω, AEUniformlyElliptic a α →
      ∀ (f : DerivLp n 2 Ω) (u : H¹₀(Ω)),
        IsInteriorWeakDivergenceSolution a f (u : H¹(Ω)) →
      ∀ M : ℝ, 0 ≤ M → (∀ᵐ x ∂domainMeasure n Ω, ‖f x‖ ≤ M) →
      ∀ (k : ℝ) (hk : 0 ≤ k),
        MemLp (baseCoordCLM (superlevelH10 P u hk)) q (domainMeasure n Ω) ∧
        (eLpNorm (baseCoordCLM (superlevelH10 P u hk)) q (domainMeasure n Ω)).toReal ≤
          C * M * (domainMeasure n Ω).real {x | k < baseCoordCLM u x} ^
            (1 - 1 / q.toReal) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr Fact.out
  obtain ⟨S, hS, hSob⟩ := exists_uniform_eLpNorm_le_gradient_on_subdomains
    hΩb hn hq2 hq
  have hqt : q ≠ ∞ := (hq.trans_lt ENNReal.coe_lt_top).ne
  refine ⟨S ^ 2 / α, div_pos (sq_pos_of_pos hS) hα, ?_⟩
  intro a ha f u hu M hM hf k hk
  let T := superlevelH10 P u hk
  let Q := (eLpNorm (baseCoordCLM T) q (domainMeasure n Ω)).toReal
  let E := {x | k < baseCoordCLM u x}
  have hE : MeasurableSet E :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable _).measurable
  have hsupport : ∀ᵐ x ∂domainMeasure n Ω, x ∉ E → baseCoordCLM T x = 0 := by
    filter_upwards [superlevelH10_base_ae P u hk] with x hx hxE
    rw [hx]
    exact max_eq_right (sub_nonpos.mpr (le_of_not_gt hxE))
  obtain ⟨hT, hs⟩ := hSob Ω hΩ.isOpen Subset.rfl T
  refine ⟨hT, ?_⟩
  have hsR : Q ≤ S * ‖∇ (T : H¹(Ω))‖ := by
    change eLpNorm (baseCoordCLM T) q (domainMeasure n Ω) ≤ _ at hs
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
    rw [ENNReal.toReal_ofReal (mul_nonneg hS.le (norm_nonneg _))] at hh
    exact hh
  have hload := loadFunctional_le_eLpNorm_mul_measure f hf T
    ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hq2) hqt hT hE hsupport hM
  have henergy := hu.superlevelH10_gradient_sq_le P a ha f u hk
  have hQ : 0 ≤ Q := ENNReal.toReal_nonneg
  have hquad : α * Q ^ 2 ≤
      S ^ 2 * M * Q * (domainMeasure n Ω).real E ^ (1 - 1 / q.toReal) := by
    have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ hsR 2) hα.le
    have hright := mul_le_mul_of_nonneg_left (henergy.trans hload) (sq_nonneg S)
    nlinarith only [hsq, hright]
  by_cases hzero : Q = 0
  · change Q ≤ _
    rw [hzero]
    positivity
  have hQpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hzero)
  have hlin : α * Q ≤
      S ^ 2 * M * (domainMeasure n Ω).real E ^ (1 - 1 / q.toReal) := by
    apply (mul_le_mul_iff_left₀ hQpos).mp
    nlinarith only [hquad]
  change Q ≤ _
  calc
    Q ≤ (S ^ 2 * M * (domainMeasure n Ω).real E ^ (1 - 1 / q.toReal)) / α :=
      (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using hlin)
    _ = _ := by ring

end SobolevSpace.GraphSpace
