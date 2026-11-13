/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Translation
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives

/-!
# Translated mollification in the Sobolev graph norm

The scale and the translation may tend to zero independently. Applying the weak
derivative identity and translation continuity to each coordinate gives convergence
in the full finite-order Sobolev graph norm.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open UpToBoundary GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translated mollifications of a whole-space Sobolev function converge in the
Sobolev graph norm. The displayed representatives keep track of the pointwise values. -/
theorem translated_mollification_approximation (μ : Mollifier n) (hp : p ≠ ∞)
    (U : W^{k,p}(ℝ^n)) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hε0 : Tendsto ε atTop (𝓝 0))
    (a : ℕ → ℝ^n) (ha : Tendsto a atTop (𝓝 0)) :
    let f (j : ℕ) (x : ℝ^n) := mollify μ (ε j) (baseRepresentative U) (x + a j)
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧
      ∃ A : ℕ → W^{k,p}(ℝ^n),
        (∀ j, baseRepresentative (A j) =ᵐ[volume] f j) ∧
        Tendsto A atTop (𝓝 U) := by
  let g (b : DerivIndex n k) : ℝ^n → ℝ := (U : WkpAmbientOn n k p univ) b
  have hg (b : DerivIndex n k) : MemLp (g b) p volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp (U.val b)
  let f (j : ℕ) (x : ℝ^n) := mollify μ (ε j) (baseRepresentative U) (x + a j)
  have hf (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f j) :=
    (mollify_contDiff_of_pos μ (hε j) _ ((hg _).locallyIntegrable Fact.out)).comp
      (contDiff_id.add contDiff_const)
  have hD (j : ℕ) (b : DerivIndex n k) (x : ℝ^n) :
      iteratedPartialDeriv b.toList (f j) x = mollify μ (ε j) (g b) (x + a j) := by
    rw [iteratedPartialDeriv_comp_add]
    by_cases hb : b.toList = []
    · have hbase := b.eq_baseIndex hb
      subst b
      simp only [baseIndex_toList, iteratedPartialDeriv, baseRepresentative, g]
    · exact congrFun (iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
        μ (hε j) hb ((hg _).locallyIntegrable Fact.out) (U.property b)) (x + a j)
  have hmem (j : ℕ) (b : DerivIndex n k) :
      MemLp (iteratedPartialDeriv b.toList (f j)) p (domainMeasure n univ) := by
    have hshift := (memLp_mollify μ (hε j) hp (hg b)).comp_measurePreserving
      (measurePreserving_add_right volume (a j))
    exact (memLp_congr_ae (Eventually.of_forall (hD j b))).mpr (hshift.restrict univ)
  let A (j : ℕ) := mkWkpSpaceOnOfContDiffMemLp (f j) (hf j) (hmem j)
  refine ⟨hf, A, ?_, ?_⟩
  · intro j
    simpa only [A, f, baseRepresentative, baseIndex_toList, iteratedPartialDeriv,
      domainMeasure, Measure.restrict_univ] using
      mkWkpSpaceOnOfContDiffMemLp_apply_ae (f j) (hf j) (hmem j) (baseIndex n k)
  · apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply tendsto_piLp_norm_of_forall (p := p) hp
    intro b
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (mollify_translate_converges_Lp μ hp (hg b) ε hε hε0 a ha)
    simp only [ENNReal.toReal_zero, Function.comp_def] at ht
    convert ht using 1
    funext j
    rw [Lp.norm_def]
    congr 1
    simp only [domainMeasure, Measure.restrict_univ]
    apply eLpNorm_congr_ae
    have hctor := mkWkpSpaceOnOfContDiffMemLp_apply_ae (f j) (hf j) (hmem j) b
    have hsub := Lp.coeFn_sub ((A j : WkpAmbientOn n k p univ) b) (U.val b)
    simp only [domainMeasure, Measure.restrict_univ] at hctor hsub
    filter_upwards [hsub, hctor] with x hx hb
    exact hx.trans (congrArg (· - g b x) (hb.trans (hD j b x)))

end SobolevSpace.Approximation
