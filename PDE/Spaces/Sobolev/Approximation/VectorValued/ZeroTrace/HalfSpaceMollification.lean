/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Translation
import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary.Translation

/-!
# Translated mollification in the Banach-valued Sobolev graph

Translation and convolution commute with each weak derivative. Applying the finite-exponent
`Lp` convergence theorem to every coordinate gives convergence in the full Sobolev norm.
The smooth representatives are retained so that a normal translation can create a
pointwise vanishing strip before compact cutoffs are applied.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Mollification and translations tending to zero approximate a Banach-valued Sobolev
function in its full graph norm, with explicit smooth representatives of all coordinates. -/
theorem translated_mollification_approximation (μ : Mollifier n) (hp : p ≠ ∞)
    (U : W^{k,p}(ℝ^n; F)) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j)
    (hε0 : Tendsto ε atTop (𝓝 0)) (a : ℕ → ℝ^n) (ha : Tendsto a atTop (𝓝 0)) :
    let f (j : ℕ) (x : ℝ^n) :=
      mollifyVector μ (ε j) (U.val (baseIndex n k)) (x + a j)
    (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j)) ∧
      ∃ A : ℕ → W^{k,p}(ℝ^n; F),
        (∀ j b, ((A j).val b : ℝ^n → F) =ᵐ[volume]
          iteratedPartialDeriv b.toList (f j)) ∧
        Tendsto A atTop (𝓝 U) := by
  let f (j : ℕ) (x : ℝ^n) :=
    mollifyVector μ (ε j) (U.val (baseIndex n k)) (x + a j)
  have hmemU (b : DerivIndex n k) : MemLp (U.val b : ℝ^n → F) p volume := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using Lp.memLp (U.val b)
  have hf (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f j) :=
    (mollifyVector_contDiff_of_pos μ (hε j) _
      ((hmemU _).locallyIntegrable Fact.out)).comp (contDiff_id.add contDiff_const)
  have hD (j : ℕ) (b : DerivIndex n k) (x : ℝ^n) :
      iteratedPartialDeriv b.toList (f j) x =
        mollifyVector μ (ε j) (U.val b) (x + a j) := by
    rw [Approximation.UpToBoundary.iteratedPartialDeriv_comp_add,
      iteratedPartialDeriv_mollifyVector_eq μ (hε j) (U.property b)]
  have hmem (j : ℕ) (b : DerivIndex n k) :
      MemLp (iteratedPartialDeriv b.toList (f j)) p
        (domainMeasure n (⊤ : Opens ℝ^n)) := by
    have ht := (memLp_mollifyVector μ (hε j) hp (hmemU b)).comp_measurePreserving
      (measurePreserving_add_right volume (a j))
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      (memLp_congr_ae (Eventually.of_forall (hD j b))).mpr ht
  have hweak (j : ℕ) (b : DerivIndex n k) :
      HasWeakDerivativeOn ⊤ b.toList (iteratedPartialDeriv (baseIndex n k).toList (f j))
        (iteratedPartialDeriv b.toList (f j)) := by
    simpa only [baseIndex_toList, iteratedPartialDeriv] using
      hasWeakDerivativeOn_iteratedPartialDeriv (Ω := ⊤) (hf j) b.toList
  let A (j : ℕ) : W^{k,p}(ℝ^n; F) :=
    ofWeakDerivatives (fun b ↦ iteratedPartialDeriv b.toList (f j)) (hmem j) (hweak j)
  have hA (j : ℕ) (b : DerivIndex n k) :
      ((A j).val b : ℝ^n → F) =ᵐ[volume] iteratedPartialDeriv b.toList (f j) := by
    simpa only [domainMeasure, Opens.coe_top, Measure.restrict_univ] using
      ofWeakDerivatives_apply_ae (Ω := ⊤) (p := p) _ (hmem j) (hweak j) b
  refine ⟨hf, A, hA, ?_⟩
  apply tendsto_subtype_rng.mpr
  apply ((PiLp.homeomorph p (fun _ : DerivIndex n k ↦
    Lp F p (domainMeasure n (⊤ : Opens ℝ^n)))).symm.continuous.tendsto _).comp
  apply tendsto_pi_nhds.mpr
  intro b
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ (U.val b)).mpr
  apply (UpToBoundary.mollifyVector_translate_converges_Lp μ hp (hmemU b)
    ε hε hε0 a ha).congr'
  filter_upwards [] with j
  simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ]
  apply eLpNorm_congr_ae
  filter_upwards [hA j b] with x hx
  exact congrArg (· - U.val b x) ((hx.trans (hD j b x)).symm)

end SobolevSpace.VectorValued
