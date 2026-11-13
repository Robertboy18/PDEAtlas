/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Mollification.Convergence
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph.Convergence
import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation

/-!
# Smoothing elements of the fractional Sobolev graph

Mollification produces a graph element with a globally smooth representative.
As the positive scale tends to zero, both of its `Lᵖ` coordinates converge,
and hence so does the full fractional Sobolev norm.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology FractionalSobolev
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Convolve the function represented by a whole-space fractional Sobolev element. -/
def mollify (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F)) :
    W^{s,p}(ℝ^n; F) :=
  ofFunction (mollifyVector μ ε (toLp n s Set.univ u))
    ((memGagliardo_toLp u).mollifyVector μ hε hp)

/-- The first coordinate of a mollified graph element is represented by the
ordinary convolution of its original `Lᵖ` representative. -/
theorem toLp_mollify_apply_ae (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F)) :
    (toLp n s Set.univ (mollify μ hε hp u) : ℝ^n → F) =ᵐ[volume]
      mollifyVector μ ε (toLp n s Set.univ u) := by
  simpa only [mollify, Measure.restrict_univ] using
    toLp_ofFunction_apply_ae _ ((memGagliardo_toLp u).mollifyVector μ hε hp)

/-- Mollification gives a globally smooth representative of the resulting
fractional Sobolev element. -/
theorem mollify_has_smooth_representative (μ : Mollifier n) {ε : ℝ}
    (hε : 0 < ε) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F)) :
    ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
      (toLp n s Set.univ (mollify μ hε hp u) : ℝ^n → F) =ᵐ[volume] f := by
  refine ⟨mollifyVector μ ε (toLp n s Set.univ u), ?_,
    toLp_mollify_apply_ae μ hε hp u⟩
  apply mollifyVector_contDiff_of_pos μ hε
  have hbase : MemLp (toLp n s Set.univ u) p volume := by
    simpa only [Measure.restrict_univ] using Lp.memLp (toLp n s Set.univ u)
  exact hbase.locallyIntegrable (Fact.out : 1 ≤ p)

/-- Mollification converges in the full fractional graph norm along any positive
scales tending to zero, for Banach-valued functions and finite `p ≥ 1`. -/
theorem tendsto_mollify [CompleteSpace F] (μ : Mollifier n) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F))
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hε0 : Tendsto ε l (𝓝[>] (0 : ℝ))) :
    Tendsto (fun i ↦ mollify μ (hε i) hp u) l (𝓝 u) := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  have hu := memGagliardo_toLp u
  have hbase : MemLp (toLp n s Set.univ u) p volume := by
    simpa only [Measure.restrict_univ] using hu.1
  have ht := (tendsto_ofFunction_iff (l := l)
    (fun i ↦ hu.mollifyVector μ (hε i) hp) hu).mpr ⟨?_, ?_⟩
  · simpa only [ofFunction_toLp, mollify] using ht
  · simpa only [Measure.restrict_univ, Function.comp_def, Pi.sub_def] using
      (tendsto_eLpNorm_mollifyVector_sub μ hp hbase).comp hε0
  · have hd := (tendsto_eLpNorm_diffQuot_mollifyVector_sub μ hp hu).comp hε0
    apply hd.congr'
    filter_upwards [] with i
    apply congrArg (fun f ↦ eLpNorm f p (gagliardoProductMeasure n Set.univ))
    funext z
    simp only [diffQuot, Pi.sub_apply]
    rw [← smul_sub]
    congr 1
    abel

end SobolevSpace.Fractional.GagliardoSpace
