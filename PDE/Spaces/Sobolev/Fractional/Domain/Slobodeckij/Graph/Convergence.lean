/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Graph.Realization

/-!
# Convergence in the Gagliardo graph

Convergence in the fractional graph norm means convergence in `Lᵖ` of both
the functions and their weighted differences. The representative-level
criterion below lets approximation proofs use ordinary functions throughout.
It also applies at exponent infinity. The smooth-density theorem proved later
assumes a finite exponent.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Graph-norm convergence is equivalent to convergence of both `Lᵖ` coordinates. -/
theorem tendsto_iff {ι : Type*} {l : Filter ι}
    {v : ι → W^{s,p}(Ω; F)}
    {u : W^{s,p}(Ω; F)} :
    Tendsto v l (𝓝 u) ↔
      Tendsto (fun i ↦ toLp n s Ω (v i)) l (𝓝 (toLp n s Ω u)) ∧
      Tendsto (fun i ↦ differenceQuotient n s Ω (v i))
        l (𝓝 (differenceQuotient n s Ω u)) := by
  rw [tendsto_subtype_rng,
    (WithLp.homeomorphProd p
      (Lp F p (volume.restrict Ω))
      (Lp F p (gagliardoProductMeasure n Ω))).isEmbedding.tendsto_nhds_iff,
    nhds_prod_eq, tendsto_prod_iff']
  rfl

/-- For function representatives, graph-norm convergence is exactly convergence
of the two extended `Lᵖ` error norms to zero. -/
theorem tendsto_ofFunction_iff {ι : Type*} {l : Filter ι}
    {v : ι → ℝ^n → F} (hv : ∀ i, MemGagliardo n s Ω (v i) (p := p))
    {u : ℝ^n → F} (hu : MemGagliardo n s Ω u (p := p)) :
    Tendsto (fun i ↦ ofFunction (v i) (hv i)) l (𝓝 (ofFunction u hu)) ↔
      Tendsto (fun i ↦ eLpNorm (v i - u) p (volume.restrict Ω)) l (𝓝 0) ∧
      Tendsto (fun i ↦ eLpNorm
        (diffQuot n s (v i) (p := p) - diffQuot n s u (p := p))
        p (gagliardoProductMeasure n Ω)) l (𝓝 0) := by
  rw [tendsto_iff]
  simp only [toLp_ofFunction, differenceQuotient_ofFunction]
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'', Lp.tendsto_Lp_iff_tendsto_eLpNorm'']

end SobolevSpace.Fractional.GagliardoSpace
