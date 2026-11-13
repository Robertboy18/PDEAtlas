/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Cutoff.Convergence
public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Density.WholeSpace

/-!
# Compactly supported smooth density in the whole space

First mollify, then multiply the smooth representative by a large smooth
cutoff. Each step costs less than half the requested error in the full
fractional norm. This gives density of `C_c^∞` for `0 < s < 1` and
`1 ≤ p < ∞`, with values in any real Banach space.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology FractionalSobolev
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every whole-space fractional Sobolev element can be approximated in graph
norm by a compactly supported smooth function. -/
theorem exists_smooth_compactly_supported_approximation
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : W^{s,p}(ℝ^n; F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (toLp n s Set.univ v : ℝ^n → F) =ᵐ[volume] f ∧ ‖v - u‖ < δ := by
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  obtain ⟨v, f, hf, hrep, hv⟩ :=
    exists_smooth_approximation (standardMollifier n) hp u (half_pos hδ)
  have hmem : MemGagliardo n s Set.univ f (p := p) :=
    (memGagliardo_toLp v).congr_ae (by simpa only [Measure.restrict_univ] using hrep)
  have hrealize : ofFunction f hmem = v := by
    apply toLp_injective
    apply Lp.ext
    exact (toLp_ofFunction_apply_ae f hmem).trans
      (by simpa only [Measure.restrict_univ] using hrep.symm)
  let R (m : ℕ) : ℝ := m + 1
  have hpos (m : ℕ) : 0 < R m := by dsimp [R]; positivity
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  have ht := tendsto_cutoff_ofFunction hs0 hs1 hp hmem R hpos hR
  rw [hrealize] at ht
  have he := ((ht.sub tendsto_const_nhds).norm).eventually
    (gt_mem_nhds (show ‖v - v‖ < δ / 2 by simpa using half_pos hδ))
  obtain ⟨m, hm⟩ := he.exists
  let g (x : ℝ^n) := cutoff (R m) x • f x
  have hgmem : MemGagliardo n s Set.univ g (p := p) :=
    hmem.cutoff hs0 hs1 hp0 hp (hpos m).ne'
  refine ⟨ofFunction g hgmem, g, (cutoff_contDiff (R m)).smul hf,
    (cutoff_hasCompactSupport (hpos m).ne').smul_right, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using toLp_ofFunction_apply_ae g hgmem
  · calc
      ‖ofFunction g hgmem - u‖ ≤ ‖ofFunction g hgmem - v‖ + ‖v - u‖ :=
        by simpa only [dist_eq_norm] using dist_triangle (ofFunction g hgmem) v u
      _ < δ / 2 + δ / 2 := add_lt_add hm hv
      _ = δ := add_halves δ

/-- Compactly supported smooth representatives are dense in the whole-space
fractional Sobolev graph for `0 < s < 1` and every finite exponent at least one. -/
theorem dense_smooth_compactly_supported (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    Dense {u : W^{s,p}(ℝ^n; F) |
      ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (toLp n s Set.univ u : ℝ^n → F) =ᵐ[volume] f} := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨v, f, hf, hc, hrep, hnorm⟩ :=
    exists_smooth_compactly_supported_approximation hs0 hs1 hp u hδ
  refine ⟨v, ⟨f, hf, hc, hrep⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hnorm

end SobolevSpace.Fractional.GagliardoSpace
