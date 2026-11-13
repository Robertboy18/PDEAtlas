/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Density.CompactSupport

/-!
# Smooth approximation through a whole-space extension

Once a Sobolev element has a whole-space extension, we can smooth that
extension and restrict it back. Restriction is contractive, so the
whole-space error also controls the error on the original domain.

The approximating functions are smooth across the boundary and compactly
supported in the ambient space. Their support need not lie inside the
domain; this is approximation in the full Sobolev space, without a
zero-boundary condition.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal FractionalSobolev Topology

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Set (ℝ^n)}

/-- A whole-space extension gives approximants smooth across the domain boundary.
Their compact support is in the ambient space, with no boundary vanishing requirement. -/
theorem exists_global_smooth_approximation_of_extension
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : W^{s,p}(Ω; F)) (U : W^{s,p}(ℝ^n; F))
    (hU : restrictCLM (subset_univ Ω) U = u) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : W^{s,p}(Ω; F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
      (toLp n s Ω v : ℝ^n → F) =ᵐ[volume.restrict Ω] f ∧ ‖v - u‖ < ε := by
  obtain ⟨V, f, hf, hc, hrep, hnorm⟩ :=
    exists_smooth_compactly_supported_approximation hs0 hs1 hp U hε
  refine ⟨restrictCLM (subset_univ Ω) V, f, hf, hc, ?_, ?_⟩
  · exact (toLp_restrictCLM_apply_ae (subset_univ Ω) V).trans
      (ae_restrict_of_ae hrep)
  · rw [← hU, ← map_sub]
    exact (norm_restrictCLM_apply_le (subset_univ Ω) (V - U)).trans_lt hnorm

/-- If every element extends to the whole space, restrictions of globally smooth,
compactly supported functions are dense in the intrinsic fractional Sobolev space. -/
theorem dense_global_smooth_of_surjective_restrict
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (hrestrict : Function.Surjective
      (restrictCLM (n := n) (s := s) (p := p) (F := F) (subset_univ Ω))) :
    Dense {u : W^{s,p}(Ω; F) |
      ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (toLp n s Ω u : ℝ^n → F) =ᵐ[volume.restrict Ω] f} := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨U, hU⟩ := hrestrict u
  obtain ⟨v, f, hf, hc, hrep, hnorm⟩ :=
    exists_global_smooth_approximation_of_extension hs0 hs1 hp u U hU hε
  exact ⟨v, ⟨f, hf, hc, hrep⟩,
    by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

end SobolevSpace.Fractional.GagliardoSpace
