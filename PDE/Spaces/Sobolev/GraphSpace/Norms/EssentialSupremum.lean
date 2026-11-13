/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Notation
import PDE.Analysis.MeasureTheory.Lp.EssentialSupremum

/-!
# Uniform bounds in the Sobolev graph at exponent infinity

The Wᵏ∞ norm is the maximum of the L∞ norms of its derivative rows.
Uniform representative bounds therefore control the graph norm and the
parameter dependence of graph elements, on arbitrary measurable domains.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal NNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Essential bounds for every derivative row control the Wᵏ∞ norm. -/
theorem norm_top_le_of_ae_rows (U : W^{k,∞}(Ω)) {C : ℝ} (hC : 0 ≤ C)
    (hU : ∀ a : DerivIndex n k, ∀ᵐ x ∂domainMeasure n Ω, ‖U.val a x‖ ≤ C) :
    ‖U‖ ≤ C := by
  have : Nonempty (DerivIndex n k) := ⟨baseIndex n k⟩
  change ‖U.val‖ ≤ C
  rw [PiLp.norm_eq_ciSup]
  exact ciSup_le fun a ↦ Lp.norm_top_le_of_ae_bound hC (hU a)

/-- Uniform Lipschitz estimates for derivative-row representatives give
a Lipschitz map into the Wᵏ∞ graph space. -/
theorem lipschitzOnWith_top_of_ae_rows
    {X : Type*} [PseudoMetricSpace X] {S : Set X} {K : ℝ≥0}
    (U : X → W^{k,∞}(Ω))
    (u : X → DerivIndex n k → ℝ^n → ℝ)
    (hrep : ∀ s ∈ S, ∀ a, ((U s).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] u s a)
    (hbound : ∀ s ∈ S, ∀ t ∈ S, ∀ a, ∀ᵐ x ∂domainMeasure n Ω,
      ‖u s a x - u t a x‖ ≤ K * dist s t) :
    LipschitzOnWith K U S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [dist_eq_norm]
  apply norm_top_le_of_ae_rows _ (mul_nonneg K.coe_nonneg dist_nonneg)
  intro a
  filter_upwards [Lp.coeFn_sub ((U s).val a) ((U t).val a),
    hrep s hs a, hrep t ht a, hbound s hs t ht a] with x hx hsx htx hxt
  change ‖(((U s).val a - (U t).val a : DerivLp n ∞ Ω) : ℝ^n → ℝ) x‖ ≤ _
  simpa only [hx, Pi.sub_apply, hsx, htx] using hxt

end SobolevSpace.GraphSpace
