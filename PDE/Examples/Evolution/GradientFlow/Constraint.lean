/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Evolution.GradientFlow.Stopping
import CAS.ExactTactic

/-!
# A nonstationary signed flow with a nondense domain

The energy is `x - 2` on the closed positive half-line and `+∞` elsewhere, and the domain
of its subdifferential is that half-line. Starting from three, the existence theorem gives
a flow toward the constraint, and weak uniqueness identifies it with the finite-stopping
curve of `Stopping`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis.Convex PDE.Analysis.Evolution

namespace PDE.Examples.GradientFlow

/-- A signed affine energy subject to a closed unilateral constraint. -/
def constrainedEnergy (x : ℝ) : EReal := if 0 ≤ x then ((x - 2 : ℝ) : EReal) else ⊤

/-- The energy is proper and takes negative values. -/
theorem constrainedEnergy_isProper : IsProper constrainedEnergy := by
  constructor
  · intro x
    by_cases hx : 0 ≤ x
    · simpa only [constrainedEnergy, ite_eq_left hx] using EReal.coe_ne_bot (x - 2)
    · simp [constrainedEnergy, hx]
  · exact ⟨0, by norm_num [constrainedEnergy]⟩

private theorem mem_constrainedEnergy_realEpigraph (p : ℝ × ℝ) :
    p ∈ realEpigraph constrainedEnergy ↔ 0 ≤ p.1 ∧ p.1 - 2 ≤ p.2 := by
  by_cases hp : 0 ≤ p.1
  · simp only [realEpigraph, mem_ofPred_eq, constrainedEnergy, hp, ite_true,
      EReal.coe_le_coe_iff, true_and]
  · simp [realEpigraph, constrainedEnergy, hp]

/-- The extended-real epigraph is convex. -/
theorem constrainedEnergy_convex : Convex ℝ (realEpigraph constrainedEnergy) := by
  intro x hx y hy a b ha hb hab
  rw [mem_constrainedEnergy_realEpigraph] at hx hy ⊢
  change 0 ≤ a * x.1 + b * y.1 ∧ a * x.1 + b * y.1 - 2 ≤ a * x.2 + b * y.2
  constructor
  · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · nlinarith [mul_nonneg ha (sub_nonneg.2 hx.2), mul_nonneg hb (sub_nonneg.2 hy.2)]

/-- The infinite extension across the closed constraint is lower semicontinuous. -/
theorem constrainedEnergy_lowerSemicontinuous : LowerSemicontinuous constrainedEnergy := by
  apply lowerSemicontinuous_iff_isClosed_preimage.2
  intro r
  by_cases hr : r = ⊤
  · simp [hr]
  have heq : constrainedEnergy ⁻¹' Iic r =
      Ici 0 ∩ {x : ℝ | ((x - 2 : ℝ) : EReal) ≤ r} := by
    ext x
    by_cases hx : 0 ≤ x <;> simp [constrainedEnergy, hx, top_le_iff, hr]
  rw [heq]
  exact isClosed_Ici.inter (isClosed_le
    (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)) continuous_const)

/-- Slope one is a supporting vector at every admissible point. -/
theorem constrainedEnergy_one_mem_subdifferential {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ∈ subdifferential constrainedEnergy x := by
  intro y
  by_cases hy : 0 ≤ y
  · simp only [constrainedEnergy, ite_eq_left hx, ite_eq_left hy, Real.inner_apply,
      one_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have heq : x - 2 + (y - x) = y - 2 := by cas
    exact heq.le
  · simp [constrainedEnergy, hy]

/-- Zero is also a supporting vector at the constrained minimizer. -/
theorem constrainedEnergy_zero_mem_subdifferential :
    (0 : ℝ) ∈ subdifferential constrainedEnergy 0 := by
  intro y
  by_cases hy : 0 ≤ y
  · simp only [constrainedEnergy, le_refl, ite_true, ite_eq_left hy, inner_zero_left,
      EReal.coe_zero, add_zero]
    exact EReal.coe_le_coe_iff.2 (by linarith)
  · simp [constrainedEnergy, hy]

/-- The subdifferential domain is the closed half-line, so it is neither full nor dense. -/
theorem constrainedEnergy_domain : subdifferentialDomain constrainedEnergy = Ici 0 := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    have hn := ne_top_of_mem_subdifferential constrainedEnergy_isProper hv
    by_contra hx
    exact hn (by simp [constrainedEnergy, show ¬0 ≤ x from hx])
  · intro hx
    exact ⟨1, constrainedEnergy_one_mem_subdifferential hx⟩

/-- In particular the domain is not dense. -/
theorem constrainedEnergy_not_dense : ¬Dense (subdifferentialDomain constrainedEnergy) := by
  rw [dense_iff_closure_eq, constrainedEnergy_domain, isClosed_Ici.closure_eq]
  intro h
  have hm : (-1 : ℝ) ∈ Ici 0 := h.symm ▸ mem_univ (-1)
  norm_num at hm

/-- The explicit motion stops at the boundary and remains a full weak subgradient flow. -/
theorem constrainedEnergy_stoppingFlow :
    IsSubgradientFlow constrainedEnergy stoppingCurve stoppingVelocity := by
  refine ⟨stoppingCurve_lipschitz.continuous.continuousOn,
    stoppingVelocity_memLp.restrict _, stoppingCurve_hasWeakTimeDerivativeOn, ?_⟩
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t < 3
  · simp only [stoppingVelocity, ite_eq_left ht, neg_neg]
    exact constrainedEnergy_one_mem_subdifferential (le_max_right _ _)
  · have hzero : stoppingCurve t = 0 := max_eq_right (sub_nonpos.2 (le_of_not_gt ht))
    rw [stoppingVelocity, ite_eq_right ht, neg_zero, hzero]
    exact constrainedEnergy_zero_mem_subdifferential

/-- The existence theorem gives a nonstationary flow for the constrained energy;
uniqueness identifies it with the stopping curve and its velocity almost everywhere. -/
theorem constrainedEnergy_raw_flow :
    ∃ u g : ℝ → ℝ, u 0 = 3 ∧ IsSubgradientFlow constrainedEnergy u g ∧
      EqOn u stoppingCurve (Ici 0) ∧
      g =ᵐ[volume.restrict (Ioi 0)] stoppingVelocity ∧
      (∀ t, 0 ≤ t → 0 ≤ u t) ∧ u 1 = 2 ∧ u 3 = 0 := by
  obtain ⟨_, _, _, u, g, hu0, hflow, _, _, _, _, hdomain, _⟩ :=
    exists_unique_subgradientFlow constrainedEnergy_isProper constrainedEnergy_convex
      constrainedEnergy_lowerSemicontinuous
      (show (3 : ℝ) ∈ subdifferentialDomain constrainedEnergy from
        ⟨1, constrainedEnergy_one_mem_subdifferential (by norm_num)⟩)
  have hinit := hu0.trans stoppingCurve_values.1.symm
  have heq := hflow.eqOn_of_initial_eq constrainedEnergy_isProper
    constrainedEnergy_stoppingFlow hinit
  refine ⟨u, g, hu0, hflow, heq,
    hflow.velocity_ae_eq_of_initial_eq constrainedEnergy_isProper constrainedEnergy_stoppingFlow
      hinit, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [constrainedEnergy_domain, mem_Ici] using hdomain t ht
  · exact (heq (by norm_num : (1 : ℝ) ∈ Ici 0)).trans stoppingCurve_values.2.1
  · exact (heq (by norm_num : (3 : ℝ) ∈ Ici 0)).trans (stoppingCurve_values.2.2 3 le_rfl)

end PDE.Examples.GradientFlow
