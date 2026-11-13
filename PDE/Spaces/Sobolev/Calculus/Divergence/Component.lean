/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Model.Definitions

/-!
# Recovering one component derivative from a weak divergence

If all but one matching component derivatives are in `L²`, the weak equation
`-div q = f` supplies the remaining derivative as `-f - ∑ dqᵢ`. This argument is
independent of ellipticity, boundary geometry, and the origin of the flux.

The boundary regularity arguments use this calculation for both linear and nonlinear
fluxes. Choosing a direction requires an element of `Fin n`; dimension one simply has
an empty complementary sum.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The weak divergence equation and the other matching weak derivatives determine
one missing component derivative, with the sign dictated by `-div q = f`. -/
theorem hasWeakDerivativeOn_component_of_weakDivergence
    (normal : Fin n)
    (q dq : Fin n → DerivLp n 2 Ω)
    (f : DerivLp n 2 Ω)
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      tsupport φ.toFun ⊆ Ω →
        (∑ i : Fin n,
          ∫ x, (q i : ℝ^n → ℝ) x *
            (∂[i] φ.toFun) x
            ∂domainMeasure n Ω) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x
            ∂domainMeasure n Ω)
    (htangential : ∀ i : Fin n, i ≠ normal →
      HasWeakDerivativeOn (n := n) Ω [i]
        (q i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ)) :
    HasWeakDerivativeOn (n := n) Ω
      [normal]
      (q normal : ℝ^n → ℝ)
      (fun x ↦ -(f : ℝ^n → ℝ) x -
        (∑ i ∈ Finset.univ.erase normal,
          (dq i : ℝ^n → ℝ) x)) := by
  set s := Finset.univ.erase normal
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num),
    memLp_locallyIntegrableOn_domain ((Lp.memLp f).neg.sub
      (memLp_finsetSum s fun i _ ↦ Lp.memLp (dq i))) (by norm_num), fun φ hφ ↦ ?_⟩
  have hint {h : ℝ^n → ℝ} (hh : MemLp h 2 (domainMeasure n Ω)) :
      Integrable (fun x ↦ h x * φ.toFun x) (domainMeasure n Ω) := by
    simpa [smul_eq_mul, mul_comm] using
      (hh.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        φ.contDiff.continuous φ.hasCompactSupport
  -- `∫ (-f - ∑ dqᵢ) φ = -(∫ f φ + ∑ ∫ dqᵢ φ)`
  have hcand : ∫ x, (-(f : ℝ^n → ℝ) x - ∑ i ∈ s, (dq i : ℝ^n → ℝ) x) * φ.toFun x
        ∂domainMeasure n Ω =
      -((∫ x, (f : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω) +
        ∑ i ∈ s, ∫ x, (dq i : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω) := by
    rw [← integral_finsetSum _ fun i _ ↦ hint (Lp.memLp (dq i)),
      ← integral_add (hint (Lp.memLp f)) (integrable_finsetSum _ fun i _ ↦ hint (Lp.memLp (dq i))),
      ← integral_neg]
    congr 1
    ext x
    rw [← Finset.sum_mul]
    ring
  -- the tangential terms of the divergence identity are `-∫ dqᵢ φ`
  have htan : ∀ i ∈ s, ∫ x, (q i : ℝ^n → ℝ) x * (∂[i] φ.toFun) x ∂domainMeasure n Ω =
      -∫ x, (dq i : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω := fun i hi ↦ by
    simpa [iteratedPartialDeriv] using htangential i (Finset.ne_of_mem_erase hi) φ hφ
  change ∫ x, (q normal : ℝ^n → ℝ) x * (∂[normal] φ.toFun) x ∂domainMeasure n Ω =
    (-1 : ℝ) ^ ([normal] : List (Fin n)).length *
      ∫ x, (-(f : ℝ^n → ℝ) x - ∑ i ∈ s, (dq i : ℝ^n → ℝ) x) * φ.toFun x ∂domainMeasure n Ω
  rw [hcand, ← hdiv φ hφ, ← Finset.add_sum_erase Finset.univ
    (fun i ↦ ∫ x, (q i : ℝ^n → ℝ) x * (∂[i] φ.toFun) x ∂domainMeasure n Ω)
    (Finset.mem_univ normal), Finset.sum_congr rfl htan, Finset.sum_neg_distrib]
  simp only [List.length_singleton, pow_one]
  ring

/-- The missing component derivative as an `L²` element, with the bound
coming directly from the equation and the triangle inequality. -/
theorem exists_component_weakDerivative_of_weakDivergence_with_norm
    (normal : Fin n)
    (q dq : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω)
    (hdiv : ∀ (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)), tsupport φ.toFun ⊆ Ω →
      (∑ i : Fin n, ∫ x, (q i : ℝ^n → ℝ) x *
        (∂[i] φ.toFun) x ∂domainMeasure n Ω) =
        ∫ x, (f : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n Ω)
    (hother : ∀ i : Fin n, i ≠ normal →
      HasWeakDerivativeOn Ω [i] (q i : ℝ^n → ℝ) (dq i : ℝ^n → ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      ‖g‖ ≤ ‖f‖ + ∑ i ∈ Finset.univ.erase normal, ‖dq i‖ ∧
      HasWeakDerivativeOn Ω [normal] (q normal : ℝ^n → ℝ) (g : ℝ^n → ℝ) := by
  let s := Finset.univ.erase normal
  let g : DerivLp n 2 Ω := -f - ∑ i ∈ s, dq i
  have hg : (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ -(f : ℝ^n → ℝ) x - ∑ i ∈ s, (dq i : ℝ^n → ℝ) x := by
    filter_upwards [Lp.coeFn_sub (-f) (∑ i ∈ s, dq i), Lp.coeFn_neg f,
      Lp.coeFn_fun_finsetSum s dq] with x hsub hneg hsum
    simp only [g, hsub, Pi.sub_apply, hneg, Pi.neg_apply, hsum]
  refine ⟨g, ?_, ?_⟩
  · calc
      ‖g‖ ≤ ‖-f‖ + ‖∑ i ∈ s, dq i‖ := norm_sub_le _ _
      _ ≤ ‖f‖ + ∑ i ∈ s, ‖dq i‖ := by
        simpa only [norm_neg] using add_le_add le_rfl (norm_sum_le s dq)
  · have hw := hasWeakDerivativeOn_component_of_weakDivergence normal q dq f hdiv hother
    exact hw.congr_ae Filter.EventuallyEq.rfl hg.symm


end SobolevSpace.GraphSpace
