/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import PDE.Analysis.MeasureTheory.Integral.ClosedSubspace
import PDE.Analysis.MeasureTheory.Lp.RealL2.Testing

/-!
# Weak spatial derivatives recovered from time averages

A curve in the ambient Sobolev graph belongs almost everywhere to the
closed graph if its smooth time averages satisfy the weak spatial identities.
The quotient-space fundamental lemma gives one exceptional set for the whole
graph, despite the uncountable family of spatial test functions.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal ContDiff

variable {n k : ℕ} {Ω : Set (ℝ^n)} {μ : Measure ℝ}

private theorem integral_coordinate_mul
    {u : ℝ → WkpAmbientOn n k 2 Ω} (hu : Integrable u μ)
    (α : DerivIndex n k) {φ : ℝ^n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) :
    (∫ x, ((∫ t, u t ∂μ) α) x * φ x ∂domainMeasure n Ω) =
      ∫ t, ∫ x, (u t α) x * φ x ∂domainMeasure n Ω ∂μ := by
  let A : WkpAmbientOn n k 2 Ω →L[ℝ] DerivLp n 2 Ω := PiLp.proj 2 _ α
  have hA := A.integral_comp_comm hu
  change (∫ x, (A (∫ t, u t ∂μ)) x * φ x ∂domainMeasure n Ω) = _
  rw [← hA]
  exact Lp.integral_mul_integral (A.integrable_comp hu)
    (hφ.memLp_of_hasCompactSupport hc)

/-- Smooth time averages satisfying every weak spatial identity imply
membership almost everywhere in the Sobolev graph. -/
theorem ae_isWkpOn_of_test_integrals
    {I : Set ℝ} (hI : IsOpen I) {u : ℝ → WkpAmbientOn n k 2 Ω}
    (hu : Integrable u μ)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ I →
      ∀ α : DerivIndex n k, ∀ φ : TestFunctionOn n Ω,
        (∫ t, ψ t * (∫ x, (u t (baseIndex n k)) x *
          iteratedPartialDeriv α.toList φ.1.toFun x ∂domainMeasure n Ω) ∂μ) =
        (-1 : ℝ) ^ α.toList.length *
          ∫ t, ψ t * (∫ x, (u t α) x * φ.1.toFun x ∂domainMeasure n Ω) ∂μ) :
    ∀ᵐ t ∂μ, t ∈ I → IsWkpOn (u t) := by
  apply (wkpSubmoduleOn n k 2 Ω).ae_mem_of_integral_contDiff_smul_mem
    (isClosed_WkpSubmoduleOn n k 2 Ω) hI hu
  intro ψ hψ hc hs
  have hint : Integrable (fun t ↦ ψ t • u t) μ :=
    hu.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
  change IsWkpOn (∫ t, ψ t • u t ∂μ)
  intro α
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num),
    memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num), ?_⟩
  intro φ hφ
  simp only [TestFunction.toFun_eq_coe]
  rw [integral_coordinate_mul hint _ (PDE.contDiff_top_iteratedPartialDeriv
      φ.contDiff α.toList).continuous (iteratedPartialDeriv_hasCompactSupport φ α.toList),
    integral_coordinate_mul hint _ φ.contDiff.continuous φ.hasCompactSupport]
  have havg (β : DerivIndex n k) (g : ℝ^n → ℝ) (t : ℝ) :
      (∫ x, ((ψ t • u t) β) x * g x ∂domainMeasure n Ω) =
        ψ t * ∫ x, (u t β) x * g x ∂domainMeasure n Ω := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (ψ t) (u t β)] with x hx
    change ((ψ t • u t β : DerivLp n 2 Ω) : ℝ^n → ℝ) x * g x = _
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  simpa only [havg, TestFunction.toFun_eq_coe] using h ψ hψ hc hs α ⟨φ, hφ⟩

end SobolevSpace.GraphSpace
