/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.PoissonWeakForm
import PDE.Elliptic.Regularity.Localization.CutoffEquation.WeakEquation
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates

/-!
# Localization of weak Poisson equations with zero trace

Multiplying an H¹₀ solution of `Δz = f ∈ L²` by a smooth compactly supported
function preserves the zero trace and gives the L² load
`ηf + 2 ∇η · ∇z + z Δη`. This is the identity-coefficient specialization of
the general divergence-form cutoff theorem. No second weak derivatives of the
state or regularity of the domain boundary are assumed.

The support statements use a chosen representative of the localized state,
so no support condition is imposed on the arbitrary representative of an L² class.
-/

@[expose] public noncomputable section

open PDE (laplacian iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Sobolev ENNReal Distributions InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A smooth cutoff of a zero-trace weak solution of `Δz = f` has the L²
Laplacian `ηf + 2 ∇η · ∇z + z Δη`. The localized state is the
continuous cutoff map on H¹₀; the equation holds against every compact smooth test. -/
theorem exists_laplacian_cutoffH10
    (hΩ : IsOpen Ω) (z : H¹₀(Ω)) (f : DerivLp n 2 Ω)
    (hweak : ∀ φ : TestFunctionOn n Ω,
      (∫ x, baseRepresentative (z : H¹(Ω)) x * laplacian φ.1.toFun x
        ∂domainMeasure n Ω) =
          ∫ x, (f : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω)
    (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ g : DerivLp n 2 Ω,
      (g : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] (fun x ↦
        η.toFun x * f x +
          2 * ∑ i : Fin n, (∂[i] η.toFun) x * derivCoordCLM i z x +
          baseCoordCLM z x * laplacian η.toFun x) ∧
      ∀ φ : TestFunctionOn n Ω,
        (∫ x, baseRepresentative (cutoffH10 hΩ η z : H¹(Ω)) x *
          laplacian φ.1.toFun x ∂domainMeasure n Ω) =
            ∫ x, (g : ℝ^n → ℝ) x * φ.1.toFun x ∂domainMeasure n Ω := by
  classical
  have hmem (c : ℝ) (a : DerivIndex n 1) :
      MemLp (iteratedPartialDeriv a.toList (fun _ : ℝ^n ↦ c))
        ∞ (domainMeasure n Ω) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [baseIndex_toList, iteratedPartialDeriv] using memLp_top_const c
    · simpa only [singleDerivIndex_toList, iteratedPartialDeriv, PDE.partialDeriv_const]
        using (memLp_top_const (0 : ℝ) : MemLp (fun _ : ℝ^n ↦ (0 : ℝ))
          ∞ (domainMeasure n Ω))
  let A (i j : Fin n) : W^{1,∞}(Ω) :=
    mkWkpSpaceOnOfContDiffMemLp (fun _ ↦ if i = j then (1 : ℝ) else 0)
      contDiff_const (hmem _)
  let a (i j : Fin n) : DerivLp n ∞ Ω :=
    (A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1)
  have ha (i j : Fin n) : (a i j : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun _ ↦ if i = j then 1 else 0 := by
    simpa only [a, A, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiffMemLp_apply_ae
        (fun _ : ℝ^n ↦ if i = j then (1 : ℝ) else 0) contDiff_const
        (hmem _) (baseIndex n 1)
  have hda (i j k : Fin n) :
      ((A i j : WkpAmbientOn n 1 ∞ Ω) (singleDerivIndex n k) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun _ ↦ 0 := by
    simpa only [A, singleDerivIndex_toList, iteratedPartialDeriv, PDE.partialDeriv_const]
      using mkWkpSpaceOnOfContDiffMemLp_apply_ae
        (fun _ : ℝ^n ↦ if i = j then (1 : ℝ) else 0) contDiff_const
        (hmem _) (singleDerivIndex n k)
  have hop := multiplicationCoefficientOperator_eq_identity_of_ae a ha
  have hz : IsWeakDivergenceSolution a (-f) z :=
    (isWeakSolution_iff_isWeakDivergenceSolution hΩ a (-f) z).mp fun v ↦ by
      rw [hop, variableCoeffForm_identity, dirichletForm_apply, loadFunctional_apply]
      exact poisson_weakForm_of_integral_laplacian_eq (z : H¹(Ω)) f hweak v
  obtain ⟨w, hw, g, hg, _, hgw⟩ :=
    exists_localized_weakDivergenceSolution hΩ A z (-f) hz η
  obtain rfl : w = cutoffH10 hΩ η z :=
    baseCoordCLM_injective hΩ (Lp.ext (hw.trans (cutoffCLM_base_apply_ae η (z : H¹(Ω))).symm))
  refine ⟨-g, ?_, ?_⟩
  · filter_upwards [hg, ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ ha i j,
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun k ↦ hda i j k,
      Lp.coeFn_neg g, Lp.coeFn_neg f] with x hx hax hdx hneg hnegf
    change ∀ i j, (A i j : WkpAmbientOn n 1 ∞ Ω) (baseIndex n 1) x =
      if i = j then 1 else 0 at hax
    rw [hneg, Pi.neg_apply, hx, hnegf]
    simp only [Pi.neg_apply, hax, hdx, zero_mul, add_zero, iteratedPartialDeriv, ite_mul,
      one_mul, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true, laplacian, mul_comm (derivCoordCLM _ z x), ← Finset.sum_mul]
    ring
  · intro φ
    have heq := (isWeakSolution_iff_isWeakDivergenceSolution hΩ a g
      (cutoffH10 hΩ η z)).mpr hgw (testFunctionToH10 φ)
    rw [hop, variableCoeffForm_identity, dirichletForm_apply, loadFunctional_apply] at heq
    change (∑ i : Fin n,
      ⟪((cutoffH10 hΩ η z : H¹(Ω)) : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i),
        derivCoordCLM i (testFunctionToH10 φ)⟫_ℝ) = _ at heq
    rw [sum_inner_deriv_test_eq_neg_integral_laplacian] at heq
    rw [← inner_base_testFunction_eq_integral, inner_neg_left, ← heq, neg_neg]

/-- The cutoff state has a representative whose zero extension is compactly
supported inside the support of the cutoff. This formulation is independent of
the representatives selected internally for the L² coordinates. -/
theorem exists_compact_representative_cutoffH10
    (hΩ : IsOpen Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (z : H¹₀(Ω)) :
    ∃ u : ℝ^n → ℝ,
      (baseCoordCLM (cutoffH10 hΩ η z) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] u ∧
      HasCompactSupport (Ω.indicator u) ∧
      tsupport (Ω.indicator u) ⊆ tsupport η.toFun := by
  let u : ℝ^n → ℝ := fun x ↦ η.toFun x * baseCoordCLM z x
  have hs : tsupport (Ω.indicator u) ⊆ tsupport η.toFun := by
    have hind : Ω.indicator u = fun x ↦ η.toFun x *
        Ω.indicator (baseCoordCLM z : ℝ^n → ℝ) x :=
      funext fun _ ↦ Set.indicator_mul_right _ _ _
    rw [hind]
    exact tsupport_mul_subset_left
  refine ⟨u, cutoffCLM_base_apply_ae η (z : H¹(Ω)), ?_, hs⟩
  exact η.hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) hs

end SobolevSpace.GraphSpace
