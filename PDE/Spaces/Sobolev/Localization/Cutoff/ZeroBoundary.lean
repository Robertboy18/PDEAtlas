/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff
public import PDE.Spaces.Sobolev.Variational.Spaces.H1
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.ZeroTrace.CompactSupport
import PDE.Spaces.Sobolev.Localization.Cutoff.CompactSupport

/-!
# Localized Sobolev fields as zero-boundary test functions

The proof of interior `H²` regularity in Evans §6.3.1, Theorem 1, tests the weak formulation
with products of a Sobolev field and a smooth cutoff compactly supported in the domain, such as
`ζ² u` in step 7. Such a product is an element of `H¹₀(Ω)`. The proof below is valid for every
open domain: it constructs the global zero extension, proves its weak derivatives by
compact-support localization, and invokes support-controlled mollification.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.1, proof of Theorem 1, pp. 328-331.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Function ENNReal
open CompactSupportLocalization
open scoped Topology

variable {n : ℕ} {Ω : Set (ℝ^n)}


/-- Multiplication by a smooth cutoff compactly supported in an open domain
maps `H¹(Ω)` into `H¹₀(Ω)`. -/
theorem cutoffCLM_mem_H10
    (hΩopen : IsOpen Ω) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hψΩ : tsupport ψ.toFun ⊆ Ω) (U : H¹(Ω)) :
    cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ U ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  set K : Set (ℝ^n) := tsupport ψ.toFun
  have hK : IsCompact K := ψ.hasCompactSupport
  obtain ⟨χ, hχΩ, -, hχnhds, -⟩ := TestFunction.exists_eq_one_on_compact hΩopen hK hψΩ
  set V : W^{1,2}(Ω) := cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ U
  -- the coordinates of `V` cut off to `K` and extended by zero to `ℝⁿ`
  let e (a : DerivIndex n 1) : ℝ^n → ℝ :=
    K.indicator ((V : WkpAmbientOn n 1 2 Ω) a : DerivLp n 2 Ω)
  have he (a : DerivIndex n 1) : MemLp (e a) 2 (domainMeasure n Set.univ) :=
    memLp_of_support_subset_of_subset hΩopen.measurableSet (subset_univ Ω)
      (support_indicator_subset.trans hψΩ)
      ((Lp.memLp _).indicator hK.measurableSet.nullMeasurableSet)
  have hweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn (n := n) Set.univ a.toList (e (baseIndex n 1)) (e a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa [iteratedPartialDeriv] using
        hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain (he _) (by norm_num))
    have hVweak := V.property.hasWeakDerivativeOn_first (by norm_num) i
    rw [firstDerivIndex_one] at hVweak
    rw [singleDerivIndex_toList]
    exact hasWeakDerivativeOn_univ_of_support_subset_of_cutoff_one_nhds hΩopen hψΩ
      support_indicator_subset support_indicator_subset χ hχΩ hχnhds
      ((hasWeakDerivativeOn_congr_ae (α := [i])
        (cutoffCLM_base_tsupport_indicator_ae (n := n) (p := 2) ψ U)
        (cutoffCLM_singleDeriv_tsupport_indicator_ae (n := n) (p := 2) ψ U i)).2 hVweak)
  let W : W^{1,2}(ℝ^n) := mkWkpSpaceOnOfWeakDerivatives _ e rfl he hweak
  have hW := mkWkpSpaceOnOfWeakDerivatives_apply_ae _ e rfl he hweak (baseIndex n 1)
  have hVW : V = restrictCLM (n := n) (k := 1) (p := 2) hΩopen.measurableSet (subset_univ Ω) W :=
    WkpSpaceOn.ext_of_base_ae hΩopen _ _ <|
      (cutoffCLM_base_tsupport_indicator_ae (n := n) (p := 2) ψ U).symm.trans <|
        (hW.filter_mono (ae_mono (Measure.restrict_mono (subset_univ Ω) le_rfl))).symm.trans
          (restrictCLM_apply_ae hΩopen.measurableSet (subset_univ Ω) W _).symm
  have hsupp : tsupport (e (baseIndex n 1)) ⊆ K :=
    closure_minimal support_indicator_subset hK.isClosed
  rw [hVW]
  exact restrict_mem_H10_of_tsupport_subset hΩopen W _ (by simpa [domainMeasure] using hW)
    (hK.of_isClosed_subset (isClosed_tsupport _) hsupp) (hsupp.trans hψΩ)

/-- Multiplication by an arbitrary global smooth compactly supported function
preserves `H¹₀(Ω)`.  Unlike `cutoffCLM_mem_H10`, the cutoff need not be
supported inside `Ω`: this is the form required by boundary partitions of
unity, whose cutoffs generally cross `∂Ω`.

The proof is the defining density argument for `H¹₀`.  On the
`C_c^∞(Ω)` core, the product is again a compactly supported smooth function
with support in `Ω`; continuity of `cutoffCLM` then extends the claim to the
closure. -/
theorem cutoffCLM_mem_H10_of_mem_H10
    (hΩopen : IsOpen Ω) (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : H¹₀(Ω)) :
    cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ (u : H¹(Ω)) ∈
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  set T := cutoffCLM (n := n) (p := 2) (Ω := Ω) ψ
  have hmaps : Set.MapsTo T (ccSmoothSubmoduleOn (n := n) (Ω := Ω) : Submodule ℝ (H¹(Ω)))
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
    rintro v ⟨φ, rfl⟩
    let productTest : TestFunctionOn n Ω := ⟨TestFunction.mul ψ φ.1,
      (show tsupport (fun x ↦ ψ.toFun x * φ.1.toFun x) ⊆ _ from tsupport_mul_subset_right).trans
        φ.2⟩
    have hproduct : T (testFunctionToH1 φ) = testFunctionToH1 productTest := by
      refine WkpSpaceOn.ext_of_base_ae hΩopen _ _ <| (cutoffCLM_base_apply_ae ψ _).trans ?_
      filter_upwards [mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
          _ φ.1.contDiff φ.1.hasCompactSupport (baseIndex n 1),
        mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
          _ productTest.1.contDiff productTest.1.hasCompactSupport (baseIndex n 1)] with x h₁ h₂
      simp only [baseIndex_toList, iteratedPartialDeriv] at h₁ h₂
      exact (congrArg (ψ.toFun x * ·) h₁).trans h₂.symm
    exact hproduct ▸ testFunctionToH1_mem_H10 productTest
  exact (h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.closure_subset
    (hmaps.closure T.continuous (H10SpaceOn.mem_closure_CcSmooth u))

/-!
## Continuous linear cutoff maps
-/

/-- Multiplication by a smooth cutoff supported inside `Ω`, as a continuous
linear map from `H¹(Ω)` to `H¹₀(Ω)`. No boundary condition is required of the
input. -/
noncomputable def cutoffH1ToH10
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) :
    H¹(Ω) →L[ℝ] H¹₀(Ω) :=
  ContinuousLinearMap.codRestrict
    (cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ)
    (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule
    (cutoffCLM_mem_H10 hΩopen ρ hρΩ)

/-- Forgetting the zero-trace codomain of an interior cutoff recovers
ordinary cutoff multiplication on `H¹(Ω)`. -/
@[simp]
theorem cutoffH1ToH10_apply_coe
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hρΩ : tsupport ρ.toFun ⊆ Ω) (u : H¹(Ω)) :
    ((cutoffH1ToH10 hΩopen ρ hρΩ u :
        H¹₀(Ω)) : H¹(Ω)) =
      cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ u :=
  rfl

/-- Multiplication by an arbitrary global smooth compactly supported
function, as a continuous linear endomorphism of `H¹₀(Ω)`. -/
noncomputable def cutoffH10
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    H¹₀(Ω) →L[ℝ]
      H¹₀(Ω) :=
  ContinuousLinearMap.codRestrict
    ((cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ).comp
      (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule.subtypeL)
    (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule
    (cutoffCLM_mem_H10_of_mem_H10 hΩopen ρ)

/-- Forgetting the zero-trace codomain of a zero-trace cutoff recovers
ordinary cutoff multiplication on the underlying `H¹(Ω)` field. -/
@[simp]
theorem cutoffH10_apply_coe
    (hΩopen : IsOpen Ω) (ρ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : H¹₀(Ω)) :
    ((cutoffH10 hΩopen ρ u :
        H¹₀(Ω)) : H¹(Ω)) =
      cutoffCLM (n := n) (p := 2) (Ω := Ω) ρ (u : H¹(Ω)) :=
  rfl

end SobolevSpace.GraphSpace
