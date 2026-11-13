/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.Slice
public import PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov.FluxEstimates
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Doubling the scalar entropy inequality

Fixing either spacetime variable in a compactly supported `C¹` test gives an admissible
test for the other solution. Local integrability on the two compact support projections
justifies integrating these frozen-state inequalities and applying Fubini.

The resulting inequality holds on the product of two open spacetime domains. It is the
doubled inequality (45) of Evans, §11.4.3, which step 2 of the proof of Theorem 3 obtains by
adding the integrated frozen-state inequalities (43) and (44).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.4.3, proof of Theorem 3, step 2, equations (42)-(45).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open PDE.Common
open scoped Distributions Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

/-- The open domain of the two independent spacetime variables. -/
def productDomain (U V : Opens ℝ^2) : Opens (ℝ^2 × ℝ^2) :=
  ⟨(U : Set ℝ^2) ×ˢ (V : Set ℝ^2), U.isOpen.prod V.isOpen⟩

variable {U V : Opens ℝ^2}

/-- Freeze the second spacetime variable of a `C¹` product test. -/
def sliceLeft (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (y : ℝ^2) : 𝓓^{1}(U, ℝ) where
  toFun x := Ψ (x, y)
  contDiff' := Ψ.contDiff.comp (contDiff_prodMk_left y)
  hasCompactSupport' := by
    have hK := (TestFunction.isProperMap_prodMk_left y).isCompact_preimage Ψ.hasCompactSupport
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage Ψ (Continuous.prodMk_left y))
  tsupport_subset' :=
    fun x hx ↦ (Ψ.tsupport_subset
      (tsupport_comp_subset_preimage Ψ (Continuous.prodMk_left y) hx)).1

/-- Freeze the first spacetime variable of a `C¹` product test. -/
def sliceRight (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (x : ℝ^2) : 𝓓^{1}(V, ℝ) where
  toFun y := Ψ (x, y)
  contDiff' := Ψ.contDiff.comp (contDiff_prodMk_right x)
  hasCompactSupport' := by
    have hK := (TestFunction.isProperMap_prodMk_right x).isCompact_preimage Ψ.hasCompactSupport
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage Ψ (Continuous.prodMk_right x))
  tsupport_subset' :=
    fun y hy ↦ (Ψ.tsupport_subset
      (tsupport_comp_subset_preimage Ψ (Continuous.prodMk_right x) hy)).2

/-- Slicing retains the derivative in the first spacetime variable. -/
theorem partialDeriv_sliceLeft (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (x y : ℝ^2) (i : Fin 2) :
    (∂[i] ((sliceLeft Ψ y) : ℝ^2 → ℝ)) x = fderiv ℝ Ψ (x, y) (EuclideanSpace.single i 1, 0) := by
  unfold partialDeriv
  change (fderiv ℝ (⇑Ψ ∘ fun z : ℝ^2 ↦ (z, y)) x) _ = _
  rw [((Ψ.contDiff.differentiable_one (x, y)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left x y)).fderiv]
  simp

/-- Slicing retains the derivative in the second spacetime variable. -/
theorem partialDeriv_sliceRight (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (x y : ℝ^2) (i : Fin 2) :
    (∂[i] ((sliceRight Ψ x) : ℝ^2 → ℝ)) y = fderiv ℝ Ψ (x, y) (0, EuclideanSpace.single i 1) := by
  unfold partialDeriv
  change (fderiv ℝ (⇑Ψ ∘ Prod.mk x) y) _ = _
  rw [((Ψ.contDiff.differentiable_one (x, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right x y)).fderiv]
  simp

/-- A fixed directional derivative of a `C¹` product test is continuous. -/
theorem continuous_test_deriv (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (d : ℝ^2 × ℝ^2) :
    Continuous (fun p ↦ fderiv ℝ Ψ p d) :=
  (Ψ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- A fixed directional derivative of a product test has compact support. -/
theorem hasCompactSupport_test_deriv (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (d : ℝ^2 × ℝ^2) :
    HasCompactSupport (fun p ↦ fderiv ℝ Ψ p d) :=
  Ψ.hasCompactSupport.fderiv_apply ℝ d

/-- Integrability on compact rectangles suffices for testing against a product derivative.
The rectangle used in the proof is the product of the two support projections. -/
theorem integrable_mul_test_deriv (Ψ : 𝓓^{1}(productDomain U V, ℝ))
    (d : ℝ^2 × ℝ^2) {g : ℝ^2 × ℝ^2 → ℝ}
    (hg : ∀ K L : Set ℝ^2, K ⊆ U → L ⊆ V → IsCompact K → IsCompact L →
      Integrable g ((volume.restrict K).prod (volume.restrict L))) :
    Integrable (fun p ↦ g p * fderiv ℝ Ψ p d) volume := by
  let K := Prod.fst '' tsupport (Ψ : ℝ^2 × ℝ^2 → ℝ)
  let L := Prod.snd '' tsupport (Ψ : ℝ^2 × ℝ^2 → ℝ)
  have hK : IsCompact K := Ψ.hasCompactSupport.image continuous_fst
  have hL : IsCompact L := Ψ.hasCompactSupport.image continuous_snd
  have hKU : K ⊆ U := by
    rintro x ⟨p, hp, rfl⟩
    exact (Ψ.tsupport_subset hp).1
  have hLV : L ⊆ V := by
    rintro y ⟨p, hp, rfl⟩
    exact (Ψ.tsupport_subset hp).2
  obtain ⟨C, hC⟩ := (continuous_test_deriv Ψ d).bounded_above_of_compact_support
    (hasCompactSupport_test_deriv Ψ d)
  have hi := (hg K L hKU hLV hK hL).mul_bdd
    (continuous_test_deriv Ψ d).aestronglyMeasurable (Eventually.of_forall hC)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hi
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero hi fun p hp ↦ ?_
  have hps : p ∉ tsupport (Ψ : ℝ^2 × ℝ^2 → ℝ) := fun h ↦ hp ⟨⟨p, h, rfl⟩, ⟨p, h, rfl⟩⟩
  simp [fderiv_of_notMem_tsupport ℝ hps]

/-- The doubled entropy density times any test derivative is integrable. -/
theorem integrable_abs_sub_mul_test_deriv {u v : ℝ^2 → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hv : LocallyIntegrableOn v V volume) (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (d : ℝ^2 × ℝ^2) :
    Integrable (fun p ↦ |u p.1 - v p.2| * fderiv ℝ Ψ p d) volume := by
  refine integrable_mul_test_deriv Ψ d fun K L hKU hLV hK hL ↦ ?_
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (volume.restrict L) := isFiniteMeasure_restrict.mpr hL.measure_ne_top
  have huK := (hu.integrableOn_compact_subset hKU hK).comp_fst (volume.restrict L)
  have hvL := (hv.integrableOn_compact_subset hLV hL).comp_snd (volume.restrict K)
  exact (huK.sub hvL).norm

/-- The doubled flux times any test derivative is integrable. Local integrability of the physical
fluxes suffices. -/
theorem integrable_flux_mul_test_deriv {flux : ℝ → ℝ} (hf : Measurable flux) {u v : ℝ^2 → ℝ}
    (hu : LocallyIntegrableOn u U volume) (hv : LocallyIntegrableOn v V volume)
    (hfu : LocallyIntegrableOn (flux ∘ u) U volume) (hfv : LocallyIntegrableOn (flux ∘ v) V volume)
    (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (d : ℝ^2 × ℝ^2) :
    Integrable (fun p ↦ kruzhkovFlux flux (v p.2) (u p.1) * fderiv ℝ Ψ p d) volume := by
  refine integrable_mul_test_deriv Ψ d fun K L hKU hLV hK hL ↦ ?_
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
  let : IsFiniteMeasure (volume.restrict L) := isFiniteMeasure_restrict.mpr hL.measure_ne_top
  have huK := (hu.integrableOn_compact_subset hKU hK).aestronglyMeasurable.comp_fst
    (ν := volume.restrict L)
  have hvL := (hv.integrableOn_compact_subset hLV hL).aestronglyMeasurable.comp_snd
    (μ := volume.restrict K)
  have hmeas := ((measurable_kruzhkovFlux hf).comp_aemeasurable
    (hvL.prodMk huK).aemeasurable).aestronglyMeasurable
  have hfuK := (hfu.integrableOn_compact_subset hKU hK).comp_fst (volume.restrict L)
  have hfvL := (hfv.integrableOn_compact_subset hLV hL).comp_snd (volume.restrict K)
  exact (hfuK.sub hfvL).norm.mono' hmeas
    (Eventually.of_forall fun p ↦ norm_kruzhkovFlux_le flux (v p.2) (u p.1))

end PDE.Hyperbolic.ConservationLaw.Scalar.Kruzhkov

namespace PDE.Hyperbolic.ConservationLaw.Scalar

open Kruzhkov

/-- The entropy difference tested in both spacetime variables.
The directions `(eᵢ, eᵢ)` express the sums of the two time or space derivatives. -/
def doubledWeakIntegrand (flux : ℝ → ℝ) (u v : ℝ^2 → ℝ)
    {U V : Opens ℝ^2} (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (p : ℝ^2 × ℝ^2) : ℝ :=
  |u p.1 - v p.2| *
      fderiv ℝ Ψ p (EuclideanSpace.single 0 1, EuclideanSpace.single 0 1) +
    kruzhkovFlux flux (v p.2) (u p.1) *
      fderiv ℝ Ψ p (EuclideanSpace.single 1 1, EuclideanSpace.single 1 1)

/-- The doubled entropy integrand is integrable for two weak solutions with measurable flux. -/
theorem IsWeakSolution.integrable_doubledWeakIntegrand {flux : ℝ → ℝ} {U V : Opens ℝ^2}
    {u v : ℝ^2 → ℝ} (hu : IsWeakSolution flux U u) (hv : IsWeakSolution flux V v)
    (hf : Measurable flux) (Ψ : 𝓓^{1}(productDomain U V, ℝ)) :
    Integrable (doubledWeakIntegrand flux u v Ψ) volume :=
  (integrable_abs_sub_mul_test_deriv hu.u_locallyIntegrable hv.u_locallyIntegrable Ψ _).add
    (integrable_flux_mul_test_deriv hf hu.u_locallyIntegrable hv.u_locallyIntegrable
      hu.flux_locallyIntegrable hv.flux_locallyIntegrable Ψ _)

/-- Two locally essentially bounded entropy weak solutions satisfy the doubled Kružkov
inequality for every nonnegative compactly supported `C¹` test on the product domain.

The proof derives the constant-state inequalities from smooth convex entropies, freezes
each solution as the other's entropy center, and applies Fubini to integrable functions.
The variables remain independent; no diagonal limit is taken. -/
theorem IsEntropyWeakSolution.doubling_inequality {flux : ℝ → ℝ} {U V : Opens ℝ^2} {u v : ℝ^2 → ℝ}
    (hu : IsEntropyWeakSolution flux U u) (hv : IsEntropyWeakSolution flux V v)
    (hf : ContDiff ℝ 1 flux)
    (hbu : ∀ K : Set ℝ^2, K ⊆ U → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖u x‖ ≤ M)
    (hbv : ∀ K : Set ℝ^2, K ⊆ V → IsCompact K → ∃ M : ℝ, ∀ᵐ x ∂volume.restrict K, ‖v x‖ ≤ M)
    (Ψ : 𝓓^{1}(productDomain U V, ℝ)) (hΨ : ∀ p, 0 ≤ Ψ p) :
    0 ≤ ∫ p, doubledWeakIntegrand flux u v Ψ p := by
  have hku := hu.satisfiesKruzhkovInequality hf hbu
  have hkv := hv.satisfiesKruzhkovInequality hf hbv
  let A : ℝ^2 × ℝ^2 → ℝ := fun p ↦
    |u p.1 - v p.2| * fderiv ℝ Ψ p (EuclideanSpace.single 0 1, 0) +
      kruzhkovFlux flux (v p.2) (u p.1) * fderiv ℝ Ψ p (EuclideanSpace.single 1 1, 0)
  let B : ℝ^2 × ℝ^2 → ℝ := fun p ↦
    |u p.1 - v p.2| * fderiv ℝ Ψ p (0, EuclideanSpace.single 0 1) +
      kruzhkovFlux flux (v p.2) (u p.1) * fderiv ℝ Ψ p (0, EuclideanSpace.single 1 1)
  have hAi : Integrable A volume := (integrable_abs_sub_mul_test_deriv
      hu.weak.u_locallyIntegrable hv.weak.u_locallyIntegrable Ψ _).add
        (integrable_flux_mul_test_deriv hf.continuous.measurable
          hu.weak.u_locallyIntegrable hv.weak.u_locallyIntegrable
          hu.weak.flux_locallyIntegrable hv.weak.flux_locallyIntegrable Ψ _)
  have hBi : Integrable B volume := (integrable_abs_sub_mul_test_deriv
      hu.weak.u_locallyIntegrable hv.weak.u_locallyIntegrable Ψ _).add
        (integrable_flux_mul_test_deriv hf.continuous.measurable
          hu.weak.u_locallyIntegrable hv.weak.u_locallyIntegrable
          hu.weak.flux_locallyIntegrable hv.weak.flux_locallyIntegrable Ψ _)
  have hA : 0 ≤ ∫ p, A p := by
    rw [Measure.volume_eq_prod, integral_prod_symm _ hAi]
    refine integral_nonneg fun y ↦ ?_
    change (0 : ℝ) ≤ ∫ x, A (x, y)
    simpa only [A, kruzhkovWeakIntegrand, partialDeriv_sliceLeft] using
      (hku (v y)).2.2 (sliceLeft Ψ y) (fun x ↦ hΨ (x, y))
  have hB : 0 ≤ ∫ p, B p := by
    rw [Measure.volume_eq_prod, integral_prod _ hBi]
    refine integral_nonneg fun x ↦ ?_
    change (0 : ℝ) ≤ ∫ y, B (x, y)
    simpa only [B, kruzhkovWeakIntegrand, partialDeriv_sliceRight,
      abs_sub_comm (v _) (u _), kruzhkovFlux_comm flux (u _) (v _)] using
        (hkv (u x)).2.2 (sliceRight Ψ x) (fun y ↦ hΨ (x, y))
  have hsum : doubledWeakIntegrand flux u v Ψ = fun p ↦ A p + B p := by
    funext p
    have hd (i : Fin 2) : fderiv ℝ Ψ p (EuclideanSpace.single i 1, EuclideanSpace.single i 1) =
          fderiv ℝ Ψ p (EuclideanSpace.single i 1, 0) +
            fderiv ℝ Ψ p (0, EuclideanSpace.single i 1) := by
      simpa using (fderiv ℝ Ψ p).map_add (EuclideanSpace.single i 1, 0)
        (0, EuclideanSpace.single i 1)
    simp only [doubledWeakIntegrand, hd, mul_add, A, B]
    abel
  rw [hsum, integral_add hAi hBi]
  exact add_nonneg hA hB

end PDE.Hyperbolic.ConservationLaw.Scalar
