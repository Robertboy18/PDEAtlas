/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.FiniteSums
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# `H¹` and `H¹₀` under linear isometries

Let `h` be a linear isometry of `ℝ^n` mapping an open set `Ω` onto itself
(`IsIsometryInvariant h Ω`), such as the whole space or a centred ball. For `f ∈ L²(Ω)` with weak
derivatives `Gₖ ∈ L²(Ω)`, the function `f ∘ h⁻¹` has the weak derivatives
`∂ⱼ(f ∘ h⁻¹) = Σₖ (h⁻¹ eⱼ)ₖ Gₖ ∘ h⁻¹` (`hasWeakDerivativeOn_comp_linearIsometryEquiv_of_invariant`),
by a change of variables in the defining integral identity. The coefficient matrix is
orthogonal, so composition with `h⁻¹` is a linear isometry equivalence of `H¹(Ω)` (`h1Isometry`)
that preserves zero boundary values. Mixing the components of a vector field by the matrix of
`h` as well gives the transform `w ↦ h ∘ w ∘ h⁻¹` as linear isometry equivalences of
`H¹(Ω; ℝ^n)` (`velocityIsometry`) and of `H¹₀(Ω; ℝ^n)` (`zeroBoundaryVelocityIsometry`); the
latter carries the divergence to the transformed divergence.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped RealInnerProductSpace Sobolev Distributions ContDiff

namespace SobolevSpace

set_option linter.missingDocs true

variable {n : ℕ}

/-- A linear isometry mapping a measurable set onto itself preserves Lebesgue measure restricted
to the set. -/
theorem measurePreserving_restrict_of_invariant (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {Ω : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hinv : ∀ x, h x ∈ Ω ↔ x ∈ Ω) :
    MeasurePreserving h (volume.restrict Ω) (volume.restrict Ω) := by
  have hpre : h ⁻¹' Ω = Ω := Set.ext hinv
  have := h.measurePreserving.restrict_preimage hΩ
  rwa [hpre] at this

/-- First weak derivatives on a domain invariant under a linear isometry transform by the
inverse transpose of the isometry. -/
theorem hasWeakDerivativeOn_comp_linearIsometryEquiv_of_invariant (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω) (hinv : ∀ x, h x ∈ Ω ↔ x ∈ Ω) {f : ℝ^n → ℝ}
    {G : Fin n → ℝ^n → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hG : ∀ k, MemLp (G k) 2 (volume.restrict Ω))
    (hw : ∀ k, HasWeakDerivativeOn Ω [k] f (G k)) (j : Fin n) :
    HasWeakDerivativeOn Ω [j] (fun x ↦ f (h.symm x))
      (fun x ↦ ∑ k, (h.symm (EuclideanSpace.single j 1)) k * G k (h.symm x)) := by
  set c := h.symm (EuclideanSpace.single j (1 : ℝ))
  set μ := volume.restrict Ω
  have hinv' : ∀ x, h.symm x ∈ Ω ↔ x ∈ Ω := fun x ↦ by
    rw [← hinv (h.symm x), LinearIsometryEquiv.apply_symm_apply]
  have hmp : MeasurePreserving h μ μ := measurePreserving_restrict_of_invariant h hΩ hinv
  have hmp' : MeasurePreserving h.symm μ μ :=
    measurePreserving_restrict_of_invariant h.symm hΩ hinv'
  have hf' : MemLp (fun x ↦ f (h.symm x)) 2 μ := hf.comp_measurePreserving hmp'
  have hG' : MemLp (fun x ↦ ∑ k, c k * G k (h.symm x)) 2 μ :=
    memLp_finsetSum _ fun k _ ↦ ((hG k).comp_measurePreserving hmp').const_mul (c k)
  refine ⟨memLp_locallyIntegrableOn_domain hf' (by norm_num),
    memLp_locallyIntegrableOn_domain hG' (by norm_num), fun φ hφΩ ↦ ?_⟩
  simp only [domainMeasure, iteratedPartialDeriv, List.length_singleton, pow_one, neg_one_mul]
  have hsuppψ : tsupport (fun y ↦ φ.toFun (h y)) ⊆ Ω := by
    intro y hy
    have hts : tsupport (fun y ↦ φ.toFun (h y)) = h ⁻¹' tsupport φ.toFun :=
      tsupport_comp_eq_preimage φ.toFun h.toHomeomorph
    have hy' : h y ∈ tsupport φ.toFun := by
      rw [hts] at hy
      exact hy
    exact (hinv y).mp (hφΩ hy')
  let ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ) :=
    _root_.TestFunction.mk (fun y ↦ φ.toFun (h y)) (φ.contDiff.comp h.contDiff)
      (φ.hasCompactSupport.comp_homeomorph h.toHomeomorph) (subset_univ _)
  have hψ : ContDiff ℝ ∞ (fun y ↦ φ.toFun (h y)) := φ.contDiff.comp h.contDiff
  have hψc : HasCompactSupport (fun y ↦ φ.toFun (h y)) :=
    φ.hasCompactSupport.comp_homeomorph h.toHomeomorph
  have hφd : Differentiable ℝ φ.toFun := φ.contDiff.differentiable (by simp)
  have hchain (y : ℝ^n) :
      PDE.partialDeriv j φ.toFun (h y) =
        ∑ k, c k * PDE.partialDeriv k (fun z ↦ φ.toFun (h z)) y := by
    have hcomp : HasFDerivAt (fun z ↦ φ.toFun (h z))
        ((fderiv ℝ φ.toFun (h y)).comp h.toContinuousLinearEquiv.toContinuousLinearMap) y :=
      (hφd _).hasFDerivAt.comp y h.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    have hsum := PDE.fderiv_apply_eq_sum_smul_partialDeriv (fun z ↦ φ.toFun (h z)) y c
    have hc : h.toContinuousLinearEquiv.toContinuousLinearMap c = EuclideanSpace.single j 1 :=
      h.apply_symm_apply _
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, hc] at hsum
    simp only [smul_eq_mul] at hsum
    exact hsum
  have hdψ (k : Fin n) : MemLp (PDE.partialDeriv k (fun z ↦ φ.toFun (h z))) 2 μ :=
    ((hψ.partialDeriv k (k := 0) (hkr := by simp)).continuous.memLp_of_hasCompactSupport
      (hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ)))).restrict Ω
  have hψ2 : MemLp (fun z ↦ φ.toFun (h z)) 2 μ :=
    (hψ.continuous.memLp_of_hasCompactSupport hψc).restrict Ω
  have hid (k : Fin n) : ∫ y, f y * PDE.partialDeriv k (fun z ↦ φ.toFun (h z)) y ∂μ =
      -∫ y, G k y * φ.toFun (h y) ∂μ := by
    have hk := (hw k).integral_identity ψ hsuppψ
    simpa [domainMeasure, iteratedPartialDeriv, ψ] using hk
  have hint (k : Fin n) :
      Integrable (fun y ↦ f y * PDE.partialDeriv k (fun z ↦ φ.toFun (h z)) y) μ :=
    hf.integrable_mul (hdψ k)
  have hintG (k : Fin n) : Integrable (fun y ↦ G k y * φ.toFun (h y)) μ :=
    (hG k).integrable_mul hψ2
  have hcv {F : ℝ^n → ℝ} : ∫ x, F x ∂μ = ∫ y, F (h y) ∂μ :=
    (hmp.integral_comp h.toHomeomorph.measurableEmbedding F).symm
  calc ∫ x, f (h.symm x) * PDE.partialDeriv j φ.toFun x ∂μ
      = ∫ y, f y * ∑ k, c k * PDE.partialDeriv k (fun z ↦ φ.toFun (h z)) y ∂μ := by
        rw [hcv]
        simp only [LinearIsometryEquiv.symm_apply_apply, hchain]
    _ = ∑ k, c k * ∫ y, f y * PDE.partialDeriv k (fun z ↦ φ.toFun (h z)) y ∂μ := by
        simp only [Finset.mul_sum]
        rw [integral_finsetSum _ fun k _ ↦ (hint k).const_mul (c k) |>.congr
          (Filter.Eventually.of_forall fun y ↦ by simp only; ring)]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by simp only; ring)
    _ = -∫ y, (∑ k, c k * G k y) * φ.toFun (h y) ∂μ := by
        simp only [hid, mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.sum_mul]
        rw [integral_finsetSum _ fun k _ ↦ (hintG k).const_mul (c k) |>.congr
          (Filter.Eventually.of_forall fun y ↦ by simp only; ring)]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ by simp only; ring)
    _ = -∫ x, (∑ k, c k * G k (h.symm x)) * φ.toFun x ∂μ := by
        rw [hcv (F := fun x ↦ (∑ k, c k * G k (h.symm x)) * φ.toFun x)]
        simp only [LinearIsometryEquiv.symm_apply_apply]

/-- First weak derivatives on the whole space transform under a linear isometry by its inverse
transpose. -/
theorem hasWeakDerivativeOn_comp_linearIsometryEquiv (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {f : ℝ^n → ℝ}
    {G : Fin n → ℝ^n → ℝ} (hf : MemLp f 2 volume) (hG : ∀ k, MemLp (G k) 2 volume)
    (hw : ∀ k, HasWeakDerivativeOn univ [k] f (G k)) (j : Fin n) :
    HasWeakDerivativeOn univ [j] (fun x ↦ f (h.symm x))
      (fun x ↦ ∑ k, (h.symm (EuclideanSpace.single j 1)) k * G k (h.symm x)) :=
  hasWeakDerivativeOn_comp_linearIsometryEquiv_of_invariant h MeasurableSet.univ
    (fun _ ↦ Iff.rfl) (by simpa only [Measure.restrict_univ] using hf)
    (fun k ↦ by simpa only [Measure.restrict_univ] using hG k) hw j

/-- An orthogonal change of coordinates preserves sums of squared norms. -/
theorem sum_norm_sq_orthogonal_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {m : ℕ} (c : Fin m → Fin m → ℝ)
    (hc : ∀ k l, ∑ j, c j k * c j l = if k = l then 1 else 0) (V : Fin m → E) :
    ∑ j, ‖∑ k, c j k • V k‖ ^ 2 = ∑ k, ‖V k‖ ^ 2 := by
  have hexp (j : Fin m) : ‖∑ k, c j k • V k‖ ^ 2 =
      ∑ k, ∑ l, c j k * c j l * ⟪V k, V l⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  simp only [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hc, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, real_inner_self_eq_norm_sq]

/-- The coordinate matrix of a linear isometry has orthonormal columns. -/
theorem sum_coord_mul_coord_isometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (k l : Fin n) :
    ∑ j, (h (EuclideanSpace.single k 1)) j * (h (EuclideanSpace.single l 1)) j =
      if k = l then 1 else 0 := by
  rw [← EuclideanSpace.real_inner_eq_sum, h.inner_map_map, EuclideanSpace.inner_single_left]
  by_cases hkl : k = l
  · subst hkl; simp
  · simp [hkl]

/-- A linear isometry `h` maps the measurable set `Ω` onto itself. -/
structure IsIsometryInvariant (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (Ω : Set (ℝ^n)) : Prop where
  /-- The set is measurable. -/
  measurableSet : MeasurableSet Ω
  /-- A point lies in the set exactly when its image does. -/
  mem_iff : ∀ x, h x ∈ Ω ↔ x ∈ Ω

/-- The inverse isometry maps an invariant set onto itself. -/
theorem IsIsometryInvariant.symm {h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n} {Ω : Set (ℝ^n)}
    (hΩ : IsIsometryInvariant h Ω) : IsIsometryInvariant h.symm Ω :=
  ⟨hΩ.measurableSet, fun x ↦ by rw [← hΩ.mem_iff (h.symm x), LinearIsometryEquiv.apply_symm_apply]⟩

/-- The whole space is invariant under every linear isometry. -/
theorem isIsometryInvariant_univ (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) : IsIsometryInvariant h Set.univ :=
  ⟨MeasurableSet.univ, fun _ ↦ Iff.rfl⟩

/-- An invariant set carries a measure-preserving action of the isometry. -/
theorem IsIsometryInvariant.measurePreserving {h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n} {Ω : Set (ℝ^n)}
    (hΩ : IsIsometryInvariant h Ω) : MeasurePreserving h (domainMeasure n Ω) (domainMeasure n Ω) :=
  measurePreserving_restrict_of_invariant h hΩ.measurableSet hΩ.mem_iff

end SobolevSpace

namespace SobolevSpace.GraphSpace

set_option linter.missingDocs true

open SobolevSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Composition with the inverse of a linear isometry on `L²` of an invariant set. -/
def l2CompSymm (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) :
    DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω :=
  (Lp.compMeasurePreservingₗᵢ ℝ h.symm hΩ.symm.measurePreserving).toContinuousLinearMap

/-- Composition with `h⁻¹` is pointwise composition almost everywhere. -/
theorem l2CompSymm_ae (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (F : DerivLp n 2 Ω) :
    l2CompSymm h hΩ F =ᵐ[domainMeasure n Ω] fun x ↦ F (h.symm x) :=
  Lp.coeFn_compMeasurePreserving F hΩ.symm.measurePreserving

/-- Composition with `h⁻¹` preserves `L²` norms. -/
theorem norm_l2CompSymm (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (F : DerivLp n 2 Ω) : ‖l2CompSymm h hΩ F‖ = ‖F‖ :=
  Lp.norm_compMeasurePreserving F _

/-- The coefficient `(h⁻¹ eⱼ)_k` of the derivative chain rule. -/
def isometryCoeff (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (j k : Fin n) : ℝ :=
  (h.symm (EuclideanSpace.single j 1)) k

/-- The first-order jet of `U ∘ h⁻¹` before restriction to the weak-derivative graph. -/
def h1CompSymmAmbient (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) :
    H¹(Ω) →L[ℝ] WkpAmbientOn n 1 2 Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivIndex n 1 ↦ DerivLp n 2 Ω)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (firstOrderRows ((l2CompSymm h hΩ).comp wkpBaseCoordinateCLM)
        (fun j ↦ ∑ k, isometryCoeff h j k •
          (l2CompSymm h hΩ).comp (wkpCoordinateCLM (singleDerivIndex n k)))))

/-- The base coordinate of the jet of `U ∘ h⁻¹`. -/
theorem h1CompSymmAmbient_base (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (U : H¹(Ω)) :
    h1CompSymmAmbient h hΩ U (baseIndex n 1) =
      l2CompSymm h hΩ ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) := by
  change firstOrderRows ((l2CompSymm h hΩ).comp wkpBaseCoordinateCLM)
    (fun j ↦ ∑ k, isometryCoeff h j k •
      (l2CompSymm h hΩ).comp (wkpCoordinateCLM (singleDerivIndex n k))) (baseIndex n 1) U = _
  rw [firstOrderRows_baseIndex]
  rfl

/-- The derivative coordinates of the jet of `U ∘ h⁻¹`. -/
theorem h1CompSymmAmbient_single (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (U : H¹(Ω)) (j : Fin n) :
    h1CompSymmAmbient h hΩ U (singleDerivIndex n j) =
      ∑ k, isometryCoeff h j k •
        l2CompSymm h hΩ ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k)) := by
  change firstOrderRows ((l2CompSymm h hΩ).comp wkpBaseCoordinateCLM)
    (fun j ↦ ∑ k, isometryCoeff h j k •
      (l2CompSymm h hΩ).comp (wkpCoordinateCLM (singleDerivIndex n k)))
      (singleDerivIndex n j) U = _
  rw [firstOrderRows_singleDerivIndex]
  simp [wkpCoordinateCLM_apply]

/-- The jet of `U ∘ h⁻¹` satisfies the weak-derivative relations. -/
theorem h1CompSymmAmbient_mem (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (U : H¹(Ω)) : h1CompSymmAmbient h hΩ U ∈ wkpSubmoduleOn n 1 2 Ω := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil
      (memLp_locallyIntegrableOn_domain (Lp.memLp (h1CompSymmAmbient h hΩ U (baseIndex n 1)))
        (by norm_num))
  · rw [singleDerivIndex_toList]
    have hw (k : Fin n) : HasWeakDerivativeOn Ω [k]
        ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : ℝ^n → ℝ)
        ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k) : ℝ^n → ℝ) := by
      simpa only [singleDerivIndex_toList] using U.property (singleDerivIndex n k)
    have hchain := hasWeakDerivativeOn_comp_linearIsometryEquiv_of_invariant h
      hΩ.measurableSet hΩ.mem_iff (Lp.memLp ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)))
      (fun k ↦ Lp.memLp ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k))) hw i
    refine hchain.congr_ae ?_ ?_
    · rw [h1CompSymmAmbient_base]
      exact (l2CompSymm_ae h hΩ _).symm
    · rw [h1CompSymmAmbient_single]
      have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun k ↦ isometryCoeff h i k •
        l2CompSymm h hΩ ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k)))
      have hk (k : Fin n) := Lp.coeFn_smul (isometryCoeff h i k)
        (l2CompSymm h hΩ ((U : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n k)))
      filter_upwards [hs, ae_all_iff.mpr hk,
        ae_all_iff.mpr fun k ↦ l2CompSymm_ae h hΩ ((U : WkpAmbientOn n 1 2 Ω)
          (singleDerivIndex n k))] with x hx hkx hcx
      rw [hx]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [hkx k, Pi.smul_apply, hcx k, smul_eq_mul]
      rfl

/-- Composition with the inverse of a linear isometry, as a continuous linear map of `H¹` of an
invariant set. -/
def h1CompSymmCLM (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) : H¹(Ω) →L[ℝ] H¹(Ω) :=
  (h1CompSymmAmbient h hΩ).codRestrict (wkpSubmoduleOn n 1 2 Ω) (h1CompSymmAmbient_mem h hΩ)

/-- The jet of the composed function. -/
theorem h1CompSymmCLM_coe (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) (U : H¹(Ω)) :
    (h1CompSymmCLM h hΩ U : WkpAmbientOn n 1 2 Ω) = h1CompSymmAmbient h hΩ U :=
  rfl

/-- The coefficient of the chain rule is the coordinate of the image of a basis vector. -/
theorem isometryCoeff_eq (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (j k : Fin n) :
    isometryCoeff h j k = (h (EuclideanSpace.single k 1)) j := by
  have h1 : (h.symm (EuclideanSpace.single j 1)) k =
      ⟪EuclideanSpace.single k 1, h.symm (EuclideanSpace.single j 1)⟫ := by
    rw [EuclideanSpace.inner_single_left]
    simp
  have h2 : (h (EuclideanSpace.single k 1)) j =
      ⟪EuclideanSpace.single j 1, h (EuclideanSpace.single k 1)⟫ := by
    rw [EuclideanSpace.inner_single_left]
    simp
  rw [isometryCoeff, h1, h2, ← h.inner_map_eq_flip, real_inner_comm]

/-- Composition with `h⁻¹` and then with `h` is the identity on `H¹` of an open invariant set. -/
theorem h1CompSymmCLM_h1CompSymmCLM_symm (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (U : H¹(Ω)) :
    h1CompSymmCLM h hΩ (h1CompSymmCLM h.symm hΩ.symm U) = U := by
  refine wkpBaseCoordinateCLM_injective hΩo (Lp.ext ?_)
  simp only [wkpBaseCoordinateCLM_apply, h1CompSymmCLM_coe, h1CompSymmAmbient_base]
  have h1 := l2CompSymm_ae h hΩ (l2CompSymm h.symm hΩ.symm
    ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)))
  have h2 := hΩ.symm.measurePreserving.quasiMeasurePreserving.ae
    (l2CompSymm_ae h.symm hΩ.symm ((U : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)))
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]
  simp

/-- Composition with the inverse of a linear isometry preserves the `H¹` norm. -/
theorem norm_h1CompSymmCLM (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) (U : H¹(Ω)) :
    ‖h1CompSymmCLM h hΩ U‖ = ‖U‖ := by
  have hsq : ‖(h1CompSymmCLM h hΩ U : WkpAmbientOn n 1 2 Ω)‖ ^ 2 =
      ‖(U : WkpAmbientOn n 1 2 Ω)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, sum_derivIndex_one, sum_derivIndex_one,
      h1CompSymmCLM_coe, h1CompSymmAmbient_base, norm_l2CompSymm]
    congr 1
    simp only [h1CompSymmAmbient_single]
    rw [sum_norm_sq_orthogonal_sum (isometryCoeff h) ?_]
    · simp only [norm_l2CompSymm]
    · intro k l
      simp only [isometryCoeff_eq]
      exact sum_coord_mul_coord_isometry h k l
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Composition with the inverse of a linear isometry of `ℝ^n`, as a linear isometry
equivalence of `H¹` of an open invariant set. -/
def h1Isometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) :
    H¹(Ω) ≃ₗᵢ[ℝ] H¹(Ω) where
  toLinearEquiv := LinearEquiv.ofLinearMap (h1CompSymmCLM h hΩ).toLinearMap
    (h1CompSymmCLM h.symm hΩ.symm).toLinearMap
    (LinearMap.ext fun U ↦ h1CompSymmCLM_h1CompSymmCLM_symm h hΩ hΩo U)
    (LinearMap.ext fun U ↦ by
      simpa using h1CompSymmCLM_h1CompSymmCLM_symm h.symm hΩ.symm hΩo U)
  norm_map' := norm_h1CompSymmCLM h hΩ

/-- A linear isometry applied to `v` is `Σₖ vₖ h eₖ`, coordinatewise. -/
theorem linearIsometryEquiv_apply_coord (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (v : ℝ^n) (i : Fin n) :
    (h v) i = ∑ k, v k * (h (EuclideanSpace.single k 1)) i := by
  rw [EuclideanSpace.map_eq_sum_smul_single h v, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [PiLp.smul_apply, smul_eq_mul]

/-- Mixing the components of a tuple by the matrix of a linear isometry `h` of `ℝ^n` after
applying an operator `P` to each component: `(w ↦ (Σₖ (h eₖ)ᵢ P wₖ)ᵢ)`. -/
def mixMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (P : E →L[ℝ] E) :
    PiLp 2 (fun _ : Fin n ↦ E) →L[ℝ] PiLp 2 (fun _ : Fin n ↦ E) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i ↦ ∑ k, (h (EuclideanSpace.single k 1)) i •
      P.comp (PiLp.proj 2 (fun _ : Fin n ↦ E) k))

/-- Components of the mixing map. -/
theorem mixMap_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (P : E →L[ℝ] E) (w : PiLp 2 (fun _ : Fin n ↦ E)) (i : Fin n) :
    mixMap h P w i = ∑ k, (h (EuclideanSpace.single k 1)) i • P (w k) := by
  simp [mixMap]

/-- Mixing by `h⁻¹` after `Q` is undone by mixing by `h` after `P` when `P ∘ Q = id`. -/
theorem mixMap_mixMap_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {P Q : E →L[ℝ] E} (hPQ : ∀ u, P (Q u) = u)
    (w : PiLp 2 (fun _ : Fin n ↦ E)) : mixMap h P (mixMap h.symm Q w) = w := by
  ext1 i
  rw [mixMap_apply]
  simp only [mixMap_apply, map_sum, map_smul, hPQ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hδ (l : Fin n) : ∑ k, (h (EuclideanSpace.single k 1)) i *
      (h.symm (EuclideanSpace.single l 1)) k = if l = i then 1 else 0 := by
    have := linearIsometryEquiv_apply_coord h (h.symm (EuclideanSpace.single l 1)) i
    rw [LinearIsometryEquiv.apply_symm_apply] at this
    simp only [mul_comm ((h (EuclideanSpace.single _ 1)) i)]
    rw [← this]
    simp [eq_comm]
  simp only [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- Mixing by an orthogonal matrix after a norm-preserving operator preserves the norm. -/
theorem norm_mixMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) {P : E →L[ℝ] E} (hP : ∀ u, ‖P u‖ = ‖u‖)
    (w : PiLp 2 (fun _ : Fin n ↦ E)) : ‖mixMap h P w‖ = ‖w‖ := by
  have hsq : ‖mixMap h P w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [mixMap_apply]
    have hm := sum_norm_sq_orthogonal_sum (E := E)
      (fun i k ↦ (h (EuclideanSpace.single k 1)) i) (sum_coord_mul_coord_isometry h)
      (fun k ↦ P (w k))
    simp only [hP] at hm
    exact hm
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Mixing the components by the matrix of `h` after a linear isometry equivalence `P` of each
component, as a linear isometry equivalence of the tuple space. -/
def mixIsometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (P : E ≃ₗᵢ[ℝ] E) :
    PiLp 2 (fun _ : Fin n ↦ E) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin n ↦ E) where
  toLinearEquiv := LinearEquiv.ofLinearMap
    (mixMap h P.toContinuousLinearEquiv.toContinuousLinearMap).toLinearMap
    (mixMap h.symm P.symm.toContinuousLinearEquiv.toContinuousLinearMap).toLinearMap
    (LinearMap.ext fun w ↦ mixMap_mixMap_symm h (fun u ↦ P.apply_symm_apply u) w)
    (LinearMap.ext fun w ↦ by
      simpa using mixMap_mixMap_symm h.symm (fun u ↦ P.symm_apply_apply u) w)
  norm_map' := norm_mixMap h fun u ↦ P.norm_map u

/-- Components of the mixing isometry. -/
theorem mixIsometry_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (P : E ≃ₗᵢ[ℝ] E) (w : PiLp 2 (fun _ : Fin n ↦ E)) (i : Fin n) :
    mixIsometry h P w i = ∑ k, (h (EuclideanSpace.single k 1)) i • P (w k) :=
  mixMap_apply h _ w i

/-- The velocity transform `w ↦ h ∘ w ∘ h⁻¹` of a linear isometry `h`, as a linear isometry
equivalence of `H¹` vector fields on an open invariant set. -/
def velocityIsometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) :
    PiLp 2 (fun _ : Fin n ↦ H¹(Ω)) ≃ₗᵢ[ℝ] PiLp 2 (fun _ : Fin n ↦ H¹(Ω)) :=
  mixIsometry h (h1Isometry h hΩ hΩo)

/-- Components of the velocity transform. -/
theorem velocityIsometry_apply (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (w : PiLp 2 (fun _ : Fin n ↦ H¹(Ω))) (i : Fin n) :
    velocityIsometry h hΩ hΩo w i =
      ∑ k, (h (EuclideanSpace.single k 1)) i • h1CompSymmCLM h hΩ (w k) :=
  mixIsometry_apply h _ w i

/-! ### Zero boundary values -/

/-- The pullback `φ ∘ h⁻¹` of a test function supported in an invariant set. -/
def isometryTestOn (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (φ : TestFunctionOn n Ω) : TestFunctionOn n Ω :=
  ⟨_root_.TestFunction.mk (fun x ↦ φ.1.toFun (h.symm x)) (φ.1.contDiff.comp h.symm.contDiff)
    (φ.1.hasCompactSupport.comp_homeomorph h.symm.toHomeomorph) (subset_univ _), by
    intro x hx
    have hts : tsupport (fun y ↦ φ.1.toFun (h.symm y)) = h.symm ⁻¹' tsupport φ.1.toFun :=
      tsupport_comp_eq_preimage φ.1.toFun h.symm.toHomeomorph
    change x ∈ tsupport (fun y ↦ φ.1.toFun (h.symm y)) at hx
    rw [hts] at hx
    exact (hΩ.symm.mem_iff x).mp (φ.2 hx)⟩

/-- Composition with `h⁻¹` maps the `H¹` class of a test function to that of its pullback. -/
theorem h1CompSymmCLM_testFunctionToH1 (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (φ : TestFunctionOn n Ω) :
    h1CompSymmCLM h hΩ (testFunctionToH1 φ) = testFunctionToH1 (isometryTestOn h hΩ φ) := by
  refine wkpBaseCoordinateCLM_injective hΩo (Lp.ext ?_)
  simp only [wkpBaseCoordinateCLM_apply]
  rw [h1CompSymmCLM_coe, h1CompSymmAmbient_base]
  have h1 := l2CompSymm_ae h hΩ
    ((testFunctionToH1 φ : WkpAmbientOn n 1 2 Ω) (baseIndex n 1))
  have h2 := hΩ.symm.measurePreserving.quasiMeasurePreserving.ae
    (testFunctionToWkp_coordinate_ae (k := 1) (p := 2) φ (baseIndex n 1))
  have h3 := testFunctionToWkp_coordinate_ae (k := 1) (p := 2) (isometryTestOn h hΩ φ)
    (baseIndex n 1)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  change _ = ((testFunctionToWkp (k := 1) (p := 2) (isometryTestOn h hΩ φ) :
    WkpAmbientOn n 1 2 Ω) (baseIndex n 1) : ℝ^n → ℝ) x
  rw [hx1, hx3]
  change ((testFunctionToWkp (k := 1) (p := 2) φ : WkpAmbientOn n 1 2 Ω)
    (baseIndex n 1) : ℝ^n → ℝ) (h.symm x) = _
  rw [hx2]
  simp [iteratedPartialDeriv, isometryTestOn]

/-- Composition with `h⁻¹` preserves zero boundary values. -/
theorem h1CompSymmCLM_mem_h10 (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (u : H¹₀(Ω)) :
    h1CompSymmCLM h hΩ (u : H¹(Ω)) ∈ (h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule := by
  refine H10SpaceOn.closed_property_of_CcSmooth
    (S := (h1CompSymmCLM h hΩ) ⁻¹' ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule :
      Set (H¹(Ω))))
    ((h10SubmoduleOn (n := n) (Ω := Ω)).isClosed'.preimage (h1CompSymmCLM h hΩ).continuous)
    ?_ u
  rintro _ ⟨φ, rfl⟩
  change h1CompSymmCLM h hΩ (testFunctionToH1 φ) ∈
    ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule : Set (H¹(Ω)))
  rw [h1CompSymmCLM_testFunctionToH1 h hΩ hΩo]
  exact testFunctionToH1_mem_H10 _

/-- Composition with the inverse of a linear isometry on `H¹₀` of an open invariant set. -/
def h10CompSymmCLM (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) :
    H¹₀(Ω) →L[ℝ] H¹₀(Ω) :=
  ((h1CompSymmCLM h hΩ).comp (h10SubtypeL (n := n) (Ω := Ω))).codRestrict
    ((h10SubmoduleOn (n := n) (Ω := Ω)).toSubmodule) fun u ↦ h1CompSymmCLM_mem_h10 h hΩ hΩo u

/-- The underlying `H¹` function of the composed zero-boundary function. -/
theorem h10CompSymmCLM_coe (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (u : H¹₀(Ω)) :
    ((h10CompSymmCLM h hΩ hΩo u : H¹₀(Ω)) : H¹(Ω)) = h1CompSymmCLM h hΩ (u : H¹(Ω)) :=
  rfl

/-- Composition with `h⁻¹` and then with `h` is the identity on `H¹₀` of an open invariant
set. -/
theorem h10CompSymmCLM_h10CompSymmCLM_symm (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) (u : H¹₀(Ω)) :
    h10CompSymmCLM h hΩ hΩo (h10CompSymmCLM h.symm hΩ.symm hΩo u) = u :=
  Subtype.ext (h1CompSymmCLM_h1CompSymmCLM_symm h hΩ hΩo u)

/-- The velocity transform on zero-boundary fields, before showing that it is isometric. -/
def zeroBoundaryVelocityMap (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) : H¹₀(Ω; ℝ^n) →L[ℝ] H¹₀(Ω; ℝ^n) :=
  mixMap h (h10CompSymmCLM h hΩ hΩo)

/-- Components of the zero-boundary velocity transform. -/
theorem zeroBoundaryVelocityMap_apply (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (u : H¹₀(Ω; ℝ^n)) (i : Fin n) :
    zeroBoundaryVelocityMap h hΩ hΩo u i =
      ∑ k, (h (EuclideanSpace.single k 1)) i • h10CompSymmCLM h hΩ hΩo (u k) :=
  mixMap_apply h _ u i

/-- The zero-boundary velocity transform preserves the norm. -/
theorem norm_zeroBoundaryVelocityMap (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (u : H¹₀(Ω; ℝ^n)) : ‖zeroBoundaryVelocityMap h hΩ hΩo u‖ = ‖u‖ := by
  let U : PiLp 2 (fun _ : Fin n ↦ H¹(Ω)) := WithLp.toLp 2 fun i ↦ (u i : H¹(Ω))
  have hcoe (i : Fin n) : ((zeroBoundaryVelocityMap h hΩ hΩo u i : H¹₀(Ω)) : H¹(Ω)) =
      mixMap h (h1CompSymmCLM h hΩ) U i := by
    rw [zeroBoundaryVelocityMap_apply, mixMap_apply]
    simp [U, h10CompSymmCLM_coe]
  have hsq : ‖zeroBoundaryVelocityMap h hΩ hΩo u‖ ^ 2 = ‖u‖ ^ 2 := by
    have hU := norm_mixMap h (P := h1CompSymmCLM h hΩ) (norm_h1CompSymmCLM h hΩ) U
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), PiLp.norm_sq_eq_of_L2,
      PiLp.norm_sq_eq_of_L2] at hU
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    have h1 (i : Fin n) : ‖zeroBoundaryVelocityMap h hΩ hΩo u i‖ =
        ‖mixMap h (h1CompSymmCLM h hΩ) U i‖ := by
      rw [← hcoe i]
      rfl
    have h2 (i : Fin n) : ‖u i‖ = ‖U i‖ := rfl
    simp only [h1, h2]
    exact hU
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The velocity transform `w ↦ h ∘ w ∘ h⁻¹` on zero-boundary `H¹` vector fields of an open
invariant set, as a linear isometry equivalence. -/
def zeroBoundaryVelocityIsometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) : H¹₀(Ω; ℝ^n) ≃ₗᵢ[ℝ] H¹₀(Ω; ℝ^n) where
  toLinearEquiv := LinearEquiv.ofLinearMap (zeroBoundaryVelocityMap h hΩ hΩo).toLinearMap
    (zeroBoundaryVelocityMap h.symm hΩ.symm hΩo).toLinearMap
    (LinearMap.ext fun u ↦ mixMap_mixMap_symm h
      (fun v ↦ h10CompSymmCLM_h10CompSymmCLM_symm h hΩ hΩo v) u)
    (LinearMap.ext fun u ↦ mixMap_mixMap_symm h.symm
      (fun v ↦ h10CompSymmCLM_h10CompSymmCLM_symm h.symm hΩ.symm hΩo v) u)
  norm_map' := norm_zeroBoundaryVelocityMap h hΩ hΩo

/-- Components of the zero-boundary velocity isometry. -/
theorem zeroBoundaryVelocityIsometry_apply (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n) (hΩ : IsIsometryInvariant h Ω)
    (hΩo : IsOpen Ω) (u : H¹₀(Ω; ℝ^n)) (i : Fin n) :
    zeroBoundaryVelocityIsometry h hΩ hΩo u i =
      ∑ k, (h (EuclideanSpace.single k 1)) i • h10CompSymmCLM h hΩ hΩo (u k) :=
  zeroBoundaryVelocityMap_apply h hΩ hΩo u i

/-- The divergence of the transformed zero-boundary field is the transformed divergence. -/
theorem divergence_zeroBoundaryVelocityIsometry (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) (u : H¹₀(Ω; ℝ^n)) :
    ZeroBoundaryVectorSpace.divergence (zeroBoundaryVelocityIsometry h hΩ hΩo u) =
      l2CompSymm h hΩ (ZeroBoundaryVectorSpace.divergence u) := by
  change ∇· (zeroBoundaryVelocityIsometry h hΩ hΩo u) = l2CompSymm h hΩ (∇· u)
  rw [ZeroBoundaryVectorSpace.divergence_apply, ZeroBoundaryVectorSpace.divergence_apply]
  simp only [zeroBoundaryVelocityIsometry_apply, map_sum, map_smul, derivCoordCLM_apply]
  have hP (k i : Fin n) :
      (((h10CompSymmCLM h hΩ hΩo (u k) : H¹₀(Ω)) : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
        (singleDerivIndex n i) = ∑ l, (h (EuclideanSpace.single l 1)) i •
          l2CompSymm h hΩ ((((u k : H¹₀(Ω)) : H¹(Ω)) : WkpAmbientOn n 1 2 Ω)
            (singleDerivIndex n l)) := by
    rw [h10CompSymmCLM_coe, h1CompSymmCLM_coe, h1CompSymmAmbient_single]
    simp only [isometryCoeff_eq]
  simp only [hP, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, sum_coord_mul_coord_isometry h k, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The zero-boundary velocity transform preserves vanishing divergence. -/
theorem zeroBoundaryVelocityIsometry_mem_solenoidal (h : ℝ^n ≃ₗᵢ[ℝ] ℝ^n)
    (hΩ : IsIsometryInvariant h Ω) (hΩo : IsOpen Ω) {u : H¹₀(Ω; ℝ^n)}
    (hu : ZeroBoundaryVectorSpace.divergence u = 0) :
    ZeroBoundaryVectorSpace.divergence (zeroBoundaryVelocityIsometry h hΩ hΩo u) = 0 := by
  rw [divergence_zeroBoundaryVelocityIsometry, hu, map_zero]

end SobolevSpace.GraphSpace
