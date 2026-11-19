/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Banach-valued spatial weak derivatives

The domain is an open subset of `ℝ^n`; the codomain is a complete normed real vector space.
We use the scalar theory's coordinate derivative words and domain measure, and Mathlib's
real test functions and Bochner integral. Local integrability is part of the relation, so
the integral identity does not rely on the value assigned to a nonintegrable function.

`hasWeakDerivativeOn_real_iff` identifies this relation with the scalar one.
Continuous linear maps preserve weak derivatives, and the first-order relation is equivalent
to the derivative identity for Mathlib's ordinary vector-valued distributions. At real
codomain this gives the same equivalence for the scalar relation on an open domain.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace SobolevSpace.VectorValued

/-- A Banach-valued weak derivative on an open Euclidean domain, using the same coordinate
words and sign convention as the scalar Sobolev theory. -/
structure HasWeakDerivativeOn {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ω : Opens ℝ^n) (α : List (Fin n)) (f g : ℝ^n → F) : Prop where
  /-- The function is Bochner locally integrable on the domain. -/
  locallyIntegrable_f : LocallyIntegrableOn f Ω volume
  /-- Its proposed weak derivative is Bochner locally integrable on the domain. -/
  locallyIntegrable_g : LocallyIntegrableOn g Ω volume
  /-- Integration by parts against each real smooth compactly supported test. -/
  integral_identity : ∀ φ : 𝓓(Ω, ℝ),
    (∫ x, iteratedPartialDeriv α φ.toFun x • f x ∂domainMeasure n Ω) =
      (-1 : ℝ) ^ α.length • ∫ x, φ x • g x ∂domainMeasure n Ω

variable {n : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {Ω : Opens ℝ^n} {α : List (Fin n)} {f g : ℝ^n → F}

omit [CompleteSpace F] in
/-- Restricting a scalar test integral to its domain does not change its value. -/
theorem integral_smul_test_eq_setIntegral (f : ℝ^n → F) (φ : 𝓓(Ω, ℝ)) :
    (∫ x, φ x • f x) = ∫ x, φ x • f x ∂domainMeasure n Ω := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_smul]

/-- Coordinate differentiation preserves the domain and compact support of a test. -/
def iteratedPartialDerivTest (α : List (Fin n)) (φ : 𝓓(Ω, ℝ)) : 𝓓(Ω, ℝ) :=
  ⟨iteratedPartialDeriv α φ.toFun, PDE.contDiff_top_iteratedPartialDeriv φ.contDiff α,
    hasCompactSupport_iteratedPartialDeriv φ.hasCompactSupport α,
    (tsupport_iteratedPartialDeriv_subset_tsupport α φ.toFun).trans φ.tsupport_subset⟩

/-- The differentiated test is the iterated coordinate derivative. -/
@[simp] theorem iteratedPartialDerivTest_apply (φ : 𝓓(Ω, ℝ)) (x : ℝ^n) :
    iteratedPartialDerivTest α φ x = iteratedPartialDeriv α φ.toFun x :=
  rfl

/-- The derivative-side test pairing is Bochner integrable. -/
theorem HasWeakDerivativeOn.integrable_smul_iteratedPartialDeriv
    (h : HasWeakDerivativeOn Ω α f g) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ iteratedPartialDeriv α φ.toFun x • f x)
      (domainMeasure n Ω) :=
  ((iteratedPartialDerivTest α φ).integrable_smul h.locallyIntegrable_f).mono_measure
    Measure.restrict_le_self

/-- The test pairing with the proposed weak derivative is Bochner integrable. -/
theorem HasWeakDerivativeOn.integrable_smul_testFunction
    (h : HasWeakDerivativeOn Ω α f g) (φ : 𝓓(Ω, ℝ)) :
    Integrable (fun x ↦ φ x • g x) (domainMeasure n Ω) :=
  (φ.integrable_smul h.locallyIntegrable_g).mono_measure Measure.restrict_le_self

/-- At real codomain this is exactly the scalar weak derivative, with no extra
integrability or regularity hypothesis. -/
theorem hasWeakDerivativeOn_real_iff {f g : ℝ^n → ℝ} :
    HasWeakDerivativeOn Ω α f g ↔
      SobolevSpace.HasWeakDerivativeOn (Ω : Set ℝ^n) α f g := by
  constructor
  · intro h
    refine ⟨h.locallyIntegrable_f, h.locallyIntegrable_g, ?_⟩
    intro φ hφ
    let ψ : 𝓓(Ω, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφ⟩
    simpa only [ψ, TestFunction.toFun_eq_coe, TestFunction.coe_mk, smul_eq_mul,
      mul_comm] using h.integral_identity ψ
  · intro h
    refine ⟨h.locallyIntegrable_f, h.locallyIntegrable_g, ?_⟩
    intro φ
    let ψ : 𝓓((⊤ : Opens ℝ^n), ℝ) :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_univ _⟩
    simpa only [ψ, TestFunction.toFun_eq_coe, TestFunction.coe_mk, smul_eq_mul,
      mul_comm] using h.integral_identity ψ φ.tsupport_subset

/-- Order zero is the identity on locally integrable functions. -/
theorem hasWeakDerivativeOn_nil (hf : LocallyIntegrableOn f Ω volume) :
    HasWeakDerivativeOn Ω [] f f := by
  refine ⟨hf, hf, ?_⟩
  intro φ
  simp [iteratedPartialDeriv]

/-- Almost-everywhere changes of either representative preserve the weak derivative. -/
theorem HasWeakDerivativeOn.congr_ae (h : HasWeakDerivativeOn Ω α f g)
    {f' g' : ℝ^n → F} (hf : f =ᵐ[domainMeasure n Ω] f')
    (hg : g =ᵐ[domainMeasure n Ω] g') :
    HasWeakDerivativeOn Ω α f' g' := by
  refine ⟨h.locallyIntegrable_f.congr hf, h.locallyIntegrable_g.congr hg, ?_⟩
  intro φ
  rw [← integral_congr_ae (ae_eq_rfl.smul hf),
    ← integral_congr_ae (ae_eq_rfl.smul hg)]
  exact h.integral_identity φ

/-- Weak differentiation is real linear in the function and its derivative. -/
theorem HasWeakDerivativeOn.add (h : HasWeakDerivativeOn Ω α f g)
    {f' g' : ℝ^n → F} (h' : HasWeakDerivativeOn Ω α f' g') :
    HasWeakDerivativeOn Ω α (f + f') (g + g') := by
  refine ⟨h.locallyIntegrable_f.add h'.locallyIntegrable_f,
    h.locallyIntegrable_g.add h'.locallyIntegrable_g, ?_⟩
  intro φ
  simp only [Pi.add_apply, smul_add]
  rw [integral_add (h.integrable_smul_iteratedPartialDeriv φ)
      (h'.integrable_smul_iteratedPartialDeriv φ),
    integral_add (h.integrable_smul_testFunction φ) (h'.integrable_smul_testFunction φ),
    h.integral_identity, h'.integral_identity, smul_add]

/-- A continuous linear map of Banach codomains commutes with spatial weak differentiation. -/
theorem HasWeakDerivativeOn.map (h : HasWeakDerivativeOn Ω α f g) (L : F →L[ℝ] G) :
    HasWeakDerivativeOn Ω α (L ∘ f) (L ∘ g) := by
  refine ⟨L.locallyIntegrableOn_comp h.locallyIntegrable_f,
    L.locallyIntegrableOn_comp h.locallyIntegrable_g, ?_⟩
  intro φ
  have heq := congrArg L (h.integral_identity φ)
  rw [map_smul, ← L.integral_comp_comm (h.integrable_smul_iteratedPartialDeriv φ),
    ← L.integral_comp_comm (h.integrable_smul_testFunction φ)] at heq
  simpa only [map_smul, Function.comp_apply] using heq

/-- Constant real scalar multiplication commutes with weak differentiation. -/
theorem HasWeakDerivativeOn.smul (h : HasWeakDerivativeOn Ω α f g) (c : ℝ) :
    HasWeakDerivativeOn Ω α (c • f) (c • g) :=
  h.map (c • ContinuousLinearMap.id ℝ F)

/-- Permuting coordinate directions leaves a weak derivative unchanged. -/
theorem HasWeakDerivativeOn.perm (h : HasWeakDerivativeOn Ω α f g)
    {β : List (Fin n)} (hαβ : α.Perm β) :
    HasWeakDerivativeOn Ω β f g := by
  refine ⟨h.locallyIntegrable_f, h.locallyIntegrable_g, ?_⟩
  intro φ
  simpa only [TestFunction.toFun_eq_coe,
    iteratedPartialDeriv_congr_perm_smooth φ.contDiff hαβ, hαβ.length_eq]
    using h.integral_identity φ

/-- On an open domain a weak derivative is unique up to almost-everywhere equality. -/
theorem HasWeakDerivativeOn.ae_eq (h : HasWeakDerivativeOn Ω α f g)
    {g' : ℝ^n → F} (h' : HasWeakDerivativeOn Ω α f g') :
    g =ᵐ[domainMeasure n Ω] g' := by
  apply Distribution.ofFun_injective h.locallyIntegrable_g h'.locallyIntegrable_g
    (n := ⊤)
  ext φ
  rw [Distribution.ofFun_apply h.locallyIntegrable_g,
    Distribution.ofFun_apply h'.locallyIntegrable_g,
    integral_smul_test_eq_setIntegral g, integral_smul_test_eq_setIntegral g']
  apply smul_right_injective F
    (show (-1 : ℝ) ^ α.length ≠ 0 from pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  exact (h.integral_identity φ).symm.trans (h'.integral_identity φ)

/-- The first weak derivative gives the same derivative of the regular distribution. -/
theorem HasWeakDerivativeOn.lineDerivCLM_ofFun {i : Fin n}
    (h : HasWeakDerivativeOn Ω [i] f g) :
    Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤ := by
  ext φ
  rw [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply h.locallyIntegrable_f,
    Distribution.ofFun_apply h.locallyIntegrable_g,
    integral_smul_test_eq_setIntegral f, integral_smul_test_eq_setIntegral g]
  have hd :
      ⇑(TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓(Ω, ℝ)) = iteratedPartialDeriv [i] φ.toFun := by
    funext x
    exact testFunction_lineDerivCLM_apply φ _ x
  rw [hd]
  simpa only [List.length_cons, List.length_nil, zero_add, pow_one, neg_one_smul,
    neg_neg] using congrArg Neg.neg (h.integral_identity φ)

/-- A regular distribution derivative recovers the first weak derivative when the two
representatives are locally integrable. -/
theorem hasWeakDerivativeOn_of_lineDerivCLM_ofFun {i : Fin n}
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (heq : Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤) :
    HasWeakDerivativeOn Ω [i] f g := by
  refine ⟨hf, hg, ?_⟩
  intro φ
  have h := congrArg (fun T : 𝓓'(Ω, F) ↦ T φ) heq
  rw [Distribution.lineDerivCLM_apply, Distribution.ofFun_apply hf,
    Distribution.ofFun_apply hg, integral_smul_test_eq_setIntegral f,
    integral_smul_test_eq_setIntegral g] at h
  have hd :
      ⇑(TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) φ :
        𝓓(Ω, ℝ)) = iteratedPartialDeriv [i] φ.toFun := by
    funext x
    exact testFunction_lineDerivCLM_apply φ _ x
  rw [hd] at h
  simpa only [List.length_cons, List.length_nil, zero_add, pow_one, neg_one_smul,
    neg_neg] using congrArg Neg.neg h

end SobolevSpace.VectorValued

namespace SobolevSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {f g : ℝ^n → ℝ} {i : Fin n}

/-- The ordinary distributional derivative of a weakly differentiable
function is represented by its weak derivative. -/
theorem HasWeakDerivativeOn.lineDerivCLM_ofFun
    (h : HasWeakDerivativeOn (Ω : Set (ℝ^n)) [i] f g) :
    Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤ :=
  (VectorValued.hasWeakDerivativeOn_real_iff.mpr h).lineDerivCLM_ofFun

/-- Ordinary distributional equality supplies the weak derivative
identity when both representatives are locally integrable on the domain. -/
theorem hasWeakDerivativeOn_of_lineDerivCLM_ofFun
    (hf : LocallyIntegrableOn f (Ω : Set (ℝ^n)) volume)
    (hg : LocallyIntegrableOn g (Ω : Set (ℝ^n)) volume)
    (heq : Distribution.lineDerivCLM (EuclideanSpace.single i (1 : ℝ))
      (Distribution.ofFun Ω f volume ⊤) = Distribution.ofFun Ω g volume ⊤) :
    HasWeakDerivativeOn (Ω : Set (ℝ^n)) [i] f g :=
  VectorValued.hasWeakDerivativeOn_real_iff.mp
    (VectorValued.hasWeakDerivativeOn_of_lineDerivCLM_ofFun hf hg heq)

end SobolevSpace
