/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.VectorValued.WeakLeibniz

/-!
# Continuous bilinear products of Banach-valued Sobolev functions

A continuous bilinear map `B : F →L[ℝ] G →L[ℝ] H` induces a continuous bilinear map
`W^{1,p}(Ω; F) →L[ℝ] W^{1,q}(Ω; G) →L[ℝ] W^{1,r}(Ω; H)` whenever
`1/r = 1/p + 1/q` and all three exponents lie in `[1, ∞]`.
Its base coordinate is the pointwise product, and each derivative coordinate is the
sum of the two weak Leibniz terms. The coordinate estimates retain the constant `‖B‖`
from Hölder's inequality.

The domain is any open subset of Euclidean space. The three codomains may be arbitrary
complete real Banach spaces, and the domain need not have finite measure.
-/

public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [ENNReal.HolderTriple p q r]

private def bilinearRows (B : F →L[ℝ] G →L[ℝ] H) :
    DerivIndex n 1 → W^{1,p}(Ω; F) →L[ℝ] W^{1,q}(Ω; G) →L[ℝ]
      Lp H r (domainMeasure n Ω) :=
  firstOrderRows
    ((B.holderL (domainMeasure n Ω) p q r).bilinearComp
      (coordinateCLM (baseIndex n 1)) (coordinateCLM (baseIndex n 1)))
    (fun i ↦
      (B.holderL (domainMeasure n Ω) p q r).bilinearComp
          (coordinateCLM (singleDerivIndex n i)) (coordinateCLM (baseIndex n 1)) +
        (B.holderL (domainMeasure n Ω) p q r).bilinearComp
          (coordinateCLM (baseIndex n 1)) (coordinateCLM (singleDerivIndex n i)))

private def bilinearAmbient (B : F →L[ℝ] G →L[ℝ] H) :
    W^{1,p}(Ω; F) →L[ℝ] W^{1,q}(Ω; G) →L[ℝ] WkpAmbientOn n 1 r Ω H :=
  let J := (PiLp.continuousLinearEquiv r ℝ
    (fun _ : DerivIndex n 1 ↦ Lp H r (domainMeasure n Ω))).symm.toContinuousLinearMap
  ∑ a, (ContinuousLinearMap.compL ℝ (W^{1,q}(Ω; G))
    (Lp H r (domainMeasure n Ω)) (WkpAmbientOn n 1 r Ω H)
    (J.comp (ContinuousLinearMap.single ℝ
      (fun _ : DerivIndex n 1 ↦ Lp H r (domainMeasure n Ω)) a))).comp (bilinearRows B a)

omit [CompleteSpace H] in
private theorem bilinearAmbient_apply (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    bilinearAmbient (r := r) B U V =
      WithLp.toLp r (fun a ↦ bilinearRows (r := r) B a U V) := by
  simp only [bilinearAmbient, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply]
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_symm_apply] using
    (ContinuousLinearMap.sum_comp_single ℝ
      (fun _ : DerivIndex n 1 ↦ Lp H r (domainMeasure n Ω))
      (PiLp.continuousLinearEquiv r ℝ
        (fun _ : DerivIndex n 1 ↦ Lp H r (domainMeasure n Ω))).symm.toContinuousLinearMap
      (fun a ↦ bilinearRows (r := r) B a U V))

omit [CompleteSpace H] in
private theorem bilinearAmbient_base (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    bilinearAmbient (r := r) B U V (baseIndex n 1) =
      B.holder r (U.val (baseIndex n 1)) (V.val (baseIndex n 1)) := by
  rw [bilinearAmbient_apply]
  simp only [bilinearRows, firstOrderRows_baseIndex,
    ContinuousLinearMap.bilinearComp_apply, coordinateCLM_apply,
    ContinuousLinearMap.holderL_apply_apply]

omit [CompleteSpace H] in
private theorem bilinearAmbient_single (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) (i : Fin n) :
    bilinearAmbient (r := r) B U V (singleDerivIndex n i) =
      B.holder r (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)) +
        B.holder r (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i)) := by
  rw [bilinearAmbient_apply]
  simp only [bilinearRows, firstOrderRows_singleDerivIndex,
    add_apply, ContinuousLinearMap.bilinearComp_apply, coordinateCLM_apply,
    ContinuousLinearMap.holderL_apply_apply]

private theorem isWkpOn_bilinearAmbient (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    IsWkpOn (bilinearAmbient (r := r) B U V) := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · rw [baseIndex_toList, bilinearAmbient_base]
    exact hasWeakDerivativeOn_nil (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp _).locallyIntegrable Fact.out))
  · rw [singleDerivIndex_toList, bilinearAmbient_base, bilinearAmbient_single]
    apply (hasWeakDerivativeOn_bilinear (r := r) B U V i).congr_ae
      (B.coeFn_holder _ _).symm
    apply Filter.EventuallyEq.symm
    apply (Lp.coeFn_add _ _).trans
    filter_upwards [B.coeFn_holder (r := r) (U.val (singleDerivIndex n i))
      (V.val (baseIndex n 1)), B.coeFn_holder (r := r) (U.val (baseIndex n 1))
      (V.val (singleDerivIndex n i))] with x h₁ h₂
    exact congrArg₂ (· + ·) h₁ h₂

/-- The continuous bilinear Sobolev product associated to `B`, at any Hölder triple
of exponents in `[1, ∞]`. Its derivative coordinates are the weak Leibniz formula. -/
def bilinearCLM (B : F →L[ℝ] G →L[ℝ] H) :
    W^{1,p}(Ω; F) →L[ℝ] W^{1,q}(Ω; G) →L[ℝ] W^{1,r}(Ω; H) := by
  let : SeminormedAddCommGroup (W^{1,q}(Ω; G) →L[ℝ] WkpAmbientOn n 1 r Ω H) :=
    inferInstance
  let : NormedSpace ℝ (W^{1,q}(Ω; G) →L[ℝ] WkpAmbientOn n 1 r Ω H) := inferInstance
  exact (LinearMap.mk₂ ℝ
    (fun U V ↦ ⟨bilinearAmbient (r := r) B U V, isWkpOn_bilinearAmbient B U V⟩)
    (fun U₁ U₂ V ↦ Subtype.ext (by simp))
    (fun c U V ↦ Subtype.ext (by simp))
    (fun U V₁ V₂ ↦ Subtype.ext (by simp))
    (fun c U V ↦ Subtype.ext (by simp))).mkContinuous₂
      ‖bilinearAmbient (p := p) (q := q) (r := r) (Ω := Ω) B‖
      (fun U V ↦ (bilinearAmbient (r := r) B).le_opNorm₂ U V)

/-- The base coordinate of the bilinear Sobolev product is the `Lp` Hölder product. -/
@[simp] theorem bilinearCLM_base (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    (bilinearCLM (r := r) B U V).val (baseIndex n 1) =
      B.holder r (U.val (baseIndex n 1)) (V.val (baseIndex n 1)) :=
  bilinearAmbient_base (r := r) B U V

/-- A derivative coordinate of the bilinear Sobolev product is the sum of the two
`Lp` Hölder products prescribed by Leibniz's rule. -/
@[simp] theorem bilinearCLM_single (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) (i : Fin n) :
    (bilinearCLM (r := r) B U V).val (singleDerivIndex n i) =
      B.holder r (U.val (singleDerivIndex n i)) (V.val (baseIndex n 1)) +
        B.holder r (U.val (baseIndex n 1)) (V.val (singleDerivIndex n i)) :=
  bilinearAmbient_single (r := r) B U V i

/-- The base representative agrees almost everywhere with pointwise application of `B`. -/
theorem bilinearCLM_base_ae (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    ((bilinearCLM (r := r) B U V).val (baseIndex n 1) : ℝ^n → H) =ᵐ[domainMeasure n Ω]
      fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x) := by
  rw [bilinearCLM_base]
  exact B.coeFn_holder _ _

/-- Each derivative representative agrees almost everywhere with the pointwise
sum of the two Leibniz terms. -/
theorem bilinearCLM_single_ae (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) (i : Fin n) :
    ((bilinearCLM (r := r) B U V).val (singleDerivIndex n i) : ℝ^n → H)
      =ᵐ[domainMeasure n Ω]
      fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x) := by
  rw [bilinearCLM_single]
  apply (Lp.coeFn_add _ _).trans
  filter_upwards [B.coeFn_holder (r := r) (U.val (singleDerivIndex n i))
    (V.val (baseIndex n 1)), B.coeFn_holder (r := r) (U.val (baseIndex n 1))
    (V.val (singleDerivIndex n i))] with x h₁ h₂
  exact congrArg₂ (· + ·) h₁ h₂

/-- The base-coordinate Hölder estimate, with the original bilinear operator norm. -/
theorem norm_bilinearCLM_base_le (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) :
    ‖(bilinearCLM (r := r) B U V).val (baseIndex n 1)‖ ≤
      ‖B‖ * ‖U.val (baseIndex n 1)‖ * ‖V.val (baseIndex n 1)‖ := by
  rw [bilinearCLM_base]
  exact B.norm_holder_apply_apply_le _ _

/-- The derivative-coordinate Hölder estimate for the two Leibniz terms. -/
theorem norm_bilinearCLM_single_le (B : F →L[ℝ] G →L[ℝ] H)
    (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G)) (i : Fin n) :
    ‖(bilinearCLM (r := r) B U V).val (singleDerivIndex n i)‖ ≤
      ‖B‖ * ‖U.val (singleDerivIndex n i)‖ * ‖V.val (baseIndex n 1)‖ +
        ‖B‖ * ‖U.val (baseIndex n 1)‖ * ‖V.val (singleDerivIndex n i)‖ := by
  rw [bilinearCLM_single]
  exact (norm_add_le _ _).trans (add_le_add (B.norm_holder_apply_apply_le _ _)
    (B.norm_holder_apply_apply_le _ _))

end SobolevSpace.VectorValued
