/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
public import PDE.Spaces.Sobolev.Calculus.Pullback.VectorValued.LpMultiplier
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Duality
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Smooth scalar multiplication on Banach-valued Sobolev spaces

Finite Leibniz rows act on the derivative coordinates by Mathlib's `Lp` scalar
multiplication. Testing by continuous linear functionals reduces preservation of
the weak-derivative graph to the scalar weak Leibniz theorem.

The multiplier `ζ` of `smoothMultiplierCLM` is smooth on all of `ℝ^n`, and the caller supplies
essential bounds on `Ω` for its derivatives of orders `0` through `k`.
Compactly supported smooth functions supply bounded coefficients on every open
domain. The construction includes every derivative order and both exponent
endpoints, with an arbitrary Banach codomain.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A derivative word is represented by its symmetric coordinate.
Words above the declared Sobolev order are assigned zero. -/
def wordRepresentative (U : W^{k,p}(Ω; F)) (β : List (Fin n)) : ℝ^n → F :=
  if hβ : β.length ≤ k then U.val (derivIndexOfList β hβ) else 0

/-- The empty derivative word gives the base representative. -/
@[simp] theorem wordRepresentative_nil (U : W^{k,p}(Ω; F)) :
    wordRepresentative U [] = (U.val (baseIndex n k) : ℝ^n → F) := by
  simp [wordRepresentative, derivIndexOfList, baseIndex]

/-- The finite Leibniz representative for `D^α(ζ • U)`.
Repeated entries in `derivativeSplits` record the binomial multiplicities. The
reverse-word convention agrees with the scalar weak Leibniz rule. -/
def smoothLeibnizRepresentative (ζ : ℝ^n → ℝ) (U : W^{k,p}(Ω; F))
    (α : List (Fin n)) : ℝ^n → F :=
  fun x ↦ ((derivativeSplits α.reverse).map fun q ↦
    iteratedPartialDeriv q.1 ζ x • wordRepresentative U q.2 x).sum

/-- The zeroth Leibniz representative is pointwise scalar multiplication. -/
@[simp] theorem smoothLeibnizRepresentative_nil (ζ : ℝ^n → ℝ)
    (U : W^{k,p}(Ω; F)) :
    smoothLeibnizRepresentative ζ U [] = fun x ↦ ζ x • U.val (baseIndex n k) x := by
  funext x
  simp only [smoothLeibnizRepresentative, List.reverse_nil, derivativeSplits,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, iteratedPartialDeriv,
    wordRepresentative_nil, add_zero]

variable [Fact (1 ≤ p)]

private theorem wordRepresentative_dual_ae (L : F →L[ℝ] ℝ)
    (U : W^{k,p}(Ω; F)) (β : List (Fin n)) :
    wordRepresentative (mapCLM L U) β =ᵐ[domainMeasure n Ω]
      fun x ↦ L (wordRepresentative U β x) := by
  by_cases hβ : β.length ≤ k
  · simp only [wordRepresentative, dite_eq_left hβ]
    exact mapCLM_apply_ae L U _
  · simp only [wordRepresentative, dite_eq_right hβ, Pi.zero_apply, map_zero]
    exact Filter.EventuallyEq.rfl

private theorem smoothLeibnizRepresentative_dual_ae (L : F →L[ℝ] ℝ)
    (ζ : ℝ^n → ℝ) (U : W^{k,p}(Ω; F)) (α : List (Fin n)) :
    smoothLeibnizRepresentative ζ (mapCLM L U) α =ᵐ[domainMeasure n Ω]
      fun x ↦ L (smoothLeibnizRepresentative ζ U α x) := by
  filter_upwards [ae_all_iff.mpr (wordRepresentative_dual_ae L U)] with x hx
  simp only [smoothLeibnizRepresentative, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply, map_smul, hx q.2]

/-- Read a derivative coordinate along a word, with zero above the declared order. -/
def wordCoordinateCLM (β : List (Fin n)) :
    W^{k,p}(Ω; F) →L[ℝ] Lp F p (domainMeasure n Ω) :=
  if hβ : β.length ≤ k then coordinateCLM (derivIndexOfList β hβ) else 0

private theorem wordCoordinateCLM_ae (U : W^{k,p}(Ω; F)) (β : List (Fin n)) :
    (wordCoordinateCLM β U : ℝ^n → F) =ᵐ[domainMeasure n Ω] wordRepresentative U β := by
  by_cases hβ : β.length ≤ k
  · simp only [wordCoordinateCLM, wordRepresentative, dite_eq_left hβ, coordinateCLM_apply]
    exact Filter.EventuallyEq.rfl
  · simp only [wordCoordinateCLM, wordRepresentative, dite_eq_right hβ, zero_apply]
    exact Lp.coeFn_zero F p (domainMeasure n Ω)

/-- The bounded multiplier derivative for a word of length at most `k`.
The zero value for longer words keeps the finite-row construction total. -/
def smoothCoefficientLp (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (β : List (Fin n)) : Lp ℝ ⊤ (domainMeasure n Ω) :=
  if hβ : β.length ≤ k then (hbound β hβ).toLp (iteratedPartialDeriv β ζ) else 0

/-- The continuous linear row of the Leibniz formula for one derivative word. -/
def smoothLeibnizCLM (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (α : List (Fin n)) : W^{k,p}(Ω; F) →L[ℝ] Lp F p (domainMeasure n Ω) :=
  ((derivativeSplits α.reverse).map fun q ↦
    (lpScalarMultiplierCLM (smoothCoefficientLp ζ hbound q.1)).comp
      (wordCoordinateCLM q.2)).sum

omit [CompleteSpace F] [NormedSpace ℝ F] [Fact (1 ≤ p)] in
private theorem lp_list_sum_ae {ι : Type*} (s : List ι)
    (u : ι → Lp F p (domainMeasure n Ω)) (f : ι → ℝ^n → F)
    (h : ∀ i ∈ s, (u i : ℝ^n → F) =ᵐ[domainMeasure n Ω] f i) :
    ((s.map u).sum : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ (s.map fun i ↦ f i x).sum := by
  induction s with
  | nil =>
      filter_upwards [Lp.coeFn_zero F p (domainMeasure n Ω)] with x hx
      exact hx
  | cons i s ih =>
      simp only [List.map_cons, List.sum_cons]
      filter_upwards [Lp.coeFn_add (u i) (s.map u).sum, h i (by simp),
        ih (fun j hj ↦ h j (by simp [hj]))] with x hsum hi hs
      exact hsum.trans (congrArg₂ (· + ·) hi hs)

private theorem smoothLeibnizCLM_ae (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) (hα : α.length ≤ k) :
    (smoothLeibnizCLM ζ hbound α U : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      smoothLeibnizRepresentative ζ U α := by
  unfold smoothLeibnizCLM
  have heval (s : List (W^{k,p}(Ω; F) →L[ℝ] Lp F p (domainMeasure n Ω))) :
      s.sum U = (s.map fun L ↦ L U).sum :=
    map_list_sum (ContinuousLinearMap.apply ℝ _ U) s
  rw [heval, List.map_map]
  apply lp_list_sum_ae
  intro q hq
  have hlen := derivativeSplits_length hq
  have hq₁ : q.1.length ≤ k := by
    simp only [List.length_reverse] at hlen
    omega
  have hc : (smoothCoefficientLp ζ hbound q.1 : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      iteratedPartialDeriv q.1 ζ := by
    simpa only [smoothCoefficientLp, dite_eq_left hq₁] using (hbound q.1 hq₁).coeFn_toLp
  filter_upwards [Lp.coeFn_lpSMul (r := p) (smoothCoefficientLp ζ hbound q.1)
    (wordCoordinateCLM q.2 U), hc, wordCoordinateCLM_ae U q.2] with x hprod hc hu
  exact hprod.trans (congrArg₂ (· • ·) hc hu)

/-- Each finite Leibniz representative belongs to `Lᵖ(Ω)`. Only multiplier
derivatives through the declared Sobolev order must be essentially bounded. -/
theorem memLp_smoothLeibnizRepresentative (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) (hα : α.length ≤ k) :
    MemLp (smoothLeibnizRepresentative ζ U α) p (domainMeasure n Ω) :=
  (memLp_congr_ae (smoothLeibnizCLM_ae ζ hbound U α hα)).mp
    (Lp.memLp (smoothLeibnizCLM ζ hbound α U))

/-- Finite-order Banach-valued weak Leibniz rule, obtained from the scalar
rule by continuous duality. Both functions are Bochner locally integrable. -/
theorem WkpSpaceOn.hasWeakDerivativeOn_smul_smooth (U : W^{k,p}(Ω; F))
    (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn Ω α (fun x ↦ ζ x • U.val (baseIndex n k) x)
      (smoothLeibnizRepresentative ζ U α) := by
  have hbase : MemLp (fun x ↦ ζ x • U.val (baseIndex n k) x) p
      (domainMeasure n Ω) := by
    simpa only [smoothLeibnizRepresentative_nil] using
      memLp_smoothLeibnizRepresentative ζ hbound U [] (by simp)
  have hderiv := memLp_smoothLeibnizRepresentative ζ hbound U α hα
  apply (hasWeakDerivativeOn_iff_forall_dual
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hbase.locallyIntegrable Fact.out))
    (locallyIntegrableOn_of_locallyIntegrable_restrict (hderiv.locallyIntegrable Fact.out))).mpr
  intro L
  have hscalar := (scalarEquiv (mapCLM L U)).hasWeakDerivativeOn_mul_smooth
    ζ hζ hbound α hα
  have hexp : weakLeibnizExpansion ζ
      (GraphSpace.wkpWordRepresentative (scalarEquiv (mapCLM L U))) α.reverse =
      smoothLeibnizRepresentative ζ (mapCLM L U) α := rfl
  rw [hexp] at hscalar
  apply (SobolevSpace.hasWeakDerivativeOn_congr_ae
    (g := L ∘ (fun x ↦ ζ x • U.val (baseIndex n k) x))
    (α := α) _ (smoothLeibnizRepresentative_dual_ae L ζ U α)).mp hscalar
  filter_upwards [mapCLM_apply_ae L U (baseIndex n k)] with x hx
  change ζ x * (mapCLM L U).val (baseIndex n k) x = L (ζ x • U.val (baseIndex n k) x)
  rw [map_smul, hx]
  rfl

/-- Assemble the finite Leibniz rows in the Sobolev ambient product. -/
def smoothMultiplierFamilyCLM (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω)) :
    W^{k,p}(Ω; F) →L[ℝ] WkpAmbientOn n k p Ω F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a ↦ smoothLeibnizCLM ζ hbound a.toList)

private theorem smoothMultiplierFamilyCLM_apply (ζ : ℝ^n → ℝ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) (a : DerivIndex n k) :
    smoothMultiplierFamilyCLM ζ hbound U a = smoothLeibnizCLM ζ hbound a.toList U :=
  rfl

/-- The finite Leibniz rows satisfy the weak derivative graph identities. -/
theorem isWkpOn_smoothMultiplierFamilyCLM (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) : IsWkpOn (smoothMultiplierFamilyCLM ζ hbound U) := by
  intro a
  have hbase : (smoothMultiplierFamilyCLM ζ hbound U (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ ζ x • U.val (baseIndex n k) x := by
    simpa only [smoothMultiplierFamilyCLM_apply, baseIndex_toList,
      smoothLeibnizRepresentative_nil] using
      smoothLeibnizCLM_ae ζ hbound U [] (by simp)
  exact (WkpSpaceOn.hasWeakDerivativeOn_smul_smooth U ζ hζ hbound
    a.toList a.toList_length_le).congr_ae
    hbase.symm (smoothLeibnizCLM_ae ζ hbound U a.toList a.toList_length_le).symm

/-- Multiplication by a smooth scalar function with essentially bounded derivatives
through order `k`, as a continuous linear map on the Banach-valued Sobolev graph. -/
def smoothMultiplierCLM (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω)) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
  (smoothMultiplierFamilyCLM ζ hbound).codRestrict (wkpSubmoduleOn n k p Ω F)
    (isWkpOn_smoothMultiplierFamilyCLM ζ hζ hbound)

/-- Each output coordinate has the finite Leibniz representative. -/
theorem smoothMultiplierCLM_coordinate_ae (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) (a : DerivIndex n k) :
    ((smoothMultiplierCLM ζ hζ hbound U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      smoothLeibnizRepresentative ζ U a.toList :=
  smoothLeibnizCLM_ae ζ hbound U a.toList a.toList_length_le

/-- The multiplier acts on the underlying function by pointwise scalar multiplication. -/
theorem smoothMultiplierCLM_base_ae (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) :
    ((smoothMultiplierCLM ζ hζ hbound U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ ζ x • U.val (baseIndex n k) x := by
  simpa only [baseIndex_toList, smoothLeibnizRepresentative_nil] using
    smoothMultiplierCLM_coordinate_ae ζ hζ hbound U (baseIndex n k)

/-- The Leibniz identity holds for every ordering of a derivative word. -/
theorem smoothMultiplierCLM_derivative_ae (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hbound : ∀ β, β.length ≤ k →
      MemLp (iteratedPartialDeriv β ζ) ⊤ (domainMeasure n Ω))
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) (hα : α.length ≤ k) :
    ((smoothMultiplierCLM ζ hζ hbound U).val (derivIndexOfList α hα) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] smoothLeibnizRepresentative ζ U α :=
  (((smoothMultiplierCLM ζ hζ hbound U).property.hasWeakDerivativeOn_list α hα).congr_ae
    (smoothMultiplierCLM_base_ae ζ hζ hbound U) Filter.EventuallyEq.rfl).ae_eq
      (WkpSpaceOn.hasWeakDerivativeOn_smul_smooth U ζ hζ hbound α hα)

/-- A compactly supported smooth scalar function multiplies `W^{k,p}(Ω; F)`
continuously for every `1 ≤ p ≤ ∞`, on any open domain and with any Banach codomain. -/
def compactSmoothMultiplierCLM (ζ : ℝ^n → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hcompact : HasCompactSupport ζ) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
  smoothMultiplierCLM ζ hζ fun β _ ↦
    (PDE.contDiff_top_iteratedPartialDeriv hζ β).continuous.memLp_top_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv hcompact β) (domainMeasure n Ω)

/-- The coordinate formula for a compact smooth multiplier. -/
theorem compactSmoothMultiplierCLM_coordinate_ae (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcompact : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F)) (a : DerivIndex n k) :
    ((compactSmoothMultiplierCLM ζ hζ hcompact U).val a : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] smoothLeibnizRepresentative ζ U a.toList :=
  smoothMultiplierCLM_coordinate_ae ζ hζ _ U a

/-- The compact multiplier represents the pointwise product on the open domain. -/
theorem compactSmoothMultiplierCLM_base_ae (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcompact : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F)) :
    ((compactSmoothMultiplierCLM ζ hζ hcompact U).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ ζ x • U.val (baseIndex n k) x :=
  smoothMultiplierCLM_base_ae ζ hζ _ U

/-- Every weak derivative of a compactly localized Sobolev element is the finite
Leibniz sum, including repeated derivative indices and both exponent endpoints. -/
theorem compactSmoothMultiplierCLM_derivative_ae (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcompact : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) (hα : α.length ≤ k) :
    ((compactSmoothMultiplierCLM ζ hζ hcompact U).val (derivIndexOfList α hα) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] smoothLeibnizRepresentative ζ U α :=
  smoothMultiplierCLM_derivative_ae ζ hζ _ U α hα

omit [Fact (1 ≤ p)] in
/-- Every Leibniz representative vanishes outside the multiplier's closed support. -/
theorem smoothLeibnizRepresentative_eq_zero (ζ : ℝ^n → ℝ)
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) {x : ℝ^n}
    (hx : x ∉ tsupport ζ) : smoothLeibnizRepresentative ζ U α x = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hv
  have hq : x ∉ tsupport (iteratedPartialDeriv q.1 ζ) :=
    fun h ↦ hx (tsupport_iteratedPartialDeriv_subset_tsupport q.1 ζ h)
  rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]

omit [Fact (1 ≤ p)] in
/-- Localization holds simultaneously for all derivative representatives. -/
theorem tsupport_smoothLeibnizRepresentative_subset (ζ : ℝ^n → ℝ)
    (U : W^{k,p}(Ω; F)) (α : List (Fin n)) :
    tsupport (smoothLeibnizRepresentative ζ U α) ⊆ tsupport ζ := by
  apply closure_minimal _ (isClosed_tsupport ζ)
  intro x hx
  by_contra hζ
  exact hx (smoothLeibnizRepresentative_eq_zero ζ U α hζ)

omit [Fact (1 ≤ p)] in
/-- A compact scalar multiplier gives compactly supported Leibniz representatives. -/
theorem hasCompactSupport_smoothLeibnizRepresentative (ζ : ℝ^n → ℝ)
    (hcompact : HasCompactSupport ζ) (U : W^{k,p}(Ω; F)) (α : List (Fin n)) :
    HasCompactSupport (smoothLeibnizRepresentative ζ U α) :=
  hcompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_smoothLeibnizRepresentative_subset ζ U α)

/-- Outside the cutoff's closed support, all output coordinates vanish almost everywhere.
The exceptional null set is shared by the whole derivative family. -/
theorem compactSmoothMultiplierCLM_eq_zero_ae (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcompact : HasCompactSupport ζ)
    (U : W^{k,p}(Ω; F)) :
    ∀ᵐ x ∂domainMeasure n Ω, x ∉ tsupport ζ →
      ∀ a, (compactSmoothMultiplierCLM ζ hζ hcompact U).val a x = 0 := by
  filter_upwards [ae_all_iff.mpr (compactSmoothMultiplierCLM_coordinate_ae ζ hζ hcompact U)]
    with x hx
  intro hzero a
  exact (hx a).trans (smoothLeibnizRepresentative_eq_zero ζ U a.toList hzero)

/-- An interior cutoff gives a simultaneous family of compactly supported representatives
whose closed supports lie in the open domain. -/
theorem compactSmoothMultiplierCLM_exists_localized_representatives (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcompact : HasCompactSupport ζ)
    (hsupport : tsupport ζ ⊆ Ω) (U : W^{k,p}(Ω; F)) :
    ∃ v : DerivIndex n k → ℝ^n → F, ∀ a,
      ((compactSmoothMultiplierCLM ζ hζ hcompact U).val a : ℝ^n → F)
        =ᵐ[domainMeasure n Ω] v a ∧
      HasCompactSupport (v a) ∧ tsupport (v a) ⊆ Ω := by
  refine ⟨fun a ↦ smoothLeibnizRepresentative ζ U a.toList, fun a ↦ ⟨
    compactSmoothMultiplierCLM_coordinate_ae ζ hζ hcompact U a,
    hasCompactSupport_smoothLeibnizRepresentative ζ hcompact U a.toList, ?_⟩⟩
  exact (tsupport_smoothLeibnizRepresentative_subset ζ U a.toList).trans hsupport

end SobolevSpace.VectorValued
