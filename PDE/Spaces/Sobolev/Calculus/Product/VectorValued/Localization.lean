/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.VectorValued.FiniteExponent
public import PDE.Spaces.Sobolev.Foundations.VectorValued.Locality

/-!
# Local square-integrability and Banach-valued products

A test function is supported inside a relatively compact open subdomain. On such a
subdomain, essentially bounded coordinates and smooth coordinates belong to `L²`.
The finite-exponent product theorem can therefore establish the weak identity locally;
global Hölder integrability then recovers it on the original domain.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

private def restrictWithMemLp {p s : ℝ≥0∞} (U : W^{1,p}(Ω; F)) {V : Opens ℝ^n}
    (hV : V ≤ Ω) (hm : ∀ a, MemLp (U.val a) s (domainMeasure n V)) :
    W^{1,s}(V; F) :=
  ofWeakDerivatives (fun a ↦ U.val a) hm (fun a ↦ (U.property a).restrict hV)

private theorem restrictWithMemLp_ae {p s : ℝ≥0∞} (U : W^{1,p}(Ω; F)) {V : Opens ℝ^n}
    (hV : V ≤ Ω) (hm : ∀ a, MemLp (U.val a) s (domainMeasure n V))
    (a : DerivIndex n 1) :
    ((restrictWithMemLp U hV hm).val a : ℝ^n → F) =ᵐ[domainMeasure n V] U.val a :=
  ofWeakDerivatives_apply_ae _ _ _ a

private theorem weak_bilinear_of_memLp_two {p q : ℝ≥0∞}
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G))
    {O : Opens ℝ^n} (hO : O ≤ Ω)
    (hU : ∀ a, MemLp (U.val a) 2 (domainMeasure n O))
    (hV : ∀ a, MemLp (V.val a) 2 (domainMeasure n O)) (i : Fin n) :
    HasWeakDerivativeOn O [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  let U₂ := restrictWithMemLp U hO hU
  let V₂ := restrictWithMemLp V hO hV
  have h := hasWeakDerivativeOn_bilinear_finite (r := 1) B (by norm_num) (by norm_num) U₂ V₂ i
  apply h.congr_ae
  · filter_upwards [restrictWithMemLp_ae U hO hU (baseIndex n 1),
      restrictWithMemLp_ae V hO hV (baseIndex n 1)] with x hu hv
    simp only [U₂, V₂, hu, hv]
  · filter_upwards [restrictWithMemLp_ae U hO hU (baseIndex n 1),
      restrictWithMemLp_ae V hO hV (baseIndex n 1),
      restrictWithMemLp_ae U hO hU (singleDerivIndex n i),
      restrictWithMemLp_ae V hO hV (singleDerivIndex n i)] with x hu hv hdu hdv
    simp only [U₂, V₂, hu, hv, hdu, hdv]

variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
  [ENNReal.HolderTriple p q r]

include r in
omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
/-- Local `L²` membership of all first-order coordinates suffices for the bilinear
weak identity. Global integrability is supplied separately by the Hölder exponents. -/
theorem hasWeakDerivativeOn_bilinear_of_locally_memLp_two
    (B : F →L[ℝ] G →L[ℝ] H) (U : W^{1,p}(Ω; F)) (V : W^{1,q}(Ω; G))
    (hU : ∀ O : Opens ℝ^n, IsCompact (closure (O : Set ℝ^n)) →
      closure (O : Set ℝ^n) ⊆ Ω → ∀ a, MemLp (U.val a) 2 (domainMeasure n O))
    (hV : ∀ O : Opens ℝ^n, IsCompact (closure (O : Set ℝ^n)) →
      closure (O : Set ℝ^n) ⊆ Ω → ∀ a, MemLp (V.val a) 2 (domainMeasure n O))
    (i : Fin n) :
    HasWeakDerivativeOn Ω [i]
      (fun x ↦ B (U.val (baseIndex n 1) x) (V.val (baseIndex n 1) x))
      (fun x ↦ B (U.val (singleDerivIndex n i) x) (V.val (baseIndex n 1) x) +
        B (U.val (baseIndex n 1) x) (V.val (singleDerivIndex n i) x)) := by
  have hm (a b : DerivIndex n 1) :=
    B.memLp_of_bilin r (Lp.memLp (U.val a)) (Lp.memLp (V.val b))
  apply hasWeakDerivativeOn_of_relativelyCompact
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      ((hm (baseIndex n 1) (baseIndex n 1)).locallyIntegrable Fact.out))
    (locallyIntegrableOn_of_locallyIntegrable_restrict
      (((hm (singleDerivIndex n i) (baseIndex n 1)).add
        (hm (baseIndex n 1) (singleDerivIndex n i))).locallyIntegrable Fact.out))
  intro O hc ho
  exact weak_bilinear_of_memLp_two B U V (subset_closure.trans ho) (hU O hc ho) (hV O hc ho) i

end SobolevSpace.VectorValued
