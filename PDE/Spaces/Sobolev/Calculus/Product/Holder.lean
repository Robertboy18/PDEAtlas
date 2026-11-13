/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Spaces.Sobolev.Calculus.Product.WholeSpaceMultiplier
import PDE.Analysis.Normed.PiLp.CompareExp
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Hölder products of whole-space Sobolev functions

Let `1/p + 1/q = 1/r` with `q < ∞`. For `f ∈ W^{k,p}(ℝ^n)` and `g ∈ W^{k,q}(ℝ^n)` the product
`f g` lies in `W^{k,r}(ℝ^n)`, its weak derivatives are given by the Leibniz formula

`D^α(f g) = ∑ D^{α₂} f D^{α₁} g`,

summed over the splittings `(α₁, α₂)` of the derivative word `α`, and

`‖f g‖_{W^{k,r}} ≤ card (DerivIndex n k) 2^k ‖f‖_{W^{k,p}} ‖g‖_{W^{k,q}}`.

The Leibniz rows are bounded bilinear maps into `Lʳ` by Hölder's inequality, so they assemble
into a bounded bilinear map into the ambient derivative bundle. When `g` is smooth and compactly
supported, the rows satisfy the weak-derivative relations by the weak Leibniz rule with a smooth
multiplier. These functions are dense in `W^{k,q}(ℝ^n)` and the Sobolev graph is closed, so the
relations hold for every `g`. The case `p = q = 4`, `r = 2` gives the product
`W^{k,4}(ℝ^n) × W^{k,4}(ℝ^n) → H^k(ℝ^n)`, and the case `p = ∞`, `q = r = 2` is the multiplier
`wkMultiplication`.

## Main results

* `holderProduct`: the bounded bilinear product `W^{k,p}(ℝ^n) →L W^{k,q}(ℝ^n) →L W^{k,r}(ℝ^n)`,
  with `holderProduct_base_ae`, `wkpCoordinateCLM_holderProduct` and `norm_holderProduct_le`.
* `l4Product`: the case `W^{k,4}(ℝ^n) × W^{k,4}(ℝ^n) → W^{k,2}(ℝ^n)`, with `l4Product_base_ae`
  and `norm_l4Product_le`.
* `wkMultiplication_eq_holderProduct`: the case `p = ∞`, `q = r = 2` is `wkMultiplication`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n k : ℕ}

section Coordinates

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The coordinate of a Sobolev bundle along a derivative word, and zero above the order. -/
def wordCoordinateCLM (k : ℕ) (β : List (Fin n)) : W^{k,p}(ℝ^n) →L[ℝ] DerivLp n p Set.univ :=
  if hβ : β.length ≤ k then wkpCoordinateCLM (derivIndexOfList β hβ) else 0

theorem wordCoordinateCLM_of_le (β : List (Fin n)) (hβ : β.length ≤ k) (U : W^{k,p}(ℝ^n)) :
    wordCoordinateCLM k β U = wkpCoordinateCLM (derivIndexOfList β hβ) U := by
  simp [wordCoordinateCLM, hβ]

/-- A word coordinate is bounded by the Sobolev norm. -/
theorem norm_wordCoordinateCLM_le (β : List (Fin n)) (U : W^{k,p}(ℝ^n)) :
    ‖wordCoordinateCLM k β U‖ ≤ ‖U‖ := by
  by_cases hβ : β.length ≤ k
  · rw [wordCoordinateCLM_of_le β hβ]
    exact wkpCoordinateCLM_norm_le _ U
  · simp [wordCoordinateCLM, hβ]

/-- In-range word coordinates are the word representatives of `WeakLeibniz`. -/
theorem coe_wordCoordinateCLM (β : List (Fin n)) (hβ : β.length ≤ k) (U : W^{k,p}(ℝ^n)) :
    (wordCoordinateCLM k β U : ℝ^n → ℝ) = wkpWordRepresentative U β := by
  rw [wordCoordinateCLM_of_le β hβ]
  simp [wkpWordRepresentative, hβ]

/-- The word coordinates of a smooth compactly supported function are its classical iterated
partial derivatives. -/
theorem wordCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (β : List (Fin n)) (hβ : β.length ≤ k)
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    (wordCoordinateCLM k β (mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := p)
        (Ω := Set.univ) f hf hcs) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ] fun x ↦ iteratedPartialDeriv (n := n) β f x := by
  rw [wordCoordinateCLM_of_le β hβ, wkpCoordinateCLM_apply]
  have h := mkWkpSpaceOnOfContDiff_apply_ae (n := n) (k := k) (p := p) (Ω := Set.univ) f hf hcs
    (derivIndexOfList β hβ)
  rw [iteratedPartialDeriv_congr_perm_smooth hf (derivIndexOfList_toList_perm β hβ)] at h
  exact h

end Coordinates

variable {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r]

/-- One Leibniz term `D^{s₂} f D^{s₁} g` for a splitting `s = (s₁, s₂)`, as a bounded bilinear
map into `Lʳ`. -/
def leibnizTermCLM (k : ℕ) (s : List (Fin n) × List (Fin n)) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,q}(ℝ^n) →L[ℝ] DerivLp n r Set.univ :=
  ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure n Set.univ) p q r).bilinearComp
    (wordCoordinateCLM k s.2) (wordCoordinateCLM k s.1)

/-- The Leibniz row `∑ D^{α₂} f D^{α₁} g` of a derivative word `α`, summed over its splittings. -/
def leibnizRowCLM (k : ℕ) (α : List (Fin n)) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,q}(ℝ^n) →L[ℝ] DerivLp n r Set.univ :=
  ∑ j : Fin (derivativeSplits α).length, leibnizTermCLM k (derivativeSplits α)[j.1]

/-- The Leibniz row is, almost everywhere, the sum of the products of word coordinates. -/
theorem leibnizRowCLM_ae (α : List (Fin n)) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    (leibnizRowCLM (r := r) k α f g : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ] fun x ↦
      ((derivativeSplits α).map fun s ↦
        wordCoordinateCLM k s.2 f x * wordCoordinateCLM k s.1 g x).sum := by
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin (derivativeSplits α).length ↦
    leibnizTermCLM (r := r) k (derivativeSplits α)[j.1] f g)
  have hterm := fun j : Fin (derivativeSplits α).length ↦
    (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := r)
      (wordCoordinateCLM k (derivativeSplits α)[j.1].2 f)
      (wordCoordinateCLM k (derivativeSplits α)[j.1].1 g)
  have hrow : leibnizRowCLM (r := r) k α f g = ∑ j : Fin (derivativeSplits α).length,
      leibnizTermCLM (r := r) k (derivativeSplits α)[j.1] f g := by
    rw [leibnizRowCLM, sum_apply, sum_apply]
  rw [hrow]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with x hx ht
  rw [hx, ← Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro j _
  exact ht j

/-- Each Leibniz row is bounded by `2 ^ |α| ‖f‖ ‖g‖`. -/
theorem norm_leibnizRowCLM_apply_le (α : List (Fin n)) (f : W^{k,p}(ℝ^n))
    (g : W^{k,q}(ℝ^n)) :
    ‖leibnizRowCLM (r := r) k α f g‖ ≤ 2 ^ α.length * ‖f‖ * ‖g‖ := by
  have hrow : leibnizRowCLM (r := r) k α f g = ∑ j : Fin (derivativeSplits α).length,
      leibnizTermCLM (r := r) k (derivativeSplits α)[j.1] f g := by
    rw [leibnizRowCLM, sum_apply, sum_apply]
  rw [hrow]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (derivativeSplits α).length, ‖f‖ * ‖g‖ := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖wordCoordinateCLM k (derivativeSplits α)[j.1].2 f‖ *
            ‖wordCoordinateCLM k (derivativeSplits α)[j.1].1 g‖ :=
          (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le _ _
        _ ≤ 1 * ‖f‖ * ‖g‖ := by
          gcongr
          · exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
          · exact norm_wordCoordinateCLM_le _ f
          · exact norm_wordCoordinateCLM_le _ g
        _ = _ := by ring
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, length_derivativeSplits,
        nsmul_eq_mul]
      push_cast
      ring

/-- The inclusion of one derivative row into the ambient derivative bundle. -/
def rowInclusion (k : ℕ) (a : DerivIndex n k) :
    DerivLp n r Set.univ →L[ℝ] WkpAmbientOn n k r Set.univ :=
  (PiLp.continuousLinearEquiv r ℝ
      (fun _ : DerivIndex n k ↦ DerivLp n r Set.univ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : DerivIndex n k ↦ DerivLp n r Set.univ) a)

/-- The Leibniz rows of all multi-indices of order at most `k`, as a bounded bilinear map into
the ambient derivative bundle. -/
def leibnizAmbientCLM (k : ℕ) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,q}(ℝ^n) →L[ℝ] WkpAmbientOn n k r Set.univ :=
  ∑ a : DerivIndex n k, (ContinuousLinearMap.compL ℝ (W^{k,q}(ℝ^n)) (DerivLp n r Set.univ)
    (WkpAmbientOn n k r Set.univ) (rowInclusion k a)).comp (leibnizRowCLM k a.toList.reverse)

/-- The rows of the assembled bundle are the Leibniz rows. -/
@[simp]
theorem leibnizAmbientCLM_apply (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) (a : DerivIndex n k) :
    leibnizAmbientCLM (r := r) k f g a = leibnizRowCLM k a.toList.reverse f g := by
  simp [leibnizAmbientCLM, rowInclusion, ContinuousLinearMap.compL_apply, Pi.single_apply,
    sum_apply]

/-- For a smooth compactly supported second factor, the Leibniz rows satisfy the weak-derivative
relations of `W^{k,r}(ℝ^n)`. -/
theorem leibnizAmbientCLM_mem_of_smooth (f : W^{k,p}(ℝ^n)) (ζ : ℝ^n → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcs : HasCompactSupport ζ) :
    leibnizAmbientCLM (r := r) k f
        (mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := q) (Ω := Set.univ) ζ hζ hcs) ∈
      wkpSubmoduleOn n k r Set.univ := by
  set g := mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := q) (Ω := Set.univ) ζ hζ hcs
  have hbound : ∀ β : List (Fin n), β.length ≤ k → MemLp
      (iteratedPartialDeriv (n := n) β ζ) ⊤ (domainMeasure n Set.univ) := fun β _ ↦
    (PDE.contDiff_top_iteratedPartialDeriv (n := n) hζ β).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_iteratedPartialDeriv (n := n) hcs β)
  -- Each row is the weak Leibniz expansion of `ζ f` along the reversed word.
  have hrow : ∀ α : List (Fin n), α.length ≤ k →
      (leibnizRowCLM (r := r) k α f g : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
        weakLeibnizExpansion ζ (wkpWordRepresentative f) α := by
    intro α hα
    have hsplit : ∀ s ∈ derivativeSplits α, s.1.length ≤ k ∧ s.2.length ≤ k := by
      intro s hs
      have := derivativeSplits_length hs
      omega
    have hg : ∀ s ∈ derivativeSplits α,
        (wordCoordinateCLM k s.1 g : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
          fun x ↦ iteratedPartialDeriv (n := n) s.1 ζ x := fun s hs ↦
      wordCoordinateCLM_mkWkpSpaceOnOfContDiff_ae s.1 (hsplit s hs).1 ζ hζ hcs
    have hgall : ∀ᵐ x ∂(domainMeasure n Set.univ), ∀ s ∈ derivativeSplits α,
        wordCoordinateCLM k s.1 g x = iteratedPartialDeriv (n := n) s.1 ζ x := by
      have := (ae_all_iff (ι := Fin (derivativeSplits α).length)).mpr fun j ↦
        hg (derivativeSplits α)[j.1] (List.getElem_mem _)
      filter_upwards [this] with x hx s hs
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
      exact hx ⟨j, hj⟩
    filter_upwards [leibnizRowCLM_ae (r := r) α f g, hgall] with x hx hgx
    rw [hx, weakLeibnizExpansion]
    congr 1
    apply List.map_congr_left
    intro s hs
    rw [hgx s hs, coe_wordCoordinateCLM s.2 (hsplit s hs).2 f, mul_comm]
  intro a
  have hweak := WkpSpaceOn.hasWeakDerivativeOn_mul_smooth f ζ hζ hbound a.toList
    a.toList_length_le
  have hbase : ((leibnizAmbientCLM (r := r) k f g : WkpAmbientOn n k r Set.univ)
      (baseIndex n k) : ℝ^n → ℝ) =ᵐ[domainMeasure n Set.univ]
        fun x ↦ ζ x * ((f : WkpAmbientOn n k p Set.univ) (baseIndex n k) : ℝ^n → ℝ) x := by
    rw [leibnizAmbientCLM_apply, baseIndex_toList, List.reverse_nil]
    filter_upwards [hrow [] (by simp)] with x hx
    rw [hx]
    simp
  have ha : ((leibnizAmbientCLM (r := r) k f g : WkpAmbientOn n k r Set.univ) a : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Set.univ]
        weakLeibnizExpansion ζ (wkpWordRepresentative f) a.toList.reverse := by
    rw [leibnizAmbientCLM_apply]
    exact hrow a.toList.reverse (by simpa using a.toList_length_le)
  exact (hasWeakDerivativeOn_congr_ae hbase ha).mpr hweak

/-- The Leibniz rows satisfy the weak-derivative relations of `W^{k,r}(ℝ^n)` for every second
factor in `W^{k,q}(ℝ^n)` with `q < ∞`. -/
theorem leibnizAmbientCLM_mem (hq : q ≠ ∞) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    leibnizAmbientCLM (r := r) k f g ∈ wkpSubmoduleOn n k r Set.univ := by
  obtain ⟨ζ, hζ, hcs, hlim⟩ :=
    globalApproximation_WkpSpace (Approximation.standardMollifier n) hq k g
  have htend : Filter.Tendsto (fun m ↦ mkWkpSpaceOnOfContDiff (n := n) (k := k) (p := q)
      (Ω := Set.univ) (ζ m) (hζ m) (hcs m)) Filter.atTop (nhds g) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  exact (isClosed_WkpSubmoduleOn n k r Set.univ).mem_of_tendsto
    (((leibnizAmbientCLM (r := r) k f).continuous.tendsto g).comp htend)
    (Filter.Eventually.of_forall fun m ↦ leibnizAmbientCLM_mem_of_smooth f (ζ m) (hζ m) (hcs m))

/-- The constant `card (DerivIndex n k) 2^k` of the Hölder product bound. -/
def holderProductBound (n k : ℕ) : ℝ :=
  Fintype.card (DerivIndex n k) * 2 ^ k

theorem holderProductBound_nonneg (n k : ℕ) : 0 ≤ holderProductBound n k := by
  unfold holderProductBound
  positivity

/-- The norm of the assembled Leibniz rows. -/
theorem norm_leibnizAmbientCLM_apply_le (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    ‖leibnizAmbientCLM (r := r) k f g‖ ≤ holderProductBound n k * ‖f‖ * ‖g‖ := by
  apply (PiLp.norm_le_sum_norm _).trans
  calc
    _ ≤ ∑ _a : DerivIndex n k, 2 ^ k * ‖f‖ * ‖g‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [leibnizAmbientCLM_apply]
      apply (norm_leibnizRowCLM_apply_le _ f g).trans
      gcongr
      · norm_num
      · simpa using a.toList_length_le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, holderProductBound]
      ring

section Product

/-- The normed group structure on bounded maps `W^{k,q}(ℝ^n) →L W^{k,r}(ℝ^n)`, named locally to
stabilize typeclass search. -/
local instance holderOperatorNormedAddCommGroup :
    NormedAddCommGroup (W^{k,q}(ℝ^n) →L[ℝ] W^{k,r}(ℝ^n)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The real normed space structure on bounded maps `W^{k,q}(ℝ^n) →L W^{k,r}(ℝ^n)`. -/
local instance holderOperatorNormedSpace :
    NormedSpace ℝ (W^{k,q}(ℝ^n) →L[ℝ] W^{k,r}(ℝ^n)) :=
  ContinuousLinearMap.toNormedSpace

/-- The product of `f ∈ W^{k,p}(ℝ^n)` and `g ∈ W^{k,q}(ℝ^n)` in `W^{k,r}(ℝ^n)`, for
`1/p + 1/q = 1/r` and `q < ∞`, as a bounded bilinear map. -/
def holderProduct (hq : q ≠ ∞) (k : ℕ) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,q}(ℝ^n) →L[ℝ] W^{k,r}(ℝ^n) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun f g ↦ ⟨leibnizAmbientCLM (r := r) k f g, leibnizAmbientCLM_mem hq f g⟩)
      (fun f₁ f₂ g ↦ Subtype.ext (by simp))
      (fun c f g ↦ Subtype.ext (by simp))
      (fun f g₁ g₂ ↦ Subtype.ext (by simp))
      (fun c f g ↦ Subtype.ext (by simp)))
    (holderProductBound n k) (fun f g ↦ norm_leibnizAmbientCLM_apply_le f g)

/-- The derivative bundle of the product is the family of Leibniz rows. -/
theorem coe_holderProduct (hq : q ≠ ∞) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    (holderProduct (r := r) hq k f g : WkpAmbientOn n k r Set.univ) =
      leibnizAmbientCLM (r := r) k f g :=
  rfl

/-- The Leibniz formula: the `a`-th weak derivative of the product is `∑ D^{α₂} f D^{α₁} g`
over the splittings of the word of `a`. -/
theorem wkpCoordinateCLM_holderProduct (hq : q ≠ ∞) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n))
    (a : DerivIndex n k) :
    wkpCoordinateCLM a (holderProduct (r := r) hq k f g) =
      leibnizRowCLM k a.toList.reverse f g := by
  rw [wkpCoordinateCLM_apply, coe_holderProduct, leibnizAmbientCLM_apply]

/-- The base representative of the product is the product of the base representatives. -/
theorem holderProduct_base_ae (hq : q ≠ ∞) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    baseRepresentative (holderProduct (r := r) hq k f g) =ᵐ[volume]
      fun x ↦ baseRepresentative f x * baseRepresentative g x := by
  have h := leibnizRowCLM_ae (r := r) [] f g
  simp only [domainMeasure, Measure.restrict_univ] at h
  change ((wkpCoordinateCLM (baseIndex n k) (holderProduct (r := r) hq k f g) :
    DerivLp n r Set.univ) : ℝ^n → ℝ) =ᵐ[volume] _
  rw [wkpCoordinateCLM_holderProduct, baseIndex_toList, List.reverse_nil]
  filter_upwards [h] with x hx
  rw [hx]
  simp [derivativeSplits, wordCoordinateCLM_of_le [] (Nat.zero_le k), baseRepresentative]

/-- The Hölder product bound
`‖f g‖_{W^{k,r}} ≤ holderProductBound n k ‖f‖_{W^{k,p}} ‖g‖_{W^{k,q}}`. -/
theorem norm_holderProduct_le (hq : q ≠ ∞) (f : W^{k,p}(ℝ^n)) (g : W^{k,q}(ℝ^n)) :
    ‖holderProduct (r := r) hq k f g‖ ≤ holderProductBound n k * ‖f‖ * ‖g‖ :=
  norm_leibnizAmbientCLM_apply_le f g

end Product

/-- The product `W^{k,4}(ℝ^n) × W^{k,4}(ℝ^n) → W^{k,2}(ℝ^n)`. -/
def l4Product (k : ℕ) : W^{k,4}(ℝ^n) →L[ℝ] W^{k,4}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  holderProduct (p := 4) (q := 4) (r := 2) (by simp) k

/-- The base representative of the `L⁴` product is the product of base representatives. -/
theorem l4Product_base_ae (f g : W^{k,4}(ℝ^n)) :
    baseRepresentative (l4Product k f g) =ᵐ[volume]
      fun x ↦ baseRepresentative f x * baseRepresentative g x :=
  holderProduct_base_ae _ f g

/-- The bound `‖f g‖_{H^k} ≤ holderProductBound n k ‖f‖_{W^{k,4}} ‖g‖_{W^{k,4}}`. -/
theorem norm_l4Product_le (f g : W^{k,4}(ℝ^n)) :
    ‖l4Product k f g‖ ≤ holderProductBound n k * ‖f‖ * ‖g‖ :=
  norm_holderProduct_le _ f g

/-- For `p = ∞` and `q = r = 2` the Hölder product is the multiplier `wkMultiplication` by a
`W^{k,∞}(ℝ^n)` coefficient. -/
theorem wkMultiplication_eq_holderProduct (k : ℕ) :
    wkMultiplication (n := n) k =
      holderProduct (p := ∞) (q := 2) (r := 2) ENNReal.ofNat_ne_top k := by
  refine ContinuousLinearMap.ext fun A ↦ ContinuousLinearMap.ext fun f ↦ ?_
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  simp only [domainMeasure, Measure.restrict_univ]
  exact (wkMultiplication_base_ae k A f).trans (holderProduct_base_ae _ A f).symm

end SobolevSpace.GraphSpace
