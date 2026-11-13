/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
import PDE.Analysis.MeasureTheory.Lp.WeightedL2
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Weak products with mixed derivative allocations

High derivatives use L2 bounds on one factor and bounded lower derivatives
on the other. The first weak product identity is applied only where a
coefficient and its first derivative are bounded.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section
set_option linter.missingDocs true

namespace SobolevSpace

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace PDE.Common
open scoped ENNReal Sobolev

/-- The first weak product rule requires only C1 regularity of its bounded
coefficient, including a bound for its first derivatives. -/
theorem weak_mul_contDiff_one
    {n : ℕ} {Ω : Set ℝ^n} (hΩ : IsOpen Ω) {a f df : ℝ^n → ℝ} (ha : ContDiff ℝ 1 a)
    (haLp : MemLp a ∞ (domainMeasure n Ω))
    (hdaLp : ∀ j, MemLp (∂[j] a) ∞ (domainMeasure n Ω))
    (hf : MemLp f 2 (domainMeasure n Ω)) (hdf : MemLp df 2 (domainMeasure n Ω))
    (i : Fin n) (hweak : HasWeakDerivativeOn Ω [i] f df) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ a x * f x)
      (fun x ↦ a x * df x + (∂[i] a) x * f x) := by
  have hmem (α : DerivIndex n 1) :
      MemLp (iteratedPartialDeriv α.toList a) ∞ (domainMeasure n Ω) := by
    rcases hword : α.toList with _ | ⟨j, rest⟩
    · exact haLp
    · have hlen := α.toList_length_le
      rw [hword] at hlen
      have hr : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst rest
      exact hdaLp j
  let A := mkWkpSpaceOnOfContDiffMemLpFinite (Ω := Ω) (k := 1) (p := ∞) a ha hmem
  have hA := mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (Ω := Ω) (k := 1) (p := ∞) a ha hmem (baseIndex n 1)
  have hdA := mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae
    (Ω := Ω) (k := 1) (p := ∞) a ha hmem (singleDerivIndex n i)
  simp only [baseIndex_toList, singleDerivIndex_toList, iteratedPartialDeriv] at hA hdA
  have hweak' : HasWeakDerivativeOn Ω [i] (hf.toLp f : ℝ^n → ℝ) (hdf.toLp df : ℝ^n → ℝ) :=
    (hasWeakDerivativeOn_congr_ae hf.coeFn_toLp hdf.coeFn_toLp).2 hweak
  have hp := WkpSpaceOn.hasWeakDerivativeOn_mul_W1Top_first hΩ A i
    (hf.toLp f) (hdf.toLp df) hweak'
  apply (hasWeakDerivativeOn_congr_ae
    (by
      filter_upwards [hA, hf.coeFn_toLp] with x hx hfx
      exact congrArg₂ (· * ·) hx hfx)
    (by
      filter_upwards [hA, hdA, hf.coeFn_toLp, hdf.coeFn_toLp] with x hx hdx hfx hdfx
      exact congrArg₂ (· + ·) (congrArg₂ (· * ·) hx hdfx)
        (congrArg₂ (· * ·) hdx hfx))).1 hp

/-- The word expansion of a product of two weak derivative families. Repeated
splittings retain the usual Leibniz multiplicities. -/
def mixedWeakLeibnizExpansion {n : ℕ}
    (F G : List (Fin n) → ℝ^n → ℝ) (α : List (Fin n)) : ℝ^n → ℝ := fun x ↦
  ((derivativeSplits α).map fun q ↦ F q.1 x * G q.2 x).sum

attribute [inherit_doc mixedWeakLeibnizExpansion] mixedWeakLeibnizExpansion.eq_1

/-- The expansion for the empty word is the product of the base representatives. -/
@[simp] theorem mixedWeakLeibnizExpansion_nil {n : ℕ}
    (F G : List (Fin n) → ℝ^n → ℝ) :
    mixedWeakLeibnizExpansion F G [] = fun x ↦ F [] x * G [] x := by
  funext x
  simp [mixedWeakLeibnizExpansion, derivativeSplits]

private theorem mixed_product_memLp {n k : ℕ} {Ω : Set ℝ^n}
    (F G : List (Fin n) → ℝ^n → ℝ)
    (hF : ∀ β, β.length ≤ k → MemLp (F β) 2 (domainMeasure n Ω))
    (hG : ∀ β, β.length ≤ k → MemLp (G β) 2 (domainMeasure n Ω))
    (hFtop : ∀ β, β.length ≤ 1 → MemLp (F β) ∞ (domainMeasure n Ω))
    (hGtop : ∀ β, β.length + 2 ≤ k → MemLp (G β) ∞ (domainMeasure n Ω))
    (β γ : List (Fin n)) (hβγ : β.length + γ.length ≤ k) :
    MemLp (fun x ↦ F β x * G γ x) 2 (domainMeasure n Ω) := by
  by_cases hβ : β.length ≤ 1
  · exact (hFtop β hβ).fun_mul (hG γ (by omega))
  · simpa only [mul_comm] using
      (hGtop γ (by omega)).fun_mul (hF β (by omega))

private theorem mixed_product_step {n k : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (F G : List (Fin n) → ℝ^n → ℝ)
    (hF : ∀ β, β.length ≤ k → MemLp (F β) 2 (domainMeasure n Ω))
    (hG : ∀ β, β.length ≤ k → MemLp (G β) 2 (domainMeasure n Ω))
    (hFtop : ∀ β, β.length ≤ 2 → MemLp (F β) ∞ (domainMeasure n Ω))
    (hGtop : ∀ β, β.length + 2 ≤ k → MemLp (G β) ∞ (domainMeasure n Ω))
    (hFc : ∀ β, β.length ≤ 1 → ContDiff ℝ 1 (F β))
    (hGc : ∀ β, β.length + 3 ≤ k → ContDiff ℝ 1 (G β))
    (hFd : ∀ β i, β.length ≤ 1 → ∂[i] (F β) = F (i :: β))
    (hGd : ∀ β i, β.length + 3 ≤ k → ∂[i] (G β) = G (i :: β))
    (hFw : ∀ β i, β.length < k → HasWeakDerivativeOn Ω [i] (F β) (F (i :: β)))
    (hGw : ∀ β i, β.length < k → HasWeakDerivativeOn Ω [i] (G β) (G (i :: β)))
    (β γ : List (Fin n)) (hβγ : β.length + γ.length < k) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (fun x ↦ F β x * G γ x)
      (fun x ↦ F β x * G (i :: γ) x + F (i :: β) x * G γ x) := by
  by_cases hβ : β.length ≤ 1
  · have hd (j : Fin n) : MemLp (∂[j] (F β)) ∞ (domainMeasure n Ω) := by
      rw [hFd β j hβ]
      exact hFtop (j :: β) (by simp only [List.length_cons]; omega)
    simpa only [hFd β i hβ] using weak_mul_contDiff_one hΩ (hFc β hβ)
      (hFtop β (by omega)) hd (hG γ (by omega))
      (hG (i :: γ) (by simp only [List.length_cons]; omega)) i (hGw γ i (by omega))
  · have hγ : γ.length + 3 ≤ k := by omega
    have hd (j : Fin n) : MemLp (∂[j] (G γ)) ∞ (domainMeasure n Ω) := by
      rw [hGd γ j hγ]
      exact hGtop (j :: γ) (by simp only [List.length_cons]; omega)
    have hp := weak_mul_contDiff_one hΩ (hGc γ hγ) (hGtop γ (by omega)) hd
      (hF β (by omega)) (hF (i :: β) (by simp only [List.length_cons]; omega))
      i (hFw β i (by omega))
    simpa only [hGd γ i hγ, mul_comm, add_comm] using hp

private theorem mixed_expansion_memLp {n k : ℕ} {Ω : Set ℝ^n}
    (F G : List (Fin n) → ℝ^n → ℝ)
    (hprod : ∀ β γ, β.length + γ.length ≤ k →
      MemLp (fun x ↦ F β x * G γ x) 2 (domainMeasure n Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    MemLp (mixedWeakLeibnizExpansion F G α) 2 (domainMeasure n Ω) := by
  have hm (j : Fin (derivativeSplits α).length) :
      MemLp (fun x ↦ F ((derivativeSplits α).get j).1 x *
        G ((derivativeSplits α).get j).2 x) 2 (domainMeasure n Ω) := by
    apply hprod
    rw [derivativeSplits_length ((derivativeSplits α).get_mem j)]
    exact hα
  have heq : mixedWeakLeibnizExpansion F G α = fun x ↦
      ∑ j : Fin (derivativeSplits α).length,
        F ((derivativeSplits α).get j).1 x * G ((derivativeSplits α).get j).2 x := by
    funext x
    exact (Fin.sum_univ_fun_getElem (derivativeSplits α) _).symm
  rw [heq]
  exact memLp_finsetSum Finset.univ (fun j _ ↦ hm j)

private theorem mixed_expansion_step {n k : ℕ} {Ω : Set ℝ^n}
    (F G : List (Fin n) → ℝ^n → ℝ)
    (hstep : ∀ β γ, β.length + γ.length < k → ∀ i,
      HasWeakDerivativeOn Ω [i] (fun x ↦ F β x * G γ x)
        (fun x ↦ F β x * G (i :: γ) x + F (i :: β) x * G γ x))
    (α : List (Fin n)) (hα : α.length < k) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (mixedWeakLeibnizExpansion F G α)
      (mixedWeakLeibnizExpansion F G (i :: α)) := by
  let S := derivativeSplits α
  let f (j : Fin S.length) : ℝ^n → ℝ := fun x ↦ F (S.get j).1 x * G (S.get j).2 x
  let g (j : Fin S.length) : ℝ^n → ℝ := fun x ↦
    F (S.get j).1 x * G (i :: (S.get j).2) x +
      F (i :: (S.get j).1) x * G (S.get j).2 x
  have hlen (j : Fin S.length) : (S.get j).1.length + (S.get j).2.length = α.length :=
    derivativeSplits_length (S.get_mem j)
  have hw (j : Fin S.length) : HasWeakDerivativeOn Ω [i] (f j) (g j) :=
    hstep _ _ (by rw [hlen]; exact hα) i
  have hs := hasWeakDerivativeOn_finsetSum Finset.univ f g [i]
    (fun j _ ↦ hw j)
  have heq : mixedWeakLeibnizExpansion F G (i :: α) = fun x ↦ ∑ j, g j x := by
    funext x
    simp only [mixedWeakLeibnizExpansion, derivativeSplits, List.map_append,
      List.map_map, List.sum_append, Function.comp_def]
    rw [← List.sum_map_add, ← Fin.sum_univ_fun_getElem]
    rfl
  rw [heq]
  convert hs using 1
  funext x
  exact (Fin.sum_univ_fun_getElem S _).symm

/-- A finite weak Leibniz formula with mixed regularity. Only the first two
velocity-type derivatives are bounded; higher ones may lie merely in L2.
The second factor supplies bounded complementary low derivatives. -/
theorem hasWeakDerivativeOn_mixedWeakLeibniz {n k : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (F G : List (Fin n) → ℝ^n → ℝ)
    (hF : ∀ β, β.length ≤ k → MemLp (F β) 2 (domainMeasure n Ω))
    (hG : ∀ β, β.length ≤ k → MemLp (G β) 2 (domainMeasure n Ω))
    (hFtop : ∀ β, β.length ≤ 2 → MemLp (F β) ∞ (domainMeasure n Ω))
    (hGtop : ∀ β, β.length + 2 ≤ k → MemLp (G β) ∞ (domainMeasure n Ω))
    (hFc : ∀ β, β.length ≤ 1 → ContDiff ℝ 1 (F β))
    (hGc : ∀ β, β.length + 3 ≤ k → ContDiff ℝ 1 (G β))
    (hFd : ∀ β i, β.length ≤ 1 → ∂[i] (F β) = F (i :: β))
    (hGd : ∀ β i, β.length + 3 ≤ k → ∂[i] (G β) = G (i :: β))
    (hFw : ∀ β i, β.length < k → HasWeakDerivativeOn Ω [i] (F β) (F (i :: β)))
    (hGw : ∀ β i, β.length < k → HasWeakDerivativeOn Ω [i] (G β) (G (i :: β)))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    HasWeakDerivativeOn Ω α (fun x ↦ F [] x * G [] x)
      (mixedWeakLeibnizExpansion F G α.reverse) := by
  have hprod := mixed_product_memLp F G hF hG (fun β hβ ↦ hFtop β (by omega)) hGtop
  have hstep := mixed_product_step hΩ F G hF hG hFtop hGtop hFc hGc hFd hGd hFw hGw
  let L := fun (β : List (Fin n)) ↦ mixedWeakLeibnizExpansion F G β.reverse
  have hbase : LocallyIntegrableOn (L []) Ω volume := by
    apply memLp_locallyIntegrableOn_domain (p := 2) _ (by norm_num)
    simpa only [L, List.reverse_nil, mixedWeakLeibnizExpansion_nil] using
      hprod [] [] (by simp)
  have hchain (β : List (Fin n)) (i : Fin n) (hβ : β.length < k) :
      HasWeakDerivativeOn Ω [i] (L β) (L (β ++ [i])) := by
    simpa only [L, List.reverse_append, List.reverse_singleton, List.singleton_append] using
      mixed_expansion_step F G hstep β.reverse (by simpa using hβ) i
  simpa only [L, List.reverse_nil, mixedWeakLeibnizExpansion_nil] using
    hasWeakDerivativeOn_of_append_single_chain_order k L hbase hchain α hα

/-- Mixed derivative allocations put every term of the finite product expansion in L2. -/
theorem mixedWeakLeibnizExpansion_memLp {n k : ℕ} {Ω : Set ℝ^n}
    (F G : List (Fin n) → ℝ^n → ℝ)
    (hF : ∀ β, β.length ≤ k → MemLp (F β) 2 (domainMeasure n Ω))
    (hG : ∀ β, β.length ≤ k → MemLp (G β) 2 (domainMeasure n Ω))
    (hFtop : ∀ β, β.length ≤ 1 → MemLp (F β) ∞ (domainMeasure n Ω))
    (hGtop : ∀ β, β.length + 2 ≤ k → MemLp (G β) ∞ (domainMeasure n Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    MemLp (mixedWeakLeibnizExpansion F G α) 2 (domainMeasure n Ω) :=
  mixed_expansion_memLp F G (mixed_product_memLp F G hF hG hFtop hGtop) α hα

/-- The mixed expansion has a quantitative L2 bound using only first-order
supremum bounds on the first factor. Its second derivatives need no uniform
supremum estimate for this bound. -/
theorem lpNorm_mixedWeakLeibnizExpansion_le {n k : ℕ} {Ω : Set ℝ^n}
    (F G : List (Fin n) → ℝ^n → ℝ)
    (hF : ∀ β, β.length ≤ k → MemLp (F β) 2 (domainMeasure n Ω))
    (hG : ∀ β, β.length ≤ k → MemLp (G β) 2 (domainMeasure n Ω))
    (hFtop : ∀ β, β.length ≤ 1 → MemLp (F β) ∞ (domainMeasure n Ω))
    (hGtop : ∀ β, β.length + 2 ≤ k → MemLp (G β) ∞ (domainMeasure n Ω))
    {AF BF AG BG : ℝ} (hAF : 0 ≤ AF) (hBF : 0 ≤ BF) (hAG : 0 ≤ AG) (hBG : 0 ≤ BG)
    (hFbound : ∀ β, β.length ≤ k → lpNorm (F β) 2 (domainMeasure n Ω) ≤ BF)
    (hGbound : ∀ β, β.length ≤ k → lpNorm (G β) 2 (domainMeasure n Ω) ≤ BG)
    (hFtopBound : ∀ β, β.length ≤ 1 → lpNorm (F β) ∞ (domainMeasure n Ω) ≤ AF)
    (hGtopBound : ∀ β, β.length + 2 ≤ k → lpNorm (G β) ∞ (domainMeasure n Ω) ≤ AG)
    (α : List (Fin n)) (hα : α.length ≤ k) :
    lpNorm (mixedWeakLeibnizExpansion F G α) 2 (domainMeasure n Ω) ≤
      2 ^ α.length * (AF * BG + BF * AG) := by
  let S := derivativeSplits α
  let f (j : Fin S.length) : ℝ^n → ℝ := fun x ↦ F (S.get j).1 x * G (S.get j).2 x
  have hlen (j : Fin S.length) : (S.get j).1.length + (S.get j).2.length = α.length :=
    derivativeSplits_length (S.get_mem j)
  have hm (j : Fin S.length) : MemLp (f j) 2 (domainMeasure n Ω) :=
    mixed_product_memLp F G hF hG hFtop hGtop _ _ (by rw [hlen]; exact hα)
  have hb (j : Fin S.length) : lpNorm (f j) 2 (domainMeasure n Ω) ≤ AF * BG + BF * AG := by
    have hj := hlen j
    by_cases hleft : (S.get j).1.length ≤ 1
    · apply (lpNorm_mul_le_lpNorm_top_mul_lpNorm
        (hFtop (S.get j).1 hleft) (hG (S.get j).2 (by omega))).trans
      exact (mul_le_mul (hFtopBound (S.get j).1 hleft) (hGbound (S.get j).2 (by omega))
        lpNorm_nonneg hAF).trans (le_add_of_nonneg_right (mul_nonneg hBF hAG))
    · have hright : (S.get j).2.length + 2 ≤ k := by omega
      have h := lpNorm_mul_le_lpNorm_top_mul_lpNorm
        (hGtop (S.get j).2 hright) (hF (S.get j).1 (by omega))
      have hb' := h.trans (mul_le_mul (hGtopBound (S.get j).2 hright)
        (hFbound (S.get j).1 (by omega)) lpNorm_nonneg hAG)
      have heq : f j = fun x ↦ G (S.get j).2 x * F (S.get j).1 x := by
        funext x
        exact mul_comm _ _
      rw [heq]
      have hsum : AG * BF ≤ AF * BG + BF * AG := by
        rw [mul_comm AG BF]
        exact le_add_of_nonneg_left (mul_nonneg hAF hBG)
      exact hb'.trans hsum
  have heq : mixedWeakLeibnizExpansion F G α = ∑ j, f j := by
    funext x
    simp only [Finset.sum_apply]
    change (S.map fun q ↦ F q.1 x * G q.2 x).sum = ∑ j, f j x
    exact (Fin.sum_univ_fun_getElem S (fun q ↦ F q.1 x * G q.2 x)).symm
  rw [heq]
  calc
    lpNorm (∑ j, f j) 2 (domainMeasure n Ω) ≤ ∑ j, lpNorm (f j) 2 (domainMeasure n Ω) :=
      lpNorm_sum_le (fun j _ ↦ hm j) (by norm_num)
    _ ≤ ∑ _j : Fin S.length, (AF * BG + BF * AG) := Finset.sum_le_sum (fun j _ ↦ hb j)
    _ = 2 ^ α.length * (AF * BG + BF * AG) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        S, length_derivativeSplits, Nat.cast_pow, Nat.cast_ofNat]

private def mixedClassicalWord {n k : ℕ} {Ω : Set ℝ^n}
    (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ) (s : ℕ) (β : List (Fin n)) : ℝ^n → ℝ :=
  if β.length ≤ s then iteratedPartialDeriv β f else wkpWordRepresentative U β

private theorem mixedClassicalWord_ae {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (hrep : f =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (β : List (Fin n)) (hβ : β.length ≤ k) :
    mixedClassicalWord U f s β =ᵐ[domainMeasure n Ω] wkpWordRepresentative U β := by
  by_cases hbs : β.length ≤ s
  · simp only [mixedClassicalWord, ite_eq_left hbs]
    have hw : HasWeakDerivativeOn Ω β (baseRepresentative U)
        (wkpWordRepresentative U β) := by
      simpa only [wkpWordRepresentative, dite_eq_left hβ, baseRepresentative] using
        U.property.hasWeakDerivativeOn_list β hβ
    have hc := hasWeakDerivativeOn_iteratedPartialDeriv_finite (Ω := Ω) β
      (hf.of_le (by exact_mod_cast hbs))
    have hc' := (hasWeakDerivativeOn_congr_ae hrep (Filter.EventuallyEq.refl _ _)).mp hc
    exact hc'.unique_ae hΩ hw
  · simp only [mixedClassicalWord, ite_eq_right hbs]
    rfl

private theorem mixedClassicalWord_memLp {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (hrep : f =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (β : List (Fin n)) (hβ : β.length ≤ k) :
    MemLp (mixedClassicalWord U f s β) 2 (domainMeasure n Ω) :=
  (wkpWordRepresentative_memLp U β hβ).ae_eq (mixedClassicalWord_ae hΩ U f hf hrep β hβ).symm

private theorem mixedClassicalWord_step {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (hrep : f =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (β : List (Fin n)) (i : Fin n) (hβ : β.length < k) :
    HasWeakDerivativeOn Ω [i] (mixedClassicalWord U f s β)
      (mixedClassicalWord U f s (i :: β)) := by
  apply (hasWeakDerivativeOn_congr_ae
    (mixedClassicalWord_ae hΩ U f hf hrep β (by omega))
    (mixedClassicalWord_ae hΩ U f hf hrep (i :: β)
      (by simp only [List.length_cons]; omega))).mpr
  exact wkpWordRepresentative_step U β i hβ

private theorem mixedClassicalWord_contDiff {n k s : ℕ} {Ω : Set ℝ^n}
    (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ) (hf : ContDiff ℝ s f)
    (β : List (Fin n)) (hβ : β.length + 1 ≤ s) :
    ContDiff ℝ 1 (mixedClassicalWord U f s β) := by
  simp only [mixedClassicalWord, ite_eq_left (show β.length ≤ s by omega)]
  exact (PDE.contDiff_iteratedPartialDeriv_of_le hf β (by omega)).of_le
    (by exact_mod_cast (show 1 ≤ s - β.length by omega))

private theorem mixedClassicalWord_partialDeriv {n k s : ℕ} {Ω : Set ℝ^n}
    (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (β : List (Fin n)) (i : Fin n) (hβ : β.length + 1 ≤ s) :
    ∂[i] (mixedClassicalWord U f s β) = mixedClassicalWord U f s (i :: β) := by
  simp only [mixedClassicalWord, ite_eq_left (show β.length ≤ s by omega),
    ite_eq_left (show (i :: β).length ≤ s by simpa using hβ), iteratedPartialDeriv]

private theorem mixedClassicalWord_lpNorm_le {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (hrep : f =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (β : List (Fin n)) (hβ : β.length ≤ k) :
    lpNorm (mixedClassicalWord U f s β) 2 (domainMeasure n Ω) ≤ ‖U‖ := by
  rw [lpNorm, eLpNorm_congr_ae (mixedClassicalWord_ae hΩ U f hf hrep β hβ)]
  simp only [wkpWordRepresentative, dite_eq_left hβ]
  exact PiLp.norm_apply_le (U : WkpAmbientOn n k 2 Ω) _

private theorem mixedClassicalWord_memLp_top {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : Bornology.IsBounded Ω) (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (β : List (Fin n)) (hβ : β.length ≤ s) :
    MemLp (mixedClassicalWord U f s β) ∞ (domainMeasure n Ω) := by
  simp only [mixedClassicalWord, ite_eq_left hβ]
  exact WeakChangeOfVariables.memLp_top_on_bounded_of_continuous hΩ
    (PDE.contDiff_iteratedPartialDeriv_of_le hf β hβ).continuous

private theorem mixedClassicalWord_lpNorm_top_le {n k s : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (U : W^{k,2}(Ω)) (f : ℝ^n → ℝ)
    (hf : ContDiff ℝ s f) (β : List (Fin n)) (hβ : β.length ≤ s)
    {A : ℝ} (hA : 0 ≤ A) (hbound : ∀ x ∈ Ω, ‖iteratedPartialDeriv β f x‖ ≤ A) :
    lpNorm (mixedClassicalWord U f s β) ∞ (domainMeasure n Ω) ≤ A := by
  have hm := mixedClassicalWord_memLp_top hΩb U f hf β hβ
  have hae : ∀ᵐ x ∂domainMeasure n Ω, ‖mixedClassicalWord U f s β x‖ ≤ A := by
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
    simpa only [mixedClassicalWord, ite_eq_left hβ] using hbound x hx
  rw [lpNorm, eLpNorm_exponent_top hm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono (by simp) (eLpNormEssSup_le_of_ae_bound hae)).trans_eq
    (ENNReal.toReal_ofReal hA)

/-- On a bounded open set, two Hk functions have an Hk product if the first
has a C2 representative and the second a C(k-2) representative. The estimate
uses only the first factor's derivatives through order one and the second
factor's derivatives through order k-2 in supremum norm. -/
theorem WkpSpaceOn.exists_mul_of_mixed_regularity {n k : ℕ} {Ω : Set ℝ^n}
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (U V : W^{k,2}(Ω)) (f g : ℝ^n → ℝ)
    (hf : ContDiff ℝ (2 : ℕ) f) (hg : ContDiff ℝ (k - 2 : ℕ) g)
    (hfrep : f =ᵐ[domainMeasure n Ω] baseRepresentative U)
    (hgrep : g =ᵐ[domainMeasure n Ω] baseRepresentative V)
    {AF AG : ℝ} (hAF : 0 ≤ AF) (hAG : 0 ≤ AG)
    (hfbound : ∀ β : List (Fin n), β.length ≤ 1 →
      ∀ x ∈ Ω, ‖iteratedPartialDeriv β f x‖ ≤ AF)
    (hgbound : ∀ β : List (Fin n), β.length + 2 ≤ k →
      ∀ x ∈ Ω, ‖iteratedPartialDeriv β g x‖ ≤ AG) :
    ∃ W : W^{k,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] (fun x ↦ f x * g x) ∧
      ‖W‖ ≤ √(Fintype.card (DerivIndex n k)) *
        (2 ^ k * (AF * ‖V‖ + ‖U‖ * AG)) := by
  let F := mixedClassicalWord U f 2
  let G := mixedClassicalWord V g (k - 2)
  have hF := mixedClassicalWord_memLp (s := 2) hΩ U f hf hfrep
  have hG := mixedClassicalWord_memLp (s := k - 2) hΩ V g hg hgrep
  have hFt := mixedClassicalWord_memLp_top (s := 2) hΩb U f hf
  have hGt (β : List (Fin n)) (hβ : β.length + 2 ≤ k) :
      MemLp (G β) ∞ (domainMeasure n Ω) :=
    mixedClassicalWord_memLp_top (s := k - 2) hΩb V g hg β (by omega)
  have hweak (α : List (Fin n)) (hα : α.length ≤ k) :
      HasWeakDerivativeOn Ω α (fun x ↦ f x * g x)
        (mixedWeakLeibnizExpansion F G α.reverse) := by
    have h := hasWeakDerivativeOn_mixedWeakLeibniz hΩ F G hF hG hFt hGt
      (fun β hβ ↦ mixedClassicalWord_contDiff (s := 2) U f hf β (by omega))
      (fun β hβ ↦ mixedClassicalWord_contDiff (s := k - 2) V g hg β (by omega))
      (fun β i hβ ↦ mixedClassicalWord_partialDeriv (s := 2) U f β i (by omega))
      (fun β i hβ ↦ mixedClassicalWord_partialDeriv (s := k - 2) V g β i (by omega))
      (mixedClassicalWord_step (s := 2) hΩ U f hf hfrep)
      (mixedClassicalWord_step (s := k - 2) hΩ V g hg hgrep) α hα
    simpa only [F, G, mixedClassicalWord, List.length_nil, Nat.zero_le, ite_true,
      iteratedPartialDeriv] using h
  let d (a : DerivIndex n k) := mixedWeakLeibnizExpansion F G a.toList.reverse
  have hbase : d (baseIndex n k) = fun x ↦ f x * g x := by
    simp only [d, baseIndex_toList, List.reverse_nil, mixedWeakLeibnizExpansion_nil,
      F, G, mixedClassicalWord, List.length_nil, Nat.zero_le, ite_true, iteratedPartialDeriv]
  have hm (a : DerivIndex n k) : MemLp (d a) 2 (domainMeasure n Ω) :=
    mixedWeakLeibnizExpansion_memLp F G hF hG (fun β hβ ↦ hFt β (by omega)) hGt
      a.toList.reverse (by simpa using a.toList_length_le)
  have hw (a : DerivIndex n k) : HasWeakDerivativeOn Ω a.toList
      (fun x ↦ f x * g x) (d a) := hweak a.toList a.toList_length_le
  let W := mkWkpSpaceOnOfWeakDerivatives (fun x ↦ f x * g x) d hbase hm hw
  have hcoord (a : DerivIndex n k) :
      ((W : WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] d a :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae _ d hbase hm hw a
  let B := 2 ^ k * (AF * ‖V‖ + ‖U‖ * AG)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (a : DerivIndex n k) : lpNorm (d a) 2 (domainMeasure n Ω) ≤ B := by
    have h := lpNorm_mixedWeakLeibnizExpansion_le F G hF hG
      (fun β hβ ↦ hFt β (by omega)) hGt hAF (norm_nonneg U) hAG (norm_nonneg V)
      (mixedClassicalWord_lpNorm_le (s := 2) hΩ U f hf hfrep)
      (mixedClassicalWord_lpNorm_le (s := k - 2) hΩ V g hg hgrep)
      (fun β hβ ↦ mixedClassicalWord_lpNorm_top_le (s := 2) hΩ hΩb U f hf β (by omega)
        hAF (hfbound β hβ))
      (fun β hβ ↦ mixedClassicalWord_lpNorm_top_le (s := k - 2) hΩ hΩb V g hg β (by omega)
        hAG (hgbound β hβ)) a.toList.reverse (by simpa using a.toList_length_le)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by simpa using a.toList_length_le)
  have hrow (a : DerivIndex n k) : ‖((W : WkpAmbientOn n k 2 Ω) a)‖ ≤ B := by
    rw [Lp.norm_def, eLpNorm_congr_ae (hcoord a)]
    exact hb a
  have hsum : ∑ a : DerivIndex n k, ‖((W : WkpAmbientOn n k 2 Ω) a)‖ ^ 2 ≤
      (Fintype.card (DerivIndex n k) : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _a : DerivIndex n k, B ^ 2 := Finset.sum_le_sum fun a _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (hrow a) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨W, ?_, ?_⟩
  · exact (hcoord (baseIndex n k)).trans (Filter.EventuallyEq.of_eq hbase)
  · change ‖(W : WkpAmbientOn n k 2 Ω)‖ ≤ _
    rw [PiLp.norm_eq_of_L2]
    apply (Real.sqrt_le_sqrt hsum).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB]

end SobolevSpace
