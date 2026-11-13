/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.PowerCutoff
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.DerivativeSplits
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderBounds
public import PDE.Spaces.Sobolev.Calculus.Product.WeakLeibniz
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Absorption in powered cutoff self-pairings

The weak Leibniz expansion separates the principal derivative from terms in
which at least one derivative hits the cutoff. Retained powers in those terms
allow their highest derivative factor to be absorbed into the same localized
energy. The remaining squares use strictly lower derivative words and are
supported in the cutoff annulus. Their constants are chosen before the radius
and the Sobolev input.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Every derivative of Sobolev cutoff multiplication is the finite
weak Leibniz expansion. No classical derivatives of the source are assumed. -/
theorem higherOrderCutoffCLM_word_ae (hk : 0 < k) (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{k,2}(Ω))
    (α : List (Fin n)) (hα : α.length ≤ k) :
    wkpWordRepresentative (higherOrderCutoffCLM hk hΩ ψ U) α =ᵐ[domainMeasure n Ω]
      weakLeibnizExpansion ψ.toFun (wkpWordRepresentative U) α.reverse := by
  have hbound (β : List (Fin n)) (_hβ : β.length ≤ k) :
      MemLp (iteratedPartialDeriv β ψ.toFun) ∞ (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv ψ.contDiff β).continuous
      |>.memLp_top_of_hasCompactSupport
        (iteratedPartialDeriv_hasCompactSupport ψ β) (domainMeasure n Ω)
  have hweak := (higherOrderCutoffCLM hk hΩ ψ U).property.hasWeakDerivativeOn_list α hα
  change HasWeakDerivativeOn Ω α (baseRepresentative (higherOrderCutoffCLM hk hΩ ψ U))
    (wkpCoordinateCLM (derivIndexOfList α hα) (higherOrderCutoffCLM hk hΩ ψ U)) at hweak
  have hprod := (hasWeakDerivativeOn_congr_ae
    (higherOrderCutoffCLM_base_ae hk hΩ ψ U) Filter.EventuallyEq.rfl).mp hweak
  simpa only [wkpWordRepresentative, dite_eq_left hα, wkpCoordinateCLM_apply] using
    hprod.unique_ae hΩ (U.hasWeakDerivativeOn_mul_smooth ψ.toFun ψ.contDiff hbound α hα)

/-- Reversing a derivative word leaves the weak derivative unchanged: the representative only
sees the length and the multiset of the word (and is `0` for words longer than `k`). -/
theorem wkpWordRepresentative_reverse_ae (U : W^{k,2}(Ω)) (α : List (Fin n)) :
    wkpWordRepresentative U α.reverse =ᵐ[domainMeasure n Ω] wkpWordRepresentative U α := by
  refine Filter.EventuallyEq.of_eq ?_
  by_cases hα : α.length ≤ k
  · have hr : α.reverse.length ≤ k := by simpa only [List.length_reverse] using hα
    simp only [wkpWordRepresentative, hα, hr, ↓reduceDIte]
    rw [derivIndexOfList_eq_of_perm hr hα (List.reverse_perm α)]
  · have hr : ¬ α.reverse.length ≤ k := by simpa only [List.length_reverse] using hα
    simp only [wkpWordRepresentative, hα, hr, ↓reduceDIte]

private theorem weakLeibnizExpansion_eq_principal_add
    (ψ : ℝ^n → ℝ) (D : List (Fin n) → ℝ^n → ℝ) (α : List (Fin n)) (x : ℝ^n) :
    weakLeibnizExpansion ψ D α x = ψ x * D α x +
      ∑ j : Fin (derivativeSplits α).tail.length,
        iteratedPartialDeriv ((derivativeSplits α).tail.get j).1 ψ x *
          D ((derivativeSplits α).tail.get j).2 x := by
  have hhead : ([], α) :: (derivativeSplits α).tail = derivativeSplits α :=
    List.cons_head?_tail (by simp only [derivativeSplits_head?, Option.mem_some_iff])
  change ((derivativeSplits α).map _).sum = _
  conv_lhs => rw [← hhead, List.map_cons, List.sum_cons]
  simp only [iteratedPartialDeriv]
  congr 1
  have hsum := congrArg (fun l ↦ (l.map (fun q : List (Fin n) × List (Fin n) ↦
    iteratedPartialDeriv q.1 ψ x * D q.2 x)).sum)
      (List.ofFn_get (derivativeSplits α).tail)
  rw [List.map_ofFn, List.sum_ofFn] at hsum
  exact hsum.symm

/-- Lower derivative squares in the annulus, with a coefficient for each
nonprincipal Leibniz split. Repeated splits preserve their multiplicities. -/
def radialCutoffLeibnizTail (α : List (Fin n))
    (C : Fin (derivativeSplits α).tail.length → ℝ) (R : ℝ)
    (D : List (Fin n) → ℝ^n → ℝ) : ℝ^n → ℝ :=
  {x | R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R}.indicator fun x ↦
    ∑ j : Fin (derivativeSplits α).tail.length,
      C j * R⁻¹ ^ (2 * ((derivativeSplits α).tail.get j).1.length) *
        D ((derivativeSplits α).tail.get j).2 x ^ 2

/-- A powered cutoff self-pairing controls its principal square up to
annular squares of strictly lower derivative words. The coefficients precede
the radius and the entire derivative family; no integrability is needed for
this pointwise algebraic estimate. -/
theorem exists_radialCutoff_weakLeibniz_pairing_lower_bound
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hα : α.length ≤ m) :
    ∃ C : Fin (derivativeSplits α).tail.length → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ (R : ℝ), 0 < R → ∀ (D : List (Fin n) → ℝ^n → ℝ) (x : ℝ^n),
      radialCutoff R x ^ (2 * m) * D α x ^ 2 ≤
        2 * (D α x * weakLeibnizExpansion (fun y ↦ radialCutoff R y ^ (2 * m)) D α x) +
          radialCutoffLeibnizTail α C R D x := by
  classical
  let S := (derivativeSplits α).tail
  have hleft (j : Fin S.length) : (S.get j).1.length ≤ m := by
    have hlen := derivativeSplits_length (List.mem_of_mem_tail (S.get_mem j))
    omega
  choose B hB hbound using fun j : Fin S.length ↦
    exists_two_mul_abs_radialCutoff_pow_derivative_mul_le (S.get j).1 hm (hleft j)
  let N : ℝ := S.length + 1
  have hN : 0 < N := by dsimp [N]; positivity
  refine ⟨fun j ↦ B j / N⁻¹, fun j ↦ div_nonneg (hB j) (inv_nonneg.mpr hN.le), ?_⟩
  intro R hR D x
  let ψ : ℝ^n → ℝ := fun y ↦ radialCutoff R y ^ (2 * m)
  let E := ψ x * D α x ^ 2
  let t (j : Fin S.length) := iteratedPartialDeriv (S.get j).1 ψ x * D (S.get j).2 x
  have hexp := weakLeibnizExpansion_eq_principal_add ψ D α x
  by_cases hx : R ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * R
  · have heach (j : Fin S.length) :
        2 * |D α x * t j| ≤ N⁻¹ * E +
          B j / N⁻¹ * R⁻¹ ^ (2 * (S.get j).1.length) * D (S.get j).2 x ^ 2 := by
      simpa only [t, E, ψ, mul_assoc] using
        hbound j R N⁻¹ hR (inv_pos.mpr hN) x (D α x) (D (S.get j).2 x)
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) ↦ heach j
    have hmain : (S.length : ℝ) * (N⁻¹ * E) ≤ E := by
      have hE : 0 ≤ E := mul_nonneg
        (pow_nonneg (radialCutoff_mem_Icc R x).1 _) (sq_nonneg _)
      have hi : N * N⁻¹ = 1 := mul_inv_cancel₀ hN.ne'
      have hi' : (S.length : ℝ) * N⁻¹ ≤ 1 := by
        dsimp [N] at hi ⊢
        have := inv_nonneg.mpr hN.le
        nlinarith
      nlinarith
    have habs : |D α x * ∑ j : Fin S.length, t j| ≤
        ∑ j : Fin S.length, |D α x * t j| := by
      rw [Finset.mul_sum]
      exact Finset.abs_sum_le_sum_abs _ _
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hneg := neg_abs_le (D α x * ∑ j : Fin S.length, t j)
    change E ≤ 2 * (D α x * weakLeibnizExpansion ψ D α x) + _
    rw [hexp]
    rw [radialCutoffLeibnizTail,
      indicator_of_mem (show x ∈ {y : ℝ^n | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} from hx)]
    dsimp only [E, t, S, ψ] at hmain hsum habs hneg ⊢
    nlinarith
  · have ht (j : Fin S.length) : t j = 0 := by
      have hne := derivativeSplits_tail_first_ne_nil α (S.get j) (S.get_mem j)
      have hz : iteratedPartialDeriv (S.get j).1 ψ x = 0 := by
        by_cases hinner : ‖x‖ < R
        · exact iteratedPartialDeriv_radialCutoff_pow_zero_inside
            (S.get j).1 hne (2 * m) hR hinner
        · exact iteratedPartialDeriv_radialCutoff_pow_zero_outside
            (S.get j).1 (by omega : 0 < 2 * m) hR
              (lt_of_not_ge (fun houter ↦ hx ⟨le_of_not_gt hinner, houter⟩))
      simp only [t, hz, zero_mul]
    have hE : 0 ≤ E := mul_nonneg
      (pow_nonneg (radialCutoff_mem_Icc R x).1 _) (sq_nonneg _)
    change E ≤ 2 * (D α x * weakLeibnizExpansion ψ D α x) + _
    rw [hexp]
    change E ≤ 2 * (D α x * (ψ x * D α x + ∑ j : Fin S.length, t j)) + _
    simp only [ht, Finset.sum_const_zero, add_zero]
    rw [radialCutoffLeibnizTail,
      indicator_of_notMem (show x ∉ {y : ℝ^n | R ≤ ‖y‖ ∧ ‖y‖ ≤ 2 * R} from hx)]
    dsimp only [E] at hE ⊢
    nlinarith

/-- Sobolev cutoff multiplication satisfies the retained-power
self-pairing estimate. The annular remainder involves only shorter words of
the input graph. All coefficients are fixed before the domain, radius,
cutoff realization, and source. -/
theorem exists_radialCutoff_sobolev_pairing_lower_bound
    (α : List (Fin n)) {m : ℕ} (hm : 0 < m) (hαm : α.length ≤ m) :
    ∃ C : Fin (derivativeSplits α).tail.length → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {k : ℕ} (hk : 0 < k)
        (_hαk : α.length ≤ k) (R : ℝ) (_hR : 0 < R)
        (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      ψ.toFun = (fun x ↦ radialCutoff R x ^ (2 * m)) → ∀ U : W^{k,2}(Ω),
      ∀ᵐ x ∂domainMeasure n Ω,
      radialCutoff R x ^ (2 * m) * wkpWordRepresentative U α x ^ 2 ≤
        2 * (wkpWordRepresentative U α x *
          wkpWordRepresentative (higherOrderCutoffCLM hk hΩ ψ U) α x) +
        radialCutoffLeibnizTail α C R (wkpWordRepresentative U) x := by
  obtain ⟨C, hC, hbound⟩ := exists_radialCutoff_weakLeibniz_pairing_lower_bound α hm hαm
  refine ⟨C, hC, ?_⟩
  intro Ω hΩ k hk hαk R hR ψ hψ U
  have hr : α.reverse.length ≤ k := by simpa only [List.length_reverse] using hαk
  have heq := (wkpWordRepresentative_reverse_ae
    (higherOrderCutoffCLM hk hΩ ψ U) α).symm.trans
      (higherOrderCutoffCLM_word_ae hk hΩ ψ U α.reverse hr)
  simp only [List.reverse_reverse, hψ] at heq
  filter_upwards [heq] with x hx
  rw [hx]
  exact hbound R hR (wkpWordRepresentative U) x

/-- Every derivative in the annular remainder has lower order than the
principal word, including the zero jet when all derivatives hit the cutoff. -/
theorem radialCutoffLeibnizTail_word_lt (α : List (Fin n))
    (j : Fin (derivativeSplits α).tail.length) :
    ((derivativeSplits α).tail.get j).2.length < α.length := by
  have hlen := derivativeSplits_length
    (List.mem_of_mem_tail ((derivativeSplits α).tail.get_mem j))
  have hne := derivativeSplits_tail_first_ne_nil α _ ((derivativeSplits α).tail.get_mem j)
  have hpos := List.length_pos_iff.mpr hne
  omega

end SobolevSpace.Approximation
