/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Iteration
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.C1Domains
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# General Sobolev inequalities on bounded C¹ domains

The subcritical estimate, in `HigherOrder.Domains`, has reciprocal exponent `1/q = 1/p - k/n`.
In the supercritical range the classical derivative order is
`k - floor(n/p) - 1`. The Hölder exponent is `floor(n/p) + 1 - n/p`
when `n/p` is not an integer, and any strict exponent between zero and one
otherwise. At `p = ∞`, `n/p` is zero.

The target is the compatible classical derivative graph on the closure. The estimate is stated for
`evansNorm`, the norm (3) of Evans §5.1, which includes every derivative supremum norm and every
top-order Hölder seminorm. Only first-order extension from the C¹ boundary is used. The main result,
`exists_general_sobolev_holder_bound_of_hasC1GraphBoundary`, is Evans §5.6.3, Theorem 6(ii), with
the estimate (32), for `1 ≤ p ≤ ∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, the norm (3), p. 255; and §5.6.3, Theorem 6(ii), (32),
  pp. 284-286.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory HolderSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}
  [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The floor-indexed supercritical representative for every finite Sobolev exponent,
including one. The two exponent conditions distinguish integer from noninteger `n/p`. -/
theorem exists_higherHolder_representative_finite {p : NNReal}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsuper : (n : ℝ) / p < k)
    (hγint : (⌊(n : ℝ) / p⌋₊ : ℝ) = (n : ℝ) / p → (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p⌋₊ : ℝ) ≠ (n : ℝ) / p →
      (γ : ℝ) = (⌊(n : ℝ) / p⌋₊ : ℝ) + 1 - (n : ℝ) / p)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    ∃ F : CKGammaOn n (k - ⌊(n : ℝ) / p⌋₊ - 1) Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hn : 0 < n := Fact.out
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  let j := ⌊(n : ℝ) / p⌋₊
  have hjk : j < k := (Nat.floor_lt (div_nonneg hnR.le hp0.le)).mpr hsuper
  have horder : k = (k - j - 1) + 1 + j := by omega
  have hf := Nat.floor_le (div_nonneg hnR.le hp0.le)
  have hf' := Nat.lt_floor_add_one ((n : ℝ) / p)
  have hmem : ∀ V : W^{(k - j - 1) + 1 + j,(p : ℝ≥0∞)}(Ω),
      ∃ F : CKGammaOn n (k - j - 1) Ω γ,
        F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative V := by
    by_cases heq : (j : ℝ) = (n : ℝ) / p
    · have hj : 0 < j := by
        have : (0 : ℝ) < j := heq ▸ div_pos hnR hp0
        exact_mod_cast this
      have hc : (j : ℝ) * p = n := (eq_div_iff hp0.ne').mp heq
      exact exists_higherHolder_of_critical_iteration hj hc (hγint heq)
    · have hsub : (j : ℝ) * p < n :=
        (lt_div_iff₀ hp0).mp (lt_of_le_of_ne hf heq)
      have hsup : (n : ℝ) < ((j : ℝ) + 1) * p := (div_lt_iff₀ hp0).mp hf'
      exact exists_higherHolder_of_subcritical_iteration hsub hsup (hγfrac heq)
  rw [← horder] at hmem
  exact hmem U

/-- A single classical representative in the exact general Sobolev target, for
all `1 ≤ p ≤ ∞`. For infinite `p`, the ratio `n / p.toReal` is zero. -/
theorem exists_higherHolder_representative {p : ℝ≥0∞} [hpFact : Fact (1 ≤ p)]
    (hsuper : (n : ℝ) / p.toReal < k)
    (hγint : (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) = (n : ℝ) / p.toReal → (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) ≠ (n : ℝ) / p.toReal →
      (γ : ℝ) = (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) + 1 - (n : ℝ) / p.toReal)
    (U : W^{k,p}(Ω)) :
    ∃ F : CKGammaOn n (k - ⌊(n : ℝ) / p.toReal⌋₊ - 1) Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  by_cases hp : p = ∞
  · subst p
    have hγ : (γ : ℝ) < 1 := hγint (by simp)
    have hk : 0 < k := by simpa using hsuper
    have h : ∀ V : W^{(k - 1) + 1,∞}(Ω),
        ∃ F : CKGammaOn n (k - 1) Ω γ,
          F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative V :=
      exists_higherHolder_of_infinity hγ
    rw [Nat.sub_add_cancel hk] at h
    have hf : ⌊(n : ℝ) / (∞ : ℝ≥0∞).toReal⌋₊ = 0 := by norm_num
    rw [hf, Nat.sub_zero]
    exact h U
  · lift p to NNReal using hp
    have hp1 : (1 : NNReal) ≤ p := by exact_mod_cast hpFact.out
    exact exists_higherHolder_representative_finite hp1 hsuper hγint hγfrac U

end SobolevSpace.GraphSpace

namespace SobolevSpace.Inequalities

open GraphSpace

/-- Evans §5.6.3, Theorem 6(ii), with the estimate (32): let `Ω` be bounded and open with C¹
graph boundary, `1 ≤ p ≤ ∞` and `n / p < k`, and let `γ = ⌊n/p⌋ + 1 - n/p` if `n / p` is not an
integer and `γ < 1` if it is. Then there is `C > 0` such that every `U ∈ W^{k,p}(Ω)` has a
representative `F ∈ C^{k-⌊n/p⌋-1,γ}(Ω̄)` with `F.evansNorm ≤ C * ‖U‖`. Neither higher-order
boundary regularity nor an embedding is assumed. -/
theorem exists_general_sobolev_holder_bound_of_hasC1GraphBoundary
    {n k : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)} {γ : Exponent} [Fact (1 ≤ p)]
    (hn : 0 < n) (hsuper : (n : ℝ) / p.toReal < k)
    (hγint : (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) = (n : ℝ) / p.toReal → (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) ≠ (n : ℝ) / p.toReal →
      (γ : ℝ) = (⌊(n : ℝ) / p.toReal⌋₊ : ℝ) + 1 - (n : ℝ) / p.toReal)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,p}(Ω),
      ∃ F : CKGammaOn n (k - ⌊(n : ℝ) / p.toReal⌋₊ - 1) Ω γ,
        F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U ∧
        F.evansNorm ≤ C * ‖U‖ := by
  have : Fact (0 < n) := ⟨hn⟩
  obtain ⟨atlas, _, _⟩ :=
    (Boundary.hasContDiffGraphBoundary_one_iff.mpr hboundary).exists_c1ExtensionAtlas
      le_rfl hopen hbounded
  let := atlas
  exact exists_pos_evansNorm_bound_of_representatives hopen
    (exists_higherHolder_representative hsuper hγint hγfrac)

/-- On the Hilbert scale, `k + floor(n/2) + 1` spatial derivatives give a
`C^{k,1/2}` representative in every positive dimension. This single budget
works for both even and odd dimensions. -/
theorem exists_halfHolder_representative_of_hasC1GraphBoundary
    {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent} (hγ : (γ : ℝ) = 1 / 2)
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω)
    (U : W^{k + n / 2 + 1,2}(Ω)) :
    ∃ F : CKGammaOn n k Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hfloor : ⌊(n : ℝ) / (2 : ℝ≥0∞).toReal⌋₊ = n / 2 := by
    simpa only [ENNReal.toReal_ofNat, Nat.cast_ofNat] using
      (Nat.floor_div_eq_div (K := ℝ) n 2)
  have hsuper : (n : ℝ) / (2 : ℝ≥0∞).toReal < (k + n / 2 + 1 : ℕ) := by
    have hlt := Nat.lt_floor_add_one ((n : ℝ) / (2 : ℝ≥0∞).toReal)
    rw [hfloor] at hlt
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hfrac : (⌊(n : ℝ) / (2 : ℝ≥0∞).toReal⌋₊ : ℝ) ≠
      (n : ℝ) / (2 : ℝ≥0∞).toReal →
      (γ : ℝ) = (⌊(n : ℝ) / (2 : ℝ≥0∞).toReal⌋₊ : ℝ) + 1 -
        (n : ℝ) / (2 : ℝ≥0∞).toReal := by
    rw [hfloor, hγ]
    norm_num only [ENNReal.toReal_ofNat]
    have he : (n % 2 : ℕ) + 2 * (n / 2 : ℕ) = n := Nat.mod_add_div n 2
    have heR : (n % 2 : ℕ) + 2 * (n / 2 : ℕ) = (n : ℝ) := by exact_mod_cast he
    intro hne
    have hrem : n % 2 = 1 := by
      have hlt := Nat.mod_lt n (by omega : 0 < 2)
      by_contra h
      have hz : n % 2 = 0 := by omega
      rw [hz] at heR
      apply hne
      linarith
    rw [hrem] at heR
    linarith
  obtain ⟨C, _, hC⟩ := exists_general_sobolev_holder_bound_of_hasC1GraphBoundary
    (γ := γ) hn hsuper (fun _ ↦ by rw [hγ]; norm_num) hfrac hopen hbounded hboundary
  have horder : (k + n / 2 + 1) - ⌊(n : ℝ) / (2 : ℝ≥0∞).toReal⌋₊ - 1 = k := by
    rw [hfloor]
    omega
  rw [horder] at hC
  obtain ⟨F, hF, _⟩ := hC U
  exact ⟨F, hF⟩

/-- The infinite-exponent case with the sum of the derivative essential suprema
on the right. The Sobolev graph norm is their maximum, so the graph-norm estimate is the
stronger one. -/
theorem exists_general_sobolev_holder_bound_infinity_of_hasC1GraphBoundary
    {n k : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}
    (hn : 0 < n) (hk : 0 < k) (hγ : (γ : ℝ) < 1)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hboundary : Boundary.HasC1GraphBoundary Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ U : W^{k,∞}(Ω),
      ∃ F : CKGammaOn n (k - 1) Ω γ,
        F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U ∧
        F.evansNorm ≤ C * ∑ a : DerivIndex n k, ‖U.val a‖ := by
  have h := exists_general_sobolev_holder_bound_of_hasC1GraphBoundary
    (n := n) (k := k) (p := ∞) (γ := γ) hn (by simpa using hk)
    (fun _ ↦ hγ) (by simp) hopen hbounded hboundary
  have hf : ⌊(n : ℝ) / (∞ : ℝ≥0∞).toReal⌋₊ = 0 := by norm_num
  rw [hf, Nat.sub_zero] at h
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun U ↦ ?_⟩
  obtain ⟨F, hF, hN⟩ := h U
  have hU : ‖U‖ ≤ ∑ a : DerivIndex n k, ‖U.val a‖ := by
    change ‖U.val‖ ≤ _
    rw [PiLp.norm_eq_ciSup]
    have : Nonempty (DerivIndex n k) := ⟨baseIndex n k⟩
    exact ciSup_le fun a ↦
      Finset.single_le_sum (fun b _ ↦ norm_nonneg (U.val b)) (Finset.mem_univ a)
  exact ⟨F, hF, hN.trans (mul_le_mul_of_nonneg_left hU hC.le)⟩

end SobolevSpace.Inequalities
