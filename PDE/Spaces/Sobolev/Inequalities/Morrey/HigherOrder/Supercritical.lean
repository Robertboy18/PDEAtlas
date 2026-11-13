/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding
import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration

/-!
# Classical representatives in the supercritical Sobolev range

For finite `p > 1`, a Sobolev field of order `m` has a `C^k` representative
on the domain closure when `(m - k) p > n`. Only a first-order
extension atlas is used. Each subcritical step spends one weak derivative
to raise the exponent; the critical step reaches any finite exponent.
Once the exponent exceeds the dimension, the higher-order Morrey theorem
reconstructs the classical derivatives.

The theorems give existence and almost-everywhere agreement, without a norm
estimate or the optimal Hölder modulus of the top derivative.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k r : ℕ} {Ω : Set (ℝ^n)}
  [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

private theorem exists_contDiffOn_rep_of_dimension_lt
    {m : ℕ} {p : NNReal} [hpFact : Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 < p) (hnp : (n : ℝ) < p) (hkm : k + 1 ≤ m) :
    ∀ U : W^{m,(p : ℝ≥0∞)}(Ω),
    ∃ f : ℝ^n → ℝ, ContDiffOn ℝ k f (closure Ω) ∧
      f =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hpR : 1 < (p : ℝ) := by exact_mod_cast hp
  revert hpFact
  rw [← (ENNReal.ofReal_coe_nnreal (p := p))]
  intro inst V
  let f := finiteMorreyDerivativeRepresentativeOn hnp
    (Real.HolderConjugate.conjExponent hpR) [] (by simp; omega) V
  refine ⟨f, ?_, ?_⟩
  · exact finiteMorreyDerivativeRepresentativeOn_contDiffOn_closure hnp
      (Real.HolderConjugate.conjExponent hpR) k [] (by simpa using hkm) V
  · have hf := finiteMorreyDerivativeRepresentativeOn_ae hnp
      (Real.HolderConjugate.conjExponent hpR) [] (by simp; omega) V
    simpa only [f, baseRepresentative, derivativeWordIndex_baseIndex,
      derivIndexOfList_nil] using hf

/-- A completed Sobolev field has a classical `C^k` representative on the closure
when its remaining `r + 1` weak derivatives are supercritical. The finite exponent
may lie below, at, or above the dimension. The proof constructs the improved
integrability by first-order Sobolev steps; no higher-order extension operator
or classical regularity of the input representative is assumed. -/
private theorem exists_contDiffOn_rep_of_supercritical_add
    {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
     (hp : 1 < p)
    (hsuper : n < ((r : ℝ) + 1) * p)
    (U : W^{k + 1 + r,(p : ℝ≥0∞)}(Ω)) :
    ∃ f : ℝ^n → ℝ, ContDiffOn ℝ k f (closure Ω) ∧
      f =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  induction r generalizing p with
  | zero =>
      exact exists_contDiffOn_rep_of_dimension_lt hp
        (by simpa using hsuper) (by omega) U
  | succ r ih =>
      have hn : 0 < n := Fact.out
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp
      by_cases hnp : (n : ℝ) < p
      · exact exists_contDiffOn_rep_of_dimension_lt hp hnp (by omega) U
      have hpn : (p : ℝ) ≤ n := le_of_not_gt hnp
      by_cases heq : (p : ℝ) = n
      · have hn2 : 2 ≤ n := by
          have : (1 : ℝ) < n := by simpa [heq] using hpR
          have : 1 < n := by exact_mod_cast this
          omega
        have hpN : p = (n : NNReal) := by exact_mod_cast heq
        subst p
        have : Fact (1 ≤ (n : ℝ≥0∞)) :=
          ⟨by exact_mod_cast (Nat.succ_le_of_lt hn)⟩
        let q : NNReal := n + 1
        have hq : (1 : NNReal) < q := by
          dsimp [q]
          exact lt_add_of_pos_left 1 (by exact_mod_cast hn)
        have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
        let V := Embedding.criticalStep (k := k + 1 + r) hq.le U
        obtain ⟨f, hf, he⟩ := exists_contDiffOn_rep_of_dimension_lt (k := k) hq
          (by dsimp [q]; norm_num) (by omega) V
        refine ⟨f, hf, he.trans ?_⟩
        convert! Embedding.criticalStep_apply_ae (k := k + 1 + r) hq.le U
          (baseIndex n (k + 1 + r)) using 1
      · have hplt : (p : ℝ) < n := lt_of_le_of_ne hpn heq
        let q := Inequalities.higherOrderExponent n 1 p
        have hpq : p ≤ q :=
          Inequalities.le_higherOrderExponent (by simpa using hplt)
        have hq : (1 : NNReal) < q := hp.trans_le hpq
        have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq.le⟩
        let V := Embedding.firstOrderStep (k := k + 1 + r) hp.le hplt U
        have hsuperq : n < ((r : ℝ) + 1) * q := by
          have hqeq : (q : ℝ) = (p : ℝ) * n / (n - p) := by
            simpa only [q, Nat.cast_one, one_mul] using
              Inequalities.higherOrderExponent_coe (k := 1) (p := p)
                (by simpa using hplt)
          rw [hqeq]
          rw [← mul_div_assoc]
          apply (lt_div_iff₀ (sub_pos.mpr hplt)).2
          have hs : n < ((r : ℝ) + 2) * p := by
            simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
              using hsuper
          nlinarith [mul_pos hnR (sub_pos.mpr hs)]
        obtain ⟨f, hf, he⟩ := ih hq hsuperq V
        refine ⟨f, hf, he.trans ?_⟩
        convert! Embedding.firstOrderStep_apply_ae (k := k + 1 + r) hp.le hplt U
          (baseIndex n (k + 1 + r)) using 1

/-- If `0 < n`, `Ω` carries a `C1ExtensionAtlas`, `1 < p < ∞` and `n < (m - k) p`, then every
`U ∈ W^{m,p}(Ω)` has a representative `f` with `ContDiffOn ℝ k f (closure Ω)` that agrees almost
everywhere on `Ω` with `baseRepresentative U`. No norm bound or Hölder exponent is asserted. -/
theorem exists_contDiffOn_representative_of_supercritical
    {m : ℕ} {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
     (hp : 1 < p)
    (hsuper : n < ((m - k : ℕ) : ℝ) * p)
    (U : W^{m,(p : ℝ≥0∞)}(Ω)) :
    ∃ f : ℝ^n → ℝ, ContDiffOn ℝ k f (closure Ω) ∧
      f =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hn : 0 < n := Fact.out
  have hkm : k < m := by
    by_contra h
    have hsub : m - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hsub, Nat.cast_zero, zero_mul] at hsuper
    linarith
  have horder : k + 1 + (m - k - 1) = m := by omega
  have hsub : m - k - 1 + 1 = m - k := by omega
  have hsuper' : n < (((m - k - 1 : ℕ) : ℝ) + 1) * p := by
    have hcast : ((m - k - 1 : ℕ) : ℝ) + 1 = ((m - k : ℕ) : ℝ) := by
      exact_mod_cast hsub
    rwa [hcast]
  have h := exists_contDiffOn_rep_of_supercritical_add (Ω := Ω) (k := k) (r := m - k - 1)
     hp hsuper'
  rw [horder] at h
  exact h U

end SobolevSpace.GraphSpace
