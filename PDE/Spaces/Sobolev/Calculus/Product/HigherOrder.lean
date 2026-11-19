/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Operator
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Higher-order Sobolev products

Closure of `W^{k,2}(Ω)` under multiplication by a coefficient in `W^{k,∞}(Ω)`, for every
positive integer order `k` and every open `Ω ⊆ ℝ^n`, with an explicit constant `C(n,k)` such
that

`‖A U‖_{W^{k,2}} ≤ C(n,k) ‖A‖_{W^{k,∞}} ‖U‖_{W^{k,2}}`.

The proof is an induction on the order. Order one is the bounded multiplier of
`Product.Operator`. Passing from order `m` to `m + 1`, the product of the order-`m` truncations
is given by the inductive hypothesis, the first derivatives of the product are the Leibniz
combinations `A ∂ᵢU + (∂ᵢA) U`, each again a product of order-`m` data, and the order-`(m+1)`
element is reassembled from these `n + 1` pieces by
`exists_succOrder_of_firstDerivatives_with_norm` from `Slicing.HigherOrder`. Uniqueness of weak
derivatives on the open set identifies the derivative coordinates of the inductive product with
the Leibniz combinations, which is where `IsOpen Ω` is used.

Evans derives `ζu ∈ W^{k,p}(U)` from the Leibniz formula
`D^α(ζu) = Σ_{β ≤ α} (α choose β) D^β ζ D^{α-β} u` for `ζ ∈ C_c^∞(U)` (PDE, §5.2.3,
Theorem 1(iv)), proved by induction on `|α|`. We also induct on the order; the multiplier is
only in `W^{k,∞}`, and only its Sobolev norm enters the constant.

## Main results

* `wkTopMultiplierNormBound`: the recursive constant `C(n,k)`. It is `1` at order zero,
  `w1TopMultiplierNormBound n` at order one, and gains a factor
  `succOrderAssemblyNormBound n (m+1) * (1 + 2n)` at each further order.
* `WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm`: the quantitative product theorem.
* `WkpSpaceOn.exists_mul_WkTop_WkTwo`: the same statement without the norm bound.

## Implementation notes

Both theorems are existence statements. On an open domain the product is unique, since a
`WkpSpaceOn` element is determined by its base coordinate, and `Product.HigherOrderOperator`
selects it as `wkTopProduct` and makes multiplication a bounded bilinear map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1(iv), (7), pp. 261-262, and step 3 of its
  proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/--
An explicit dimension-and-order dependent bound for multiplication
`W^{k,∞}(Ω) × W^{k,2}(Ω) → W^{k,2}(Ω)`.

The recurrence records the quantitative first-order Leibniz estimate and
the loss from assembling one additional Sobolev order. At order zero it
reduces to the sharp `L∞`-by-`L²` Hölder bound with constant one.
-/
noncomputable def wkTopMultiplierNormBound (n : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => w1TopMultiplierNormBound n
  | m + 2 =>
      succOrderAssemblyNormBound n (m + 1) *
        ((1 + 2 * (n : ℝ)) * wkTopMultiplierNormBound n (m + 1))

/-- The explicit higher-order multiplier bound is nonnegative. -/
theorem wkTopMultiplierNormBound_nonneg (n k : ℕ) :
    0 ≤ wkTopMultiplierNormBound n k := by
  induction k with
  | zero => simp [wkTopMultiplierNormBound]
  | succ k ih =>
    rcases k with _ | m
    · simpa [wkTopMultiplierNormBound] using w1TopMultiplierNormBound_nonneg (n := n)
    · exact mul_nonneg (succOrderAssemblyNormBound_nonneg (n := n) (m := m + 1))
        (mul_nonneg (by positivity) ih)

private theorem WkpSpaceOn.exists_mul_succTop_succTwo
    {m : ℕ} (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hmul :
      ∀ (B : W^{m,∞}(Ω)) (Z : W^{m,2}(Ω)),
        ∃ P : W^{m,2}(Ω),
          (((((P : WkpAmbientOn n m 2 Ω) (baseIndex n m) :
                DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
              fun x ↦
                (((B : WkpAmbientOn n m ∞ Ω) (baseIndex n m) :
                  DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
                (((Z : WkpAmbientOn n m 2 Ω) (baseIndex n m) :
                  DerivLp n 2 Ω) : ℝ^n → ℝ) x) ∧
            ‖P‖ ≤ C * ‖B‖ * ‖Z‖)
    (hΩopen : IsOpen Ω)
    (A : W^{m + 1,∞}(Ω))
    (U : W^{m + 1,2}(Ω)) :
    ∃ V : W^{m + 1,2}(Ω),
      (((((V : WkpAmbientOn n (m + 1) 2 Ω) (baseIndex n (m + 1)) :
            DerivLp n 2 Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω]
          fun x ↦
            (((A : WkpAmbientOn n (m + 1) ∞ Ω) (baseIndex n (m + 1)) :
              DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
            (((U : WkpAmbientOn n (m + 1) 2 Ω) (baseIndex n (m + 1)) :
              DerivLp n 2 Ω) : ℝ^n → ℝ) x) ∧
        ‖V‖ ≤
          (succOrderAssemblyNormBound n m *
              ((1 + 2 * (n : ℝ)) * C)) * ‖A‖ * ‖U‖ := by
  classical
  let A0 : W^{m,∞}(Ω) := lowerOrderCLM (by omega) A
  let U0 : W^{m,2}(Ω) := lowerOrderCLM (by omega) U
  let A1 : W^{1,∞}(Ω) := lowerOrderCLM (by omega) A
  let dA : Fin n → W^{m,∞}(Ω) := fun i ↦
    derivativeWordCLM (m := m + 1) (r := m) [i] (by simp [Nat.add_comm]) A
  let dU : Fin n → W^{m,2}(Ω) := fun i ↦
    derivativeWordCLM (m := m + 1) (r := m) [i] (by simp [Nat.add_comm]) U
  obtain ⟨P, hP, hPnorm⟩ := hmul A0 U0
  choose X hX hXnorm using fun i ↦ hmul A0 (dU i)
  choose Y hY hYnorm using fun i ↦ hmul (dA i) U0
  let D : Fin n → W^{m,2}(Ω) := fun i ↦ X i + Y i
  have hA0 : ‖A0‖ ≤ ‖A‖ := norm_lowerOrderCLM_apply_le (by omega) A
  have hU0 : ‖U0‖ ≤ ‖U‖ := norm_lowerOrderCLM_apply_le (by omega) U
  have hdA (i : Fin n) : ‖dA i‖ ≤ ‖A‖ := by
    simpa [dA] using norm_derivativeWordCLM_apply_le (m := m + 1) (r := m) (p := (∞ : ℝ≥0∞))
      [i] (by simp [Nat.add_comm]) A
  have hdU (i : Fin n) : ‖dU i‖ ≤ ‖U‖ := by
    simpa [dU] using norm_derivativeWordCLM_apply_le (m := m + 1) (r := m) (p := (2 : ℝ≥0∞))
      [i] (by simp [Nat.add_comm]) U
  have hbound {B : W^{m,∞}(Ω)} {Z Q : W^{m,2}(Ω)} (hB : ‖B‖ ≤ ‖A‖) (hZ : ‖Z‖ ≤ ‖U‖)
      (hQ : ‖Q‖ ≤ C * ‖B‖ * ‖Z‖) : ‖Q‖ ≤ C * ‖A‖ * ‖U‖ :=
    hQ.trans (by gcongr)
  have hDbase (i : Fin n) :
      ((((D i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω] fun x ↦
          (((A0 : WkpAmbientOn n m ∞ Ω) (baseIndex n m) : DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
            (((dU i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) : ℝ^n → ℝ) x +
          (((dA i : WkpAmbientOn n m ∞ Ω) (baseIndex n m) : DerivLp n ∞ Ω) : ℝ^n → ℝ) x *
            (((U0 : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) : ℝ^n → ℝ) x := by
    filter_upwards [Lp.coeFn_add ((X i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω)
      ((Y i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω), hX i, hY i]
      with x hx hxi hyi
    simpa [D, hxi, hyi] using hx
  have hDcompat (i : Fin n) :
      ((D i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω) =
        ((P : WkpAmbientOn n m 2 Ω) (firstDerivIndex n m hm i) : DerivLp n 2 Ω) := by
    refine Lp.ext ((P.property.hasWeakDerivativeOn_first hm i).unique_ae hΩopen
      ((hasWeakDerivativeOn_congr_ae hP (hDbase i)).2 ?_)).symm
    simpa [A0, U0, A1, dA, derivIndexOfList_singleton] using
      A1.hasWeakDerivativeOn_mul_W1Top_first hΩopen i
        ((U0 : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω)
        ((dU i : WkpAmbientOn n m 2 Ω) (baseIndex n m) : DerivLp n 2 Ω)
        (by simpa [U0, dU] using
          (U.property (firstDerivIndex n (m + 1) (by omega) i)).perm (by simp))
  obtain ⟨V, hV, hVnorm⟩ := exists_succOrder_of_firstDerivatives_with_norm hm P D
    fun i ↦ by simpa using hDcompat i
  have hsum : ∑ i, ‖D i‖ ≤ n * (2 * (C * ‖A‖ * ‖U‖)) := by
    refine (Finset.sum_le_card_nsmul _ _ (2 * (C * ‖A‖ * ‖U‖)) fun i _ ↦ ?_).trans_eq (by simp)
    exact (norm_add_le (X i) (Y i)).trans (by
      linarith [hbound hA0 (hdU i) (hXnorm i), hbound (hdA i) hU0 (hYnorm i)])
  refine ⟨V, hV.trans (by simpa [A0, U0] using hP), hVnorm.trans ?_⟩
  calc _ ≤ succOrderAssemblyNormBound n m * ((1 + 2 * (n : ℝ)) * (C * ‖A‖ * ‖U‖)) := by
        gcongr
        · exact succOrderAssemblyNormBound_nonneg
        · linarith [hbound hA0 hU0 hPnorm]
    _ = _ := by ring

/--
Quantitative higher-order Sobolev multiplication:

`‖A U‖_{W^{k,2}} ≤ C(n,k) ‖A‖_{W^{k,∞}} ‖U‖_{W^{k,2}}`.

The recursive constant `wkTopMultiplierNormBound` is explicit.  It starts
from the first-order weak Leibniz estimate and records the loss in each
successor-order assembly.
-/
theorem WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm
    (k : ℕ) (hk : 0 < k)
    (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω))
    (U : W^{k,2}(Ω)) :
    ∃ V : W^{k,2}(Ω),
      (baseRepresentative V =ᵐ[domainMeasure n Ω]
          fun x ↦ baseRepresentative A x * baseRepresentative U x) ∧
        ‖V‖ ≤ wkTopMultiplierNormBound n k * ‖A‖ * ‖U‖ := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases k with _ | r
    · exact ⟨w1TopMultiplierCLM hΩopen A U, w1TopMultiplierCLM_base_ae hΩopen A U, by
        simpa [wkTopMultiplierNormBound] using norm_w1TopMultiplierCLM_apply_le hΩopen A U⟩
    · simpa [wkTopMultiplierNormBound, baseRepresentative] using
        WkpSpaceOn.exists_mul_succTop_succTwo (by omega) _
          (wkTopMultiplierNormBound_nonneg n (r + 1)) (fun B Z ↦ ih (by omega) B Z) hΩopen A U

/--
Every positive Sobolev order is closed under multiplication by a coefficient
of the same `W^{k,infinity}` order:

`W^{k,infinity}(Ω) * W^{k,2}(Ω) subset W^{k,2}(Ω)`.

This is the existence form; `Product.HigherOrderOperator` selects the
unique product `wkTopProduct` and its bounded operators.
-/
theorem WkpSpaceOn.exists_mul_WkTop_WkTwo
    (k : ℕ) (hk : 0 < k)
    (hΩopen : IsOpen Ω)
    (A : W^{k,∞}(Ω))
    (U : W^{k,2}(Ω)) :
    ∃ V : W^{k,2}(Ω),
      baseRepresentative V =ᵐ[domainMeasure n Ω]
        fun x ↦ baseRepresentative A x * baseRepresentative U x := by
  obtain ⟨V, hV, _⟩ :=
    WkpSpaceOn.exists_mul_WkTop_WkTwo_with_norm
      (n := n) (Ω := Ω) k hk hΩopen A U
  exact ⟨V, hV⟩

end SobolevSpace.GraphSpace
