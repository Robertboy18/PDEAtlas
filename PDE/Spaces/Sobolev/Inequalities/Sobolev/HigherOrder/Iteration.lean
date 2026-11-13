/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domains -- shake: keep

/-!
# Iterated Higher-Order Sobolev Embeddings

Higher-order bounded-domain embeddings, derived from the operational
first-order extension theorem. The point is to avoid assuming
an order-`k` extension operator when only an order-one extension is needed:
each derivative of order at most `k` is viewed as the base row of a
`W^{1,p}` slice, embedded at the first-order Sobolev exponent, and then the
resulting rows are reassembled into a `W^{k,p*}` bundle.

The construction preserves the original weak-derivative representatives
almost everywhere. It therefore composes without making arbitrary
pointwise choices and can be iterated in completed Sobolev spaces. The
constructions here are plain functions between completed graph spaces;
`Domain.BoundedEmbedding` proves that they are bounded linear maps.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, proof of Theorem 6, step 3, pp. 285-286.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace GraphSpace
namespace Embedding

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}

section FirstOrderStep

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
  {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]

/--
One operational Sobolev step

`W^{k+1,p}(Ω) -> W^{k,p*}(Ω)`,

where `p* = np/(n-p)` and `1 <= p < n`.

The proof applies the concrete first-order extension theorem separately to
each order-at-most-`k` derivative slice and then reassembles the resulting
rows. Thus no higher-order extension operator is assumed. This declaration
is a noncomputable function between completed graph spaces, not a bundled
linear or continuous map.
-/
noncomputable def firstOrderStep
    (hp : (1 : NNReal) ≤ p) (hsub : (p : ℝ) < n)
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω)) :
    W^{k,(Inequalities.higherOrderExponent n 1 p : ℝ≥0∞)}(Ω) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    (((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_succ k)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k)
    (p := (Inequalities.higherOrderExponent n 1 p : ℝ≥0∞))
    (Ω := Ω) (d (baseIndex n k)) d rfl
  · intro a
    let V : W^{1,(p : ℝ≥0∞)}(Ω) :=
      derivativeWordCLM (n := n) (m := k + 1) (r := 1)
        (p := (p : ℝ≥0∞)) (Ω := Ω) a.toList
        (Nat.add_le_add_right a.toList_length_le 1) U
    have hV :=
      Inequalities.memLp_firstOrderSobolevExponent_of_c1ExtensionAtlas
        (n := n) (p := p) (Ω := Ω) hp hsub V
    simpa [d, V] using hV
  · intro a
    simpa [d] using U.property (a.castOrder (Nat.le_succ k))

/--
The operational first-order step preserves every retained derivative
representative almost everywhere.
-/
theorem firstOrderStep_apply_ae
    (hp : (1 : NNReal) ≤ p) (hsub : (p : ℝ) < n)
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω))
    (a : DerivIndex n k) :
    ((((firstOrderStep hp hsub U :
        WkpAmbientOn n k
          (Inequalities.higherOrderExponent n 1 p : ℝ≥0∞) Ω) a :
            DerivLp n
              (Inequalities.higherOrderExponent n 1 p : ℝ≥0∞)
              Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Ω)
          (a.castOrder (Nat.le_succ k)) :
            DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun b ↦
    (((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Ω)
      (b.castOrder (Nat.le_succ k)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  simpa [firstOrderStep, d] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k)
      (p := (Inequalities.higherOrderExponent n 1 p : ℝ≥0∞))
      (Ω := Ω) (d (baseIndex n k)) d rfl
      (fun a ↦ by
        let V : W^{1,(p : ℝ≥0∞)}(Ω) :=
          derivativeWordCLM (n := n) (m := k + 1) (r := 1)
            (p := (p : ℝ≥0∞)) (Ω := Ω) a.toList
            (Nat.add_le_add_right a.toList_length_le 1) U
        have hV :=
          Inequalities.memLp_firstOrderSobolevExponent_of_c1ExtensionAtlas
            (n := n) (p := p) (Ω := Ω) hp hsub V
        simpa [d, V] using hV)
      (fun b ↦ by
        simpa [d] using U.property (b.castOrder (Nat.le_succ k))) a

end FirstOrderStep

section Iteration

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/--
The base row of `W^{j,p}` belongs to the closed-form Sobolev exponent
`p_j = np/(n-jp)`.

The proof iterates the operational first-order atlas embedding. Its
conclusion is stated directly as `MemLp`, avoiding any transport of a
completed Sobolev subtype across propositionally equal exponent formulas.
-/
theorem base_memLp_iterated
    {j : ℕ} {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p)
    (hsub : ((j : ℝ) * (p : ℝ)) < (n : ℝ))
    (U : W^{j,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      ((((U : WkpAmbientOn n j (p : ℝ≥0∞) Ω)
          (baseIndex n j) : DerivLp n (p : ℝ≥0∞) Ω) :
        ℝ^n → ℝ))
      (Inequalities.higherOrderExponent n j p : ℝ≥0∞)
      (domainMeasure n Ω) := by
  induction j generalizing p with
  | zero =>
      have hn : 0 < n := Fact.out
      simpa [Inequalities.higherOrderExponent_zero hn] using
        (MeasureTheory.Lp.memLp
          ((U : WkpAmbientOn n 0 (p : ℝ≥0∞) Ω)
            (baseIndex n 0)))
  | succ j ih =>
      have hn : 0 < n := Fact.out
      have hp0nn : (0 : NNReal) < p :=
        lt_of_lt_of_le (by norm_num) hp
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0nn
      have hpLt : (p : ℝ) < (n : ℝ) := by
        have hj0 : (0 : ℝ) ≤ j := by positivity
        have hsub' : ((j : ℝ) + 1) * (p : ℝ) < (n : ℝ) := by
          simpa [Nat.cast_add, Nat.cast_one] using hsub
        nlinarith [mul_nonneg hj0 (le_of_lt hp0)]
      let q : NNReal :=
        Inequalities.higherOrderExponent n 1 p
      have hq1 : (1 : NNReal) ≤ q :=
        Inequalities.one_le_higherOrderExponent hp
          (by simpa using hpLt)
      have : Fact (1 ≤ (q : ℝ≥0∞)) :=
        ⟨by exact_mod_cast hq1⟩
      let V :=
        firstOrderStep (n := n) (k := j) (Ω := Ω)
          hp hpLt U
      have hVU :
          ((((V : WkpAmbientOn n j (q : ℝ≥0∞) Ω)
                (baseIndex n j) : DerivLp n (q : ℝ≥0∞) Ω) :
              ℝ^n → ℝ))
            =ᵐ[domainMeasure n Ω]
              (((U : WkpAmbientOn n (j + 1) (p : ℝ≥0∞) Ω)
                  (baseIndex n (j + 1)) :
                DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ) := by
        simpa [q, V] using
          firstOrderStep_apply_ae
            (n := n) (k := j) (Ω := Ω)
            hp hpLt U (baseIndex n j)
      have hjqSub : (j : ℝ) * (q : ℝ) < (n : ℝ) := by
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
        have hqCoe :=
          Inequalities.higherOrderExponent_coe
            (n := n) (k := 1) (p := p) (by simpa using hpLt)
        simp only [Nat.cast_one, one_mul] at hqCoe
        rw [hqCoe]
        have hden : 0 < (n : ℝ) - (p : ℝ) := sub_pos.mpr hpLt
        rw [show
          (j : ℝ) *
              ((p : ℝ) * (n : ℝ) / ((n : ℝ) - (p : ℝ))) =
            ((j : ℝ) * ((p : ℝ) * (n : ℝ))) /
              ((n : ℝ) - (p : ℝ)) by ring]
        rw [div_lt_iff₀ hden]
        have hsub' : ((j : ℝ) + 1) * (p : ℝ) < (n : ℝ) := by
          simpa [Nat.cast_add, Nat.cast_one] using hsub
        nlinarith [mul_pos hn0 hden]
      have hV := ih (p := q) hq1 hjqSub V
      have hU :
          MemLp
            ((((U : WkpAmbientOn n (j + 1) (p : ℝ≥0∞) Ω)
                (baseIndex n (j + 1)) :
              DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ))
            (Inequalities.higherOrderExponent n j q : ℝ≥0∞)
            (domainMeasure n Ω) :=
        (MeasureTheory.memLp_congr_ae hVU).1 hV
      have hcomp :
          Inequalities.higherOrderExponent n j q =
            Inequalities.higherOrderExponent n (j + 1) p :=
        by
          simpa [q, Nat.add_comm] using
            Inequalities.higherOrderExponent_add
              (n := n) (k := 1) (j := j) (p := p) hp0 (by
                simpa [Nat.add_comm] using hsub)
      simpa [hcomp] using hU

/--
Every retained coordinate of `W^{k+j,p}` has the `j`-step Sobolev
integrability exponent.
-/
theorem coordinate_memLp_iterated
    {j k : ℕ} {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p)
    (hsub : ((j : ℝ) * (p : ℝ)) < (n : ℝ))
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω))
    (a : DerivIndex n k) :
    MemLp
      ((((U : WkpAmbientOn n (k + j) (p : ℝ≥0∞) Ω)
          (a.castOrder (Nat.le_add_right k j)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ))
      (Inequalities.higherOrderExponent n j p : ℝ≥0∞)
      (domainMeasure n Ω) := by
  let V : W^{j,(p : ℝ≥0∞)}(Ω) :=
    derivativeWordCLM (n := n) (m := k + j) (r := j)
      (p := (p : ℝ≥0∞)) (Ω := Ω) a.toList
      (Nat.add_le_add_right a.toList_length_le j) U
  simpa [V] using
    base_memLp_iterated (n := n) (Ω := Ω)
       hp hsub V

/--
Operational higher-order Sobolev construction on completed graph spaces:

`W^{k+j,p}(Ω) -> W^{k,p_j}(Ω)`,

with `p_j = np/(n-jp)`. The target bundle is assembled directly from the
original weak derivatives at their newly proved integrability exponent.
No linearity, continuity, or operator-norm estimate is part of this
declaration.
-/
noncomputable def iteratedStep
    {j k : ℕ} {p : NNReal}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p)
    (hsub : ((j : ℝ) * (p : ℝ)) < (n : ℝ))
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) :
    W^{k,(Inequalities.higherOrderExponent n j p : ℝ≥0∞)}(Ω) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    (((U : WkpAmbientOn n (k + j) (p : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_add_right k j)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k)
    (p := (Inequalities.higherOrderExponent n j p : ℝ≥0∞))
    (Ω := Ω) (d (baseIndex n k)) d rfl
  · intro a
    exact coordinate_memLp_iterated
      (n := n) (Ω := Ω) hp hsub U a
  · intro a
    simpa [d] using U.property (a.castOrder (Nat.le_add_right k j))

/--
The iterated operational embedding preserves every retained derivative
representative almost everywhere.
-/
theorem iteratedStep_apply_ae
    {j k : ℕ} {p : NNReal}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p)
    (hsub : ((j : ℝ) * (p : ℝ)) < (n : ℝ))
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω))
    (a : DerivIndex n k) :
    ((((iteratedStep hp hsub U :
        WkpAmbientOn n k
          (Inequalities.higherOrderExponent n j p : ℝ≥0∞) Ω) a :
      DerivLp n
        (Inequalities.higherOrderExponent n j p : ℝ≥0∞)
        Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n (k + j) (p : ℝ≥0∞) Ω)
          (a.castOrder (Nat.le_add_right k j)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun b ↦
    (((U : WkpAmbientOn n (k + j) (p : ℝ≥0∞) Ω)
      (b.castOrder (Nat.le_add_right k j)) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  simpa [iteratedStep, d] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k)
      (p := (Inequalities.higherOrderExponent n j p : ℝ≥0∞))
      (Ω := Ω) (d (baseIndex n k)) d rfl
      (coordinate_memLp_iterated
        (n := n) (Ω := Ω) hp hsub U)
      (fun b ↦ by
        simpa [d] using
          U.property (b.castOrder (Nat.le_add_right k j))) a

end Iteration

section CriticalStep

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
  [Fact (1 ≤ (n : ℝ≥0∞))]
  {q : NNReal}

/--
Consume one derivative at the critical exponent:

`W^{k+1,n}(Ω) -> W^{k,q}(Ω)`

for every finite `q >= 1` and `n >= 2`. As with `firstOrderStep`, this is a
representative-preserving noncomputable function; it is not bundled as a
continuous linear map.
-/
noncomputable def criticalStep
    (hq1 : (1 : NNReal) ≤ q)
    (U : W^{k + 1,(n : ℝ≥0∞)}(Ω)) :
    W^{k,(q : ℝ≥0∞)}(Ω) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    (((U : WkpAmbientOn n (k + 1) (n : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_succ k)) : DerivLp n (n : ℝ≥0∞) Ω) :
        ℝ^n → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k) (p := (q : ℝ≥0∞)) (Ω := Ω)
    (d (baseIndex n k)) d rfl
  · intro a
    let V : W^{1,(n : ℝ≥0∞)}(Ω) :=
      derivativeWordCLM (n := n) (m := k + 1) (r := 1)
        (p := (n : ℝ≥0∞)) (Ω := Ω) a.toList
        (Nat.add_le_add_right a.toList_length_le 1) U
    have hV :=
      Inequalities.memLp_critical_firstOrder_of_c1ExtensionAtlas
        (n := n) (q := q) (Ω := Ω) hq1 V
    simpa [d, V] using hV
  · intro a
    simpa [d] using U.property (a.castOrder (Nat.le_succ k))

/--
The critical step retains the original weak-derivative representatives.
-/
theorem criticalStep_apply_ae
    (hq1 : (1 : NNReal) ≤ q)
    (U : W^{k + 1,(n : ℝ≥0∞)}(Ω))
    (a : DerivIndex n k) :
    ((((criticalStep hq1 U :
        WkpAmbientOn n k (q : ℝ≥0∞) Ω) a :
      DerivLp n (q : ℝ≥0∞) Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n (k + 1) (n : ℝ≥0∞) Ω)
          (a.castOrder (Nat.le_succ k)) : DerivLp n (n : ℝ≥0∞) Ω) :
        ℝ^n → ℝ) := by
  let d : DerivIndex n k → ℝ^n → ℝ := fun b ↦
    (((U : WkpAmbientOn n (k + 1) (n : ℝ≥0∞) Ω)
      (b.castOrder (Nat.le_succ k)) : DerivLp n (n : ℝ≥0∞) Ω) :
        ℝ^n → ℝ)
  simpa [criticalStep, d] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k) (p := (q : ℝ≥0∞)) (Ω := Ω)
      (d (baseIndex n k)) d rfl
      (fun a ↦ by
        let V : W^{1,(n : ℝ≥0∞)}(Ω) :=
          derivativeWordCLM (n := n) (m := k + 1) (r := 1)
            (p := (n : ℝ≥0∞)) (Ω := Ω) a.toList
            (Nat.add_le_add_right a.toList_length_le 1) U
        have hV :=
          Inequalities.memLp_critical_firstOrder_of_c1ExtensionAtlas
            (n := n) (q := q) (Ω := Ω) hq1 V
        simpa [d, V] using hV)
      (fun b ↦ by
        simpa [d] using U.property (b.castOrder (Nat.le_succ k))) a

end CriticalStep

section CriticalHigherOrder

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
  [hnOne : Fact (1 ≤ (n : ℝ≥0∞))]

/--
Reduce a critical higher-order Sobolev field to its first-order critical
representative:

`W^{k,p}(Ω) -> W^{1,n}(Ω)` when `k > 0` and `kp = n`.

The construction performs `k - 1` operational first-order Sobolev steps.
It uses only the concrete `C1ExtensionAtlas`; no order-`k` extension operator
is assumed. The result is a graph-space element with the required
integrability and weak-derivative rows; the construction gives no continuity
estimate.
-/
noncomputable def toCriticalFirstOrder
    {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p) (hk : 0 < k)
    (hcrit : (k : ℝ) * (p : ℝ) = (n : ℝ))
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    W^{1,(n : ℝ≥0∞)}(Ω) := by
  have hp0nn : (0 : NNReal) < p :=
    lt_of_lt_of_le (by norm_num) hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0nn
  have hpred : ((k - 1 : ℕ) : ℝ) * (p : ℝ) < (n : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))]
    norm_num
    nlinarith
  have hexponent :
      Inequalities.higherOrderExponent n (k - 1) p = (n : NNReal) :=
    Inequalities.higherOrderExponent_pred_eq_dimension
      hk hp0 hcrit
  have : Fact
      (1 ≤ (Inequalities.higherOrderExponent n (k - 1) p : ℝ≥0∞)) :=
    ⟨by rw [hexponent]; exact hnOne.1⟩
  have horder : 1 + (k - 1) ≤ k := by omega
  let U' : W^{1 + (k - 1),(p : ℝ≥0∞)}(Ω) :=
    lowerOrderCLM (n := n) (p := (p : ℝ≥0∞))
      (Ω := Ω) horder U
  let d : DerivIndex n 1 → ℝ^n → ℝ := fun a ↦
    (((U' : WkpAmbientOn n (1 + (k - 1)) (p : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_add_right 1 (k - 1))) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 1) (p := (n : ℝ≥0∞)) (Ω := Ω)
    (d (baseIndex n 1)) d rfl
  · intro a
    have ha := coordinate_memLp_iterated
      (n := n) (j := k - 1) (k := 1) (p := p) (Ω := Ω)
       hp hpred U' a
    simpa [d, hexponent] using ha
  · intro a
    simpa [d] using
      U'.property (a.castOrder (Nat.le_add_right 1 (k - 1)))

/-- The critical first-order reduction preserves the original base function almost everywhere. -/
theorem toCriticalFirstOrder_base_ae
    {p : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p) (hk : 0 < k)
    (hcrit : (k : ℝ) * (p : ℝ) = (n : ℝ))
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    ((((toCriticalFirstOrder hp hk hcrit U :
        WkpAmbientOn n 1 (n : ℝ≥0∞) Ω) (baseIndex n 1) :
      DerivLp n (n : ℝ≥0∞) Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
          (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
        ℝ^n → ℝ) := by
  have hp0nn : (0 : NNReal) < p :=
    lt_of_lt_of_le (by norm_num) hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp0nn
  have hpred : ((k - 1 : ℕ) : ℝ) * (p : ℝ) < (n : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))]
    norm_num
    nlinarith
  have hexponent :
      Inequalities.higherOrderExponent n (k - 1) p = (n : NNReal) :=
    Inequalities.higherOrderExponent_pred_eq_dimension
      hk hp0 hcrit
  have : Fact
      (1 ≤ (Inequalities.higherOrderExponent n (k - 1) p : ℝ≥0∞)) :=
    ⟨by rw [hexponent]; exact hnOne.1⟩
  have horder : 1 + (k - 1) ≤ k := by omega
  let U' : W^{1 + (k - 1),(p : ℝ≥0∞)}(Ω) :=
    lowerOrderCLM (n := n) (p := (p : ℝ≥0∞))
      (Ω := Ω) horder U
  let d : DerivIndex n 1 → ℝ^n → ℝ := fun a ↦
    (((U' : WkpAmbientOn n (1 + (k - 1)) (p : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_add_right 1 (k - 1))) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  have hVU' :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := 1) (p := (n : ℝ≥0∞)) (Ω := Ω)
      (d (baseIndex n 1)) d rfl
      (fun a ↦ by
        have ha := coordinate_memLp_iterated
          (n := n) (j := k - 1) (k := 1) (p := p) (Ω := Ω)
           hp hpred U' a
        simpa [d, hexponent] using ha)
      (fun a ↦ by
        simpa [d] using
          U'.property (a.castOrder (Nat.le_add_right 1 (k - 1))))
      (baseIndex n 1)
  have hU'U :
      ((((U' : WkpAmbientOn n (1 + (k - 1)) (p : ℝ≥0∞) Ω)
          (baseIndex n (1 + (k - 1))) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
          (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
        ℝ^n → ℝ) := by
    simp [U']
  have hVU'' :
      ((((toCriticalFirstOrder hp hk hcrit U :
          WkpAmbientOn n 1 (n : ℝ≥0∞) Ω) (baseIndex n 1) :
        DerivLp n (n : ℝ≥0∞) Ω) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Ω]
      (((U' : WkpAmbientOn n (1 + (k - 1)) (p : ℝ≥0∞) Ω)
          (baseIndex n (1 + (k - 1))) :
        DerivLp n (p : ℝ≥0∞) Ω) : ℝ^n → ℝ) := by
    simpa [toCriticalFirstOrder, d, U', hexponent] using hVU'
  exact hVU''.trans hU'U

/--
The critical higher-order embedding on a domain with a `C1ExtensionAtlas`: if `k > 0`,
`kp = n`, and `n >= 1`, then `W^{k,p}(Ω)` is contained in `L^q(Ω)` for every finite `q >= 1`.
Evans obtains this in step 3 of the proof of §5.6.3, Theorem 6, from `u ∈ W^{1,n}(U)` and the
Gagliardo-Nirenberg-Sobolev inequality.

This theorem obtains all intermediate first-order extensions from the atlas.
Its conclusion is qualitative `MemLp` membership. The bounded linear inclusion
and its quantitative norm estimate are proved in `HigherOrder.Domain.CriticalEmbedding`.
-/
theorem memLp_critical_finite_of_c1ExtensionAtlas
    {p q : NNReal} [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (1 : NNReal) ≤ p) (hk : 0 < k)
    (hcrit : (k : ℝ) * (p : ℝ) = (n : ℝ))
    (hq1 : (1 : NNReal) ≤ q)
    (U : W^{k,(p : ℝ≥0∞)}(Ω)) :
    MemLp
      ((((U : WkpAmbientOn n k (p : ℝ≥0∞) Ω)
          (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Ω) :
        ℝ^n → ℝ))
      (q : ℝ≥0∞) (domainMeasure n Ω) := by
  let V := toCriticalFirstOrder
    (n := n) (k := k) (Ω := Ω) hp hk hcrit U
  have hV :=
    Inequalities.memLp_critical_firstOrder_of_c1ExtensionAtlas
      (n := n) (q := q) (Ω := Ω) hq1 V
  exact hV.ae_eq <|
    toCriticalFirstOrder_base_ae
      (n := n) (k := k) (Ω := Ω) hp hk hcrit U

end CriticalHigherOrder

section DimensionBootstrap

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/--
The endpoint of the subcritical iteration from exponent one:

`W^{k+n-1,1}(Ω) -> W^{k,n}(Ω)`.
-/
noncomputable def toDimensionExponent
    (U : W^{k + (n - 1),(1 : ℝ≥0∞)}(Ω)) :
    W^{k,(n : ℝ≥0∞)}(Ω) := by
  have hn : 0 < n := Fact.out
  have hsub : (((n - 1 : ℕ) : ℝ) * (1 : ℝ)) < (n : ℝ) := by
    norm_num only [mul_one]
    exact_mod_cast Nat.sub_lt hn (by omega : 0 < 1)
  have hexponent :
      Inequalities.higherOrderExponent n (n - 1) 1 =
        (n : NNReal) := by
    apply Inequalities.higherOrderExponent_pred_eq_dimension
      (n := n) (k := n) (p := 1) hn
    · norm_num
    · norm_num
  let d : DerivIndex n k → ℝ^n → ℝ := fun a ↦
    (((U : WkpAmbientOn n (k + (n - 1)) (1 : ℝ≥0∞) Ω)
      (a.castOrder (Nat.le_add_right k (n - 1))) :
        DerivLp n (1 : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  apply mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := k) (p := (n : ℝ≥0∞)) (Ω := Ω)
    (d (baseIndex n k)) d rfl
  · intro a
    have ha := coordinate_memLp_iterated
      (n := n) (j := n - 1) (k := k) (p := 1) (Ω := Ω)
       (by norm_num) hsub U a
    simpa [d, hexponent] using ha
  · intro a
    simpa [d] using
      U.property (a.castOrder (Nat.le_add_right k (n - 1)))

/--
The dimension bootstrap retains every original derivative coordinate.
-/
theorem toDimensionExponent_apply_ae
    (U : W^{k + (n - 1),(1 : ℝ≥0∞)}(Ω))
    (a : DerivIndex n k) :
    ((((toDimensionExponent U :
        WkpAmbientOn n k (n : ℝ≥0∞) Ω) a :
      DerivLp n (n : ℝ≥0∞) Ω) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n Ω]
        (((U : WkpAmbientOn n (k + (n - 1)) (1 : ℝ≥0∞) Ω)
          (a.castOrder (Nat.le_add_right k (n - 1))) :
        DerivLp n (1 : ℝ≥0∞) Ω) : ℝ^n → ℝ) := by
  have hn : 0 < n := Fact.out
  have hsub : (((n - 1 : ℕ) : ℝ) * (1 : ℝ)) < (n : ℝ) := by
    norm_num only [mul_one]
    exact_mod_cast Nat.sub_lt hn (by omega : 0 < 1)
  have hexponent :
      Inequalities.higherOrderExponent n (n - 1) 1 =
        (n : NNReal) := by
    apply Inequalities.higherOrderExponent_pred_eq_dimension
      (n := n) (k := n) (p := 1) hn
    · norm_num
    · norm_num
  let d : DerivIndex n k → ℝ^n → ℝ := fun b ↦
    (((U : WkpAmbientOn n (k + (n - 1)) (1 : ℝ≥0∞) Ω)
      (b.castOrder (Nat.le_add_right k (n - 1))) :
        DerivLp n (1 : ℝ≥0∞) Ω) : ℝ^n → ℝ)
  simpa [toDimensionExponent, d, hexponent] using
    mkWkpSpaceOnOfWeakDerivatives_apply_ae
      (n := n) (k := k) (p := (n : ℝ≥0∞)) (Ω := Ω)
      (d (baseIndex n k)) d rfl
      (fun a ↦ by
        have ha := coordinate_memLp_iterated
          (n := n) (j := n - 1) (k := k) (p := 1) (Ω := Ω)
           (by norm_num) hsub U a
        simpa [d, hexponent] using ha)
      (fun b ↦ by
        simpa [d] using
          U.property (b.castOrder (Nat.le_add_right k (n - 1)))) a

end DimensionBootstrap

end Embedding
end GraphSpace
end SobolevSpace
