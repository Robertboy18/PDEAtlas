/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Exponent

/-!
# Global higher-order Sobolev embeddings

The subcritical higher-order Sobolev embedding on `ℝ^n`, stated for the completed graph spaces
`WkpSpace n k p`. If `1 ≤ p` and `kp < n`, the order-zero coordinate of any
`u ∈ W^{k,p}(ℝ^n)` lies in `L^q(ℝ^n)` with

`q = np / (n - kp)`, equivalently `1/q = 1/p - k/n`.

This is the whole-space form of the general Sobolev inequality of Evans, PDE, §5.6.3, Theorem 6(i),
which is stated for bounded `C¹` domains. The proof is an induction on `k`; as in step 1 of Evans's
proof, the first-order inequality raises the exponent `k` times. The base coordinate and the
first-derivative coordinates of a `W^{k+1,p}` element are themselves `W^{k,p}` elements, so by
induction they lie in `L^{p_k}` with `p_k = np/(n-kp)`. They assemble into a `W^{1,p_k}` function,
and the first-order Gagliardo–Nirenberg–Sobolev embedding on the completed space
(`Inequalities.memLp_pStar_of_sobolevSpace`) places it in `L^{p_k^*}`, where `p_k^* = p_{k+1}`.

## Main results

* `memLp_higherOrderExponent`: the base coordinate of `u ∈ W^{k,p}(ℝ^n)` lies in
  `L^{np/(n-kp)}`.
* `memLp_of_inv_eq`: the same statement with the target exponent given by `1/q = 1/p - k/n`.
* `subcriticalEmbeddingCLM`: the inclusion `W^{k,p}(ℝ^n) → L^q(ℝ^n)` as a continuous linear
  map, with the quantitative form `norm_subcriticalEmbeddingCLM_le`.
* `memLp_derivativeWord_higherOrderExponent`, `memLp_derivativeWord_of_inv_eq`: the
  derivative-family form. For `u ∈ W^{m,p}` and a word `α` with `|α| + r ≤ m` and `rp < n`, the
  derivative `D^α u` lies in `L^{np/(n-rp)}`.

## Implementation notes

The first-order theorem supplies the approximation by smooth compactly supported functions.
Continuity of the inclusion is not obtained from an explicit constant. The inclusion is first
built as a linear map and then shown to have sequentially closed graph: convergence in `W^{k,p}`
and in `L^q` both imply convergence in measure, whose limit is unique almost everywhere. The
closed graph theorem then gives a bounded operator whose norm is not made explicit here. The
exponent arithmetic (`higherOrderExponent`, `pStar`, and their relations) is in
`HigherOrder.Exponent`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6(i), (29)-(30), pp. 284-285, and step 1 of
  its proof, p. 285.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Inequalities

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

section Global

open SobolevSpace.GraphSpace

variable {n k : ℕ} {p : NNReal}

/-- General global Sobolev embedding, Evans §5.6.3, Theorem 6(i).

If `u ∈ W^{k,p}(ℝ^n)`, `1 ≤ p`, and `kp < n`, then the order-zero
representative of `u` belongs to `L^q(ℝ^n)` for

`q = np / (n - kp)`,

equivalently `1/q = 1/p - k/n`. -/
theorem memLp_higherOrderExponent
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (U : W^{k,(p : ℝ≥0∞)}(ℝ^n)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Set.univ) :
          ℝ^n → ℝ)
      (higherOrderExponent n k p : ℝ≥0∞)
      (volume : Measure (ℝ^n)) := by
  induction k with
  | zero =>
      simpa [higherOrderExponent_zero hn] using
        (MeasureTheory.Lp.memLp ((U : WkpAmbientOn n 0 (p : ℝ≥0∞) Set.univ) (baseIndex n 0)))
  | succ k ih =>
      have hp0 : 0 < (p : ℝ) := NNReal.coe_pos.2 (zero_lt_one.trans_le hp)
      have hsub' : ((k : ℝ) + 1) * p < n := by exact_mod_cast hsub
      have hksub : (k : ℝ) * p < n := by nlinarith
      let q : NNReal := higherOrderExponent n k p
      have hq_one : (1 : NNReal) ≤ q := one_le_higherOrderExponent hp hksub
      have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq_one⟩
      have hbase : MemLp (((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Set.univ)
          (baseIndex n (k + 1)) : DerivLp n (p : ℝ≥0∞) Set.univ) : ℝ^n → ℝ)
          (q : ℝ≥0∞) (volume : Measure (ℝ^n)) := by
        let Ulower : W^{k,(p : ℝ≥0∞)}(ℝ^n) := lowerOrderCLM (n := n) (k := k) (m := k + 1)
          (p := (p : ℝ≥0∞)) (Ω := Set.univ) (by omega) U
        have h := ih hksub Ulower
        simpa [Ulower, q] using h
      have hderiv (i : Fin n) : MemLp (((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Set.univ)
          (firstDerivIndex n (k + 1) (by omega) i) : DerivLp n (p : ℝ≥0∞) Set.univ) : ℝ^n → ℝ)
          (q : ℝ≥0∞) (volume : Measure (ℝ^n)) := by
        let Ui : W^{k,(p : ℝ≥0∞)}(ℝ^n) := derivativeWordCLM (n := n) (m := k + 1) (r := k)
          (p := (p : ℝ≥0∞)) (Ω := Set.univ) [i] (by simp [Nat.add_comm]) U
        have h := ih hksub Ui
        simpa [Ui, q] using h
      let u1 : GlobalSobolevSpace n 1 (q : ℝ≥0∞) :=
        { toFun := ((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Set.univ) (baseIndex n (k + 1)) :
            DerivLp n (p : ℝ≥0∞) Set.univ)
          memLp := by simpa [domainMeasure] using hbase
          weak_derivs_inLp := fun α hα ↦ by
            rcases α with _ | ⟨i, _ | ⟨j, tail⟩⟩
            · exact ⟨((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Set.univ) (baseIndex n (k + 1)) :
                DerivLp n (p : ℝ≥0∞) Set.univ), by simpa [domainMeasure] using hbase,
                by simpa using U.property (baseIndex n (k + 1))⟩
            · exact ⟨((U : WkpAmbientOn n (k + 1) (p : ℝ≥0∞) Set.univ)
                (firstDerivIndex n (k + 1) (by omega) i) : DerivLp n (p : ℝ≥0∞) Set.univ),
                by simpa [domainMeasure] using hderiv i,
                U.property.hasWeakDerivativeOn_first (by omega) i⟩
            · simp at hα }
      have hq_lt : (q : ℝ) < (n : ℝ) := higherOrderExponent_lt_dimension hsub'
      have : Fact (1 ≤ (Inequalities.pStar n q : ℝ≥0∞)) :=
        ⟨by exact_mod_cast Inequalities.one_le_pStar hn hq_one hq_lt⟩
      rw [← pStar_higherOrderExponent hp0 hsub']
      exact Inequalities.memLp_pStar_of_sobolevSpace (n := n) (p := q)
        (p' := Inequalities.pStar n q) hq_one hn
        (Inequalities.inv_pStar_eq hn (NNReal.coe_pos.2 (zero_lt_one.trans_le hq_one)) hq_lt) u1

/-- Global higher-order Sobolev embedding with the target exponent specified
by Evans's reciprocal relation `1/q = 1/p - k/n`. -/
theorem memLp_of_inv_eq
    {q : NNReal}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ =
      (p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (U : W^{k,(p : ℝ≥0∞)}(ℝ^n)) :
    MemLp
      (((U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
        (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Set.univ) :
          ℝ^n → ℝ)
      (q : ℝ≥0∞) (volume : Measure (ℝ^n)) := by
  rw [eq_higherOrderExponent_of_inv_eq (NNReal.coe_pos.2 (zero_lt_one.trans_le hp)) hsub hq]
  exact memLp_higherOrderExponent hp hn hsub U

/-- The base coordinate of a completed global Sobolev element, as a function
on `ℝ^n`. -/
abbrev globalBaseFunction
    {n k : ℕ} {p : NNReal}
    (U : W^{k,(p : ℝ≥0∞)}(ℝ^n)) : ℝ^n → ℝ :=
  ((U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ)
    (baseIndex n k) : DerivLp n (p : ℝ≥0∞) Set.univ)

/-- The algebraic inclusion from the completed global Sobolev space into
the target `L^q` space in the subcritical range. -/
noncomputable def subcriticalEmbeddingLinearMap
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))] :
    W^{k,(p : ℝ≥0∞)}(ℝ^n) →ₗ[ℝ]
      MeasureTheory.Lp ℝ (higherOrderExponent n k p : ℝ≥0∞)
        (volume : Measure (ℝ^n)) where
  toFun U :=
    (memLp_higherOrderExponent hp hn hsub U).toLp
      (globalBaseFunction U)
  map_add' U V := Lp.ext <| (memLp_higherOrderExponent hp hn hsub (U + V)).coeFn_toLp.trans <|
    (show globalBaseFunction (U + V) =ᵐ[(volume : Measure (ℝ^n))]
        globalBaseFunction U + globalBaseFunction V by
      simpa [globalBaseFunction, domainMeasure] using
        Lp.coeFn_add ((U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ) (baseIndex n k))
          ((V : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ) (baseIndex n k))).trans <|
    ((memLp_higherOrderExponent hp hn hsub U).coeFn_toLp.symm.add
      (memLp_higherOrderExponent hp hn hsub V).coeFn_toLp.symm).trans (Lp.coeFn_add _ _).symm
  map_smul' c U := Lp.ext <| (memLp_higherOrderExponent hp hn hsub (c • U)).coeFn_toLp.trans <|
    (show globalBaseFunction (c • U) =ᵐ[(volume : Measure (ℝ^n))] c • globalBaseFunction U by
      simpa [globalBaseFunction, domainMeasure] using
        Lp.coeFn_smul c ((U : WkpAmbientOn n k (p : ℝ≥0∞) Set.univ) (baseIndex n k))).trans <|
    ((memLp_higherOrderExponent hp hn hsub U).coeFn_toLp.symm.const_smul c).trans
      (Lp.coeFn_smul c _).symm

/-- The subcritical Sobolev inclusion has sequentially closed graph.

Convergence in the source controls the base coordinate in `L^p`, while
convergence in the target controls the same representatives in `L^q`.
Both imply convergence in measure, whose limit is unique almost
everywhere. -/
theorem subcriticalEmbeddingLinearMap_seqClosedGraph
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n k p : ℝ≥0∞))] :
    ∀ (u : ℕ → W^{k,(p : ℝ≥0∞)}(ℝ^n))
      (x : W^{k,(p : ℝ≥0∞)}(ℝ^n))
      (y : MeasureTheory.Lp ℝ
        (higherOrderExponent n k p : ℝ≥0∞)
        (volume : Measure (ℝ^n))),
      Filter.Tendsto u Filter.atTop (𝓝 x) →
      Filter.Tendsto
        (subcriticalEmbeddingLinearMap hp hn hsub ∘ u)
        Filter.atTop (𝓝 y) →
      y = subcriticalEmbeddingLinearMap hp hn hsub x := by
  intro u x y hux huy
  have hbaseMeasure : TendstoInMeasure (volume : Measure (ℝ^n))
      (fun j ↦ globalBaseFunction (u j)) Filter.atTop (globalBaseFunction x) := by
    simpa [globalBaseFunction, domainMeasure] using tendstoInMeasure_of_tendsto_Lp
      (((wkpBaseCoordinateCLM (n := n) (m := k) (p := (p : ℝ≥0∞))
        (Ω := Set.univ)).continuous.tendsto x).comp hux)
  exact Lp.ext ((tendstoInMeasure_ae_unique hbaseMeasure
    ((tendstoInMeasure_of_tendsto_Lp huy).congr_left fun j ↦
      (memLp_higherOrderExponent hp hn hsub (u j)).coeFn_toLp)).symm.trans
    (memLp_higherOrderExponent hp hn hsub x).coeFn_toLp.symm)

/-- Continuous completed-space realization of the global subcritical
Sobolev embedding. Continuity is obtained from the closed graph theorem,
not assumed as an extra analytic hypothesis. -/
noncomputable def subcriticalEmbeddingCLM
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n k p : ℝ≥0∞))] :
    W^{k,(p : ℝ≥0∞)}(ℝ^n) →L[ℝ]
      MeasureTheory.Lp ℝ (higherOrderExponent n k p : ℝ≥0∞)
        (volume : Measure (ℝ^n)) :=
  ContinuousLinearMap.ofSeqClosedGraph
    (subcriticalEmbeddingLinearMap_seqClosedGraph
      hp hn hsub)

/-- Quantitative completed-space form of Evans's subcritical higher-order
Sobolev inequality:

`‖u‖_{L^q} ≤ ‖I_{n,k,p}‖ ‖u‖_{W^{k,p}}`,

where `q = np/(n-kp)` and `I_{n,k,p}` is the verified continuous inclusion
constructed by the closed graph theorem. -/
theorem norm_subcriticalEmbeddingCLM_le
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n k p : ℝ≥0∞))]
    (U : W^{k,(p : ℝ≥0∞)}(ℝ^n)) :
    ‖subcriticalEmbeddingCLM hp hn hsub U‖ ≤
      ‖subcriticalEmbeddingCLM hp hn hsub‖ * ‖U‖ :=
  ContinuousLinearMap.le_opNorm _ _

/-- Derivative-family form of the general global Sobolev embedding.

If `u ∈ W^{m,p}(ℝ^n)`, the derivative word `D^α u` retains `r` weak
derivatives whenever `|α| + r ≤ m`. If additionally `rp < n`, then this
chosen derivative representative belongs to
`L^{np/(n-rp)}(ℝ^n)`.

This is the form used when lower derivatives of a higher-order Sobolev
function must be placed in progressively stronger `L^q` spaces. -/
theorem memLp_derivativeWord_higherOrderExponent
    {m r : ℕ}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (r : ℝ) * p < n)
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (U : W^{m,(p : ℝ≥0∞)}(ℝ^n)) :
    MemLp
      ((((derivativeWordCLM
            (n := n) (m := m) (r := r) (p := (p : ℝ≥0∞))
            (Ω := Set.univ) α hα U :
              W^{r,(p : ℝ≥0∞)}(ℝ^n)) :
            WkpAmbientOn n r (p : ℝ≥0∞) Set.univ)
          (baseIndex n r) :
            DerivLp n (p : ℝ≥0∞) Set.univ) : ℝ^n → ℝ)
      (higherOrderExponent n r p : ℝ≥0∞)
      (volume : Measure (ℝ^n)) :=
  memLp_higherOrderExponent hp hn hsub (derivativeWordCLM (n := n) (m := m) (r := r)
    (p := (p : ℝ≥0∞)) (Ω := Set.univ) α hα U)

/-- Derivative-family embedding with the target exponent given by
`1/q = 1/p - r/n`. -/
theorem memLp_derivativeWord_of_inv_eq
    {m r : ℕ} {q : NNReal}
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (r : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ =
      (p : ℝ)⁻¹ - (r : ℝ) * (n : ℝ)⁻¹)
    (α : List (Fin n)) (hα : α.length + r ≤ m)
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (U : W^{m,(p : ℝ≥0∞)}(ℝ^n)) :
    MemLp
      ((((derivativeWordCLM
            (n := n) (m := m) (r := r) (p := (p : ℝ≥0∞))
            (Ω := Set.univ) α hα U :
              W^{r,(p : ℝ≥0∞)}(ℝ^n)) :
            WkpAmbientOn n r (p : ℝ≥0∞) Set.univ)
          (baseIndex n r) :
            DerivLp n (p : ℝ≥0∞) Set.univ) : ℝ^n → ℝ)
      (q : ℝ≥0∞) (volume : Measure (ℝ^n)) := by
  rw [eq_higherOrderExponent_of_inv_eq (NNReal.coe_pos.2 (zero_lt_one.trans_le hp)) hsub hq]
  exact memLp_derivativeWord_higherOrderExponent hp hn hsub α hα U

end Global

end Inequalities
end SobolevSpace
