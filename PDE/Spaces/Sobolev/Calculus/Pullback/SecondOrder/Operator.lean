/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.SecondOrder.WeakChainRule
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Localized second-order pullback operator

The compactly localized pullback of an `H²` function through a `C²` chart, as an
element of the graph space `W^{2,2}` on the compact source patch `E.symm '' K`. The
base coordinate is `(1_K u) ∘ E`, the gradient coordinates are the first-order chain-rule rows
and the Hessian coordinates are the second-order rows of `Pullback.SecondOrder.Rows`; the
weak-derivative relations between them are the chain rules proved in
`Pullback.SecondOrder.WeakChainRule`. The row estimates are then summed into a bound on the
graph norm, with a constant that depends only on the chart, the patch and the norm of the
localized `L²` pullback operator.

Evans uses without comment that a C² change of coordinates preserves `H²` with a bound: in step 10
of the proof of §6.3.2, Theorem 4, the estimate for `u' = u ∘ Ψ` in `H²(V')` gives (71) for `u` on
`V = Ψ(V')`. The same fact underlies the `W^{2,p}` bound (10) for the extension operator in §5.4,
Remark (i). `localizedH2Pullback` and `norm_localizedH2Pullback_sq_le` prove it for `p = 2`, for the
pullback through a C² chart `E` with C¹ inverse of a function localized to a compact subset `K` of
`E.target`.

## Main results

* `localizedH2Pullback`: the `W^{2,2}` element, with `localizedH2Pullback_apply_ae`
  identifying each coordinate almost everywhere with its canonical row.
* `norm_localizedH2Pullback_coordinate_le`: each coordinate is bounded by the corresponding
  explicit chart constant times `‖U‖`.
* `norm_localizedH2Pullback_sq_le`: the squared graph norm is at most the sum of the squared
  coordinate bounds, `localizedH2PullbackNormBoundSq`.

## Implementation notes

The carrier `E.symm '' K` is compact, not open, so the coordinates are certified by weak
derivative relations on a measurable set and the open-domain uniqueness theorem is not
invoked. On open subsets the same construction gives the usual `H²` space. The mollifier argument
`μ` is only used to construct smooth approximants inside the chain-rule proofs; the resulting
element does not depend on it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Remark (i), (10), p. 271; and §6.3.2, proof of
  Theorem 4, steps 7 and 10, (58) and (71), pp. 338 and 340.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set Function ENNReal
open scoped Sobolev
open SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Canonical representative of every derivative row of the localized `H²`
pullback. -/
noncomputable def localizedH2PullbackRow
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) : ℝ^n → ℝ :=
  secondOrderRows
    (localizedSobolevPullbackBase (n := n)
      (hE.of_le (by norm_num)) hEsymm hK hKsub U : ℝ^n → ℝ)
    (fun i ↦ (firstSobolevPullbackRow (n := n)
      hE hEsymm hK hKsub U i : ℝ^n → ℝ))
    (fun i k ↦ (secondSobolevPullbackRow (n := n)
      hE hEsymm hK hKsub U i k : ℝ^n → ℝ))
    a

/-- The pullback through the chart `E` of `U ∈ W^{2,2}(E.target)` localized to the compact set
`K ⊆ E.target`, as an element of `W^{2,2}(E.symm '' K)`, with base coordinate `(1_K U) ∘ E` and
derivative coordinates `localizedH2PullbackRow`.

The set `E.symm '' K` need not be open, so the coordinates are certified by their
weak-derivative relations on it; the open-domain uniqueness theorem is not used. -/
noncomputable def localizedH2Pullback
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) :
    W^{2,2}(compactPullbackSource (n := n) E K) := by
  let L := compactPullbackSource (n := n) E K
  let f : ℝ^n → ℝ :=
    (localizedSobolevPullbackBase (n := n)
      (hE.of_le (by norm_num)) hEsymm hK hKsub U : ℝ^n → ℝ)
  let d : DerivIndex n 2 → ℝ^n → ℝ :=
    localizedH2PullbackRow (n := n) hE hEsymm hK hKsub U
  have hbase : d (baseIndex n 2) = f := by
    simp [d, f, localizedH2PullbackRow]
  have hmem : ∀ a : DerivIndex n 2,
      MemLp (d a) 2 (domainMeasure n L) := by
    intro a
    exact a.inductionOnOrderTwo
      (motive := fun b ↦ MemLp (d b) 2 (domainMeasure n L))
      (by
        simpa [d, localizedH2PullbackRow] using
          (Lp.memLp (localizedSobolevPullbackBase (n := n)
            (hE.of_le (by norm_num)) hEsymm hK hKsub U)))
      (fun i ↦ by
        simpa [d, localizedH2PullbackRow] using
          (Lp.memLp (firstSobolevPullbackRow (n := n)
            hE hEsymm hK hKsub U i)))
      (fun b i k hlist ↦ by
        simpa [d, localizedH2PullbackRow,
          secondOrderRows_of_toList_eq_pair _ _ _ b i k hlist] using
          (Lp.memLp (secondSobolevPullbackRow (n := n)
            hE hEsymm hK hKsub U i k)))
  have hweak : ∀ a : DerivIndex n 2,
      HasWeakDerivativeOn (n := n) L a.toList f (d a) := by
    intro a
    exact a.inductionOnOrderTwo
      (motive := fun b ↦ HasWeakDerivativeOn (n := n) L b.toList f (d b))
      (by
        have hfLp : MemLp f 2 (domainMeasure n L) := by
          simpa [f] using (Lp.memLp (localizedSobolevPullbackBase (n := n)
            (hE.of_le (by norm_num)) hEsymm hK hKsub U))
        have hloc := memLp_locallyIntegrableOn_domain hfLp (by norm_num)
        simpa [f, d, localizedH2PullbackRow, iteratedPartialDeriv] using
          (show HasWeakDerivativeOn (n := n) L [] f f from
            hasWeakDerivativeOn_nil hloc))
      (fun i ↦ by
        simpa [f, d, localizedH2PullbackRow] using
          (hasWeakDerivativeOn_firstSobolevPullbackRow_compactCarrier
            (n := n) μ hE hEsymm hK hKsub U i))
      (fun b i k hlist ↦ by
        simpa [f, d, localizedH2PullbackRow, hlist,
          secondOrderRows_of_toList_eq_pair _ _ _ b i k hlist] using
          (hasWeakDerivativeOn_secondSobolevPullbackRow_compactCarrier
            (n := n) μ hE hEsymm hK hKsub U i k))
  exact mkWkpSpaceOnOfWeakDerivatives
    (n := n) (k := 2) (p := (2 : ENNReal)) (Ω := L)
    f d hbase hmem hweak

/-- Every coordinate of the pullback agrees almost everywhere with
the canonical base, gradient, or Hessian row used in its construction. -/
theorem localizedH2Pullback_apply_ae
    (μ : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) :
    ((((localizedH2Pullback (n := n) μ hE hEsymm hK hKsub U :
        WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K)) a :
        DerivLp n 2 (compactPullbackSource (n := n) E K)) : ℝ^n → ℝ))
      =ᵐ[domainMeasure n (compactPullbackSource (n := n) E K)]
        localizedH2PullbackRow (n := n) hE hEsymm hK hKsub U a := by
  classical
  unfold localizedH2Pullback
  apply mkWkpSpaceOnOfWeakDerivatives_apply_ae

/-- Unified componentwise norm bound for the compact `H²` pullback. The
three cases are the bounded base pullback, the first-order chart rule, and
the second-order chart rule. -/
noncomputable def localizedH2PullbackRowNormBound
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) : ℝ :=
  let Pnorm := ‖localizedPullbackCLM (n := n) (p := (2 : ENNReal))
    (hE.of_le (by norm_num)) hEsymm hK hKsub‖
  secondOrderRows
    (Pnorm * ‖U‖)
    (fun i ↦
      (firstPullbackCoefficientBound (n := n) hE hEsymm hK i * Pnorm) * ‖U‖)
    (fun i k ↦
      (secondPullbackCoefficientBound (n := n) hE hEsymm hK i k * Pnorm) * ‖U‖)
    a

/-- Every coordinate `a` of `localizedH2Pullback` has `L²` norm at most
`localizedH2PullbackRowNormBound hE hEsymm hK hKsub U a`, a chart constant times `‖U‖`. -/
theorem norm_localizedH2Pullback_coordinate_le
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) (a : DerivIndex n 2) :
    ‖((localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
        WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K)) a :
        DerivLp n 2 (compactPullbackSource (n := n) E K))‖ ≤
      localizedH2PullbackRowNormBound (n := n) hE hEsymm hK hKsub U a := by
  let P := localizedPullbackCLM (n := n) (p := (2 : ENNReal))
    (hE.of_le (by norm_num)) hEsymm hK hKsub
  exact a.inductionOnOrderTwo
    (motive := fun b ↦
      ‖((localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
          WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K)) b :
          DerivLp n 2 (compactPullbackSource (n := n) E K))‖ ≤
        localizedH2PullbackRowNormBound (n := n) hE hEsymm hK hKsub U b)
    (by
      have heq :
          ((localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
              WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K))
                (baseIndex n 2) :
              DerivLp n 2 (compactPullbackSource (n := n) E K)) =
            localizedSobolevPullbackBase (n := n)
              (hE.of_le (by norm_num)) hEsymm hK hKsub U := by
        apply MeasureTheory.Lp.ext
        simpa [localizedH2PullbackRow] using
          localizedH2Pullback_apply_ae
            (n := n) mu hE hEsymm hK hKsub U (baseIndex n 2)
      rw [heq]
      change ‖P ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2))‖ ≤
        localizedH2PullbackRowNormBound
          (n := n) hE hEsymm hK hKsub U (baseIndex n 2)
      calc
        ‖P ((U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2))‖ ≤
            ‖P‖ * ‖(U : WkpAmbientOn n 2 2 E.target) (baseIndex n 2)‖ :=
          ContinuousLinearMap.le_opNorm P _
        _ ≤ ‖P‖ * ‖U‖ :=
          mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ _) (norm_nonneg P)
        _ = localizedH2PullbackRowNormBound
            (n := n) hE hEsymm hK hKsub U (baseIndex n 2) := by
          simp [localizedH2PullbackRowNormBound, P])
    (fun i ↦ by
      have heq :
          ((localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
              WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K))
                (firstDerivIndex n 2 (by omega) i) :
              DerivLp n 2 (compactPullbackSource (n := n) E K)) =
            firstSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i := by
        apply MeasureTheory.Lp.ext
        simpa [localizedH2PullbackRow] using
          localizedH2Pullback_apply_ae
            (n := n) mu hE hEsymm hK hKsub U
              (firstDerivIndex n 2 (by omega) i)
      rw [heq]
      simpa [localizedH2PullbackRowNormBound, P] using
        norm_firstSobolevPullbackRow_le_chartConstant
          (n := n) hE hEsymm hK hKsub U i)
    (fun b i k hlist ↦ by
      have heq :
          ((localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
              WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K)) b :
              DerivLp n 2 (compactPullbackSource (n := n) E K)) =
            secondSobolevPullbackRow (n := n) hE hEsymm hK hKsub U i k := by
        apply MeasureTheory.Lp.ext
        simpa [localizedH2PullbackRow,
          secondOrderRows_of_toList_eq_pair _ _ _ b i k hlist] using
          localizedH2Pullback_apply_ae
            (n := n) mu hE hEsymm hK hKsub U b
      rw [heq]
      simpa [localizedH2PullbackRowNormBound, P,
        secondOrderRows_of_toList_eq_pair _ _ _ b i k hlist] using
        norm_secondSobolevPullbackRow_le_chartConstant
          (n := n) hE hEsymm hK hKsub U i k)

/-- The squared chart constant obtained by summing the explicit bound for
every weak-derivative coordinate of the compact `H²` pullback.  Keeping this
as the finite coordinate sum avoids hiding dimension-dependent multiplicities
for first and second derivatives. -/
noncomputable def localizedH2PullbackNormBoundSq
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) : ℝ :=
  ∑ a : DerivIndex n 2,
    localizedH2PullbackRowNormBound (n := n) hE hEsymm hK hKsub U a ^ 2

/-- Quantitative `H²` pullback estimate on a compact chart patch: the squared graph norm of
`localizedH2Pullback` is at most `localizedH2PullbackNormBoundSq`, the sum over all coordinates of
the squared bounds of `norm_localizedH2Pullback_coordinate_le`. The graph norm is the Euclidean
norm of the coordinates. -/
theorem norm_localizedH2Pullback_sq_le
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x))
    {K : Set (ℝ^n)} (hK : IsCompact K) (hKsub : K ⊆ E.target)
    (U : W^{2,2}(E.target)) :
    ‖localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U‖ ^ 2 ≤
      localizedH2PullbackNormBoundSq (n := n) hE hEsymm hK hKsub U := by
  classical
  change
    ‖(localizedH2Pullback (n := n) mu hE hEsymm hK hKsub U :
        WkpAmbientOn n 2 2 (compactPullbackSource (n := n) E K))‖ ^ 2 ≤ _
  rw [PiLp.norm_sq_eq_of_L2]
  unfold localizedH2PullbackNormBoundSq
  apply Finset.sum_le_sum
  intro a _
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_localizedH2Pullback_coordinate_le
      (n := n) mu hE hEsymm hK hKsub U a) 2


end SobolevSpace.WeakChangeOfVariables
