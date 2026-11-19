/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.Spaces.Sobolev.Extension.Pullback.FirstOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.GraphSpace.FiniteSums

/-!
# Arbitrary-order Sobolev pullback

Every positive finite Sobolev order is preserved by pullback through a
bounded chart of the same differentiability order.  The proof uses only the
first-order weak chain rule: at each successor step, pull back the target
field and its first derivatives at the preceding order, multiply by the
chart derivative rows, and assemble the compatible first derivatives.

Invariance of `W^{m,p}` under `C^m` changes of variables is standard (Adams–Fournier, *Sobolev
Spaces*, Chapter 3, coordinate transformations; the first-order case is used in Evans, PDE, §5.4
to flatten a `C¹` boundary). We prove it for `p = 2` and bounded charts, with `C¹`
regularity of the inverse chart: the inverse enters solely through measure transport, while the
`m`-fold chain rule differentiates the forward chart up to order `m`.

## Main results

* `exists_WkTwo_pullback_on_bounded_chart`: for `0 < m`, a `C^m` chart `E` with `C¹` inverse and
  bounded source and target, and `U ∈ H^m(E.target)`, there is `P ∈ H^m(E.source)` whose base
  coordinate is `u ∘ E` almost everywhere.

## Implementation notes

The induction is on `m`, with `exists_W1Two_pullback_on_bounded_chart` as the base case. At
order `m + 1` the lower-order part `lowerOrderCLM U` and the first-derivative words
`derivativeWordCLM [j] U` are pulled back at order `m` by the inductive hypothesis. The chart
derivative entries `∂ᵢEⱼ` are `C^m` and bounded together with their derivatives on the bounded
source, so `mkWkpSpaceOnOfContDiffMemLpFinite` turns them into `W^{m,∞}` elements; their
products with the pulled-back derivatives are formed with `wkTopProduct`, summed over `j`, and
the resulting first-derivative rows are assembled into an order-`m + 1` element by
`exists_succOrder_of_firstDerivatives` from `Calculus.Slicing.HigherOrder`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 3, The Sobolev Spaces `W^{m,p}(Ω)`, pp. 59-78, for coordinate
  transformations of `W^{m,p}`.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; step 5 of the proof, p. 270,
  straightens the boundary by `y = Φ(x)` and applies the change of variables to `C¹` functions
  before the density argument.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set
open SobolevSpace.GraphSpace
open scoped ENNReal

variable {n : ℕ}

/--
A `W^{m,2}` field pulls back through the full source of a bounded `C^m`
chart for every positive finite order `m`.

Only `C^1` regularity of the inverse chart is needed for measure transport
and the weak chain rule.  Higher derivatives fall on the forward chart rows.
-/
theorem exists_WkTwo_pullback_on_bounded_chart
    (m : ℕ) (hm : 0 < m)
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ m (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{m,2}(E.target)) :
    ∃ P : W^{m,2}(E.source),
      ((((P : WkpAmbientOn n m 2 E.source) (baseIndex n m) :
          DerivLp n 2 E.source) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n E.source] fun x ↦
          (((U : WkpAmbientOn n m 2 E.target) (baseIndex n m) :
            DerivLp n 2 E.target) : ℝ^n → ℝ) (E x) := by
  classical
  induction m generalizing E with
  | zero => omega
  | succ k ih =>
    rcases k with _ | r
    · simpa using exists_W1Two_pullback_on_bounded_chart mu hE hEsymm hSource hTarget U
    let U0 : W^{(r + 1),2}(E.target) := lowerOrderCLM (n := n) (p := 2) (by omega) U
    let dU : Fin n → W^{(r + 1),2}(E.target) := fun j ↦
      derivativeWordCLM (m := r + 2) (r := r + 1) (p := 2) [j]
        (by simp only [List.length_singleton]; omega) U
    have hU0dU (j : Fin n) :
        ((U0 : WkpAmbientOn n (r + 1) 2 E.target) (firstDerivIndex n (r + 1) (by omega) j) :
          DerivLp n 2 E.target) =
        ((dU j : WkpAmbientOn n (r + 1) 2 E.target) (baseIndex n (r + 1)) :
          DerivLp n 2 E.target) := by
      simp [U0, dU]
    obtain ⟨P, hP⟩ := ih (by omega) (hE.of_le (by simp)) hEsymm hSource hTarget U0
    choose Q hQ using fun j ↦ ih (by omega) (hE.of_le (by simp)) hEsymm hSource hTarget (dU j)
    let c : Fin n → Fin n → ℝ^n → ℝ := fun i j x ↦
      ((fderiv ℝ (fun y ↦ E y) x) (EuclideanSpace.single i (1 : ℝ))) j
    have hc (i j : Fin n) : ContDiff ℝ (r + 1) (c i j) :=
      (PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin n ↦ ℝ) j).contDiff.comp
        ((hE.fderiv_right (m := r + 1) (by norm_cast)).clm_apply contDiff_const)
    have hcMem (i j : Fin n) (a : DerivIndex n (r + 1)) :
        MemLp (fun x ↦ iteratedPartialDeriv (n := n) a.toList (c i j) x) ∞
          (domainMeasure n E.source) :=
      memLp_top_on_bounded_of_continuous hSource
        (PDE.contDiff_iteratedPartialDeriv_of_le (hc i j) a.toList a.toList_length_le).continuous
    let C : Fin n → Fin n → W^{(r + 1),∞}(E.source) := fun i j ↦
      mkWkpSpaceOnOfContDiffMemLpFinite (c i j) (hc i j) (hcMem i j)
    let D : Fin n → W^{(r + 1),2}(E.source) := fun i ↦
      ∑ j : Fin n, wkTopProduct (by omega) E.open_source (C i j) (Q j)
    have hDBase (i : Fin n) :
        ((((D i : WkpAmbientOn n (r + 1) 2 E.source) (baseIndex n (r + 1)) :
          DerivLp n 2 E.source) : ℝ^n → ℝ)) =ᵐ[domainMeasure n E.source] fun x ↦
            ∑ j : Fin n, (((dU j : WkpAmbientOn n (r + 1) 2 E.target) (baseIndex n (r + 1)) :
              DerivLp n 2 E.target) : ℝ^n → ℝ) (E x) * c i j x := by
      have hTBase (j : Fin n) := wkTopProduct_base_ae (by omega) E.open_source (C i j) (Q j)
      filter_upwards [coeFn_finsetSum_coordinate (p := (2 : ℝ≥0∞)) Finset.univ
          (fun j ↦ wkTopProduct (by omega) E.open_source (C i j) (Q j)) (baseIndex n (r + 1)),
        ae_all_iff.2 hTBase, ae_all_iff.2 fun j ↦ hQ j,
        ae_all_iff.2 fun j ↦ mkWkpSpaceOnOfContDiffMemLpFinite_apply_ae (c i j) (hc i j)
          (hcMem i j) (baseIndex n (r + 1))] with x hx hT hq hC
      refine hx.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
      simp only [baseRepresentative] at hT
      rw [hT j, hq j, mul_comm]
      congr 1
      simpa [baseIndex_toList, iteratedPartialDeriv] using hC j
    have hPderiv (i : Fin n) : HasWeakDerivativeOn (n := n) E.source [i]
        ((P : WkpAmbientOn n (r + 1) 2 E.source) (baseIndex n (r + 1)))
        ((D i : WkpAmbientOn n (r + 1) 2 E.source) (baseIndex n (r + 1))) :=
      (hasWeakDerivativeOn_congr_ae hP.symm (hDBase i).symm).1 <| by
        simpa [c] using hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp
          (p := (2 : ℝ≥0∞)) mu (by norm_num) (hE.of_le (by simp)) hEsymm (Lp.memLp _)
          (fun j ↦ Lp.memLp _) (fun j ↦ by
            simpa [hU0dU j] using U0.property (firstDerivIndex n (r + 1) (by omega) j)) i
    have hDcompat (i : Fin n) :
        ((D i : WkpAmbientOn n (r + 1) 2 E.source) (baseIndex n (r + 1)) :
          DerivLp n 2 E.source) =
        ((P : WkpAmbientOn n (r + 1) 2 E.source) (firstDerivIndex n (r + 1) (by omega) i) :
          DerivLp n 2 E.source) :=
      Lp.ext ((P.property.hasWeakDerivativeOn_first (by omega) i).unique_ae E.open_source
        (hPderiv i)).symm
    obtain ⟨W, hW⟩ := exists_succOrder_of_firstDerivatives (by omega) P D hDcompat
    exact ⟨W, hW.trans (by simpa [U0] using hP)⟩

end SobolevSpace.WeakChangeOfVariables
