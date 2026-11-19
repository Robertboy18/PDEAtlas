/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback

/-!
# First-order pullback on bounded charts

If `E` is a `C¹` diffeomorphism between bounded open sets with `C¹` inverse and
`u ∈ W^{1,2}(E.target)`, then `u ∘ E ∈ W^{1,2}(E.source)` with weak derivatives given by the
chain rule, `∂ᵢ(u ∘ E) = ∑ⱼ (∂ⱼu) ∘ E · ∂ᵢEⱼ`. This is the change of variables that flattens a
`C¹` boundary in the extension theorem (Evans, PDE, §5.4, where it is applied to `C¹`
functions before a density argument) and in the treatment of coordinate transformations of
Sobolev spaces (Adams–Fournier, *Sobolev Spaces*, Chapter 3). The `C¹`
inverse is what transports Lebesgue measure with a bounded Jacobian, so that `L²` membership
survives composition; boundedness of the source makes the continuous chart derivatives `L^∞`.

## Main results

* `exists_W1Two_pullback_on_bounded_chart`: existence of the pulled-back graph-space element
  `P ∈ WkpSpaceOn n 1 2 E.source` whose base coordinate is `u ∘ E` a.e.

This is the base case of the induction in `Extension.Pullback.HigherOrder`. The analytic
content, the weak chain rule `hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp`, is proved
in `Calculus.Pullback.FirstOrder.LocalizedPullback`; we assemble the rows into a
graph-space element.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271; step 5 of the proof, p. 270,
  straightens the boundary by `y = Φ(x)` and applies the change of variables to `C¹` functions
  before the density argument.
  <https://doi.org/10.1090/gsm/019>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 3, The Sobolev Spaces `W^{m,p}(Ω)`, pp. 59-78, for coordinate
  transformations of `W^{m,p}`.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory
open SobolevSpace.GraphSpace
open scoped ENNReal

variable {n : ℕ}

/-- A `W^{1,2}` field pulls back through the full source of a bounded
`C^1` chart with `C^1` inverse. -/
theorem exists_W1Two_pullback_on_bounded_chart
    (mu : SobolevSpace.Approximation.Mollifier n)
    {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hSource : Bornology.IsBounded E.source)
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{1,2}(E.target)) :
    ∃ P : W^{1,2}(E.source),
      ((((P : WkpAmbientOn n 1 2 E.source) (baseIndex n 1) :
          DerivLp n 2 E.source) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n E.source] fun x ↦
          (((U : WkpAmbientOn n 1 2 E.target) (baseIndex n 1) :
            DerivLp n 2 E.target) : ℝ^n → ℝ) (E x) := by
  classical
  set u : ℝ^n → ℝ := ((U : WkpAmbientOn n 1 2 E.target) (baseIndex n 1) : ℝ^n → ℝ)
  let du : Fin n → ℝ^n → ℝ := fun j ↦
    ((U : WkpAmbientOn n 1 2 E.target) (singleDerivIndex n j) : ℝ^n → ℝ)
  let c : Fin n → Fin n → ℝ^n → ℝ := fun i j x ↦
    ((fderiv ℝ (fun y ↦ E y) x) (EuclideanSpace.single i (1 : ℝ))) j
  have hcomp {f : ℝ^n → ℝ} (hf : MemLp f 2 (domainMeasure n E.target)) :
      MemLp (fun x ↦ f (E x)) 2 (domainMeasure n E.source) :=
    memLp_comp_partialHomeomorph_of_bounded_target (by norm_num) hE hEsymm hTarget hf
  have hc (i j : Fin n) : Continuous (c i j) :=
    ((PiLp.proj (𝕜 := ℝ) (2 : ℝ≥0∞) (fun _ : Fin n ↦ ℝ) j).contDiff.comp
      ((hE.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const)).continuous
  let d : DerivIndex n 1 → ℝ^n → ℝ :=
    firstOrderRows (fun x ↦ u (E x)) fun i x ↦ ∑ j, du j (E x) * c i j x
  have hmem (a : DerivIndex n 1) : MemLp (d a) 2 (domainMeasure n E.source) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa [d] using hcomp (Lp.memLp _)
    · simpa [d] using memLp_finsetSum (p := 2) Finset.univ fun j _ ↦
        (hcomp (f := du j) (Lp.memLp _)).fun_mul
          (memLp_top_on_bounded_of_continuous hSource (hc i j))
  have hchain (i : Fin n) :
      HasWeakDerivativeOn E.source [i] (fun x ↦ u (E x)) fun x ↦ ∑ j, du j (E x) * c i j x :=
    hasWeakDerivativeOn_comp_partialHomeomorph_W1p_of_memLp mu (by norm_num) hE hEsymm
      (Lp.memLp _) (fun j ↦ Lp.memLp _) (fun j ↦ by
        simpa [u, du, firstDerivIndex_one] using
          U.property.hasWeakDerivativeOn_first (by norm_num) j) i
  have hweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn E.source a.toList (fun x ↦ u (E x)) (d a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa [d] using hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain (hcomp (Lp.memLp _)) (by norm_num))
    · simpa [d] using hchain i
  exact ⟨mkWkpSpaceOnOfWeakDerivatives _ d (by simp [d]) hmem hweak,
    (mkWkpSpaceOnOfWeakDerivatives_apply_ae _ d _ hmem hweak _).trans (by simp [d])⟩

end SobolevSpace.WeakChangeOfVariables
