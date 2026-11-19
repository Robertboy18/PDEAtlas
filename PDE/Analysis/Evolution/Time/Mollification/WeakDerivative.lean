/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.Mollification
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.Analysis.Evolution.Time.Euclidean
import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean
import PDE.Spaces.Sobolev.Approximation.Mollification.WeakDerivatives

/-!
# Mollification of weak time derivatives

A Banach-valued weak time derivative becomes a classical derivative after
positive-scale convolution in time. The proof scalarizes against the
continuous dual, applies the Euclidean weak-derivative calculus for
mollifiers, and then uses separation by the dual, Mathlib's
`SeparatingDual.eq_zero_of_forall_dual_eq_zero`, to identify the
Banach-valued derivative. This is the identity `(u^ε)' = η_ε * u'` in step 1 of the proof of
Evans, §5.9.2, Theorem 2, which he checks as in the scalar case; here the weak derivative is
taken on all of `ℝ`.

## Main results

* `apply_mollifyVector`: continuous linear functionals commute with Banach-valued
  mollification.
* `hasDerivAt_timeMollify_of_hasWeakTimeDerivative`,
  `hasDerivAt_regularizeTime_of_hasWeakTimeDerivative`: if `g` is the weak time derivative of
  `f` on `ℝ`, every positive-scale mollification of `f` is differentiable, with derivative the
  mollification of `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.9.2, Theorem 2 (Calculus in an abstract space) and
  step 1 of its proof, p. 302. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory
open scoped ENNReal Topology

namespace PDE.Analysis.Evolution

open SobolevSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Continuous linear functionals commute with Banach-valued mollification.
This is the Bochner-integral naturality used to reduce weak differentiation
to the scalar theorem. -/
theorem apply_mollifyVector
    [CompleteSpace X]
    (ell : StrongDual ℝ X) (μ : SobolevSpace.Approximation.Mollifier 1)
    {ε : ℝ} (hε : 0 < ε) (f : ℝ^1 → X)
    (hf : LocallyIntegrable f (volume : Measure (ℝ^1))) (x : ℝ^1) :
    ell (SobolevSpace.Approximation.mollifyVector μ ε f x) =
      SobolevSpace.Approximation.mollify μ ε (ell ∘ f) x := by
  have hcs : HasCompactSupport (SobolevSpace.Approximation.scaled μ ε) :=
    SobolevSpace.Approximation.scaled_hasCompactSupport μ hε
  have hcont : Continuous (SobolevSpace.Approximation.scaled μ ε) :=
    (SobolevSpace.Approximation.scaled_contDiff μ).continuous
  have hex := hcs.convolutionExists_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (volume : Measure (ℝ^1))) hcont hf
  have hint : Integrable
      (fun y : ℝ^1 ↦ SobolevSpace.Approximation.scaled μ ε y • f (x - y))
      (volume : Measure (ℝ^1)) := hex x
  calc
    ell (SobolevSpace.Approximation.mollifyVector μ ε f x) =
        ell (∫ y : ℝ^1, SobolevSpace.Approximation.scaled μ ε y • f (x - y)
          ∂(volume : Measure (ℝ^1))) := by
            rfl
    _ = ∫ y : ℝ^1,
          ell (SobolevSpace.Approximation.scaled μ ε y • f (x - y))
          ∂(volume : Measure (ℝ^1)) := by
            exact (ell.integral_comp_comm hint).symm
    _ = SobolevSpace.Approximation.mollify μ ε (ell ∘ f) x := by
          simp [SobolevSpace.Approximation.mollify, MeasureTheory.convolution]

/-- If `g` is the Banach-valued weak time derivative of `f`, then every
positive-scale mollification is classically differentiable with derivative
the corresponding mollification of `g`. -/
theorem hasDerivAt_timeMollify_of_hasWeakTimeDerivative
    [CompleteSpace X]
    (μ : SobolevSpace.Approximation.Mollifier 1) {ε : ℝ} (hε : 0 < ε)
    {f g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn Set.univ f g) (t : ℝ) :
    HasDerivAt (timeMollify μ ε f) (timeMollify μ ε g t) t := by
  have hf : LocallyIntegrable f (volume : Measure ℝ) :=
    locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f
  have hg : LocallyIntegrable g (volume : Measure ℝ) :=
    locallyIntegrableOn_univ.mp hweak.locallyIntegrable_g
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  let fE : ℝ^1 → X := f ∘ e.symm
  let gE : ℝ^1 → X := g ∘ e.symm
  have hfE : LocallyIntegrable fE (volume : Measure (ℝ^1)) :=
    locallyIntegrable_comp_oneDimensionalEquiv_symm f hf
  have hgE : LocallyIntegrable gE (volume : Measure (ℝ^1)) :=
    locallyIntegrable_comp_oneDimensionalEquiv_symm g hg
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (timeMollify μ ε f) :=
    timeMollify_contDiff μ hε f hf
  have hbase : HasDerivAt (timeMollify μ ε f)
      (deriv (timeMollify μ ε f) t) t :=
    hsmooth.differentiable (by simp) t |>.hasDerivAt
  suffices hvalue : deriv (timeMollify μ ε f) t = timeMollify μ ε g t by
    simpa [hvalue] using hbase
  apply sub_eq_zero.mp
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro ell
  have hellf : LocallyIntegrable (ell ∘ fE) (volume : Measure (ℝ^1)) := by
    intro x
    exact ell.integrableAtFilter_comp (hfE x)
  have hellg : LocallyIntegrable (ell ∘ gE) (volume : Measure (ℝ^1)) := by
    intro x
    exact ell.integrableAtFilter_comp (hgE x)
  have hscalar :=
    SobolevSpace.Approximation.iteratedPartialDeriv_mollify_eq_mollify_of_hasWeakDerivative_univ
      (n := 1) (μ := μ) hε (α := [0]) (by simp)
      (f := ell ∘ fE) (g := ell ∘ gE)
      hellf
      (by
        simpa [fE, gE, e, Function.comp_def] using
          hweak.to_hasWeakDerivativeOn ell)
  have hpair_f :
      (fun s ↦ ell (timeMollify μ ε f s)) =
        (SobolevSpace.Approximation.mollify μ ε (ell ∘ fE)) ∘ e := by
    funext s
    change ell (SobolevSpace.Approximation.mollifyVector μ ε fE (e s)) =
      SobolevSpace.Approximation.mollify μ ε (ell ∘ fE) (e s)
    exact apply_mollifyVector ell μ hε fE hfE (e s)
  have hpair_g :
      ell (timeMollify μ ε g t) =
        SobolevSpace.Approximation.mollify μ ε (ell ∘ gE) (e t) := by
    change ell (SobolevSpace.Approximation.mollifyVector μ ε gE (e t)) = _
    rw [← apply_mollifyVector ell μ hε gE hgE (e t)]
  have hscalar_deriv :
      deriv ((SobolevSpace.Approximation.mollify μ ε (ell ∘ fE)) ∘ e) t =
        SobolevSpace.Approximation.mollify μ ε (ell ∘ gE) (e t) := by
    rw [deriv_comp_equivOfUnique_symm]
    · simpa only [iteratedPartialDeriv] using congrFun hscalar (e t)
    · exact (SobolevSpace.Approximation.mollify_contDiff_of_pos
        μ hε (ell ∘ fE) hellf).differentiable (by simp) _
  have hchain :
      deriv (fun s ↦ ell (timeMollify μ ε f s)) t =
        ell (deriv (timeMollify μ ε f) t) := by
    have := ell.hasFDerivAt.comp_hasDerivAt t hbase
    simpa [Function.comp_def] using this.deriv
  rw [sub_eq_add_neg, map_add, map_neg, hchain.symm, hpair_f, hscalar_deriv,
    hpair_g, add_neg_cancel]

/-- Canonical time regularization commutes with a Banach-valued weak time
derivative. -/
theorem hasDerivAt_regularizeTime_of_hasWeakTimeDerivative
    [CompleteSpace X] {ε : ℝ} (hε : 0 < ε) {f g : ℝ → X}
    (hweak : HasWeakTimeDerivativeOn Set.univ f g) (t : ℝ) :
    HasDerivAt (regularizeTime ε f) (regularizeTime ε g t) t := by
  exact hasDerivAt_timeMollify_of_hasWeakTimeDerivative
    (SobolevSpace.Approximation.standardMollifier 1) hε hweak t

end PDE.Analysis.Evolution
