/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
public import PDE.Elliptic.Regularity.Global.ShiftedDivergenceSolver
public import PDE.Elliptic.Variational.ShiftedDivergenceForm
import PDE.Elliptic.Regularity.Global.ShiftedDivergence

/-!
# The nonsymmetric global `H²` lift used in wave regularity

For the full divergence-form operator

`L u = -∂ᵢ(aᵢⱼ ∂ⱼu) + bᵢ ∂ᵢu + c u`,

Evans's estimate (59) in §7.2.3 compensates for the fact that `L` need not be
symmetric.  Its elliptic consequence is

`‖u‖_{H²} <= C (‖L u‖_{L²} + ‖u‖_{L²})`.

We prove that consequence in four steps:

1. the Gårding inequality supplies a canonical mass shift;
2. Lax-Milgram constructs the shifted full weak solver;
3. the global full-operator `H²` theorem gives every solver value an
   `H²` representative;
4. the closed graph theorem assembles those representatives into one bounded
   linear `L² -> H²` operator.

An unshifted weak solution is then rewritten as a shifted solution with
right-hand side `f + μu`.  Uniqueness identifies it with the bounded shifted
solver, yielding the displayed estimate with an explicit operator-norm
constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, proof of Theorem 5, step 3, equations (59)-(60),
  and §6.3.2, Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace Hyperbolic.DivergenceFormWave

open MeasureTheory
open PDE.Analysis.Variational
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal BigOperators

variable {n : ℕ} [Fact (0 < n)]
variable {Omega : Set (ℝ^n)}

/--
The Gårding-shifted full weak solution operator for scalar `L²` forcing.

The load is scalar `L²` forcing, the case used after writing a wave equation as
`L u = f - u_tt`.
-/
noncomputable def fullGardingWeakSolveCLM
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega) (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (b : Fin n → DerivLp n ∞ Omega) (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma) :
    DerivLp n 2 Omega →L[ℝ] H¹₀(Omega) :=
  fullDivergenceWeakSolveCLM (coefficientBase A) b c0
    (integratedElliptic_multiplication_of_ae _ (coefficientBase_aeUniformlyElliptic
      hOmega.toC1ExtensionAtlas.isOpen.measurableSet A a haRep alpha halpha hElliptic))
    hbeta hgamma hb hc0 le_rfl

/-- The shifted weak solver satisfies the full distributional equation. -/
theorem fullGardingWeakSolveCLM_isWeakSolution (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (b : Fin n → DerivLp n ∞ Omega) (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma)
    (f : DerivLp n 2 Omega) :
    IsWeakShiftedFullDivergenceSolution (n := n) (Ω := Omega) (coefficientBase A) b c0
      (coerciveShift (n := n) alpha beta gamma) f (0 : Fin n → DerivLp n 2 Omega)
      (fullGardingWeakSolveCLM hOmega A a haRep b c0 alpha beta gamma halpha hElliptic hbeta
        hgamma hb hc0 f) :=
  fullDivergenceWeakSolveCLM_isWeakSolution _ _ _ _ _ _ _ _ _ hOmega.toC1ExtensionAtlas.isOpen f

/--
Every value of the shifted full weak solver has the global `H²`
representative supplied by the proved full-operator boundary theorem.
-/
theorem fullGardingWeakSolveCLM_hasH2 (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (b : Fin n → DerivLp n ∞ Omega)
    (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma) (f : DerivLp n 2 Omega) :
    ∃ W : W^{2,2}(Omega),
      ⇑((W : WkpAmbientOn n 2 2 Omega) (baseIndex n 2) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑((((fullGardingWeakSolveCLM hOmega A a haRep b c0 alpha beta gamma halpha hElliptic
              hbeta hgamma hb hc0 f : H¹₀(Omega)) : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) := by
  obtain ⟨W, hW⟩ := exists_global_h2_of_weak_shifted_full_divergence_solution hOmega A a haRep
    haC1 b c0 (coerciveShift (n := n) alpha beta gamma) f _
    (fullGardingWeakSolveCLM_isWeakSolution hOmega A a haRep b c0 alpha beta gamma halpha
      hElliptic hbeta hgamma hb hc0 f) alpha halpha hElliptic
  exact ⟨W, by simpa [baseRepresentative] using hW⟩

/--
The bounded full-operator `L² -> H²` solution map obtained from qualitative
global regularity by the closed graph theorem.
-/
noncomputable def fullGardingH2SolveCLM
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega) (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (b : Fin n → DerivLp n ∞ Omega) (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma) :
    DerivLp n 2 Omega →L[ℝ] W^{2,2}(Omega) :=
  (higherSolutionOperator (m := 0) hOmega.toC1ExtensionAtlas.isOpen
      (fullGardingWeakSolveCLM hOmega A a haRep b c0 alpha beta gamma halpha hElliptic hbeta
        hgamma hb hc0)
      (hasHigherSolutionLift_zero _ fun f ↦ by
        simpa using fullGardingWeakSolveCLM_hasH2 hOmega A a haRep haC1 b c0 alpha beta gamma
          halpha hElliptic hbeta hgamma hb hc0 f)).comp
    (orderZeroSobolevCLM (n := n) (p := 2) (Omega := Omega))

/-- The bounded shifted solver represents its full weak solution. -/
theorem fullGardingH2SolveCLM_base_ae (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{1,∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j)) (b : Fin n → DerivLp n ∞ Omega)
    (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma) (f : DerivLp n 2 Omega) :
    ⇑((fullGardingH2SolveCLM hOmega A a haRep haC1 b c0 alpha beta gamma halpha hElliptic hbeta
          hgamma hb hc0 f : WkpAmbientOn n 2 2 Omega) (baseIndex n 2) : DerivLp n 2 Omega)
      =ᵐ[domainMeasure n Omega]
        ⇑((((fullGardingWeakSolveCLM hOmega A a haRep b c0 alpha beta gamma halpha hElliptic
            hbeta hgamma hb hc0 f : H¹₀(Omega)) : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
          (baseIndex n 1) : DerivLp n 2 Omega) := by
  rw [← wkpBaseCoordinateCLM_apply, ← wkpBaseCoordinateCLM_apply, fullGardingH2SolveCLM,
    ContinuousLinearMap.comp_apply, higherSolutionOperator_base]
  simp only [higherWeakSolutionBaseCLM, ContinuousLinearMap.comp_apply, orderZeroSobolevCLM_base]
  simp [h10SubtypeL, h10Submodule]

/--
Usable nonsymmetric form of Evans, §7.2.3 (59)-(60).

If `u` solves the unshifted full equation `L u = f`, then `u` has a global
`H²` representative satisfying

`‖u‖_{H²} <= C (‖f‖_{L²} + |μ| ‖u‖_{L²})`,

where `μ` is the Gårding shift and `C` is the operator norm of the shifted
full `L² -> H²` solver constructed above.
-/
theorem exists_h2_with_norm_of_unshifted_full_weakSolution
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega) (A : Fin n → Fin n → W^{1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) : DerivLp n ∞ Omega)
      =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haC1 : ∀ i j, ContDiff ℝ 1 (fun x ↦ a x i j))
    (b : Fin n → DerivLp n ∞ Omega) (c0 : DerivLp n ∞ Omega) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hb : ∀ i, ‖b i‖ ≤ beta) (hc0 : ‖c0‖ ≤ gamma)
    (f : DerivLp n 2 Omega) (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution (n := n) (Ω := Omega) (coefficientBase A) b c0 0 f
      (0 : Fin n → DerivLp n 2 Omega) u) :
    ∃ W : W^{2,2}(Omega),
      ⇑((W : WkpAmbientOn n 2 2 Omega) (baseIndex n 2) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega]
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega) (baseIndex n 1) : DerivLp n 2 Omega) ∧
      ‖W‖ ≤ ‖fullGardingH2SolveCLM hOmega A a haRep haC1 b c0 alpha beta gamma halpha hElliptic
          hbeta hgamma hb hc0‖ *
        (‖f‖ + |coerciveShift (n := n) alpha beta gamma| *
          ‖baseCoordCLM (n := n) (Ω := Omega) u‖) := by
  let hOpen := hOmega.toC1ExtensionAtlas.isOpen
  let g : DerivLp n 2 Omega :=
    f + coerciveShift (n := n) alpha beta gamma • baseCoordCLM (n := n) (Ω := Omega) u
  have huEq : u = fullGardingWeakSolveCLM hOmega A a haRep b c0 alpha beta gamma halpha hElliptic
      hbeta hgamma hb hc0 g :=
    (existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic hOpen _ b c0
      (coefficientBase_aeUniformlyElliptic hOpen.measurableSet A a haRep alpha halpha hElliptic)
      hbeta hgamma hb hc0 g 0).unique
      (by simpa only [sub_zero] using
        (isWeakShiftedFullDivergenceSolution_change_shift _ b c0 0 _ f u).1 hu)
      (fullGardingWeakSolveCLM_isWeakSolution hOmega A a haRep b c0 alpha beta gamma halpha
        hElliptic hbeta hgamma hb hc0 g)
  refine ⟨_, ?_, (ContinuousLinearMap.le_opNorm _ g).trans
    (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) (by positivity))⟩
  · rw [huEq]
    exact fullGardingH2SolveCLM_base_ae hOmega A a haRep haC1 b c0 alpha beta gamma halpha
      hElliptic hbeta hgamma hb hc0 g
  · rw [norm_smul, Real.norm_eq_abs]

end Hyperbolic.DivergenceFormWave
