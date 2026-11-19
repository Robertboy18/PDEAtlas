/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.DivergenceForm.NonsymmetricH2
import PDE.Elliptic.Regularity.Global.ShiftedDivergenceHigher
import PDE.Elliptic.Regularity.Global.ShiftedDivergenceSolver

/-!
# Higher-order regularity for nonsymmetric divergence-form operators

The principal divergence-form part is uniformly elliptic,
while the first- and zero-order terms are controlled by a Gårding shift.
We apply the elliptic all-order theorem to prove the
operator-theoretic ingredients needed at every Sobolev order:

* a bounded `H^k → H^{k+2}` solution operator at every order, so its norm
  gives an elliptic constant;
* the resulting two-step estimate for an unshifted weak solution.

These results supply the spatial regularity input used by nonsymmetric
higher-wave estimates. Ellipticity is the quadratic lower bound `MatrixEllipticLowerBound`; the
principal coefficient matrix need not be symmetric.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5, and §7.2.3, proof of Theorem 5, step 3,
  equations (59)-(60), and estimate (64).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.DivergenceFormWave

open PDE.Analysis.Variational
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal BigOperators

variable {n : ℕ} [Fact (0 < n)]
variable {Omega : Set (ℝ^n)}

/--
The Gårding-shifted full solution has an `H^{k+2}` representative for every
Sobolev forcing order `k`.
-/
theorem fullGarding_hasHigherSolutionLift
    (k : ℕ) (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j))
    (B : Fin n → W^{k,∞}(Omega)) (C : W^{k,∞}(Omega)) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)‖ ≤ beta)
    (hc : ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C‖ ≤ gamma) :
    let A1 : Fin n → Fin n → W^{1,∞}(Omega) := fun i j ↦
      lowerOrderCLM (n := n) (k := 1) (m := k + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
    let b0 : Fin n → DerivLp n ∞ Omega := fun i ↦
      wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)
    let c0 : DerivLp n ∞ Omega := wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C
    HasHigherSolutionLift (n := n) (Omega := Omega) k
      (fullGardingWeakSolveCLM hOmega A1 a (fun i j ↦ by simpa [A1] using haRep i j)
        b0 c0 alpha beta gamma halpha hElliptic hbeta hgamma hb hc) := by
  intro A1 b0 c0 f
  obtain ⟨W, hW⟩ := globalHigherRegularity.exists_of_weak_shifted_full_divergence_solution k
    hOmega hChart hChartSymm A a haRep haContDiff B C _ f _
    (fullGardingWeakSolveCLM_isWeakSolution hOmega A1 a _ b0 c0 alpha beta gamma halpha
      hElliptic hbeta hgamma hb hc _) alpha halpha hElliptic
  exact ⟨W, Lp.ext (by simpa [baseRepresentative, higherWeakSolutionBaseCLM] using hW)⟩

/--
The bounded Gårding-shifted full solution operator
`H^k(Omega) → H^{k+2}(Omega)`.

Its norm is the level-`k` elliptic constant used in the nonsymmetric form of
Evans estimate (64).
-/
noncomputable def fullGardingHigherSolveCLM
    (k : ℕ) (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j))
    (B : Fin n → W^{k,∞}(Omega)) (C : W^{k,∞}(Omega)) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)‖ ≤ beta)
    (hc : ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C‖ ≤ gamma) :
    W^{k,2}(Omega) →L[ℝ] W^{(k + 2),2}(Omega) :=
  higherSolutionOperator hOmega.toC1ExtensionAtlas.isOpen _
    (fullGarding_hasHigherSolutionLift k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
      beta gamma halpha hElliptic hbeta hgamma hb hc)

/-- The verified operator-norm estimate at Sobolev level `k`. -/
theorem fullGardingHigherSolveCLM_norm_le (k : ℕ) (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j)) (B : Fin n → W^{k,∞}(Omega))
    (C : W^{k,∞}(Omega)) (alpha beta gamma : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)‖ ≤ beta)
    (hc : ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C‖ ≤ gamma)
    (f : W^{k,2}(Omega)) :
    ‖fullGardingHigherSolveCLM k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
      beta gamma halpha hElliptic hbeta hgamma hb hc f‖ ≤
      ‖fullGardingHigherSolveCLM k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
        beta gamma halpha hElliptic hbeta hgamma hb hc‖ * ‖f‖ :=
  ContinuousLinearMap.le_opNorm _ f

/--
The base coordinate of the all-order solver is the canonical shifted weak
solution.
-/
theorem fullGardingHigherSolveCLM_base
    (k : ℕ) (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j))
    (B : Fin n → W^{k,∞}(Omega)) (C : W^{k,∞}(Omega)) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)‖ ≤ beta)
    (hc : ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C‖ ≤ gamma)
    (f : W^{k,2}(Omega)) :
    let A1 : Fin n → Fin n → W^{1,∞}(Omega) := fun i j ↦
      lowerOrderCLM (n := n) (k := 1) (m := k + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
    let b0 : Fin n → DerivLp n ∞ Omega := fun i ↦
      wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)
    let c0 : DerivLp n ∞ Omega := wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C
    wkpBaseCoordinateCLM (n := n) (m := k + 2) (p := 2) (Ω := Omega)
        (fullGardingHigherSolveCLM k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
          beta gamma halpha hElliptic hbeta hgamma hb hc f) =
      higherWeakSolutionBaseCLM (n := n) (Omega := Omega) (m := k)
        (fullGardingWeakSolveCLM hOmega A1 a (fun i j ↦ by simpa [A1] using haRep i j)
          b0 c0 alpha beta gamma halpha hElliptic hbeta hgamma hb hc) f :=
  higherSolutionOperator_base hOmega.toC1ExtensionAtlas.isOpen _
    (fullGarding_hasHigherSolutionLift k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
      beta gamma halpha hElliptic hbeta hgamma hb hc) f

/--
The arbitrary-order nonsymmetric analogue of Evans estimates (59)-(60).

Let `L` be the unshifted full operator. If `u ∈ H¹₀` solves `L u = f` and a
representative of `u` is already available in `H^k`, then `u` has an
`H^{k+2}` representative and

`‖u‖_{H^{k+2}} ≤ ‖S_k‖ (‖f‖_{H^k} + |μ| ‖u‖_{H^k})`,

where `S_k` is the verified shifted full solution operator and `μ` is the
Gårding shift. This is the recurrence required by the spatial induction in
the nonsymmetric wave theorem.
-/
theorem exists_higher_with_norm_of_unshifted_full_weakSolution (k : ℕ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j)) (B : Fin n → W^{k,∞}(Omega))
    (C : W^{k,∞}(Omega)) (alpha beta gamma : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) (hbeta : 0 ≤ beta)
    (hgamma : 0 ≤ gamma)
    (hb : ∀ i, ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) (B i)‖ ≤ beta)
    (hc : ‖wkpBaseCoordinateCLM (n := n) (m := k) (p := ∞) (Ω := Omega) C‖ ≤ gamma)
    (f : W^{k,2}(Omega)) (u : H¹₀(Omega))
    (hu : IsWeakShiftedFullDivergenceSolution (n := n) (Ω := Omega)
      (fun i j ↦ ((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega)) (fun i ↦ ((B i : WkpAmbientOn n k ∞ Omega) (baseIndex n k) :
      DerivLp n ∞ Omega)) ((C : WkpAmbientOn n k ∞ Omega) (baseIndex n k) : DerivLp n ∞ Omega) 0
      ((f : WkpAmbientOn n k 2 Omega) (baseIndex n k) : DerivLp n 2 Omega)
      (0 : Fin n → DerivLp n 2 Omega) u)
    (Uprevious : W^{k,2}(Omega))
    (hUprevious : wkpBaseCoordinateCLM (n := n) (m := k) (p := 2) (Ω := Omega) Uprevious =
      baseCoordCLM (n := n) (Ω := Omega) u) :
    ∃ W : W^{(k + 2),2}(Omega),
      wkpBaseCoordinateCLM (n := n) (m := k + 2) (p := 2) (Ω := Omega) W =
        baseCoordCLM (n := n) (Ω := Omega) u ∧
      ‖W‖ ≤ ‖fullGardingHigherSolveCLM k hOmega hChart hChartSymm A a haRep haContDiff B C alpha
          beta gamma halpha hElliptic hbeta hgamma hb hc‖ *
        (‖f‖ + |coerciveShift (n := n) alpha beta gamma| * ‖Uprevious‖) := by
  let hOpen := hOmega.toC1ExtensionAtlas.isOpen
  let A1 : Fin n → Fin n → W^{1,∞}(Omega) := fun i j ↦
    lowerOrderCLM (n := n) (k := 1) (m := k + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  have haRep1 : ∀ i j, ⇑((A1 i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j :=
    fun i j ↦ by simpa [A1] using haRep i j
  let g : W^{k,2}(Omega) := f + coerciveShift (n := n) alpha beta gamma • Uprevious
  have hshift := (isWeakShiftedFullDivergenceSolution_change_shift _ _ _ 0
    (coerciveShift (n := n) alpha beta gamma) _ u).1 hu
  rw [sub_zero, ← hUprevious] at hshift
  have huEq : u = fullGardingWeakSolveCLM hOmega A1 a haRep1 _ _ alpha beta gamma halpha
      hElliptic hbeta hgamma hb hc (wkpBaseCoordinateCLM g) :=
    (existsUnique_weakShiftedFullDivergenceSolution_of_aeElliptic hOpen (coefficientBase A1) _ _
      (coefficientBase_aeUniformlyElliptic hOpen.measurableSet A1 a haRep1 alpha halpha
        hElliptic) hbeta hgamma hb hc _ 0).unique
      (by rwa [map_add, map_smul])
      (fullGardingWeakSolveCLM_isWeakSolution hOmega A1 a haRep1 _ _ alpha beta gamma halpha
        hElliptic hbeta hgamma hb hc _)
  refine ⟨_, (fullGardingHigherSolveCLM_base k hOmega hChart hChartSymm A a haRep haContDiff B C
      alpha beta gamma halpha hElliptic hbeta hgamma hb hc g).trans
      (congrArg (baseCoordCLM (n := n) (Ω := Omega)) huEq.symm),
    (ContinuousLinearMap.le_opNorm _ g).trans
      (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans_eq ?_) (by positivity))⟩
  rw [norm_smul, Real.norm_eq_abs]

end Hyperbolic.DivergenceFormWave
