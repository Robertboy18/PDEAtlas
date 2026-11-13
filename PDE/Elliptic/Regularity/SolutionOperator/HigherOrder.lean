/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.H2
import PDE.Elliptic.Regularity.Global.HigherOrder

/-!
# Arbitrary-order elliptic solution operator

On a bounded domain with a `C2BoundaryAtlas` whose charts are `C^{m+2}` with `C^{m+1}` inverses, for
uniformly elliptic principal coefficients in `W^{m+1,∞}` with `C^{m+1}` representatives on `ℝⁿ`, the
weak Dirichlet solution depends linearly and boundedly on its `H^m` forcing, with values in
`H^{m+2}` (`globalHigherSolveCLM`, `globalHigherSolveCLM_base`). The all-order theorem
`exists_global_higherOrder_of_isWeakDivergenceSolution` supplies the qualitative hypothesis of the
closed-graph construction of `PDE.Elliptic.Regularity.SolutionOperator.Lift` at every order
(`globalHigherRegularity_hasHigherSolutionLift`).

The operator norm of `globalHigherSolveCLM m` is a constant for the estimate
`‖u‖_{H^{m+2}(U)} ≤ C ‖f‖_{H^m(U)}` of the remark after Evans's §6.3.2, Theorem 5, for an operator
without lower-order terms. Evans assumes `aⁱʲ, bⁱ, c ∈ C^{m+1}(Ū)`, (72), and a `C^{m+2}` boundary,
(75).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, Theorem 5 (Higher boundary regularity), (72)-(77),
  and the remark after it, pp. 340-341.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Omega : Set (ℝ^n)}

/--
The global all-order theorem `exists_global_higherOrder_of_isWeakDivergenceSolution`
supplies the qualitative lift required by the closed-graph construction at every forcing
order.

The weak solver uses only the canonical `W^{1,∞}` restriction of the
principal coefficients. The original `W^{m+1,∞}` bundle is retained in the
weak equation passed to the global regularity theorem.
-/
theorem globalHigherRegularity_hasHigherSolutionLift
    (m : ℕ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 1)
        (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (m + 1) ∞ Omega)
          (baseIndex n (m + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j,
      ContDiff ℝ (m + 1) (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    HasHigherSolutionLift (n := n) (Omega := Omega) m
      (globalH2WeakSolveCLM
        hOmega
        (fun i j ↦
          lowerOrderCLM
            (n := n) (k := 1) (m := m + 1) (p := ∞)
            (Ω := Omega) (by omega) (A i j))
        a
        (fun i j ↦ by simpa using haRep i j)
        alpha halpha hElliptic) := by
  intro f
  let A1 : Fin n → Fin n → W^{1,∞}(Omega) := fun i j ↦
    lowerOrderCLM
      (n := n) (k := 1) (m := m + 1) (p := ∞)
      (Ω := Omega) (by omega) (A i j)
  have haRep1 : ∀ i j,
      ⇑((A1 i j : WkpAmbientOn n 1 ∞ Omega)
          (baseIndex n 1) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j := by
    intro i j
    simpa [A1] using haRep i j
  let S :=
    globalH2WeakSolveCLM hOmega A1 a haRep1 alpha halpha hElliptic
  have hcoeff :
      coefficientBase A1 =
        (fun i j ↦
          ((A i j : WkpAmbientOn n (m + 1) ∞ Omega)
            (baseIndex n (m + 1)) : DerivLp n ∞ Omega)) := by
    funext i j
    rfl
  have hweak :
      IsWeakDivergenceSolution
        (n := n) (Ω := Omega)
        (fun i j ↦
          ((A i j : WkpAmbientOn n (m + 1) ∞ Omega)
            (baseIndex n (m + 1)) : DerivLp n ∞ Omega))
        ((f : WkpAmbientOn n m 2 Omega)
          (baseIndex n m) : DerivLp n 2 Omega)
        (S (wkpBaseCoordinateCLM
          (n := n) (m := m) (p := 2) (Ω := Omega) f)) := by
    rw [← hcoeff]
    simpa only [S, wkpBaseCoordinateCLM_apply] using
      globalH2WeakSolveCLM_isWeakDivergenceSolution
        hOmega A1 a haRep1 alpha halpha hElliptic
        (wkpBaseCoordinateCLM
          (n := n) (m := m) (p := 2) (Ω := Omega) f)
  obtain ⟨regularityW, hregularityW⟩ :=
    exists_global_higherOrder_of_isWeakDivergenceSolution
      m hOmega hChart hChartSymm A a haRep haContDiff f
      (S (wkpBaseCoordinateCLM
        (n := n) (m := m) (p := 2) (Ω := Omega) f))
      hweak alpha halpha hElliptic
  refine ⟨regularityW, ?_⟩
  apply Lp.ext
  simpa [baseRepresentative, higherWeakSolutionBaseCLM, S, A1] using
    hregularityW

/--
The bounded solution operator `H^m → H^{m+2}` at arbitrary Sobolev order.

It is the canonical weak Dirichlet solution, lifted by the global
regularity theorem and made continuous by the closed graph theorem.
-/
noncomputable def globalHigherSolveCLM
    (m : ℕ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 1)
        (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (m + 1) ∞ Omega)
          (baseIndex n (m + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j,
      ContDiff ℝ (m + 1) (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha) :
    W^{m,2}(Omega) →L[ℝ] W^{m + 2,2}(Omega) :=
  higherSolutionOperator
    hOmega.toC1ExtensionAtlas.isOpen
    (globalH2WeakSolveCLM
      hOmega
      (fun i j ↦
        lowerOrderCLM
          (n := n) (k := 1) (m := m + 1) (p := ∞)
          (Ω := Omega) (by omega) (A i j))
      a
      (fun i j ↦ by simpa using haRep i j)
      alpha halpha hElliptic)
    (globalHigherRegularity_hasHigherSolutionLift
      m hOmega hChart hChartSymm A a haRep haContDiff
      alpha halpha hElliptic)

/--
The arbitrary-order solution operator represents the canonical weak
Dirichlet solution in its base `L²` coordinate.

This is the public characterization theorem for `globalHigherSolveCLM`.
Downstream arguments should use it instead of unfolding the closed-graph
construction or the coefficient-order restriction used by the weak solver.
-/
theorem globalHigherSolveCLM_base
    (m : ℕ)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (m + 1)
        (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{m + 1,∞}(Omega))
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j,
      ⇑((A i j : WkpAmbientOn n (m + 1) ∞ Omega)
          (baseIndex n (m + 1)) : DerivLp n ∞ Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j,
      ContDiff ℝ (m + 1) (fun x ↦ a x i j))
    (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (f : W^{m,2}(Omega)) :
    wkpBaseCoordinateCLM
        (n := n) (m := m + 2) (p := 2) (Ω := Omega)
        (globalHigherSolveCLM
          m hOmega hChart hChartSymm A a haRep haContDiff
            alpha halpha hElliptic f) =
      higherWeakSolutionBaseCLM
        (globalH2WeakSolveCLM
          hOmega
          (fun i j ↦
            lowerOrderCLM
              (n := n) (k := 1) (m := m + 1) (p := ∞)
              (Ω := Omega) (by omega) (A i j))
          a
          (fun i j ↦ by simpa using haRep i j)
          alpha halpha hElliptic)
        f := by
  exact higherSolutionOperator_base
    hOmega.toC1ExtensionAtlas.isOpen
    (globalH2WeakSolveCLM
      hOmega
      (fun i j ↦
        lowerOrderCLM
          (n := n) (k := 1) (m := m + 1) (p := ∞)
          (Ω := Omega) (by omega) (A i j))
      a
      (fun i j ↦ by simpa using haRep i j)
      alpha halpha hElliptic)
    (globalHigherRegularity_hasHigherSolutionLift
      m hOmega hChart hChartSymm A a haRep haContDiff
      alpha halpha hElliptic)
    f

end SobolevSpace.GraphSpace.BoundaryRegularity
