/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import PDE.Elliptic.Regularity.SolutionOperator.HigherOrder
import PDE.Hyperbolic.HigherRegularity.EllipticInduction.FiniteChain
public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.SpatialLift
public import PDE.Elliptic.Regularity.Boundary.CoefficientGeometry
public import PDE.Elliptic.Regularity.Boundary.Domain
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Arbitrary-order regularity for divergence-form waves

We combine Evans's finite differentiated-wave induction (Evans,
§7.2.3, Theorem 6) with the global arbitrary-order elliptic regularity theorem
for divergence-form operators on a domain with a `C^{k+2}` boundary atlas.  A
single autonomous divergence-form operator `Lu = -div(a ∇u)` is used
throughout the weak-wave chain.  The elliptic step that Evans invokes at each
level of the induction, namely that the Dirichlet solution operator maps
`H^r` into `H^{r+2}` (Evans, §6.3.2, Theorem 5), is
supplied by `globalHigherRegularity_hasHigherSolutionLift`.

## Main results

* `exists_sobolevTimeJet_of_divergenceFormWeakWaveChain`: given the weak wave
  and its first `k + 1` time derivatives as weak waves on the Dirichlet
  Gelfand triple, linked by the adjacent velocity and acceleration identities
  and with `L∞` bounds on the most differentiated displacement and velocity,
  produce an essentially bounded order-`k + 2` Sobolev time jet whose head is
  the original displacement and whose first derivative is the original
  velocity.  For `k = 0` this is the `H²` conclusion.

## Implementation notes

The chain is indexed in reverse derivative order, with `Fin.last (k + 1)` the
original wave.  The coefficient matrix enters twice: as a `W^{k+1,∞}` class
`A` used by the variational form, and as a pointwise `C^{k+1}` function `a`
used by the boundary regularity theorem; `haRep` identifies the two almost
everywhere.  Restricting `A` with `lowerOrderCLM` provides the coefficient
regularity required by the elliptic theorem at each order `r ≤ k`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6 and step 3 of its proof, and §6.3.2,
  Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.DivergenceFormWave

open Hyperbolic.HigherRegularity
open SobolevSpace
open SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity
open scoped ENNReal

variable {n : ℕ} [Fact (0 < n)]
variable {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

/--
Evans's arbitrary-order wave regularity conclusion for an autonomous
divergence-form weak-wave chain.

For `k = 0` this gives the `H^2` spatial conclusion.  In general, the chain
contains the original wave and its first `k + 1` time derivatives, indexed in
reverse derivative order.  The global elliptic theorem supplies the
`H^r -> H^(r+2)` lift at every `r <= k`; the finite-chain theorem then
constructs an essentially bounded order-`k + 2` Sobolev time jet.
-/
theorem exists_sobolevTimeJet_of_divergenceFormWeakWaveChain (k : ℕ) (ht : t0 < t1)
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (hChart : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 2) (fun x ↦ hOmega.toC1ExtensionAtlas.chart i x))
    (hChartSymm : ∀ i : Fin hOmega.toC1ExtensionAtlas.N,
      ContDiff ℝ (k + 1) (fun y ↦ (hOmega.toC1ExtensionAtlas.chart i).symm y))
    (A : Fin n → Fin n → W^{(k + 1),∞}(Omega)) (a : ℝ^n → Fin n → Fin n → ℝ)
    (haRep : ∀ i j, ⇑((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j)
    (haContDiff : ∀ i j, ContDiff ℝ (k + 1) (fun x ↦ a x i j)) (alpha : ℝ) (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Omega, MatrixEllipticLowerBound (a x) alpha)
    (forcing : (r : Fin (k + 2)) → SobolevTimeJet n r.1 Omega t0 t1)
    (u : Fin (k + 2) → Lp (H¹₀(Omega)) 2 (volume.restrict (Set.Ioc t0 t1)))
    (velocity : Fin (k + 2) → Lp (DerivLp n 2 Omega) 2 (volume.restrict (Set.Ioc t0 t1)))
    (acceleration : Fin (k + 2) →
      Lp (StrongDual ℝ (H¹₀(Omega))) 2 (volume.restrict (Set.Ioc t0 t1)))
    (q0 : Fin (k + 2) → H¹₀(Omega)) (p0 : Fin (k + 2) → DerivLp n 2 Omega)
    (hWave : ∀ r : Fin (k + 2), Hyperbolic.Variational.IsGelfandWeakWaveSolution
      (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmega.toC1ExtensionAtlas.isOpen)
      (fun _ ↦ variableCoeffForm (n := n) (Ω := Omega) (multiplicationCoefficientOperator (n := n)
      (Ω := Omega) (fun i j ↦ ((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) :
      DerivLp n ∞ Omega)))) (dirichletLoadTimeLp hOmega.toC1ExtensionAtlas.isOpen (forcing r).head)
      (u r) (velocity r) (acceleration r) (q0 r) (p0 r))
    (hvelocityLink : ∀ r : Fin (k + 1), (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple
      hOmega.toC1ExtensionAtlas.isOpen).inclusion ((u r.castSucc : ℝ → H¹₀(Omega)) t))
      =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦ (velocity r.succ : ℝ → DerivLp n 2 Omega) t)
    (haccelerationLink : ∀ r : Fin (k + 1), (fun t ↦ (SobolevSpace.GraphSpace.h10L2GelfandTriple
      hOmega.toC1ExtensionAtlas.isOpen).pivotToDual ((velocity r.castSucc : ℝ → DerivLp n 2 Omega)
      t)) =ᵐ[(volume.restrict (Set.Ioc t0 t1))] fun t ↦
      (acceleration r.succ : ℝ → StrongDual ℝ (H¹₀(Omega))) t)
    (huTop : MemLp (fun t ↦ (u (0 : Fin (k + 2)) : ℝ → H¹₀(Omega)) t) (⊤ : ENNReal)
      (volume.restrict (Set.Ioc t0 t1)))
    (hvelocityTop : MemLp (fun t ↦ (velocity (0 : Fin (k + 2)) : ℝ → DerivLp n 2 Omega) t)
      (⊤ : ENNReal) (volume.restrict (Set.Ioc t0 t1))) :
    ∃ solution : SobolevTimeJet n (k + 2) Omega t0 t1,
      ((fun t ↦ wkpBaseCoordinateCLM (n := n) (m := k + 2) (p := 2) (Ω := Omega)
            ((solution.head : ℝ → W^{(k + 2),2}(Omega)) t))
        =ᵐ[(volume.restrict (Set.Ioc t0 t1))]
        fun t ↦ wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)
          (h10SubtypeL (n := n) (Ω := Omega) ((u (Fin.last (k + 1)) : ℝ → H¹₀(Omega)) t))) ∧
      baseCoordinateTimeLp solution.timeDerivative.head = velocity (Fin.last (k + 1)) ∧
      solution.IsEssentiallyBounded := by
  let hOpen := hOmega.toC1ExtensionAtlas.isOpen
  let A1 : Fin n → Fin n → W^{1,∞}(Omega) := fun i j ↦
    lowerOrderCLM (n := n) (k := 1) (m := k + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  have haRep1 : ∀ i j, ⇑((A1 i j : WkpAmbientOn n 1 ∞ Omega) (baseIndex n 1) :
      DerivLp n ∞ Omega) =ᵐ[domainMeasure n Omega] fun x ↦ a x i j :=
    fun i j ↦ by simpa [A1] using haRep i j
  let coeffOp := multiplicationCoefficientOperator (n := n) (Ω := Omega) (fun i j ↦
    ((A i j : WkpAmbientOn n (k + 1) ∞ Omega) (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
  have hL : IsCoercive (variableCoeffForm (n := n) (Ω := Omega) coeffOp) :=
    variableCoeffForm_isCoercive (Fact.out : 0 < n) hOmega.toC1ExtensionAtlas.bounded coeffOp
      (integratedElliptic_multiplication_of_ae _ (coefficientBase_aeUniformlyElliptic
        hOpen.measurableSet A1 a haRep1 alpha halpha hElliptic))
  refine exists_sobolevTimeJet_of_finiteWeakWaveChain (m := k + 1) ht hOpen _ hL
    (fun r f ↦ ?_) forcing u velocity acceleration q0 p0 hWave hvelocityLink haccelerationLink
    huTop hvelocityTop
  let Ar : Fin n → Fin n → W^{(r.1 + 1),∞}(Omega) := fun i j ↦
    lowerOrderCLM (n := n) (k := r.1 + 1) (m := k + 1) (p := ∞) (Ω := Omega) (by omega) (A i j)
  obtain ⟨representative, hbase⟩ := globalHigherRegularity_hasHigherSolutionLift r.1 hOmega
    (fun i ↦ (hChart i).of_le (by gcongr; omega))
    (fun i ↦ (hChartSymm i).of_le (by gcongr; omega)) Ar a
    (fun i j ↦ by simpa [Ar] using haRep i j)
    (fun i j ↦ (haContDiff i j).of_le (by gcongr; omega)) alpha halpha hElliptic f
  have hrestrict : (fun i j ↦ lowerOrderCLM (n := n) (k := 1) (m := r.1 + 1) (p := ∞)
      (Ω := Omega) (by omega) (Ar i j)) = A1 := funext₂ fun i j ↦
    lowerOrderCLM_trans_apply (n := n) (r := 1) (k := r.1 + 1) (m := k + 1) (p := ∞)
      (Ω := Omega) (by omega) (by omega) (A i j)
  have hSolver : coerciveDirichletSolutionOperator _ hL =
      globalH2WeakSolveCLM hOmega A1 a haRep1 alpha halpha hElliptic := rfl
  exact ⟨representative, by simpa only [hrestrict, hSolver] using hbase⟩

end Hyperbolic.DivergenceFormWave
