/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Compatibility.Conditions
public import PDE.Hyperbolic.HigherRegularity.Data.Forcing

/-!
# Initial data for Evans's differentiated wave chain

Differentiating the wave equation `u_tt + Lu = f` `k` times in time gives a
wave equation for `∂ₜᵏ u` with initial displacement `∂ₜᵏ u(0)` and initial
velocity `∂ₜᵏ⁺¹ u(0)`.  These values are not free: the equation forces
`∂ₜᵏ⁺¹ u(0) = ∂ₜᵏ⁻¹ f(0) - L ∂ₜᵏ⁻¹ u(0)`, and Evans's `m`-th order
compatibility conditions (Evans, §7.2.3, Theorem 6) ask that the
recursively defined values `g_k, h_k` have the Sobolev regularity and zero
boundary trace needed to start each differentiated problem.

We turn a `WaveProblemData.IsCompatible` certificate into the ambient
`H¹₀ × L²` initial data required at every level of the finite chain.  The
value `f(0)` entering the recurrence is the canonical Lions-Magenes trace,
supplied through the Dirichlet-load forcing representatives of
`Data.Forcing`.

## Main results

* `WaveProblemData.IsCompatible.exists_ambientInitialDataFamily`: from a
  compatible problem and a coherent forcing chain, produce
  `q : Fin (m + 1) → H¹₀` and `p : Fin (m + 1) → L²` such that the top level
  `Fin.last m` is the given displacement and velocity, the displacement of
  each further differentiated problem is the velocity of the previous one, and
  its velocity is the initial weak residual `f_r(t0) - A q_r` of the previous
  equation, read in the pivot `L²` through the Gelfand triple.

## Implementation notes

The chain is indexed in reverse, with `Fin.last m` the original problem, to
match `SobolevTimeJet.iteratedTimeDerivative`.  The proof is an induction on
`m` that peels the head off the compatibility family and applies
`WaveProblemData.IsCompatible.timeDerivative` to the tail; the head identity
`A g = L_m g` in the dual is what identifies the weak residual with the
compatibility value.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, compatibility conditions (62), and step 2
  of its proof, equation (69).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory

namespace Hyperbolic.HigherRegularity

open PDE.Analysis.Evolution
open SobolevSpace
open SobolevSpace.GraphSpace

variable {n m : ℕ} {Omega : Set (ℝ^n)} {t0 t1 : ℝ}

private theorem WaveCompatibilityValues.head_hasDirichletTraceZero
    (Q : WaveCompatibilityValues n Omega m) :
    HasDirichletTraceZero
      (n := n) (Omega := Omega)
      (by omega : 1 ≤ m + 1) Q.head := by
  cases Q with
  | zero _ hzero =>
      exact hzero
  | succ _ hzero _ =>
      exact hzero

private theorem WaveCompatibilityValues.Realizes.head_eq {F : SobolevTimeJet n m Omega t0 t1}
    {Q : WaveCompatibilityValues n Omega m} {A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega))}
    {spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)}
    {forcingTraces : InitialTraceData (F := F)} {g : W^{(m + 1),2}(Omega)} {h : W^{m,2}(Omega)}
    (hQ : Q.Realizes A spatialOperator forcingTraces g h) :
    Q.head = g := by
  cases Q with
  | zero =>
      cases forcingTraces with
      | zero =>
          exact hQ
  | succ =>
      cases forcingTraces with
      | succ =>
          exact hQ.1

private theorem WaveCompatibilityValues.Realizes.head_operator_eq
    {F : SobolevTimeJet n (m + 1) Omega t0 t1}
    {Q : WaveCompatibilityValues n Omega (m + 1)}
    {A :
      H¹₀(Omega) →L[ℝ]
        StrongDual ℝ (H¹₀(Omega))}
    {spatialOperator :
      ∀ r : ℕ,
        W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega)}
    {forcingTraces : InitialTraceData (F := F)}
    {g : W^{(m + 2),2}(Omega)}
    {h : W^{(m + 1),2}(Omega)}
    (hQ : Q.Realizes A spatialOperator forcingTraces g h) :
    A
        (⟨lowerOrderCLM
            (n := n) (p := 2) (Ω := Omega)
            (by omega : 1 ≤ m + 2) Q.head,
          Q.head_hasDirichletTraceZero⟩ :
          H¹₀(Omega)) =
      loadFunctional (n := n) (Ω := Omega)
        (wkpBaseCoordinateCLM
          (n := n) (m := m) (p := 2) (Ω := Omega)
          (spatialOperator m Q.head)) := by
  cases Q with
  | succ =>
      cases forcingTraces with
      | succ =>
          simpa only [WaveCompatibilityValues.head] using hQ.2.1

/--
Evans compatibility supplies the ambient initial position and velocity at
every level of the finite time-differentiated wave chain.

The reverse index `Fin.last m` is the original equation.  At each adjacent
pair, the differentiated position is the preceding velocity and the
differentiated velocity is the initial weak residual of the preceding
equation.
-/
theorem WaveProblemData.IsCompatible.exists_ambientInitialDataFamily
    (D : WaveProblemData n m Omega t0 t1) (hOmegaOpen : IsOpen Omega)
    (A : H¹₀(Omega) →L[ℝ] StrongDual ℝ (H¹₀(Omega)))
    (spatialOperator : ∀ r : ℕ, W^{(r + 2),2}(Omega) →L[ℝ] W^{r,2}(Omega))
    (hD : D.IsCompatible A spatialOperator)
    (forcing : Fin (m + 1) → ℝ → StrongDual ℝ (H¹₀(Omega)))
    (hforcingRepresents :
      ∀ r : Fin (m + 1),
        (dirichletLoadTimeLp hOmegaOpen (D.forcing.iteratedTimeDerivative r).head :
            ℝ → StrongDual ℝ (H¹₀(Omega)))
          =ᵐ[volume.restrict (Set.Ioc t0 t1)] forcing r)
    (hforcingAdjacent :
      ∀ r : Fin m,
        AbsolutelyContinuousOnInterval (forcing r.succ) t0 t1 ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioc t0 t1),
          HasDerivAt (forcing r.succ) (forcing r.castSucc t) t) :
    ∃ (q : Fin (m + 1) → H¹₀(Omega)) (p : Fin (m + 1) → DerivLp n 2 Omega),
      h10SubtypeL (n := n) (Ω := Omega) (q (Fin.last m)) =
        lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega : 1 ≤ m + 1) D.displacement ∧
      p (Fin.last m) = wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega) D.velocity ∧
      (∀ r : Fin m,
        p r.succ = (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).inclusion
          (q r.castSucc)) ∧
      ∀ r : Fin m,
        forcing r.succ t0 - A (q r.succ) =
          (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).pivotToDual
            (p r.castSucc) := by
  obtain ⟨Q, hQ⟩ := hD
  induction m with
  | zero =>
    exact ⟨fun _ ↦ ⟨lowerOrderCLM (n := n) (p := 2) (Ω := Omega) le_rfl Q.head,
        Q.head_hasDirichletTraceZero⟩,
      fun _ ↦ wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2) (Ω := Omega) D.velocity,
      congrArg (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) le_rfl) hQ.head_eq, rfl,
      fun r ↦ r.elim0, fun r ↦ r.elim0⟩
  | succ m ih =>
    let qOriginal : H¹₀(Omega) :=
      ⟨lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega : 1 ≤ m + 2) Q.head,
        Q.head_hasDirichletTraceZero⟩
    have hoperator : A qOriginal = loadFunctional (n := n) (Ω := Omega)
        (wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Omega)
          (spatialOperator m Q.head)) := hQ.head_operator_eq
    let q2 : W^{m,2}(Omega) := D.forcingTraces.head - spatialOperator m D.displacement
    obtain ⟨Q', hQ'⟩ := WaveProblemData.IsCompatible.timeDerivative ⟨Q, hQ⟩ q2 rfl
    obtain ⟨qTail, pTail, hqTailLast, hpTailLast, hTailAdjacent, hTailCompatibility⟩ :=
      ih (D := D.timeDerivative q2) (forcing := fun r ↦ forcing r.castSucc)
        (hforcingRepresents := fun r ↦ by
          simpa only [WaveProblemData.timeDerivative_forcing,
            SobolevTimeJet.iteratedTimeDerivative_castSucc] using hforcingRepresents r.castSucc)
        (hforcingAdjacent := fun r ↦ by
          simpa only [Fin.succ_castSucc] using hforcingAdjacent r.castSucc) Q' hQ'
    have hinclusionTailLast :
        (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).inclusion (qTail (Fin.last m)) =
          wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega) D.velocity :=
      congrArg (wkpBaseCoordinateCLM (n := n) (m := 1) (p := 2) (Ω := Omega)) hqTailLast
    have hforcingInitial := D.forcing.initialValue_eq_dirichletLoadTrace D.forcingTraces
      hOmegaOpen D.time_lt (forcing (Fin.last (m + 1)))
      (by simpa only [Fin.succ_last] using (hforcingAdjacent (Fin.last m)).1)
      (by simpa only [SobolevTimeJet.iteratedTimeDerivative_last] using
        hforcingRepresents (Fin.last (m + 1)))
    have hOriginalCompatibility : forcing (Fin.last (m + 1)) t0 - A qOriginal =
          (SobolevSpace.GraphSpace.h10L2GelfandTriple hOmegaOpen).pivotToDual
            (pTail (Fin.last m)) := by
      rw [hforcingInitial, hoperator, ← loadFunctional_sub, ← map_sub, hQ.head_eq, hpTailLast]
      rfl
    refine ⟨Fin.lastCases qOriginal qTail, Fin.lastCases
      (wkpBaseCoordinateCLM (n := n) (m := m + 1) (p := 2) (Ω := Omega) D.velocity) pTail, ?_,
      by simp only [Fin.lastCases_last], fun r ↦ ?_, fun r ↦ ?_⟩
    · simp only [Fin.lastCases_last]
      exact congrArg (lowerOrderCLM (n := n) (p := 2) (Ω := Omega) _) hQ.head_eq
    · refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simpa only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using
          hinclusionTailLast.symm
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hTailAdjacent s
    · refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simpa only [Fin.succ_last, Fin.lastCases_last, Fin.lastCases_castSucc] using
          hOriginalCompatibility
      · simpa only [Fin.succ_castSucc, Fin.lastCases_castSucc] using hTailCompatibility s

end Hyperbolic.HigherRegularity
