/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import PDE.Hyperbolic.Variational.GelfandGalerkin.AutonomousDifferentiation
import PDE.Hyperbolic.Variational.GelfandGalerkin.Basic
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.Galerkin
import PDE.Hyperbolic.Variational.GelfandGalerkin.FiniteTimeDerivative.InitialData

/-!
# Finite differentiated Galerkin approximations

For a sequence of finite-dimensional trial spaces, Evans compatibility and
Ritz orthogonality determine every initial value in the recursively
differentiated Galerkin family.  The construction keeps the exact
finite-dimensional time-derivative identities before any compactness
argument is applied.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, compatibility conditions (62).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Hyperbolic.Variational.GelfandGalerkin

open PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/--
Construct Evans's finite differentiated Galerkin approximations
simultaneously along a sequence of trial spaces.

At every trial index, the original trajectory starts from the energy and
pivot projections of the ambient compatibility data.  Recursive
differentiation supplies all lower reverse-index levels.  Ritz
orthogonality then identifies every recursively generated initial position
and velocity with the corresponding ambient projection.
-/
theorem exists_finiteTimeDerivativeApproximation (T : GelfandTriple (V := V) (H := H))
    (Sseq : ℕ → Submodule ℝ V) [∀ n, FiniteDimensional ℝ (Sseq n)]
    {K : NNReal} (P : ∀ n, StableTrialProjection T (Sseq n) K) (B : V →L[ℝ] StrongDual ℝ V) {m : ℕ}
    (forcing : Fin (m + 1) → ℝ → StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (hforcingIntegrable : IntegrableOn (forcing (Fin.last m)) (Set.Icc a b) volume) (MB : NNReal)
    (hB_bound : ∀ t ∈ Set.Icc a b, ‖B‖ ≤ MB)
    (hforcingAC : ∀ r : Fin m, AbsolutelyContinuousOnInterval (forcing r.succ) a b)
    (hforcingDeriv : ∀ r : Fin m, ∀ᵐ t ∂volume.restrict (Set.Ioc a b),
      HasDerivAt (forcing r.succ) (forcing r.castSucc t) t)
    (q : Fin (m + 1) → V) (p : Fin (m + 1) → H)
    (hadjacent : ∀ r : Fin m, p r.succ = T.inclusion (q r.castSucc))
    (hcompatibility : ∀ r : Fin m, forcing r.succ a - B (q r.succ) = T.pivotToDual (p r.castSucc))
    (hRitz : ∀ n, ∀ r : Fin m, ∀ w : Sseq n,
      B (q r.succ - ((P n).energyProjection (q r.succ) : V)) (w : V) = 0) :
    ∃ (Uoriginal : (n : ℕ) →
          SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T (Sseq n) B)
            (gelfandGalerkinForcing T (Sseq n) (forcing (Fin.last m))) a b
            ((P n).energyProjection (q (Fin.last m))) ((P n).projection (p (Fin.last m))))
        (q0 p0 : (n : ℕ) → Fin (m + 1) → Sseq n)
        (U : (n : ℕ) → (r : Fin (m + 1)) →
          SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T (Sseq n) B)
            (gelfandGalerkinForcing T (Sseq n) (forcing r)) a b (q0 n r) (p0 n r)),
      (∀ n, HEq (U n (Fin.last m)) (Uoriginal n)) ∧
      (∀ n, ∀ r : Fin (m + 1),
        q0 n r = (P n).energyProjection (q r) ∧ p0 n r = (P n).projection (p r)) ∧
      ∀ n, ∀ r : Fin m,
        q0 n r.castSucc = p0 n r.succ ∧
        p0 n r.castSucc = -(gelfandGalerkinOperator T (Sseq n) B) (q0 n r.succ) +
          gelfandGalerkinForcing T (Sseq n) (forcing r.succ) a ∧
        HEq (U n r.castSucc)
          (timeDerivative T (Sseq n) B (U n r.succ) (hforcingAC r) (hforcingDeriv r)) ∧
        (U n r.castSucc).displacement = (U n r.succ).velocity ∧
        (U n r.castSucc).velocity = fun t ↦
          -(gelfandGalerkinOperator T (Sseq n) B) ((U n r.succ).displacement t) +
            gelfandGalerkinForcing T (Sseq n) (forcing r.succ) t := by
  have hB : AEStronglyMeasurable (fun _ : ℝ ↦ B) (volume.restrict (Set.Icc a b)) := by fun_prop
  let Uoriginal (n : ℕ) : SecondOrderSolutionOn (fun _ ↦ gelfandGalerkinOperator T (Sseq n) B)
      (gelfandGalerkinForcing T (Sseq n) (forcing (Fin.last m))) a b
      ((P n).energyProjection (q (Fin.last m))) ((P n).projection (p (Fin.last m))) :=
    Classical.choice (GelfandGalerkin.exists T (Sseq n) (fun _ : ℝ ↦ B) (forcing (Fin.last m))
      hab hB hforcingIntegrable MB (fun t ht ↦ hB_bound t ht)
      ((P n).energyProjection (q (Fin.last m))) ((P n).projection (p (Fin.last m))))
  choose q0 p0 U hq0Last hp0Last hUoriginal hrecursive using fun n ↦
    exists_finiteTimeDerivativeFamily T (Sseq n) B forcing hforcingAC hforcingDeriv (Uoriginal n)
  exact ⟨Uoriginal, q0, p0, U, hUoriginal, fun n r ↦
    finiteTimeDerivativeFamily_initialData_eq_projections T (Sseq n) (P n) B forcing a q p
      (q0 n) (p0 n) (hq0Last n) (hp0Last n)
      (fun s ↦ ⟨(hrecursive n s).1, (hrecursive n s).2.1⟩) hadjacent hcompatibility (hRitz n) r,
    hrecursive⟩

end Hyperbolic.Variational.GelfandGalerkin
