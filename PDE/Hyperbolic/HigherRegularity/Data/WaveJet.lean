/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Data.Forcing

/-!
# Identifying the acceleration in a wave jet

At order zero the energy solution has its acceleration in the energy dual.
At positive order the second member of the Sobolev time jet represents
that same acceleration. This predicate states the identification uniformly
over the order, without demanding an `L²` acceleration in the energy case.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set

namespace Hyperbolic.HigherRegularity.SobolevTimeJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- At positive order, the second weak derivative of the jet is exactly the
original wave acceleration after the canonical dual embedding. -/
def RepresentsAcceleration (hopen : IsOpen Ω) :
    {m : ℕ} → SobolevTimeJet n (m + 1) Ω a b →
      Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)) → Prop
  | 0, _, _ => True
  | _ + 1, U, w => dirichletLoadTimeLp hopen U.timeDerivative.timeDerivative.head = w

/-- Adjacent reverse indices select successive derivatives of one jet. -/
theorem iteratedTimeDerivative_succ_timeDerivative
    {m : ℕ} (U : SobolevTimeJet n m Ω a b) (r : Fin m) :
    (U.iteratedTimeDerivative r.succ).timeDerivative = U.iteratedTimeDerivative r.castSucc := by
  induction m with
  | zero => exact Fin.elim0 r
  | succ m ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simp only [Fin.succ_last, iteratedTimeDerivative_last, iteratedTimeDerivative_castSucc]
      · simpa only [Fin.succ_castSucc, iteratedTimeDerivative_castSucc] using ih U.timeDerivative s

/-- Every adjacent pair is an ordinary weak time derivative after
the one required spatial restriction. -/
theorem hasWeakTimeDerivative_iterated {m : ℕ} (U : SobolevTimeJet n m Ω a b) (r : Fin m) :
    HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ lowerOrderCLM (Nat.le_succ r.1)
      ((U.iteratedTimeDerivative r.succ).head t)) (U.iteratedTimeDerivative r.castSucc).head := by
  have h := (U.iteratedTimeDerivative r.succ).hasWeakTimeDerivative_timeDerivative
  simpa only [iteratedTimeDerivative_succ_timeDerivative] using h

/-- Essential boundedness is inherited by every derivative level. -/
theorem IsEssentiallyBounded.iteratedTimeDerivative {m : ℕ} {U : SobolevTimeJet n m Ω a b}
    (hU : U.IsEssentiallyBounded) (r : Fin (m + 1)) :
    (U.iteratedTimeDerivative r).IsEssentiallyBounded := by
  induction m with
  | zero =>
      refine Fin.lastCases ?_ (fun s ↦ Fin.elim0 s) r
      simpa only [iteratedTimeDerivative_last] using hU
  | succ m ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · simpa only [iteratedTimeDerivative_last] using hU
      · simpa only [SobolevTimeJet.iteratedTimeDerivative_castSucc] using ih hU.timeDerivative s

/-- Every level has the stated regularity on the closed time interval. -/
theorem IsEssentiallyBounded.memLp_iterated_Icc {m : ℕ} {U : SobolevTimeJet n m Ω a b}
    (hU : U.IsEssentiallyBounded) (r : Fin (m + 1)) :
    MemLp (fun t ↦ (U.iteratedTimeDerivative r).head t) ⊤ (volume.restrict (Icc a b)) := by
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  exact (hU.iteratedTimeDerivative r).head

end Hyperbolic.HigherRegularity.SobolevTimeJet
