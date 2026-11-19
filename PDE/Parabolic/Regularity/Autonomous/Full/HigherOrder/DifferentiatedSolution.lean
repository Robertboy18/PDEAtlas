/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.TimeDerivative
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional

/-!
# The differentiated full parabolic problem

The primitive and uniqueness argument for improved regularity also gives
the weak equation and initial datum of the differentiated solution, which is
what the induction on the order needs. The given forcing trace is
identified with its absolutely continuous pivot representative by continuity;
the higher Sobolev trace theorem provides this trace in the applications.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Compatible initial data and a weak forcing derivative construct the
differentiated weak solution. It is the derivative of every original weak
solution and satisfies its own weak equation and initial condition. -/
theorem exists_differentiated_full_form_solution
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ v, C * ‖v‖ ^ 2 ≤ A v v)
    (f df : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (g g₁ : H¹₀(Ω))
    (hf : HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ f t) (fun t ↦ df t))
    (fTrace : ℝ → DerivLp n 2 Ω)
    (hfCont : ContinuousOn fTrace (Icc a b))
    (hfTrace : fTrace =ᵐ[volume.restrict (Ioc a b)] fun t ↦ f t)
    (hcompat : (h10L2GelfandTriple hopen).pivotToDual (baseCoordCLM (n := n) (Ω := Ω) g₁) =
      (h10L2GelfandTriple hopen).pivotToDual (fTrace a) -
        (A + (h10L2GelfandTriple hopen).pivotToDual.comp R) g)
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (hu : IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
      (fun _ ↦ A + (h10L2GelfandTriple hopen).pivotToDual.comp R)
      ((h10L2GelfandTriple hopen).pivotToDual.compLpL
        2 (volume.restrict (Ioc a b)) f) u (baseCoordCLM (n := n) (Ω := Ω) g)) :
    ∃ v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
        ((h10L2GelfandTriple hopen).energyToDual.compLpL
          2 (volume.restrict (Ioc a b)) v) ∧
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ A + (h10L2GelfandTriple hopen).pivotToDual.comp R)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) df) v (baseCoordCLM (n := n) (Ω := Ω) g₁) := by
  have htrace :=
    hf.exists_absolutelyContinuousRepresentative_eq_initial hab fTrace hfCont hfTrace
  obtain ⟨fRep, hfAC, hfRep, hfDeriv, hrepInitial⟩ := htrace
  have hbasic :=
    @exists_full_form_differentiated_solution_of_representative_with_bound n Ω
      hopen hbounded A R C a b hC hab hcoercive
  dsimp only at hbasic
  obtain ⟨_, _, hexists⟩ := hbasic
  have hinit : (h10L2GelfandTriple hopen).pivotToDual
      (baseCoordCLM (n := n) (Ω := Ω) g₁) =
      (h10L2GelfandTriple hopen).pivotToDual (fRep a) -
        (A + (h10L2GelfandTriple hopen).pivotToDual.comp R) g :=
    hcompat.trans (congrArg
      (fun z : DerivLp n 2 Ω ↦ (h10L2GelfandTriple hopen).pivotToDual z -
        (A + (h10L2GelfandTriple hopen).pivotToDual.comp R) g) hrepInitial.symm)
  have hvelocity :=
    hexists f df g (baseCoordCLM (n := n) (Ω := Ω) g₁) fRep u
      hfAC hfRep.symm hfDeriv hinit hu
  obtain ⟨V, huDeriv, _⟩ := hvelocity
  exact ⟨V.state, huDeriv, V.properties.solution⟩

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
