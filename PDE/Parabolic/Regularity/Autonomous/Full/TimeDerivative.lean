/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.AutonomousPrimitive
public import PDE.Analysis.Evolution.LionsMagenes.TimeSobolevNorm
public import PDE.Parabolic.Regularity.Autonomous.Full.Existence

/-!
# Differentiating an autonomous equation with lower-order terms

The differentiated equation starts from `f(a) - Lg` in the pivot space.
Its energy-valued primitive solves the original equation. Uniqueness then
identifies the primitive with any given weak solution. The initial
velocity needs no boundary compatibility in the energy space.
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Differentiating the forcing constructs a full weak solution for the time derivative.
The primitive is identified with every original weak solution by uniqueness. Its initial
value need only belong to the pivot space, and the bound is fixed before all solution data. -/
theorem exists_full_form_differentiated_solution_of_representative_with_bound
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ v, C * ‖v‖ ^ 2 ≤ A v v) :
    let T := h10L2GelfandTriple hopen
    let B := A + T.pivotToDual.comp R
    let μ := volume.restrict (Ioc a b)
    ∃ K : ℝ, 0 < K ∧
      ∀ (f df : Lp (DerivLp n 2 Ω) 2 μ)
        (g : H¹₀(Ω)) (v₀ : DerivLp n 2 Ω)
        (fRep : ℝ → DerivLp n 2 Ω) (u : Lp (H¹₀(Ω)) 2 μ),
      AbsolutelyContinuousOnInterval fRep a b →
      (fRep =ᵐ[μ] fun t ↦ f t) →
      (∀ᵐ t ∂μ, HasDerivAt fRep (df t) t) →
      T.pivotToDual v₀ = T.pivotToDual (fRep a) - B g →
      IsGelfandIntegratedWeakSolution T (fun _ ↦ B)
        (T.pivotToDual.compLpL 2 μ f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ V : GardingWeakSolutionOn T (fun _ ↦ B)
          (T.pivotToDual.compLpL 2 μ df) v₀ a b (C / 2) (‖R‖ ^ 2 / (2 * C)),
        HasGelfandWeakTimeDerivativeOn T u (T.energyToDual.compLpL 2 μ V.state) ∧
        ∀ t ∈ Icc a b,
          ‖V.evolution.representative t‖ + ‖V.state‖ + ‖V.derivative‖ ≤
            K * (‖v₀‖ + ‖df‖) := by
  dsimp only
  let T := h10L2GelfandTriple hopen
  let B := A + T.pivotToDual.comp R
  let μ := volume.restrict (Ioc a b)
  have hbasic :=
    @exists_full_form_solution_with_bound n Ω hopen hbounded A R C a b hC hab hcoercive
  obtain ⟨K, hK, hexists⟩ := hbasic
  refine ⟨K, hK, ?_⟩
  intro f df g v₀ fRep u hfAC hfRep hfDeriv hcompat hu
  have hvelocity := hexists df v₀
  obtain ⟨V, hV⟩ := hvelocity
  have hinit : T.pivotToDual (V.evolution.representative a) =
      T.pivotToDual (fRep a) - B g :=
    (congrArg T.pivotToDual V.properties.initial).trans hcompat
  have hresidual : ∀ᵐ t ∂μ,
      V.derivative t = T.pivotToDual (df t) - B (V.state t) := by
    filter_upwards [V.properties.residual, T.pivotToDual.coeFn_compLpL df] with t ht hft
    exact ht.trans (congrArg
      (fun z : StrongDual ℝ (H¹₀(Ω)) ↦ z - B (V.state t)) hft)
  have horiginal := hexists f (baseCoordCLM (n := n) (Ω := Ω) g)
  obtain ⟨U, _⟩ := horiginal
  have huU := U.properties.unique u hu
  refine ⟨V, ?_, hV⟩
  exact V.evolution.has_weak_derivative_of_unique_solution hab B f df g
    hfAC hfRep hfDeriv hinit hresidual u
    (fun w hw ↦ (U.properties.unique w hw).trans huU.symm)

/-- A pivot-valued initial elliptic load and `H¹` forcing give an
energy-valued time derivative, with its own dual derivative and continuous
pivot representative. The constant is independent of all solution data. -/
theorem exists_full_form_time_derivative
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (A : H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (R : H¹₀(Ω) →L[ℝ] DerivLp n 2 Ω)
    {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hcoercive : ∀ v, C * ‖v‖ ^ 2 ≤ A v v) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (f df : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (g : H¹₀(Ω)) (load : DerivLp n 2 Ω)
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))),
      HasGelfandWeakTimeDerivativeOn (GelfandTriple.identity (DerivLp n 2 Ω)) f
        ((GelfandTriple.identity (DerivLp n 2 Ω)).energyToDual.compLpL
          2 (volume.restrict (Ioc a b)) df) →
      (h10L2GelfandTriple hopen).pivotToDual load =
        (A + (h10L2GelfandTriple hopen).pivotToDual.comp R) g →
      IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
        (fun _ ↦ A + (h10L2GelfandTriple hopen).pivotToDual.comp R)
        ((h10L2GelfandTriple hopen).pivotToDual.compLpL
          2 (volume.restrict (Ioc a b)) f) u (baseCoordCLM (n := n) (Ω := Ω) g) →
      ∃ (v : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (dv : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
        (E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen)
          (fun t ↦ v t) (fun t ↦ dv t) a b),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u
          ((h10L2GelfandTriple hopen).energyToDual.compLpL
            2 (volume.restrict (Ioc a b)) v) ∧
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) v dv ∧
        ∀ t ∈ Icc a b, ‖E.representative t‖ + ‖v‖ + ‖dv‖ ≤
          K * (‖load‖ + ‖f‖ + ‖df‖) := by
  let T := h10L2GelfandTriple hopen
  let B := A + T.pivotToDual.comp R
  have hbasic :=
    @exists_full_form_differentiated_solution_of_representative_with_bound n Ω
      hopen hbounded A R C a b hC hab hcoercive
  dsimp only at hbasic
  obtain ⟨K₀, hK₀, hexists⟩ := hbasic
  let F := Real.sqrt (1 / (b - a) + 2)
  let K := K₀ * (F + 2)
  have hF : 0 ≤ F := Real.sqrt_nonneg _
  have hK : 0 < K := mul_pos hK₀ (by positivity)
  refine ⟨K, hK, ?_⟩
  intro f df g load u hf hload hu
  let : MeasurableSpace (DerivLp n 2 Ω) := borel (DerivLp n 2 Ω)
  let : BorelSpace (DerivLp n 2 Ω) := ⟨rfl⟩
  let : MeasurableSpace (StrongDual ℝ (DerivLp n 2 Ω)) :=
    borel (StrongDual ℝ (DerivLp n 2 Ω))
  let : BorelSpace (StrongDual ℝ (DerivLp n 2 Ω)) := ⟨rfl⟩
  have htrace := hf.exists_absolutelyContinuousRepresentative_norm_le_of_identity hab
  obtain ⟨fRep, hfAC, hfRep, hfDeriv, hfPoint, _⟩ := htrace
  let velocity := fRep a - load
  have hinit : T.pivotToDual velocity =
      T.pivotToDual (fRep a) - B g := by
    change T.pivotToDual (fRep a - load) = _
    rw [map_sub, hload]
  have hvelocity := hexists f df g velocity fRep u hfAC hfRep hfDeriv hinit hu
  obtain ⟨V, huDeriv, hV⟩ := hvelocity
  refine ⟨V.state, V.derivative, V.evolution, ?_, ?_, ?_⟩
  · exact huDeriv
  · exact V.properties.weakDerivative
  · intro t ht
    have hfNorm : ‖fRep a‖ ≤ F * (‖f‖ + ‖df‖) :=
      (hfPoint a ⟨le_rfl, hab.le⟩).trans (timeSobolevBound_le_sum_norm hab f df)
    have hvNorm : ‖velocity‖ ≤ F * (‖f‖ + ‖df‖) + ‖load‖ :=
      (norm_sub_le _ _).trans (by linarith only [hfNorm])
    have hdata : ‖velocity‖ + ‖df‖ ≤ (F + 2) * (‖load‖ + ‖f‖ + ‖df‖) := by
      nlinarith only [hvNorm, hF, norm_nonneg load, norm_nonneg f, norm_nonneg df]
    exact (hV t ht).trans ((mul_le_mul_of_nonneg_left hdata hK₀.le).trans_eq (by
      dsimp only [K]
      ring))

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity
