/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.WeakCauchy.Identification
public import PDE.Parabolic.Heat.Variational.Dirichlet
import PDE.Analysis.Evolution.Integrated.Regularity

/-!
# The spectral heat orbit belongs to the natural energy class

The variational existence theorem of `Heat.Variational.Dirichlet` constructs an L²(H¹₀)
solution for
every L² initial datum. Lions–Magenes derives its L²(H⁻¹) derivative, closed-time
representative, and energy identity. The eigenfunction coefficient argument
identifies that representative with the independently constructed heat series.

Thus energy-class membership of the spectral orbit is a conclusion. Uniqueness
comes from the weak parabolic uniqueness theorem, without a second solution
predicate or an assumed strong pivot derivative.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution MeasureTheory Set
open scoped Sobolev

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} (S : DirichletHeatSpectrum n Ω)

/-- The continuous representative derived from an integrated variational heat
solution is the spectral orbit, with its natural dual derivative and energy law. -/
theorem exists_spectral_representative_of_weakSolution (hopen : IsOpen Ω)
    {a b : ℝ} (hab : a < b)
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b))} {f : DerivLp n 2 Ω}
    (hu : Variational.Dirichlet.IsWeakSolution hopen 0 u f) :
    ∃ g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)),
      ∃ E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen)
          (fun t ↦ u t) (fun t ↦ g t) a b,
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u g ∧
        (∀ᵐ t ∂volume.restrict (Ioc a b), g t + dirichletForm (u t) = 0) ∧
        EqOn E.representative
          (fun t ↦ spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
            f (t - a).toNNReal) (Icc a b) := by
  let h10Inner : InnerProductSpace ℝ (H¹₀(Ω)) := inferInstance
  let h10Complete : CompleteSpace (H¹₀(Ω)) := inferInstance
  change IsGelfandIntegratedWeakSolution (h10L2GelfandTriple hopen)
    (Variational.Dirichlet.form (n := n) (Ω := Ω))
    (fun t ↦ (0 : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))) t)
    u f at hu
  have hmeas : ∀ v : H¹₀(Ω), AEStronglyMeasurable
      (fun t : ℝ ↦ Variational.Dirichlet.form t v) (volume.restrict (Ioc a b)) :=
    fun _ ↦ aestronglyMeasurable_const
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖Variational.Dirichlet.form (n := n) (Ω := Ω) t‖ ≤
        ‖dirichletForm (n := n) (Ω := Ω)‖ := .of_forall (fun _ ↦ le_rfl)
  obtain ⟨g, E, hg, hinit, hres⟩ :=
    @IsGelfandIntegratedWeakSolution.exists_continuousPivotEvolutionOn_initial_L2
      (H¹₀(Ω)) (DerivLp n 2 Ω)
      inferInstance h10Inner h10Complete inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance
      a b (h10L2GelfandTriple hopen) (Variational.Dirichlet.form (n := n) (Ω := Ω)) 0 u f
      hmeas ‖dirichletForm (n := n) (Ω := Ω)‖ hbound hu hab
  have heq : ∀ᵐ t ∂volume.restrict (Ioc a b), g t + dirichletForm (u t) = 0 := by
    filter_upwards [hres, Lp.coeFn_zero (StrongDual ℝ (H¹₀(Ω))) 2
      (volume.restrict (Ioc a b))] with t ht hzero
    rw [ht, hzero]
    change 0 - dirichletForm (u t) + dirichletForm (u t) = 0
    abel
  refine ⟨g, E, hg, heq, ?_⟩
  intro t ht
  rw [S.representative_eq_spectralHeatEvolution hopen hab.le E ?_ ht, hinit]
  intro v
  filter_upwards [heq] with s hs
  exact congrArg (fun L : StrongDual ℝ (H¹₀(Ω)) ↦ L v) hs

/-- Every L² datum gives a unique variational weak solution whose Lions–Magenes
representative is the spectral heat series at all closed times. The state and
weak derivative have the natural L²(H¹₀) and L²(H⁻¹) regularity. The bundled
evolution includes the derived integrated derivative and exact energy identity. -/
theorem existsUnique_weakSolution_spectralHeatEvolution (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b)
    (f : DerivLp n 2 Ω) :
    ∃! u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)),
      Variational.Dirichlet.IsWeakSolution hopen 0 u f ∧
        ∃ g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)),
          ∃ E : ContinuousPivotEvolutionOn (h10L2GelfandTriple hopen)
              (fun t ↦ u t) (fun t ↦ g t) a b,
            HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u g ∧
            (∀ᵐ t ∂volume.restrict (Ioc a b), g t + dirichletForm (u t) = 0) ∧
            EqOn E.representative
              (fun t ↦ spectralHeatEvolution S.basis S.eigenvalue S.eigenvalue_nonneg
                f (t - a).toNNReal) (Icc a b) := by
  obtain ⟨u, hu, hunique⟩ :=
    Variational.Dirichlet.existsUnique_weakSolution hopen hbounded hab 0 f
  exact ⟨u, ⟨hu, S.exists_spectral_representative_of_weakSolution hopen hab hu⟩,
    fun v hv ↦ hunique v hv.1⟩

end HeatEquation.DirichletHeatSpectrum
