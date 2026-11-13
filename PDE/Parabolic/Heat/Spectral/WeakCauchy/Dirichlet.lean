/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Spectral.WeakCauchy.EnergyClass
public import PDE.Parabolic.Heat.Spectral.DirichletInitial

/-!
# Weak Cauchy characterization of the classical domain heat series

The classical spectral heat trajectory of `Spectral.DirichletInitial` has the natural energy
regularity for arbitrary L² initial data. It agrees at every closed time with
any continuous L² competitor satisfying the variational heat equation and
having an L²(H⁻¹) distributional time derivative.

Boundary smoothness here is used to refer to the classical representative.
The underlying Hilbert-series identification and energy-class construction
in the imported modules only require the weak Dirichlet spectral basis.
-/

@[expose] public noncomputable section

namespace HeatEquation.DirichletHeatSpectrum

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution MeasureTheory HolderSpace Set
open scoped Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {γ : Exponent}
  (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
  (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω) (hγ : (γ : ℝ) < 1)
  (S : DirichletHeatSpectrum n Ω)

/-- The constructed classical L² trajectory represents an L²(H¹₀) state with an
L²(H⁻¹) weak time derivative and the variational heat equation. -/
theorem exists_energyClass_dirichletHeatL2 {T : ℝ} (hT : 0 < T)
    (f : DerivLp n 2 Ω) :
    ∃ u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc 0 T)),
      ∃ g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc 0 T)),
        HasGelfandWeakTimeDerivativeOn (h10L2GelfandTriple hopen) u g ∧
        (∀ᵐ t ∂volume.restrict (Ioc 0 T), g t + dirichletForm (u t) = 0) ∧
        S.dirichletHeatL2 hopen hbounded hgraph hγ f =ᵐ[volume.restrict (Ioc 0 T)]
          fun t ↦ baseCoordCLM (u t) := by
  obtain ⟨u, ⟨_, g, E, hg, heq, hE⟩, _⟩ :=
    S.existsUnique_weakSolution_spectralHeatEvolution hopen hbounded hT f
  refine ⟨u, g, hg, heq, ?_⟩
  have hEa : E.representative =ᵐ[volume.restrict (Ioc 0 T)]
      fun t ↦ baseCoordCLM (u t) := by
    have h := E.ae_eq_inclusion
    rw [uIcc_of_le hT.le] at h
    exact h.filter_mono (ae_mono (volume.restrict_mono_set Ioc_subset_Icc_self))
  filter_upwards [hEa, ae_restrict_mem measurableSet_Ioc] with t ht htime
  rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ]
  have hEt := hE (Ioc_subset_Icc_self htime)
  simp only [sub_zero] at hEt
  exact hEt.symm.trans ht

/-- The closed-time classical heat series is unique against the natural energy
competitor class. Only a distributional H⁻¹ time derivative is assumed, and each
spatial variational test may have its own exceptional time null set. -/
theorem eq_dirichletHeatL2_of_weak_equation {T : ℝ} (hT : 0 < T)
    {u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc 0 T))}
    {g : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc 0 T))}
    (hg : HasWeakTimeDerivativeOn (Ioo 0 T)
      (fun t ↦ (h10L2GelfandTriple hopen).energyToDual (u t)) g)
    {w : ℝ → DerivLp n 2 Ω} (hw : ContinuousOn w (Icc 0 T))
    (hwae : w =ᵐ[volume.restrict (Ioc 0 T)] fun t ↦ baseCoordCLM (u t))
    (heq : ∀ v : H¹₀(Ω), ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      g t v + dirichletForm (u t) v = 0)
    {f : DerivLp n 2 Ω} (hinit : w 0 = f) :
    EqOn w (S.dirichletHeatL2 hopen hbounded hgraph hγ f) (Icc 0 T) := by
  have h := S.eq_spectralHeatEvolution_of_weak_equation hopen hT hg hw hwae heq hinit
  intro t ht
  rw [S.dirichletHeatL2_eq_spectralHeatEvolution hopen hbounded hgraph hγ]
  simpa only [sub_zero] using h ht

end HeatEquation.DirichletHeatSpectrum
