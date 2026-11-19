/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.Coefficients
public import PDE.Examples.Hyperbolic.FirstOrder.Viscosity.Data
public import PDE.Parabolic.Systems.Transport.Solution.SpaceTime
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Viscous solutions for nonzero data and a variable coupled matrix

For the coupled matrix of `Coefficients` and the data of `Data`, the viscous
transport-diffusion problem with mollified initial data has a unique strong solution for
every viscosity `ε > 0` (`coupled_exists_unique`, from
`exists_unique_viscous_approximation`). The solutions for `0 < ε ≤ 1` satisfy one energy
bound (`coupled_uniform_bound`, from `exists_uniform_viscous_approximation_bound`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Viscosity

open MeasureTheory Set PDE.Common
open PDE.Hyperbolic.FirstOrder PDE.Parabolic.Systems PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal NNReal Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

/-- The inherited finite-component spatial L² scalar multiplication. -/
local instance coupledL2NormedSpace :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin 2 ↦ DerivLp 1 2 univ)) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin 2 ↦ DerivLp 1 2 univ)

/-- Every positive viscosity gives a unique coupled solution for
the prescribed nonzero initial profile and affine-time forcing. -/
theorem coupled_exists_unique {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ (U : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{3,2}(ℝ^1))) 2
        (volume.restrict (Ioc 0 T)))
      (G : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))) 2
        (volume.restrict (Ioc 0 T)))
      (z : ℝ → PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))),
      IsStrongTransportDiffusionSolution ε 0 T
        (fun j y p q ↦ coupledMatrix j (timeSpaceCons y.1 y.2) p q)
        (fun p y ↦ wkpBaseCoordinateCLM (forcingData hT p) (timeSpaceCons y.1 y.2))
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin 2 ↦ mollifierHkCLM (standardMollifier 1) hε) initialData) U G z ∧
      (∀ V H w, IsStrongTransportDiffusionSolution ε 0 T
        (fun j y p q ↦ coupledMatrix j (timeSpaceCons y.1 y.2) p q)
        (fun p y ↦ wkpBaseCoordinateCLM (forcingData hT p) (timeSpaceCons y.1 y.2))
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin 2 ↦ mollifierHkCLM (standardMollifier 1) hε) initialData) V H w →
        V = U ∧ H = G ∧ EqOn w z (Icc 0 T)) := by
  exact exists_unique_viscous_approximation hT coupledMatrix
    (fun j p q ↦ (coupledMatrix_contDiff j p q).contDiffOn)
    (fun j y _ ↦ coupledMatrix_isSymm j y) 4
    (fun j p q y _ ↦ coupledMatrix_norm_le j p q y)
    (coupledMatrix_norm_fderivWithin_le hT)
    (coupledMatrix_norm_iteratedFDerivWithin_le hT)
    hε initialData (forcingData hT)

/-- There is one constant `C` such that every strong solution with viscosity `0 < ε ≤ 1`
satisfies `max ‖z‖ + ‖G‖ ≤ C (‖initialData‖ + ‖F‖ + ‖Fₜ‖)`. -/
theorem coupled_uniform_bound {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
      ∃ (F : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))) 2
          (volume.restrict (Ioc 0 T)))
        (Ft : Lp (PiLp 2 (fun _ : Fin 2 ↦ DerivLp 1 2 univ)) 2
          (volume.restrict (Ioc 0 T))),
        HasWeakTimeDerivativeOn (Ioo 0 T)
          (fun t ↦ ContinuousLinearMap.piLpMap 2 (fun _ : Fin 2 ↦
            (wkpBaseCoordinateCLM : W^{1,2}(ℝ^1) →L[ℝ] DerivLp 1 2 univ)) (F t)) Ft ∧
        (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p,
          wkpBaseCoordinateCLM (F t p) x =
            wkpBaseCoordinateCLM (forcingData hT p) (timeSpaceCons t x)) ∧
        ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
        ∀ (U : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{3,2}(ℝ^1))) 2
            (volume.restrict (Ioc 0 T)))
          (G : Lp (PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))) 2
            (volume.restrict (Ioc 0 T)))
          (z : ℝ → PiLp 2 (fun _ : Fin 2 ↦ W^{1,2}(ℝ^1))),
        IsStrongTransportDiffusionSolution ε 0 T
          (fun j y p q ↦ coupledMatrix j (timeSpaceCons y.1 y.2) p q)
          (fun p y ↦ wkpBaseCoordinateCLM (forcingData hT p) (timeSpaceCons y.1 y.2))
          (ContinuousLinearMap.piLpMap 2
            (fun _ : Fin 2 ↦ mollifierHkCLM (standardMollifier 1) hε) initialData) U G z →
        ∃ t ∈ Icc 0 T, IsMaxOn (fun s ↦ ‖z s‖) (Icc 0 T) t ∧
          ‖z t‖ + ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin 2 ↦
            (wkpBaseCoordinateCLM : W^{1,2}(ℝ^1) →L[ℝ] DerivLp 1 2 univ))).compLpL
              2 (volume.restrict (Ioc 0 T)) G‖ ≤
            C * (‖initialData‖ + ‖F‖ + ‖Ft‖) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_viscous_approximation_bound hT coupledMatrix
    (fun j p q ↦ (coupledMatrix_contDiff j p q).contDiffOn)
    (fun j y _ ↦ coupledMatrix_isSymm j y) 4
    (fun j p q y _ ↦ coupledMatrix_norm_le j p q y)
    (coupledMatrix_norm_fderivWithin_le hT)
    (coupledMatrix_norm_iteratedFDerivWithin_le hT)
  obtain ⟨F, Ft, hweak, hbase, _hfirst, _htime, h⟩ :=
    hbound initialData (forcingData hT)
  exact ⟨C, hC, F, Ft, hweak, hbase, h⟩

end PDE.Examples.Hyperbolic.Viscosity
