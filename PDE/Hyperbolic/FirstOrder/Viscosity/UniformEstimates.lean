/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.Viscosity.Existence
public import PDE.Spaces.Sobolev.Approximation.Mollification.ProductHk
import PDE.Parabolic.Systems.Transport.Energy.Uniform

/-!
# Uniform estimates for the viscous approximations

Bounded C² symmetric matrix coefficients determine one constant before
the initial datum, forcing, or viscosity. For `0 < ε ≤ 1`, every
viscous solution satisfies the closed-time H¹ maximum and L²(L²) velocity
estimate. The initial mollifier is contractive in H¹.

The forcing and its time derivative are constructed from the spacetime
H¹ graph, with all spatial and time rows identified. The right-hand side is
`C (‖g‖_{H¹} + ‖f‖_{L²(H¹)} + ‖f_t‖_{L²(L²)})`.
The forcing term uses its spatial H¹ norm, not only `‖f‖_{L²(L²)}`.
The energy argument bounds the velocity with L²(H¹) forcing; the
nonnegative time-derivative norm is then added to the bound.
The `H¹` maximum is the estimate given by (21) and (23) in the proof of Theorem 2 of Evans,
§7.3.2; the velocity part of (17) is proved in
`PDE.Hyperbolic.FirstOrder.Viscosity.UniformVelocity`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, Theorem 2 and its proof, equations (17)-(23).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev
open scoped SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.FirstOrder

open MeasureTheory Set PDE.Common
open PDE.Analysis.Evolution PDE.Parabolic.Systems
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal NNReal

/-- Real scalar multiplication on the finite spatial L² Hilbert product. -/
local instance viscousBoundProductL2NormedSpace {n m : ℕ} :
    NormedSpace ℝ (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin m ↦ DerivLp n 2 univ)

variable {n m : ℕ} {T : ℝ}

/-- The coefficient field fixes a uniform bound before all data and
positive viscosities at most one. The forcing slices and their weak
time derivative come from the given spacetime Sobolev function.
The forcing norm `‖F‖` is L² in time with values in spatial H¹. -/
theorem exists_uniform_viscous_approximation_bound (hT : 0 < T)
    (B : Fin n → SpaceTime n → Matrix (Fin m) (Fin m) ℝ)
    (hB : ∀ j p q, ContDiffOn ℝ 2 (fun y ↦ B j y p q) {y | y 0 ∈ Icc 0 T})
    (hsym : ∀ j y, y 0 ∈ Icc 0 T → (B j y).IsSymm) (M : ℝ≥0)
    (hzero : ∀ j p q y, y 0 ∈ Icc 0 T → ‖B j y p q‖ ≤ M)
    (hone : ∀ j p q y, y 0 ∈ Icc 0 T →
      ‖fderivWithin ℝ (fun z ↦ B j z p q) {z | z 0 ∈ Icc 0 T} y‖ ≤ M)
    (htwo : ∀ j p q y, y 0 ∈ Icc 0 T →
      ‖iteratedFDerivWithin ℝ 2 (fun z ↦ B j z p q) {z | z 0 ∈ Icc 0 T} y‖ ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (g : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n)))
        (f : PiLp 2 (fun _ : Fin m ↦
          W^{1,2}({y : ℝ^(n + 1) | y 0 ∈ Ioo 0 T}))),
      ∃ (F : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
          (volume.restrict (Ioc 0 T)))
        (Ft : Lp (PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ)) 2
          (volume.restrict (Ioc 0 T))),
      HasWeakTimeDerivativeOn (Ioo 0 T)
        (fun t ↦ ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
          (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)) (F t)) Ft ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p,
        wkpBaseCoordinateCLM (F t p) x =
          wkpBaseCoordinateCLM (f p) (timeSpaceCons t x)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p j,
        wkpCoordinateCLM (singleDerivIndex n j) (F t p) x =
          wkpCoordinateCLM (singleDerivIndex (n + 1) j.succ) (f p)
            (timeSpaceCons t x)) ∧
      (∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ p,
        Ft t p x = wkpCoordinateCLM (singleDerivIndex (n + 1) 0) (f p)
          (timeSpaceCons t x)) ∧
      ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ∀ (U : Lp (PiLp 2 (fun _ : Fin m ↦ W^{3,2}(ℝ^n))) 2
          (volume.restrict (Ioc 0 T)))
        (G : Lp (PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))) 2
          (volume.restrict (Ioc 0 T)))
        (z : ℝ → PiLp 2 (fun _ : Fin m ↦ W^{1,2}(ℝ^n))),
      IsStrongTransportDiffusionSolution ε 0 T
        (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q)
        (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2))
        (ContinuousLinearMap.piLpMap 2
          (fun _ : Fin m ↦ mollifierHkCLM (standardMollifier n) hε) g) U G z →
      ∃ t ∈ Icc 0 T, IsMaxOn (fun s ↦ ‖z s‖) (Icc 0 T) t ∧
        ‖z t‖ + ‖(ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
          (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ))).compLpL
            2 (volume.restrict (Ioc 0 T)) G‖ ≤ C * (‖g‖ + ‖F‖ + ‖Ft‖) := by
  obtain ⟨A, hA, _hAnorm, hAbase, _hAfirst⟩ :=
    exists_wkpSpace_matrix_timeSlices hT B hB M hzero hone htwo
  have hAsym := base_timeSlices_symmetric B hsym A hAbase
  obtain ⟨C, hC, hbound⟩ := exists_uniform_transport_diffusion_constant hT A hA hAsym
  have hBrep : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (timeSpaceCons t x) p q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun p ↦ ae_all_iff.mpr fun q ↦
      hAbase t (Ioc_subset_Icc_self ht) j p q
  refine ⟨C, hC, fun g f ↦ ?_⟩
  obtain ⟨F, Ft, hFt, hFbase, hFfirst, hFtime⟩ := Slices.exists_vector_timeSlices_of_wkpSpaceOn f
  refine ⟨F, Ft, hFt, hFbase, hFfirst, hFtime, fun ε hε hε1 U G z h ↦ ?_⟩
  obtain ⟨t, ht, hmax, hnorm⟩ := hbound ε hε.le hε1
    (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q) hBrep
    (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2)) F hFbase
    _ U G z h
  refine ⟨t, ht, hmax, hnorm.trans ?_⟩
  gcongr C * ?_
  linarith [norm_piLpMap_mollifierHkCLM_le (standardMollifier n) hε g, norm_nonneg Ft]

end PDE.Hyperbolic.FirstOrder
