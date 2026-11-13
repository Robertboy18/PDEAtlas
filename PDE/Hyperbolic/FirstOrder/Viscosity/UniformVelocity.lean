/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.FirstOrder.Viscosity.Existence
public import PDE.Spaces.Sobolev.Approximation.Mollification.ProductHk
import PDE.Hyperbolic.FirstOrder.Coefficients.TimeDerivative
import PDE.Parabolic.Systems.Transport.Energy.UniformVelocity
import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.Norms

/-!
# Uniform-in-time velocity of the viscous approximations

On a fixed finite time slab, bounded C² symmetric coefficients
and H¹ initial and spacetime forcing data give the closed-time maximum of
`‖u(t)‖H¹ + ‖u_t(t)‖L²`. The constant precedes all data, positive viscosities
at most one, and strong solutions. Its dependence includes the fixed slab.

The L² velocity is constructed from the weak time derivative, with its
initial trace derived from the PDE and the prescribed scale-ε mollification.
Fubini identifies the sum of the squared Bochner slice norms with the joint
spacetime H¹ norm squared, so a fixed factor absorbs both slice norms into the
forcing term.
This proves the fixed-slab uniform velocity estimate (17) of Evans, §7.3.2, Theorem 2. The bound
includes the forcing's time derivative; the constant may depend on the fixed time slab.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.3.2, Theorem 2 and step 4 of its proof, equations (17)
  and (24)-(27).
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

variable {n m : ℕ} {T : ℝ}

/-- For fixed `T > 0`, the joint C² symmetric coefficient field fixes a constant
which may depend on `T`, before all H¹ data and positive viscosities at most one.
Every original strong viscous solution has a continuous L² velocity, and the sum
of its H¹ state norm and L² velocity norm attains a uniformly bounded maximum
on the closed time slab. -/
theorem exists_uniform_viscous_approximation_velocity_bound (hT : 0 < T)
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
      ∃ v : ℝ → PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 univ),
        ContinuousOn v (Icc 0 T) ∧
        (v =ᵐ[volume.restrict (Ioc 0 T)] fun t ↦
          ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
            (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)) (G t)) ∧
        ∃ t ∈ Icc 0 T, IsMaxOn (fun s ↦ ‖z s‖ + ‖v s‖) (Icc 0 T) t ∧
          ‖z t‖ + ‖v t‖ ≤ C * (‖g‖ + ‖f‖) := by
  obtain ⟨A, hA, _hAnorm, hAbase, _hAfirst⟩ :=
    exists_wkpSpace_matrix_timeSlices hT B hB M hzero hone htwo
  have hAsym := base_timeSlices_symmetric B hsym A hAbase
  let C := fun t ↦ vectorTransportPiLpCLM (fun j p q ↦ wkpBaseCoordinateCLM (A t j p q))
  obtain ⟨dC, _hCcont, hdC, hderiv, _hdBound, _hdActual⟩ :=
    exists_vectorTransportPiLpCLM_timeDerivative hT B hB M hone htwo A hAbase
  obtain ⟨C₀, hC₀, hbound⟩ := exists_uniform_transport_velocity_constant hT A hA hAsym
    C dC (fun _ _ _ _ ↦ rfl) hdC hderiv (standardMollifier n)
  have hBrep : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ x ∂volume, ∀ j p q,
      wkpBaseCoordinateCLM (A t j p q) x = B j (timeSpaceCons t x) p q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ae_all_iff.mpr fun j ↦ ae_all_iff.mpr fun p ↦ ae_all_iff.mpr fun q ↦
      hAbase t (Ioc_subset_Icc_self ht) j p q
  have hinclusion : (GelfandTriple.finiteProduct
      (fun _ : Fin m ↦ hOneLTwoGelfandTriple (n := n) isOpen_univ)).inclusion =
      ContinuousLinearMap.piLpMap 2 (fun _ : Fin m ↦
        (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)) :=
    ContinuousLinearMap.ext fun _ ↦ PiLp.ext fun _ ↦ rfl
  refine ⟨2 * C₀, by positivity, fun g f ↦ ?_⟩
  obtain ⟨F, Ft, hFt, hFbase, hFfirst, hFtime⟩ := Slices.exists_vector_timeSlices_of_wkpSpaceOn f
  have hslice : ‖F‖ + ‖Ft‖ ≤ 2 * ‖f‖ := by
    have hnorm := Slices.norm_vector_timeSlices_add_timeDerivative_le (I := Ioo 0 T) f
    rw [restrict_Ioo_eq_restrict_Ioc] at hnorm
    exact hnorm F Ft hFbase hFfirst hFtime
  refine ⟨F, Ft, hFt, hFbase, hFfirst, hFtime, fun ε hε hε1 U G z h ↦ ?_⟩
  obtain ⟨v, hv, hvAE, t, ht, hmax, hnorm⟩ := hbound g F Ft
    (by simpa only [vectorHOneLTwoGelfandTriple, hinclusion] using hFt) ε hε hε1
    (fun j y p q ↦ B j (timeSpaceCons y.1 y.2) p q) hBrep
    (fun p y ↦ wkpBaseCoordinateCLM (f p) (timeSpaceCons y.1 y.2)) hFbase U G z h
  refine ⟨v, hv, ?_, t, ht, hmax, ?_⟩
  · simpa only [vectorHOneLTwoGelfandTriple, hinclusion] using hvAE
  · apply hnorm.trans
    have hforcing := mul_le_mul_of_nonneg_left hslice hC₀.le
    have hdata := mul_nonneg hC₀.le (norm_nonneg g)
    nlinarith

end PDE.Hyperbolic.FirstOrder
