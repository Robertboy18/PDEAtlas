/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.VorticityForm
public import PDE.Fluid.NavierStokes.Operators
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Analysis.Calculus.LocalExtension
import PDE.FDeriv.SpaceTime
import PDE.Fluid.Incompressible.Locality
import PDE.Fluid.Incompressible.ParametricPressure
import PDE.Analysis.Calculus.Potential.Convex

/-!
# Pressure reconstruction from vorticity evolution

A velocity whose vorticity two-form satisfies the transport-diffusion equation has a pressure
closing the force-free Navier–Stokes momentum equation on every open convex spatial domain. The
equation is `vorticityFormTransportResidual n ν u = 0` for the vorticity two-form
`spatialVorticityForm`, and the Euler statements are its case `ν = 0`.

The Navier–Stokes slice-wise existence theorems require only local `C³` velocity regularity on the
selected time-space domain. The inviscid vector-vorticity theorem
`exists_pressure_euler_momentum_equation_of_vectorVorticity_of_contDiffAt_two` uses local `C²`
regularity. Neither requires an extension through a terminal time. The jointly regular, normalized
pressure theorems assume global regularity.

No incompressibility hypothesis is needed for the two-form calculation. In three dimensions,
incompressibility is used only when rewriting the same two-form equation as the familiar vector
identity `Dₜω = (ω · ∇)u + νΔω`, which Majda and Bertozzi, Chapter 1, derive by taking the curl of
the momentum equation.

All reconstructed momentum equations are force-free: the conclusion is `D_t u + ∇p = ν Δu` (or
`D_t u + ∇p = 0` for Euler) with no external force, because the vorticity equation as stated carries
no forcing term.

## Main results

* `antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual`: the
  antisymmetric spatial derivative of `ν Δu - D_t u` is minus the vorticity
  residual, for a `C³` velocity.
* `exists_pressure_navierStokes_momentum_equation_of_vorticity`: slice-wise
  pressure on an open convex spatial domain from local `C³` regularity and the
  two-form equation; `exists_jointly_contDiff_one_normalized_pressure_navierStokes_of_vorticity`
  and its continuous and smooth variants give a pressure that is jointly regular
  in `(t, x)` and normalized at a base point.
* `vorticityFormTransportResidual_eq_zero_iff_vectorVorticity`: in three
  dimensions, for a divergence-free `C³` velocity, the two-form equation is
  equivalent to the vector vorticity equation.
* `exists_pressure_navierStokes_momentum_equation_of_vectorVorticity` and the
  corresponding Euler statements: the three-dimensional vector-vorticity form of
  the reconstruction.
* `exists_pressure_euler_momentum_equation_of_vectorVorticity_of_contDiffAt_two`:
  slice-wise Euler pressure from local `C²` velocity, zero divergence, and the
  transport equation for the curl.

## How it works

For a `C³` velocity we differentiate the material derivative and the viscous term and commute mixed
derivatives: the antisymmetric part of the spatial derivative of the candidate `ν Δu - D_t u` is
minus the vorticity residual
(`antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual`). Where the vorticity
equation holds, the spatial coordinate derivatives of the candidate therefore commute
(`partialDeriv_navierStokesPressureCandidate_comm_of_vorticity`), and the Poincaré lemma on an open
convex domain (`EuclideanSpace.exists_potential_of_partialDeriv_comm`, which rests on Mathlib's
`Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric`) gives a pressure on each time slice. For the
jointly regular pressures we take instead the segment integral `normalizedPressure` from the base
point, through `exists_jointly_contDiff_normalized_pressure_of_partialDeriv_comm` and its variants.
The `C³` Euler statements specialize the Navier–Stokes ones at `ν = 0`. The `C²` vector-vorticity
theorem works with `-D_t u` directly: the three cyclic components of the two-form residual are
combinations of the vector residual and the divergence, so they vanish, and with `ν = 0` they are
the antisymmetric derivatives of `D_t u`.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

open scoped Gradient

@[expose] public section

open PDE (partialDeriv)

namespace IncompressibleFlow

open EuclideanSpace
open Filter
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- The pressure-gradient candidate depends only on the local velocity field. -/
theorem navierStokesPressureCandidate_eventuallyEq
    {n : ℕ} (ν : ℝ) {u v : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : u =ᶠ[𝓝 x] v) :
    (fun y ↦ NavierStokes.viscousTerm n ν u y - materialDerivative n u u y) =ᶠ[𝓝 x]
      (fun y ↦ NavierStokes.viscousTerm n ν v y - materialDerivative n v v y) := by
  filter_upwards [spatialVectorLaplacian_eventuallyEq hu,
    materialDerivative_eventuallyEq hu hu] with y hlap hmat
  simp only [NavierStokes.viscousTerm, hlap, hmat]

private theorem partialDeriv_convective_component
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (hu : ContDiff ℝ 2 u)
    (a : Fin (n + 1)) (b : Fin n) (x : ℝ^(n + 1)) :
    (∂[a]
        (fun y ↦ ∑ k : Fin n,
          u y k * (∂[k.succ] (fun z ↦ u z b)) y)) x =
      ∑ k : Fin n,
        ((∂[a] (fun y ↦ u y k)) x *
            (∂[k.succ] (fun y ↦ u y b)) x +
          u x k * (∂[a]
            (fun y ↦ (∂[k.succ] (fun z ↦ u z b)) y)) x) := by
  have huComponent (k : Fin n) : ContDiff ℝ 2 (fun y ↦ u y k) := contDiff_euclidean.1 hu k
  unfold partialDeriv
  rw [fderiv_fun_sum, sum_apply]
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [fderiv_fun_mul]
    · simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    · exact (huComponent k).differentiable (by norm_num) x
    · exact (PDE.contDiff_partialDeriv_of_succ (m := 1) (huComponent b)).differentiable
        (by norm_num) x
  · exact fun k _ ↦ (((huComponent k).of_le (by norm_num)).mul
      (PDE.contDiff_partialDeriv_of_succ (m := 1) (huComponent b))).differentiable (by norm_num) x

private theorem antisymmetric_materialDerivative_eq
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (hu : ContDiff ℝ 2 u)
    (i j : Fin n) (x : ℝ^(n + 1)) :
    (∂[i.succ] (fun y ↦ materialDerivative n u u y j)) x -
        (∂[j.succ] (fun y ↦ materialDerivative n u u y i)) x =
      scalarMaterialDerivative n u
          (fun y ↦ spatialVorticityForm n u y (i, j)) x +
        ∑ k : Fin n,
          ((∂[i.succ] (fun y ↦ u y k)) x *
              spatialVorticityForm n u x (k, j) +
            (∂[j.succ] (fun y ↦ u y k)) x *
              spatialVorticityForm n u x (i, k)) := by
  have huComponent (k : Fin n) : ContDiff ℝ 2 (fun y ↦ u y k) := contDiff_euclidean.1 hu k
  have hfirst (a : Fin (n + 1)) (k : Fin n) : ContDiff ℝ 1 (fun y ↦ (∂[a] (fun z ↦ u z k)) y) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (huComponent k)
  have hconvective (k : Fin n) :
      ContDiff ℝ 1 (fun y ↦ ∑ l : Fin n, u y l * (∂[l.succ] (fun z ↦ u z k)) y) :=
    ContDiff.sum fun l _ ↦ ((huComponent l).of_le (by norm_num)).mul (hfirst _ k)
  have hmaterial (a : Fin (n + 1)) (b : Fin n) :
      (∂[a] (fun y ↦ materialDerivative n u u y b)) x =
        (∂[a] (fun y ↦ (∂[(0 : Fin (n + 1))] (fun z ↦ u z b)) y)) x +
          ∑ k : Fin n, ((∂[a] (fun y ↦ u y k)) x * (∂[k.succ] (fun y ↦ u y b)) x +
            u x k * (∂[a] (fun y ↦ (∂[k.succ] (fun z ↦ u z b)) y)) x) := by
    rw [show (fun y ↦ materialDerivative n u u y b) = fun y ↦ (∂[(0 : Fin (n + 1))]
        (fun z ↦ u z b)) y + ∑ k : Fin n, u y k * (∂[k.succ] (fun z ↦ u z b)) y
        from funext fun y ↦ materialDerivative_apply n u u y b,
      PDE.partialDeriv_add ((hfirst 0 b).differentiable (by norm_num)).differentiableAt
        ((hconvective b).differentiable (by norm_num)).differentiableAt,
      partialDeriv_convective_component u hu a b x]
  rw [hmaterial i.succ j, hmaterial j.succ i, scalarMaterialDerivative_apply]
  simp only [spatialVorticityForm_apply]
  have hsub (a : Fin (n + 1)) : (∂[a] (fun y ↦ (∂[i.succ] (fun z ↦ u z j)) y -
      (∂[j.succ] (fun z ↦ u z i)) y)) x = (∂[a] (fun y ↦ (∂[i.succ] (fun z ↦ u z j)) y)) x -
        (∂[a] (fun y ↦ (∂[j.succ] (fun z ↦ u z i)) y)) x :=
    PDE.partialDeriv_sub ((hfirst _ j).differentiable (by norm_num)).differentiableAt
      ((hfirst _ i).differentiable (by norm_num)).differentiableAt
  have hcomm (a : Fin (n + 1)) (b k : Fin n) :
      (∂[a] (fun y ↦ (∂[k.succ] (fun z ↦ u z b)) y)) x =
        (∂[k.succ] (fun y ↦ (∂[a] (fun z ↦ u z b)) y)) x :=
    PDE.partialDeriv_partialDeriv_comm a k.succ (huComponent b) x
  simp_rw [hsub, hcomm i.succ j, hcomm j.succ i]
  rw [PDE.partialDeriv_partialDeriv_comm i.succ 0 (huComponent j) x,
    PDE.partialDeriv_partialDeriv_comm j.succ 0 (huComponent i) x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_sub, sub_mul, mul_comm]
  ring

private theorem antisymmetric_viscousTerm_eq
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u) (i j : Fin n) (x : ℝ^(n + 1)) :
    (∂[i.succ] (fun y ↦ NavierStokes.viscousTerm n ν u y j)) x -
        (∂[j.succ]
          (fun y ↦ NavierStokes.viscousTerm n ν u y i)) x =
      ν * spatialLaplacian n
        (fun y ↦ spatialVorticityForm n u y (i, j)) x := by
  have huComponent (k : Fin n) : ContDiff ℝ 3 (fun y ↦ u y k) := contDiff_euclidean.1 hu k
  have hfirst (a : Fin (n + 1)) (b : Fin n) :
      ContDiff ℝ 2 (fun y ↦ (∂[a] (fun z ↦ u z b)) y) :=
    PDE.contDiff_partialDeriv_of_succ (m := 2) (huComponent b)
  have hsmul (a : Fin (n + 1)) (f : ℝ^(n + 1) → ℝ) :
      (∂[a] (fun y ↦ ν * f y)) x = ν * (∂[a] f) x := by
    simpa [smul_eq_mul] using PDE.partialDeriv_const_smul (E := ℝ) ν (i := a) (f := f) (x := x)
  simp only [NavierStokes.viscousTerm_apply, spatialVectorLaplacian_apply]
  rw [hsmul, hsmul]
  unfold spatialLaplacian
  have hlaplacianDerivative (a : Fin (n + 1)) (b : Fin n) :
      (∂[a] (fun y ↦ ∑ k : Fin n, (∂[k.succ] (fun z ↦ (∂[k.succ] (fun w ↦ u w b)) z)) y)) x =
        ∑ k : Fin n, (∂[a] (fun y ↦ (∂[k.succ] (fun z ↦ (∂[k.succ] (fun w ↦ u w b)) z)) y)) x :=
    PDE.partialDeriv_sum _ (fun k _ ↦ ((PDE.contDiff_partialDeriv_of_succ
      (hfirst k.succ b)).differentiable (by norm_num)).differentiableAt) a
  rw [hlaplacianDerivative i.succ j, hlaplacianDerivative j.succ i, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  have homegaSecond (k : Fin n) :
      (∂[k.succ] (fun y ↦ (∂[k.succ] (fun z ↦ spatialVorticityForm n u z (i, j))) y)) x =
        (∂[k.succ] (fun y ↦ (∂[k.succ] (fun z ↦ (∂[i.succ] (fun w ↦ u w j)) z)) y)) x -
          (∂[k.succ] (fun y ↦ (∂[k.succ] (fun z ↦ (∂[j.succ] (fun w ↦ u w i)) z)) y)) x := by
    rw [show (fun z ↦ spatialVorticityForm n u z (i, j)) = fun z ↦
        (∂[i.succ] (fun w ↦ u w j)) z - (∂[j.succ] (fun w ↦ u w i)) z
        from funext fun z ↦ spatialVorticityForm_apply n u z i j,
      PDE.secondPartialDeriv_sub k.succ k.succ (hfirst i.succ j).contDiffAt
        (hfirst j.succ i).contDiffAt]
  simp_rw [homegaSecond]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [PDE.partialDeriv_partialDeriv_comm i.succ k.succ (hfirst _ j) x,
    PDE.partialDeriv_partialDeriv_comm j.succ k.succ (hfirst _ i) x,
    PDE.partialDeriv_partialDeriv_comm_of_contDiff i.succ k.succ
      ((huComponent j).of_le (by norm_num)),
    PDE.partialDeriv_partialDeriv_comm_of_contDiff j.succ k.succ
      ((huComponent i).of_le (by norm_num))]

/-- The vorticity-form residual is exactly the antisymmetric spatial
derivative of the pressure-gradient candidate, up to sign. -/
theorem antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u) (i j : Fin n) (x : ℝ^(n + 1)) :
    (∂[i.succ]
          (fun y ↦
            (NavierStokes.viscousTerm n ν u y -
              materialDerivative n u u y) j)) x -
        (∂[j.succ]
          (fun y ↦
            (NavierStokes.viscousTerm n ν u y -
              materialDerivative n u u y) i)) x =
      -vorticityFormTransportResidual n ν u x (i, j) := by
  have hviscousComponent (k : Fin n) :
      ContDiff ℝ 1 (fun y ↦ NavierStokes.viscousTerm n ν u y k) := by
    simp only [NavierStokes.viscousTerm_apply, spatialVectorLaplacian_apply]
    unfold spatialLaplacian
    exact contDiff_const.mul (ContDiff.sum fun l _ ↦ PDE.contDiff_partialDeriv_of_succ (m := 1)
      (PDE.contDiff_partialDeriv_of_succ (m := 2) (contDiff_euclidean.1 hu k)))
  have hmaterialComponent (k : Fin n) :
      ContDiff ℝ 1 (fun y ↦ materialDerivative n u u y k) := by
    simp only [materialDerivative_apply]
    exact ((PDE.contDiff_partialDeriv_of_succ (contDiff_euclidean.1 hu k)).of_le
      (by norm_num)).add (ContDiff.sum fun l _ ↦ ((contDiff_euclidean.1 hu l).of_le
        (by norm_num)).mul ((PDE.contDiff_partialDeriv_of_succ (contDiff_euclidean.1 hu k)).of_le
          (by norm_num)))
  simp only [PiLp.sub_apply]
  rw [PDE.partialDeriv_sub ((hviscousComponent j).differentiable (by norm_num)).differentiableAt
      ((hmaterialComponent j).differentiable (by norm_num)).differentiableAt,
    PDE.partialDeriv_sub ((hviscousComponent i).differentiable (by norm_num)).differentiableAt
      ((hmaterialComponent i).differentiable (by norm_num)).differentiableAt]
  simp only [vorticityFormTransportResidual_apply]
  linear_combination antisymmetric_viscousTerm_eq ν u hu i j x -
    antisymmetric_materialDerivative_eq u (hu.of_le (by norm_num)) i j x

/-- The pressure/vorticity differential identity requires only a `C³` velocity germ.
A compactly supported representative reduces it to the global calculation. -/
theorem antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual_of_contDiffAt
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n) (i j : Fin n) (x : ℝ^(n + 1))
    (hu : ContDiffAt ℝ 3 u x) :
    (∂[i.succ]
          (fun y ↦ (NavierStokes.viscousTerm n ν u y - materialDerivative n u u y) j)) x -
        (∂[j.succ]
          (fun y ↦ (NavierStokes.viscousTerm n ν u y - materialDerivative n u u y) i)) x =
      -vorticityFormTransportResidual n ν u x (i, j) := by
  obtain ⟨v, hv, _, huv⟩ := hu.exists_contDiff_compactSupport_eventuallyEq
  have hc := navierStokesPressureCandidate_eventuallyEq ν huv
  have hi := (hc.fun_comp (fun z ↦ z j)).partialDeriv i.succ |>.eq_of_nhds
  have hj := (hc.fun_comp (fun z ↦ z i)).partialDeriv j.succ |>.eq_of_nhds
  dsimp only [Function.comp_def] at hi hj
  rw [hi, hj,
    (vorticityFormTransportResidual_eventuallyEq ν huv).eq_of_nhds]
  exact antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual ν v hv i j x

private theorem contDiff_navierStokesPressureCandidate
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 1 (fun xt ↦ NavierStokes.viscousTerm n ν u xt -
      materialDerivative n u u xt) := by
  apply (contDiff_piLp (p := (2 : ENNReal))).2
  intro i
  simp only [PiLp.sub_apply, NavierStokes.viscousTerm_apply,
    spatialVectorLaplacian_apply, materialDerivative_apply]
  apply ContDiff.sub
  · exact contDiff_const.mul (by
      unfold spatialLaplacian
      apply ContDiff.sum
      intro k _hk
      exact PDE.contDiff_partialDeriv_of_succ (m := 1)
        (PDE.contDiff_partialDeriv_of_succ (m := 2)
          (contDiff_euclidean.1 hu i)))
  · apply ContDiff.add
    · exact (PDE.contDiff_partialDeriv_of_succ (m := 2)
        (contDiff_euclidean.1 hu i)).of_le (by norm_num)
    · apply ContDiff.sum
      intro k _hk
      exact (contDiff_euclidean.1 hu k).of_le (by norm_num) |>.mul
        ((PDE.contDiff_partialDeriv_of_succ (m := 2)
          (contDiff_euclidean.1 hu i)).of_le (by norm_num))

/-- The pressure-gradient candidate is `C¹` near every point where the velocity is `C³`. -/
theorem contDiffAt_navierStokesPressureCandidate
    {n : ℕ} (ν : ℝ) {u : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 3 u x) :
    ContDiffAt ℝ 1
      (fun y ↦ NavierStokes.viscousTerm n ν u y - materialDerivative n u u y) x := by
  obtain ⟨v, hv, _, huv⟩ := hu.exists_contDiff_compactSupport_eventuallyEq
  exact (contDiff_navierStokesPressureCandidate ν v hv).contDiffAt.congr_of_eventuallyEq
    (navierStokesPressureCandidate_eventuallyEq ν huv)

private theorem contDiff_infty_navierStokesPressureCandidate
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (fun xt ↦ NavierStokes.viscousTerm n ν u xt -
      materialDerivative n u u xt) := by
  apply (contDiff_piLp (p := (2 : ENNReal))).2
  intro i
  simp only [PiLp.sub_apply, NavierStokes.viscousTerm_apply,
    spatialVectorLaplacian_apply, materialDerivative_apply]
  apply ContDiff.sub
  · exact contDiff_const.mul (by
      unfold spatialLaplacian
      apply ContDiff.sum
      intro k _hk
      exact PDE.contDiff_top_partialDeriv
        (PDE.contDiff_top_partialDeriv (contDiff_euclidean.1 hu i)))
  · apply ContDiff.add
    · exact PDE.contDiff_top_partialDeriv (contDiff_euclidean.1 hu i)
    · apply ContDiff.sum
      intro k _hk
      exact (contDiff_euclidean.1 hu k).mul
        (PDE.contDiff_top_partialDeriv (contDiff_euclidean.1 hu i))

/-- The vorticity transport-diffusion equation forces the Navier–Stokes
pressure-gradient candidate to have commuting spatial coordinate derivatives. -/
theorem partialDeriv_navierStokesPressureCandidate_comm_of_vorticity
    {n : ℕ} (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u) (i j : Fin n) (x : ℝ^(n + 1))
    (hvorticity : vorticityFormTransportResidual n ν u x = 0) :
    (∂[i.succ]
          (fun y ↦
            (NavierStokes.viscousTerm n ν u y -
              materialDerivative n u u y) j)) x =
      (∂[j.succ]
        (fun y ↦
          (NavierStokes.viscousTerm n ν u y -
            materialDerivative n u u y) i)) x := by
  rw [← sub_eq_zero]
  rw [antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual
    ν u hu i j x]
  simp [hvorticity]

/-- On a time slice where the vorticity equation holds, the spatial partial derivatives of the
pressure-gradient candidate commute. -/
private theorem partialDeriv_slice_navierStokesPressureCandidate_comm
    {n : ℕ} (ν : ℝ) {u : ℝ^(n + 1) → ℝ^n} (hu : ContDiff ℝ 3 u) {t : ℝ} {x : ℝ^n}
    (hvorticity : vorticityFormTransportResidual n ν u (PDE.Common.timeSpaceCons t x) = 0)
    (i j : Fin n) :
    (∂[i] (fun y ↦ (NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t y) -
        materialDerivative n u u (PDE.Common.timeSpaceCons t y)) j)) x =
      (∂[j] (fun y ↦ (NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t y) -
        materialDerivative n u u (PDE.Common.timeSpaceCons t y)) i)) x := by
  have hcandidate := (contDiff_piLp (p := (2 : ENNReal))).1
    (contDiff_navierStokesPressureCandidate ν u hu)
  have hi := PDE.partialDeriv_timeSpaceCons_spatial i _ t x
    ((hcandidate j).differentiable (by norm_num) (PDE.Common.timeSpaceCons t x))
  have hj := PDE.partialDeriv_timeSpaceCons_spatial j _ t x
    ((hcandidate i).differentiable (by norm_num) (PDE.Common.timeSpaceCons t x))
  exact hi.trans ((partialDeriv_navierStokesPressureCandidate_comm_of_vorticity ν u hu i j _
    hvorticity).trans hj.symm)

/-- A `C³` velocity satisfying its vorticity-form equation admits a jointly `C¹` pressure
normalized at a chosen point, closing the force-free Navier–Stokes momentum equation
`D_t u + grad p = nu Delta u` on every slice of the convex domain.

The pressure is constructed by one parametric line integral, so the additive
gauge is coherent in time rather than selected independently on each slice. -/
theorem exists_jointly_contDiff_one_normalized_pressure_navierStokes_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u)
    (hvorticity : ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      vorticityFormTransportResidual n ν u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ,
      ContDiff ℝ 1 p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
          HasGradientAt (p t)
              (NavierStokes.viscousTerm n ν u
                  (PDE.Common.timeSpaceCons t x) -
                materialDerivative n u u
                  (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x =
              NavierStokes.viscousTerm n ν u
                (PDE.Common.timeSpaceCons t x) := by
  let g : ℝ → ℝ^n → ℝ^n := fun t x ↦
    NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) -
      materialDerivative n u u (PDE.Common.timeSpaceCons t x)
  have hcandidate := contDiff_navierStokesPressureCandidate ν u hu
  have hgSmooth : ContDiff ℝ 1 g.uncurry := by
    change ContDiff ℝ 1
      ((fun xt ↦ NavierStokes.viscousTerm n ν u xt -
        materialDerivative n u u xt) ∘
          fun tx : ℝ × ℝ^n ↦ PDE.Common.timeSpaceCons tx.1 tx.2)
    exact hcandidate.comp (PDE.Common.contDiff_timeSpaceCons_uncurry n (m := 1))
  have hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s := by
    intro t
    have hslice := hcandidate.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t)
    exact (hslice.differentiable (by norm_num)).differentiableOn
  have hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      (∂[i] (fun y ↦ g t y j)) x = (∂[j] (fun y ↦ g t y i)) x := fun t x hx i j ↦
    partialDeriv_slice_navierStokesPressureCandidate_comm ν hu (hvorticity t x hx) i j
  obtain ⟨p, hpSmooth, hpBase, hpGradient⟩ :=
    exists_jointly_contDiff_normalized_pressure_of_partialDeriv_comm
      1 hs hso ha hgSmooth hgDifferentiable hcomm
  refine ⟨p, hpSmooth, hpBase, fun t x hx ↦ ⟨hpGradient t x hx, ?_⟩⟩
  rw [(hpGradient t x hx).gradient]
  dsimp [g]
  abel

/-- A smooth velocity satisfying its vorticity-form equation admits a jointly smooth pressure
normalized at a chosen point and closing the force-free Navier–Stokes momentum equation. -/
theorem exists_jointly_smooth_normalized_pressure_navierStokes_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hvorticity : ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      vorticityFormTransportResidual n ν u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
          HasGradientAt (p t)
              (NavierStokes.viscousTerm n ν u
                  (PDE.Common.timeSpaceCons t x) -
                materialDerivative n u u
                  (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x =
              NavierStokes.viscousTerm n ν u
                (PDE.Common.timeSpaceCons t x) := by
  let g : ℝ → ℝ^n → ℝ^n := fun t x ↦
    NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) -
      materialDerivative n u u (PDE.Common.timeSpaceCons t x)
  have hcandidate := contDiff_infty_navierStokesPressureCandidate ν u hu
  have hthree : (3 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have huThree : ContDiff ℝ 3 u := hu.of_le hthree
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g.uncurry := by
    change ContDiff ℝ (⊤ : ℕ∞)
      ((fun xt ↦ NavierStokes.viscousTerm n ν u xt -
        materialDerivative n u u xt) ∘
          fun tx : ℝ × ℝ^n ↦ PDE.Common.timeSpaceCons tx.1 tx.2)
    exact hcandidate.comp (PDE.Common.contDiff_timeSpaceCons_uncurry n)
  have hgDifferentiable : ∀ t : ℝ, DifferentiableOn ℝ (g t) s := by
    intro t
    have hslice := hcandidate.comp (PDE.Common.contDiff_timeSpaceCons_spatial n t)
    exact hslice.differentiable (by simp) |>.differentiableOn
  have hcomm : ∀ (t : ℝ) (x : ℝ^n), x ∈ s → ∀ i j : Fin n,
      (∂[i] (fun y ↦ g t y j)) x = (∂[j] (fun y ↦ g t y i)) x := fun t x hx i j ↦
    partialDeriv_slice_navierStokesPressureCandidate_comm ν huThree (hvorticity t x hx) i j
  obtain ⟨p, hpSmooth, hpBase, hpGradient⟩ :=
    exists_jointly_smooth_normalized_pressure_of_partialDeriv_comm
      hs hso ha hgSmooth hgDifferentiable hcomm
  refine ⟨p, hpSmooth, hpBase, fun t x hx ↦ ⟨hpGradient t x hx, ?_⟩⟩
  rw [(hpGradient t x hx).gradient]
  dsimp [g]
  abel

/-- A `C³` velocity satisfying its vorticity-form equation admits a jointly continuous pressure
normalized at a chosen point and closing the force-free Navier–Stokes momentum equation. -/
theorem exists_jointly_continuous_normalized_pressure_navierStokes_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u)
    (hvorticity : ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      vorticityFormTransportResidual n ν u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
          HasGradientAt (p t)
              (NavierStokes.viscousTerm n ν u
                  (PDE.Common.timeSpaceCons t x) -
                materialDerivative n u u
                  (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x =
              NavierStokes.viscousTerm n ν u
                (PDE.Common.timeSpaceCons t x) := by
  obtain ⟨p, hpSmooth, hpBase, hpEquation⟩ :=
    exists_jointly_contDiff_one_normalized_pressure_navierStokes_of_vorticity
      hs hso ha ν u hu hvorticity
  exact ⟨p, hpSmooth.continuous, hpBase, hpEquation⟩

/-- A velocity satisfying its vorticity-form equation admits a slice-wise pressure closing
the force-free Navier–Stokes momentum equation on an open convex spatial domain at every
selected time.

Only local `C³` regularity at those spacetime points is assumed. In particular,
`I` may exclude a finite blow-up time. The pressure is chosen independently on each
time slice. -/
theorem exists_pressure_navierStokes_momentum_equation_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s) (I : Set ℝ)
    (ν : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ∀ t ∈ I, ∀ x ∈ s, ContDiffAt ℝ 3 u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ t ∈ I, ∀ x ∈ s,
      vorticityFormTransportResidual n ν u (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ, ∀ t ∈ I, ∀ x ∈ s,
      HasGradientAt (p t)
          (NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) -
            materialDerivative n u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative n u u (PDE.Common.timeSpaceCons t x) + ∇ (p t) x =
          NavierStokes.viscousTerm n ν u (PDE.Common.timeSpaceCons t x) := by
  classical
  let candidate : ℝ^(n + 1) → ℝ^n := fun y ↦
    NavierStokes.viscousTerm n ν u y - materialDerivative n u u y
  have hcandidate (t : ℝ) (ht : t ∈ I) (x : ℝ^n) (hx : x ∈ s) :
      ContDiffAt ℝ 1 candidate (PDE.Common.timeSpaceCons t x) :=
    contDiffAt_navierStokesPressureCandidate ν (hu t ht x hx)
  have hpotential (t : ℝ) (ht : t ∈ I) :
      ∃ p : ℝ^n → ℝ, ∀ x ∈ s,
        HasGradientAt p (candidate (PDE.Common.timeSpaceCons t x)) x := by
    apply EuclideanSpace.exists_potential_of_partialDeriv_comm hs hso
    · intro x hx
      exact ((hcandidate t ht x hx).comp x
        (PDE.Common.contDiff_timeSpaceCons_spatial n t).contDiffAt).differentiableAt
          (by norm_num) |>.differentiableWithinAt
    · intro x hx i j
      have hcomm :
          (∂[i.succ] (fun y ↦ candidate y j)) (PDE.Common.timeSpaceCons t x) =
            (∂[j.succ] (fun y ↦ candidate y i)) (PDE.Common.timeSpaceCons t x) := by
        rw [← sub_eq_zero,
          antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual_of_contDiffAt
            ν u i j (PDE.Common.timeSpaceCons t x) (hu t ht x hx)]
        simp [hvorticity t ht x hx]
      have hi := PDE.partialDeriv_timeSpaceCons_spatial i (fun y ↦ candidate y j) t x
        (((contDiffAt_piLp (p := (2 : ENNReal))).1 (hcandidate t ht x hx) j).differentiableAt
          (by norm_num))
      have hj := PDE.partialDeriv_timeSpaceCons_spatial j (fun y ↦ candidate y i) t x
        (((contDiffAt_piLp (p := (2 : ENNReal))).1 (hcandidate t ht x hx) i).differentiableAt
          (by norm_num))
      exact hi.trans (hcomm.trans hj.symm)
  choose! p hp using hpotential
  refine ⟨p, fun t ht x hx ↦ ⟨hp t ht x hx, ?_⟩⟩
  rw [(hp t ht x hx).gradient]
  dsimp only [candidate]
  abel

/-- The inviscid specialization reconstructs a slice-wise pressure for the
force-free Euler momentum equation from the Euler vorticity-form equation. -/
theorem exists_pressure_euler_momentum_equation_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s) (I : Set ℝ)
    (u : ℝ^(n + 1) → ℝ^n)
    (hu : ∀ t ∈ I, ∀ x ∈ s, ContDiffAt ℝ 3 u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ t ∈ I, ∀ x ∈ s,
      vorticityFormTransportResidual n 0 u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ, ∀ t ∈ I, ∀ x ∈ s,
      HasGradientAt (p t)
          (-materialDerivative n u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
          ∇ (p t) x = 0 := by
  simpa [NavierStokes.viscousTerm] using
    exists_pressure_navierStokes_momentum_equation_of_vorticity
    hs hso I 0 u hu hvorticity

/-- The inviscid specialization gives a jointly continuous Euler pressure
with a time-coherent point normalization. -/
theorem exists_jointly_continuous_normalized_pressure_euler_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ 3 u)
    (hvorticity : ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      vorticityFormTransportResidual n 0 u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
          HasGradientAt (p t)
              (-materialDerivative n u u
                (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x = 0 := by
  simpa [NavierStokes.viscousTerm] using
    exists_jointly_continuous_normalized_pressure_navierStokes_of_vorticity
      hs hso ha 0 u hu hvorticity

/-- The inviscid specialization reconstructs a jointly smooth pressure from a smooth Euler
vorticity-form solution. -/
theorem exists_jointly_smooth_normalized_pressure_euler_of_vorticity
    {n : ℕ} {s : Set (ℝ^n)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^n} (ha : a ∈ s) (u : ℝ^(n + 1) → ℝ^n)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hvorticity : ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
      vorticityFormTransportResidual n 0 u
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^n), x ∈ s →
          HasGradientAt (p t)
              (-materialDerivative n u u
                (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative n u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x = 0 := by
  simpa [NavierStokes.viscousTerm] using
    exists_jointly_smooth_normalized_pressure_navierStokes_of_vorticity
      hs hso ha 0 u hu hvorticity

/-! ## Three-dimensional vector vorticity -/

/-- For a divergence-free `C³` velocity, vanishing of the three-dimensional
vector-vorticity residual implies vanishing of the vorticity two-form residual,
which is the direction needed for pressure reconstruction.

The proof includes the exact correction before incompressibility:
each cyclic two-form component is the corresponding vector residual plus
`(div u)ω`. -/
theorem vorticityFormTransportResidual_eq_zero_of_vectorVorticity
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 3 u) (xt : ℝ^4)
    (hdiv : DivergenceFreeAt u xt)
    (hvorticity : vorticityTransportResidual 3 ν u
      (spacetimeSpatialCurl u) xt = 0) :
    vorticityFormTransportResidual 3 ν u xt = 0 := by
  have huOne : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hres (k : Fin 3) : vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt k = 0 := by
    simpa using congrArg (fun v : ℝ^3 ↦ v k) hvorticity
  have hdiv' : spatialDivergence 3 u xt = 0 := hdiv
  have hcyclic0 : vorticityFormTransportResidual 3 ν u xt (1, 2) = 0 := by
    rw [vorticityFormTransportResidual_apply_one_two ν u huOne xt, hres 0, hdiv']; simp
  have hcyclic1 : vorticityFormTransportResidual 3 ν u xt (2, 0) = 0 := by
    rw [vorticityFormTransportResidual_apply_two_zero ν u huOne xt, hres 1, hdiv']; simp
  have hcyclic2 : vorticityFormTransportResidual 3 ν u xt (0, 1) = 0 := by
    rw [vorticityFormTransportResidual_apply_zero_one ν u huOne xt, hres 2, hdiv']; simp
  have hdiag (i : Fin 3) : vorticityFormTransportResidual 3 ν u xt (i, i) = 0 := by
    linarith [antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual ν u hu i i xt]
  have hswap (i j : Fin 3) : vorticityFormTransportResidual 3 ν u xt (j, i) =
      -vorticityFormTransportResidual 3 ν u xt (i, j) := by
    linarith [antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual ν u hu i j xt,
      antisymmetric_navierStokesPressureCandidate_eq_neg_vorticityResidual ν u hu j i xt]
  ext ij
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact hdiag 0
  · exact hcyclic2
  · simpa [hcyclic1] using hswap (2 : Fin 3) (0 : Fin 3)
  · simpa [hcyclic2] using hswap (0 : Fin 3) (1 : Fin 3)
  · exact hdiag 1
  · exact hcyclic0
  · exact hcyclic1
  · simpa [hcyclic0] using hswap (1 : Fin 3) (2 : Fin 3)
  · exact hdiag 2

/-- The vector-to-two-form implication is local in spacetime; no regularity
at a terminal time or outside the solution's domain is required. -/
theorem vorticityFormTransportResidual_eq_zero_of_vectorVorticity_of_contDiffAt
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (xt : ℝ^4) (hu : ContDiffAt ℝ 3 u xt)
    (hdiv : DivergenceFreeAt u xt)
    (hvorticity : vorticityTransportResidual 3 ν u
      (spacetimeSpatialCurl u) xt = 0) :
    vorticityFormTransportResidual 3 ν u xt = 0 := by
  obtain ⟨v, hv, _, huv⟩ := hu.exists_contDiff_compactSupport_eventuallyEq
  have hdivV : DivergenceFreeAt v xt := by
    change spatialDivergence 3 v xt = 0
    rw [← (spatialDivergence_eventuallyEq huv).eq_of_nhds]
    exact hdiv
  have hresV : vorticityTransportResidual 3 ν v (spacetimeSpatialCurl v) xt = 0 := by
    rw [← (vorticityTransportResidual_eventuallyEq ν huv
      (spacetimeSpatialCurl_eventuallyEq huv)).eq_of_nhds]
    exact hvorticity
  rw [(vorticityFormTransportResidual_eventuallyEq ν huv).eq_of_nhds]
  exact vorticityFormTransportResidual_eq_zero_of_vectorVorticity ν v hv xt hdivV hresV

/-- For a divergence-free `C³` velocity in three dimensions, the familiar
vector-vorticity equation and the intrinsic two-form equation are equivalent. -/
theorem vorticityFormTransportResidual_eq_zero_iff_vectorVorticity
    (ν : ℝ) (u : ℝ^4 → ℝ^3) (hu : ContDiff ℝ 3 u) (xt : ℝ^4)
    (hdiv : DivergenceFreeAt u xt) :
    vorticityFormTransportResidual 3 ν u xt = 0 ↔
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u) xt = 0 := by
  constructor
  · exact vorticityTransportResidual_eq_zero_of_vorticityForm
      ν u (hu.of_le (by norm_num)) xt hdiv
  · exact vorticityFormTransportResidual_eq_zero_of_vectorVorticity
      ν u hu xt hdiv

/-- A divergence-free `C³` velocity satisfying the familiar vector-vorticity
equation admits a jointly continuous pressure normalized at a chosen point. -/
theorem exists_jointly_continuous_normalized_pressure_navierStokes_of_vectorVorticity
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^3} (ha : a ∈ s) (ν : ℝ) (u : ℝ^4 → ℝ^3)
    (hu : ContDiff ℝ 3 u)
    (hdiv : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
          HasGradientAt (p t)
              (NavierStokes.viscousTerm 3 ν u
                  (PDE.Common.timeSpaceCons t x) -
                materialDerivative 3 u u
                  (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x =
              NavierStokes.viscousTerm 3 ν u
                (PDE.Common.timeSpaceCons t x) := by
  apply exists_jointly_continuous_normalized_pressure_navierStokes_of_vorticity
    hs hso ha ν u hu
  intro t x hx
  exact vorticityFormTransportResidual_eq_zero_of_vectorVorticity
    ν u hu (PDE.Common.timeSpaceCons t x) (hdiv t x hx) (hvorticity t x hx)

/-- The inviscid vector-vorticity equation reconstructs a jointly continuous
Euler pressure with a time-coherent point normalization. -/
theorem exists_jointly_continuous_normalized_pressure_euler_of_vectorVorticity
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^3} (ha : a ∈ s) (u : ℝ^4 → ℝ^3)
    (hu : ContDiff ℝ 3 u)
    (hdiv : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      vorticityTransportResidual 3 0 u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ,
      Continuous p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
          HasGradientAt (p t)
              (-materialDerivative 3 u u
                (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x = 0 := by
  simpa [NavierStokes.viscousTerm] using
    exists_jointly_continuous_normalized_pressure_navierStokes_of_vectorVorticity
      hs hso ha 0 u hu hdiv hvorticity

/-- A smooth divergence-free three-dimensional vector-vorticity solution reconstructs a jointly
smooth normalized Navier–Stokes pressure. -/
theorem exists_jointly_smooth_normalized_pressure_navierStokes_of_vectorVorticity
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^3} (ha : a ∈ s) (ν : ℝ) (u : ℝ^4 → ℝ^3)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hdiv : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
          HasGradientAt (p t)
              (NavierStokes.viscousTerm 3 ν u
                  (PDE.Common.timeSpaceCons t x) -
                materialDerivative 3 u u
                  (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x =
              NavierStokes.viscousTerm 3 ν u
                (PDE.Common.timeSpaceCons t x) := by
  exact exists_jointly_smooth_normalized_pressure_navierStokes_of_vorticity hs hso ha ν u hu
    fun t x hx ↦ vorticityFormTransportResidual_eq_zero_of_vectorVorticity ν u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) _ (hdiv t x hx) (hvorticity t x hx)

/-- The inviscid specialization reconstructs a jointly smooth normalized Euler pressure. -/
theorem exists_jointly_smooth_normalized_pressure_euler_of_vectorVorticity
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s)
    {a : ℝ^3} (ha : a ∈ s) (u : ℝ^4 → ℝ^3)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hdiv : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
      vorticityTransportResidual 3 0 u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) p.uncurry ∧
        (∀ t : ℝ, p t a = 0) ∧
        ∀ (t : ℝ) (x : ℝ^3), x ∈ s →
          HasGradientAt (p t)
              (-materialDerivative 3 u u
                (PDE.Common.timeSpaceCons t x)) x ∧
            materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
                ∇ (p t) x = 0 := by
  simpa [NavierStokes.viscousTerm] using
    exists_jointly_smooth_normalized_pressure_navierStokes_of_vectorVorticity
      hs hso ha 0 u hu hdiv hvorticity

/-- A locally `C³`, divergence-free velocity satisfying the familiar vector-vorticity
equation admits a slice-wise pressure closing the force-free Navier–Stokes
momentum equation on an open convex spatial domain at each selected time. -/
theorem exists_pressure_navierStokes_momentum_equation_of_vectorVorticity
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s) (I : Set ℝ)
    (ν : ℝ) (u : ℝ^4 → ℝ^3)
    (hu : ∀ t ∈ I, ∀ x ∈ s, ContDiffAt ℝ 3 u (PDE.Common.timeSpaceCons t x))
    (hdiv : ∀ t ∈ I, ∀ x ∈ s,
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ t ∈ I, ∀ x ∈ s,
      vorticityTransportResidual 3 ν u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ, ∀ t ∈ I, ∀ x ∈ s,
      HasGradientAt (p t)
          (NavierStokes.viscousTerm 3 ν u
              (PDE.Common.timeSpaceCons t x) -
            materialDerivative 3 u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
            ∇ (p t) x =
          NavierStokes.viscousTerm 3 ν u
            (PDE.Common.timeSpaceCons t x) := by
  apply exists_pressure_navierStokes_momentum_equation_of_vorticity
    hs hso I ν u hu
  intro t ht x hx
  exact vorticityFormTransportResidual_eq_zero_of_vectorVorticity_of_contDiffAt
    ν u (PDE.Common.timeSpaceCons t x) (hu t ht x hx) (hdiv t ht x hx)
      (hvorticity t ht x hx)

private theorem contDiff_materialDerivative_self
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (materialDerivative n u u) := by
  apply (contDiff_piLp (p := (2 : ENNReal))).2
  intro i
  simp only [materialDerivative_apply]
  apply ContDiff.add
  · exact PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_euclidean.1 hu i)
  · apply ContDiff.sum
    intro k _hk
    exact (contDiff_euclidean.1 hu k).of_le (by norm_num) |>.mul
      (PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_euclidean.1 hu i))

private theorem eulerPressureCandidate_regular_and_closed
    (u : ℝ^4 → ℝ^3) (xt : ℝ^4) (hu : ContDiffAt ℝ 2 u xt)
    (hdiv : DivergenceFreeAt u xt)
    (hvorticity : vorticityTransportResidual 3 0 u (spacetimeSpatialCurl u) xt = 0) :
    ContDiffAt ℝ 1 (fun y ↦ -materialDerivative 3 u u y) xt ∧
      ∀ i j : Fin 3,
        (∂[i.succ] (fun y ↦ (-materialDerivative 3 u u y) j)) xt =
          (∂[j.succ] (fun y ↦ (-materialDerivative 3 u u y) i)) xt := by
  obtain ⟨v, hv, _, huv⟩ := hu.exists_contDiff_compactSupport_eventuallyEq
  have hc : (fun y ↦ -materialDerivative 3 u u y) =ᶠ[𝓝 xt]
      (fun y ↦ -materialDerivative 3 v v y) := by
    filter_upwards [materialDerivative_eventuallyEq huv huv] with y hy
    exact congrArg Neg.neg hy
  have hdivV : DivergenceFreeAt v xt := by
    change spatialDivergence 3 v xt = 0
    rw [← (spatialDivergence_eventuallyEq huv).eq_of_nhds]
    exact hdiv
  have hresV : vorticityTransportResidual 3 0 v (spacetimeSpatialCurl v) xt = 0 := by
    rw [← (vorticityTransportResidual_eventuallyEq 0 huv
      (spacetimeSpatialCurl_eventuallyEq huv)).eq_of_nhds]
    exact hvorticity
  have hvOne : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hres (k : Fin 3) : vorticityTransportResidual 3 0 v (spacetimeSpatialCurl v) xt k = 0 := by
    simpa using congrArg (fun w : ℝ^3 ↦ w k) hresV
  have hdivV' : spatialDivergence 3 v xt = 0 := hdivV
  have hcyclic0 : vorticityFormTransportResidual 3 0 v xt (1, 2) = 0 := by
    rw [vorticityFormTransportResidual_apply_one_two 0 v hvOne xt, hres 0, hdivV']; simp
  have hcyclic1 : vorticityFormTransportResidual 3 0 v xt (2, 0) = 0 := by
    rw [vorticityFormTransportResidual_apply_two_zero 0 v hvOne xt, hres 1, hdivV']; simp
  have hcyclic2 : vorticityFormTransportResidual 3 0 v xt (0, 1) = 0 := by
    rw [vorticityFormTransportResidual_apply_zero_one 0 v hvOne xt, hres 2, hdivV']; simp
  -- Only cyclic pairs are needed; reversed pairs follow by symmetry of equality.
  have hmaterial (i j : Fin 3) :
      (∂[i.succ] (fun y ↦ materialDerivative 3 v v y j)) xt -
          (∂[j.succ] (fun y ↦ materialDerivative 3 v v y i)) xt =
        vorticityFormTransportResidual 3 0 v xt (i, j) := by
    simpa only [vorticityFormTransportResidual_apply, zero_mul, sub_zero] using
      antisymmetric_materialDerivative_eq v hv i j xt
  have h12 := sub_eq_zero.mp ((hmaterial 1 2).trans hcyclic0)
  have h20 := sub_eq_zero.mp ((hmaterial 2 0).trans hcyclic1)
  have h01 := sub_eq_zero.mp ((hmaterial 0 1).trans hcyclic2)
  have hcomm (i j : Fin 3) :
      (∂[i.succ] (fun y ↦ materialDerivative 3 v v y j)) xt =
        (∂[j.succ] (fun y ↦ materialDerivative 3 v v y i)) xt := by
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01
    · exact h20.symm
    · exact h01.symm
    · rfl
    · exact h12
    · exact h20
    · exact h12.symm
    · rfl
  constructor
  · exact (contDiff_materialDerivative_self v hv).neg.contDiffAt.congr_of_eventuallyEq hc
  · intro i j
    have hi := (hc.fun_comp (fun z ↦ z j)).partialDeriv i.succ |>.eq_of_nhds
    have hj := (hc.fun_comp (fun z ↦ z i)).partialDeriv j.succ |>.eq_of_nhds
    dsimp only [Function.comp_def] at hi hj
    rw [hi, hj]
    change (∂[i.succ] (-(fun y ↦ materialDerivative 3 v v y j))) xt =
      (∂[j.succ] (-(fun y ↦ materialDerivative 3 v v y i))) xt
    simpa only [PDE.partialDeriv_neg] using congrArg Neg.neg (hcomm i j)

/-- A locally `C²` velocity with zero divergence and vanishing Euler transport residual
for its curl admits pressure on each open convex spatial slice.

The pressure is chosen independently on each time slice. -/
theorem exists_pressure_euler_momentum_equation_of_vectorVorticity_of_contDiffAt_two
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s) (I : Set ℝ)
    (u : ℝ^4 → ℝ^3)
    (hu : ∀ t ∈ I, ∀ x ∈ s, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons t x))
    (hdiv : ∀ t ∈ I, ∀ x ∈ s,
      DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hvorticity : ∀ t ∈ I, ∀ x ∈ s,
      vorticityTransportResidual 3 0 u (spacetimeSpatialCurl u)
        (PDE.Common.timeSpaceCons t x) = 0) :
    ∃ p : ℝ → ℝ^3 → ℝ, ∀ t ∈ I, ∀ x ∈ s,
      HasGradientAt (p t)
          (-materialDerivative 3 u u (PDE.Common.timeSpaceCons t x)) x ∧
        materialDerivative 3 u u (PDE.Common.timeSpaceCons t x) +
          ∇ (p t) x = 0 := by
  classical
  let candidate : ℝ^4 → ℝ^3 := fun y ↦ -materialDerivative 3 u u y
  have hcandidate (t : ℝ) (ht : t ∈ I) (x : ℝ^3) (hx : x ∈ s) :
      ContDiffAt ℝ 1 candidate (PDE.Common.timeSpaceCons t x) ∧
        ∀ i j : Fin 3,
          (∂[i.succ] (fun y ↦ candidate y j)) (PDE.Common.timeSpaceCons t x) =
            (∂[j.succ] (fun y ↦ candidate y i)) (PDE.Common.timeSpaceCons t x) :=
    eulerPressureCandidate_regular_and_closed u (PDE.Common.timeSpaceCons t x)
      (hu t ht x hx) (hdiv t ht x hx) (hvorticity t ht x hx)
  have hpotential (t : ℝ) (ht : t ∈ I) :
      ∃ p : ℝ^3 → ℝ, ∀ x ∈ s,
        HasGradientAt p (candidate (PDE.Common.timeSpaceCons t x)) x := by
    apply EuclideanSpace.exists_potential_of_partialDeriv_comm hs hso
    · intro x hx
      exact ((hcandidate t ht x hx).1.comp x
        (PDE.Common.contDiff_timeSpaceCons_spatial 3 t).contDiffAt).differentiableAt
          (by norm_num) |>.differentiableWithinAt
    · intro x hx i j
      have hi := PDE.partialDeriv_timeSpaceCons_spatial i (fun y ↦ candidate y j) t x
        (((contDiffAt_piLp (p := (2 : ENNReal))).1 (hcandidate t ht x hx).1 j).differentiableAt
          (by norm_num))
      have hj := PDE.partialDeriv_timeSpaceCons_spatial j (fun y ↦ candidate y i) t x
        (((contDiffAt_piLp (p := (2 : ENNReal))).1 (hcandidate t ht x hx).1 i).differentiableAt
          (by norm_num))
      exact hi.trans (((hcandidate t ht x hx).2 i j).trans hj.symm)
  choose! p hp using hpotential
  refine ⟨p, fun t ht x hx ↦ ⟨hp t ht x hx, ?_⟩⟩
  rw [(hp t ht x hx).gradient]
  exact add_neg_cancel _

end

end IncompressibleFlow
