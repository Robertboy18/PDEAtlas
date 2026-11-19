/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Radial.SquaredRadius
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The joint Laplacian at a radial axis

For a joint C² profile `Φ(s,z)`, the lift `Φ(|y|²,z)` is C² even when `y = 0`.
The coordinate chain rule identifies its Laplacian there with
`n ∂rr Φ(r²,z)|_{r=0} + ∂zz Φ(0,z)`. Joint C² regularity also makes the
axial second derivative continuous as the radius tends to zero.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Radial

open Filter
open scoped Topology Laplacian

/-- Two derivatives of an axial slice are the axial entry of the joint Hessian. -/
theorem secondDeriv_snd_eq_fderiv (Φ : ℝ → ℝ → ℝ) (s z : ℝ)
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (s, z)) :
    deriv (deriv (fun ζ ↦ Φ s ζ)) z =
      fderiv ℝ (fun p ↦ fderiv ℝ (Function.uncurry Φ) p (0, 1)) (s, z) (0, 1) := by
  let dΦ : ℝ × ℝ → ℝ := fun p ↦ fderiv ℝ (Function.uncurry Φ) p (0, 1)
  have hdΦ : ContDiffAt ℝ 1 dΦ (s, z) :=
    (hΦ.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hnear : ∀ᶠ ζ in 𝓝 z, ContDiffAt ℝ 2 (Function.uncurry Φ) (s, ζ) :=
    (continuous_const.prodMk continuous_id).continuousAt.eventually (hΦ.eventually (by simp))
  have hfirst : deriv (fun ζ ↦ Φ s ζ) =ᶠ[𝓝 z] fun ζ ↦ dΦ (s, ζ) := by
    filter_upwards [hnear] with ζ hζ
    exact (hζ.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt ζ
      ((hasDerivAt_const ζ s).prodMk (hasDerivAt_id ζ))).deriv
  rw [hfirst.deriv_eq]
  exact (hdΦ.differentiableAt_one.hasFDerivAt.comp_hasDerivAt z
    ((hasDerivAt_const z s).prodMk (hasDerivAt_id z))).deriv

/-- The second axial derivative is jointly continuous wherever the profile is C². -/
theorem continuousAt_secondDeriv_snd (Φ : ℝ → ℝ → ℝ) (s z : ℝ)
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (s, z)) :
    ContinuousAt (fun p : ℝ × ℝ ↦ deriv (deriv (fun ζ ↦ Φ p.1 ζ)) p.2) (s, z) := by
  have hdΦ : ContDiffAt ℝ 1
      (fun p ↦ fderiv ℝ (Function.uncurry Φ) p (0, 1)) (s, z) :=
    (hΦ.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  have hddΦ : ContDiffAt ℝ 0
      (fun p ↦ fderiv ℝ (fun q ↦ fderiv ℝ (Function.uncurry Φ) q (0, 1)) p (0, 1))
      (s, z) :=
    (hdΦ.fderiv_right (by norm_num)).clm_apply contDiffAt_const
  apply hddΦ.continuousAt.congr
  filter_upwards [hΦ.eventually (by simp)] with p hp
  exact (secondDeriv_snd_eq_fderiv Φ p.1 p.2 hp).symm

/-- Lift a squared-radius profile to `n` transverse coordinates and one axial coordinate. -/
def squaredRadiusLift (n : ℕ) (Φ : ℝ → ℝ → ℝ) (X : ℝ^(n + 1)) : ℝ :=
  Φ (∑ i : Fin n, (X i.castSucc) ^ 2) (X (Fin.last n))

/-- Joint C² regularity of the profile gives joint C² regularity of its Cartesian lift. -/
theorem contDiffAt_squaredRadiusLift (n : ℕ) (Φ : ℝ → ℝ → ℝ) (X : ℝ^(n + 1))
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ)
      (∑ i : Fin n, (X i.castSucc) ^ 2, X (Fin.last n))) :
    ContDiffAt ℝ 2 (squaredRadiusLift n Φ) X := by
  apply hΦ.comp (f := fun Y : ℝ^(n + 1) ↦
    (∑ i : Fin n, (Y i.castSucc) ^ 2, Y (Fin.last n))) X
  have hcoord (i : Fin (n + 1)) : ContDiffAt ℝ 2 (fun Y : ℝ^(n + 1) ↦ Y i) X :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) ↦ ℝ) i).contDiff.contDiffAt
  exact (ContDiffAt.sum fun i _ ↦ (hcoord i.castSucc).pow 2).prodMk (hcoord (Fin.last n))

/-- A squared-radius lift is C² at the axis under a local joint C² hypothesis. -/
theorem contDiffAt_squaredRadiusLift_axis (n : ℕ) (Φ : ℝ → ℝ → ℝ) (z : ℝ)
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (0, z)) :
    ContDiffAt ℝ 2 (squaredRadiusLift n Φ) (EuclideanSpace.single (Fin.last n) z) := by
  apply contDiffAt_squaredRadiusLift
  simpa using hΦ

/-- Each transverse coordinate contributes the same radial second derivative at the axis. -/
theorem laplacian_squaredRadiusLift_axis (n : ℕ) (Φ : ℝ → ℝ → ℝ) (z : ℝ)
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (0, z)) :
    laplacian (squaredRadiusLift n Φ) (EuclideanSpace.single (Fin.last n) z) =
      (n : ℝ) * deriv (deriv (fun r ↦ Φ (r ^ 2) z)) 0 +
        deriv (deriv (fun ζ ↦ Φ 0 ζ)) z := by
  let a : ℝ^(n + 1) := EuclideanSpace.single (Fin.last n) z
  have hF := contDiffAt_squaredRadiusLift_axis n Φ z hΦ
  have hline (i : Fin (n + 1)) :
      (∂[i] (∂[i] (squaredRadiusLift n Φ))) a =
        deriv (deriv (squaredRadiusLift n Φ ∘ coordinateLine i a)) (a i) := by
    simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
      iteratedDeriv_succ, iteratedDeriv_zero] using
      iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at i 2 hF
  have htransverse (i : Fin n) :
      squaredRadiusLift n Φ ∘ coordinateLine i.castSucc a = fun r ↦ Φ (r ^ 2) z := by
    funext r
    simp [squaredRadiusLift, coordinateLine, a, PiLp.single_apply, Finset.sum_ite_eq']
  have haxial :
      squaredRadiusLift n Φ ∘ coordinateLine (Fin.last n) a = fun ζ ↦ Φ 0 ζ := by
    funext ζ
    simp [squaredRadiusLift, coordinateLine, a]
  change laplacian (squaredRadiusLift n Φ) a = _
  unfold laplacian
  rw [Fin.sum_univ_castSucc]
  simp only [hline, htransverse, haxial]
  simp [a]

/-- The canonical Euclidean Laplacian splits into the transverse Laplacian and
the axial second derivative at the axis. -/
theorem canonicalLaplacian_squaredRadiusLift_axis
    (n : ℕ) (Φ : ℝ → ℝ → ℝ) (z : ℝ)
    (hΦ : ContDiffAt ℝ 2 (Function.uncurry Φ) (0, z)) :
    Δ (squaredRadiusLift n Φ) (EuclideanSpace.single (Fin.last n) z) =
      laplacian (fun y : ℝ^n ↦ Φ (‖y‖ ^ 2) z) 0 +
        deriv (deriv (fun ζ ↦ Φ 0 ζ)) z := by
  have hslice : ContDiffAt ℝ 2 (fun s ↦ Φ s z) 0 :=
    hΦ.comp (f := fun s : ℝ ↦ (s, z)) 0 (by fun_prop)
  rw [← (contDiffAt_squaredRadiusLift_axis n Φ z hΦ).coordinate_laplacian_eq_laplacian,
    laplacian_squaredRadiusLift_axis n Φ z hΦ,
    laplacian_comp_norm_sq_zero n (fun s ↦ Φ s z) hslice]

end PDE.Elliptic.Radial
