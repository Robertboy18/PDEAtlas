/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Energy slices for reactions not differentiable at zero

Local inversion of the time path forces the velocity to vanish at zeros of
a C³ solution. Compact displacement then gives compact velocity and
integrable physical energy at an interior time. The equation is used only
on a time neighborhood, with no equation assumed for an extension.

With a spacetime equation germ, inversion along arbitrary affine lines gives
the full zero first jet. The time-germ theorem retains its weaker hypotheses.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common
open scoped Topology

namespace WaveEquation

/-- A nonzero derivative of the inner scalar function detects differentiability
of the outer function from differentiability of the composition. -/
private theorem differentiableAt_of_comp_of_deriv_ne_zero {f g : ℝ → ℝ} {a : ℝ}
    (hg : ContDiffAt ℝ 1 g a) (hfg : DifferentiableAt ℝ (f ∘ g) a) (hg' : deriv g a ≠ 0) :
    DifferentiableAt ℝ f (g a) := by
  have hs := hg.hasStrictDerivAt (by norm_num)
  let v := hs.localInverse g (deriv g a) a hg'
  have hv : v (g a) = a := (hs.hasStrictFDerivAt_equiv hg').localInverse_apply_image
  have hfg' : DifferentiableAt ℝ (f ∘ g) (v (g a)) := by
    rw [hv]
    exact hfg
  have hc := hfg'.comp (g a) (hs.to_localInverse hg').hasDerivAt.differentiableAt
  apply hc.congr_of_eventuallyEq
  exact (hs.eventually_right_inverse hg').mono fun y hy ↦ (congrArg f hy).symm

/-- Nondifferentiability of the reaction forces the full first derivative to
vanish at a zero of a C³ solution of the equation on a spacetime neighborhood. -/
theorem fderiv_eq_zero_of_not_differentiable_reaction {n : ℕ} {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hf : ¬ DifferentiableAt ℝ f 0) (hu : ContDiffAt ℝ 3 u p)
    (hwave : ∀ᶠ q in 𝓝 p, waveOperator u q + f (u q) = 0) (hzero : u p = 0) :
    fderiv ℝ u p = 0 := by
  have hsecond (i : Fin (n + 1)) : ContDiffAt ℝ 1 (∂[i] (∂[i] u)) p :=
    (hu.partialDeriv i (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).partialDeriv i le_rfl
  have hop : ContDiffAt ℝ 1 (waveOperator u) p :=
    (hsecond 0).sub (ContDiffAt.sum fun i _ ↦ hsecond i.succ)
  have hcomp : DifferentiableAt ℝ (f ∘ u) p := by
    apply (hop.neg.differentiableAt one_ne_zero).congr_of_eventuallyEq
    exact hwave.mono fun q hq ↦ eq_neg_of_add_eq_zero_right hq
  ext v
  change fderiv ℝ u p v = 0
  by_contra hv
  have hpath : ContDiff ℝ 1 (fun s : ℝ ↦ p + s • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hpath' : HasDerivAt (fun s : ℝ ↦ p + s • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hdu : HasFDerivAt u (fderiv ℝ u p) (p + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      (hu.differentiableAt (by norm_num)).hasFDerivAt
  have hg' : deriv (fun s : ℝ ↦ u (p + s • v)) 0 = fderiv ℝ u p v :=
    (hdu.comp_hasDerivAt 0 hpath').deriv
  have hu1 : ContDiffAt ℝ 1 u (p + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hcomp' : DifferentiableAt ℝ (f ∘ u) (p + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hcomp
  have hfg : DifferentiableAt ℝ (f ∘ fun s : ℝ ↦ u (p + s • v)) 0 :=
    hcomp'.comp (f := fun s : ℝ ↦ p + s • v) 0 (hpath.differentiable one_ne_zero).differentiableAt
  have hd := differentiableAt_of_comp_of_deriv_ne_zero (hu1.comp 0 hpath.contDiffAt) hfg (hg' ▸ hv)
  exact hf (by simpa only [Function.comp_apply, zero_smul, add_zero, hzero] using hd)

/-- A reaction not differentiable at zero forces zero time derivative at a
zero of a C³ field, if the equation holds on a time neighborhood of that point. -/
theorem time_partial_eq_zero_of_not_differentiable_reaction {n : ℕ} {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {t : ℝ} {x : ℝ^n} (hf : ¬ DifferentiableAt ℝ f 0) (hu : ContDiffAt ℝ 3 u (timeSpaceCons t x))
    (hwave : ∀ᶠ s in 𝓝 t, waveOperator u (timeSpaceCons s x) + f (u (timeSpaceCons s x)) = 0)
    (hzero : u (timeSpaceCons t x) = 0) :
    (∂[0] u) (timeSpaceCons t x) = 0 := by
  have hsecond (i : Fin (n + 1)) : ContDiffAt ℝ 1 (∂[i] (∂[i] u)) (timeSpaceCons t x) :=
    (hu.partialDeriv i (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).partialDeriv i le_rfl
  have hop : ContDiffAt ℝ 1 (waveOperator u) (timeSpaceCons t x) :=
    (hsecond 0).sub (ContDiffAt.sum fun i _ ↦ hsecond i.succ)
  have hpath : ContDiff ℝ 1 (fun s ↦ timeSpaceCons s x) :=
    (contDiff_timeSpaceCons_uncurry n).comp (contDiff_id.prodMk contDiff_const)
  have hcomp : DifferentiableAt ℝ (fun s ↦ f (u (timeSpaceCons s x))) t := by
    apply ((hop.neg.comp t hpath.contDiffAt).differentiableAt one_ne_zero).congr_of_eventuallyEq
    exact hwave.mono fun s hs ↦ eq_neg_of_add_eq_zero_right hs
  by_contra hne
  have hg' : deriv (fun s ↦ u (timeSpaceCons s x)) t ≠ 0 := by
    rw [← partialDeriv_timeSpaceCons_eq_deriv u x t (hu.differentiableAt (by norm_num))]
    exact hne
  have hdf := differentiableAt_of_comp_of_deriv_ne_zero
    ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp t hpath.contDiffAt) hcomp hg'
  exact hf (hzero ▸ hdf)

/-- Compact displacement gives compact velocity when the reaction is not
differentiable at zero and the equation holds locally in time at the slice. -/
theorem hasCompactSupport_time_partial_of_not_differentiable_reaction {n : ℕ} {f : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hf : ¬ DifferentiableAt ℝ f 0) (t : ℝ)
    (hu : ∀ x, ContDiffAt ℝ 3 u (timeSpaceCons t x))
    (hwave : ∀ x, ∀ᶠ s in 𝓝 t, waveOperator u (timeSpaceCons s x) + f (u (timeSpaceCons s x)) = 0)
    (hs : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    HasCompactSupport (fun x : ℝ^n ↦ (∂[0] u) (timeSpaceCons t x)) := by
  refine HasCompactSupport.intro hs.isCompact fun x hx ↦ ?_
  exact time_partial_eq_zero_of_not_differentiable_reaction hf (hu x) (hwave x)
    (image_eq_zero_of_notMem_tsupport (f := fun y : ℝ^n ↦ u (timeSpaceCons t y)) hx)

/-- In the nondifferentiable-reaction branch, each compact displacement slice
has integrable energy density for every continuous potential vanishing at zero. -/
theorem integrable_semilinearWaveSpatialEnergyDensity_of_not_differentiable_reaction {n : ℕ}
    {f V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hf : ¬ DifferentiableAt ℝ f 0) (hV : Continuous V)
    (hVzero : V 0 = 0) (t : ℝ) (hu : ∀ x, ContDiffAt ℝ 3 u (timeSpaceCons t x))
    (hwave : ∀ x, ∀ᶠ s in 𝓝 t, waveOperator u (timeSpaceCons s x) + f (u (timeSpaceCons s x)) = 0)
    (hs : HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) :
    Integrable (semilinearWaveSpatialEnergyDensity V u t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have hmap : Continuous (fun x : ℝ^n ↦ timeSpaceCons t x) :=
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_const.prodMk continuous_id)
    refine continuous_iff_continuousAt.mpr fun x ↦ ?_
    exact (contDiffAt_semilinearWaveEnergyDensity (contDiff_zero.mpr hV).contDiffAt
      ((hu x).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))).continuousAt.comp hmap.continuousAt
  · refine HasCompactSupport.intro hs.isCompact fun x hx ↦ ?_
    have hz := image_eq_zero_of_notMem_tsupport hx
    have ht := time_partial_eq_zero_of_not_differentiable_reaction hf (hu x) (hwave x) hz
    have hg : classicalWaveSpatialGradient u (timeSpaceCons t x) = 0 := by
      ext i
      change (∂[i.succ] u) (timeSpaceCons t x) = 0
      rw [← partialDeriv_timeSpaceCons_spatial i u t x ((hu x).differentiableAt (by norm_num))]
      simp only [PDE.partialDeriv, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
    simp only [semilinearWaveSpatialEnergyDensity,
      semilinearWaveEnergyDensity, classicalWaveEnergyDensity,
      ht, hg, hz, hVzero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero]

end WaveEquation
