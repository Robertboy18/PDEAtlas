/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.WeightedDerivative.ParameterDerivative
public import PDE.Analysis.Calculus.Radial.WeightedDerivative.Linearity
public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Hyperbolic.Models.Wave.OddDimensions

/-!
# Regularity and spatial derivatives of odd-dimensional wave profiles

Spherical averaging preserves finite joint regularity. The weighted radial
transform then loses one derivative per iteration, including at radius zero.
Spatial derivatives commute with both operations at the exact finite order.
The data need no support or growth restrictions.
-/

@[expose] public noncomputable section

open PDE (partialDeriv laplacian)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The odd-dimensional profile loses exactly the transform order in joint
space and signed-time regularity. -/
theorem contDiff_oddSphericalProfile (k s : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + s) f) :
    ContDiff ℝ s (fun p : ℝ^(2 * k + 3) × ℝ ↦ oddSphericalProfile k f p.1 p.2) :=
  contDiff_oddRadialTransform_pow_mul k s (contDiff_unitSphereAverage hf)

/-- A spatial derivative commutes with the transformed spherical mean at
every signed radius, using only `k+1` derivatives of the data. -/
theorem partialDeriv_oddSphericalProfile (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + 1) f)
    (i : Fin (2 * k + 3)) (x : ℝ^(2 * k + 3)) (r : ℝ) :
    (∂[i] (fun y ↦ oddSphericalProfile k f y r)) x = oddSphericalProfile k (∂[i] f) x r := by
  unfold partialDeriv oddSphericalProfile
  rw [fderiv_oddRadialTransform_pow_mul k (contDiff_unitSphereAverage hf)]
  congr 2
  funext s
  congr 1
  exact partialDeriv_unitSphereAverage (hf.of_le (by norm_cast; omega)) i x s

/-- Two spatial derivatives commute with the profile for `k+2` derivatives
of the data. No `C³` hypothesis on the transformed profile is needed. -/
theorem secondPartialDeriv_oddSphericalProfile (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ}
    (hf : ContDiff ℝ (k + 2) f) (i j : Fin (2 * k + 3)) (x : ℝ^(2 * k + 3)) (r : ℝ) :
    (∂[i] (∂[j] (fun y ↦ oddSphericalProfile k f y r))) x =
      oddSphericalProfile k (∂[i] (∂[j] f)) x r := by
  have hdf : ContDiff ℝ (k + 1) (∂[j] f) := by
    apply PDE.contDiff_partialDeriv_of_succ (m := k + 1)
    convert hf using 1
    push_cast
    ring
  have he : (∂[j] (fun y ↦ oddSphericalProfile k f y r)) =
      fun y ↦ oddSphericalProfile k (∂[j] f) y r := by
    funext y
    exact partialDeriv_oddSphericalProfile k (hf.of_le (by norm_cast; omega)) j y r
  rw [he, partialDeriv_oddSphericalProfile k hdf]

/-- The spatial Laplacian commutes with the odd-dimensional profile at its
sharp finite differentiability budget. -/
theorem laplacian_oddSphericalProfile (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + 2) f)
    (x : ℝ^(2 * k + 3)) (r : ℝ) :
    laplacian (fun y ↦ oddSphericalProfile k f y r) x =
      oddSphericalProfile k (laplacian f) x r := by
  have hf₂ : ContDiff ℝ 2 f := hf.of_le (by norm_cast; omega)
  have hdf (i : Fin (2 * k + 3)) : ContDiff ℝ (k + 1) (∂[i] f) := by
    apply PDE.contDiff_partialDeriv_of_succ (m := k + 1)
    convert hf using 1
    push_cast
    ring
  have hddf (i : Fin (2 * k + 3)) : ContDiff ℝ k (∂[i] (∂[i] f)) :=
    PDE.contDiff_partialDeriv_of_succ (m := k) (hdf i)
  have hmean (i : Fin (2 * k + 3)) : ContDiff ℝ k (fun s ↦ unitSphereAverage (2 * k + 3)
        (∂[i] (∂[i] f)) x s) :=
    (contDiff_unitSphereAverage (hddf i)).comp (contDiff_const.prodMk contDiff_id)
  have hsum (s : ℝ) : (∑ i : Fin (2 * k + 3), unitSphereAverage (2 * k + 3) (∂[i] (∂[i] f)) x s) =
        unitSphereAverage (2 * k + 3) (laplacian f) x s := by
    rw [← laplacian_unitSphereAverage hf₂]
    unfold laplacian
    simp_rw [partialDeriv_unitSphereAverage (hf₂.of_le (by norm_num)),
      partialDeriv_unitSphereAverage (PDE.contDiff_partialDeriv_of_succ (m := 1) hf₂)]
  unfold laplacian
  simp_rw [secondPartialDeriv_oddSphericalProfile k hf]
  change (∑ i : Fin (2 * k + 3), oddRadialTransform k
    (fun s ↦ s ^ (2 * k + 1) * unitSphereAverage (2 * k + 3) (∂[i] (∂[i] f)) x s) r) = _
  rw [← oddRadialTransform_pow_mul_sum k Finset.univ (fun i _ ↦ hmean i)]
  simp_rw [hsum]
  rfl

end WaveEquation
