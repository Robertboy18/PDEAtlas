/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.ClassicalSolution
public import PDE.Analysis.Calculus.SphericalMean.ContinuousFamily
public import PDE.Analysis.Calculus.Radial.WeightedDerivative.ContinuousFamily

/-!
# Continuously indexed odd-dimensional waves

Joint continuity of the data's finite spatial jets passes to the
center and signed-age derivatives of the wave potential and Cauchy solution.
The index needs no differentiability, and age zero uses the same transform.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common

variable {A : Type*} [TopologicalSpace A] [FirstCountableTopology A]

/-- The Cauchy formula retains `s` derivatives from displacement data
of order `k+s+1` and velocity data of order `k+s`. -/
theorem contDiff_oddWaveSolution (k s : ℕ) {g h : ℝ^(2 * k + 3) → ℝ}
    (hg : ContDiff ℝ (k + (s + 1)) g) (hh : ContDiff ℝ (k + s) h) :
    ContDiff ℝ s (oddWaveSolution k g h) := by
  unfold oddWaveSolution
  exact contDiff_const.mul
    ((PDE.contDiff_partialDeriv_of_succ (contDiff_oddWavePotential k (s + 1) hg)).add
      (contDiff_oddWavePotential k s hh))

/-- The spherical profile loses at most `k` spatial derivatives in a continuous family. -/
theorem continuous_iteratedFDeriv_oddSphericalProfile_family (k s : ℕ) {f : A → ℝ^(2 * k + 3) → ℝ}
    (hf : ∀ a, ContDiff ℝ (k + s) (f a))
    (hjet : ∀ j ≤ k + s, Continuous (fun p : A × ℝ^(2 * k + 3) ↦ iteratedFDeriv ℝ j (f p.1) p.2)) :
    Continuous (fun p : A × (ℝ^(2 * k + 3) × ℝ) ↦ iteratedFDeriv ℝ s
      (fun q : ℝ^(2 * k + 3) × ℝ ↦ oddSphericalProfile k (f p.1) q.1 q.2) p.2) :=
  continuous_iteratedFDeriv_oddRadialTransform_pow_mul_family k s
    (fun a ↦ contDiff_unitSphereAverage (hf a))
    (fun _ hj ↦ continuous_iteratedFDeriv_unitSphereAverage_family hf hjet hj)

/-- The canonical spacetime jets are jointly continuous in the data index too. -/
theorem continuous_iteratedFDeriv_oddWavePotential_family (k s : ℕ) {f : A → ℝ^(2 * k + 3) → ℝ}
    (hf : ∀ a, ContDiff ℝ (k + s) (f a))
    (hjet : ∀ j ≤ k + s, Continuous (fun p : A × ℝ^(2 * k + 3) ↦ iteratedFDeriv ℝ j (f p.1) p.2)) :
    Continuous (fun p : A × ℝ^(2 * k + 3 + 1) ↦
      iteratedFDeriv ℝ s (oddWavePotential k (f p.1)) p.2) :=
  PDE.continuous_iteratedFDeriv_comp_linear_family
    (L := fun _ ↦ (spaceTimeContinuousLinearEquiv (2 * k + 3)).toContinuousLinearMap)
    (fun a ↦ contDiff_oddSphericalProfile k s (hf a))
      (continuous_iteratedFDeriv_oddSphericalProfile_family k s hf hjet) continuous_const

/-- The odd-dimensional solution preserves continuous finite data jets,
with one additional derivative required of the displacement data. -/
theorem continuous_iteratedFDeriv_oddWaveSolution_family (k s : ℕ) {g h : A → ℝ^(2 * k + 3) → ℝ}
    (hg : ∀ a, ContDiff ℝ (k + (s + 1)) (g a)) (hh : ∀ a, ContDiff ℝ (k + s) (h a))
    (hgj : ∀ j ≤ k + (s + 1),
      Continuous (fun p : A × ℝ^(2 * k + 3) ↦ iteratedFDeriv ℝ j (g p.1) p.2))
    (hhj : ∀ j ≤ k + s, Continuous (fun p : A × ℝ^(2 * k + 3) ↦ iteratedFDeriv ℝ j (h p.1) p.2)) :
    Continuous (fun p : A × ℝ^(2 * k + 3 + 1) ↦
      iteratedFDeriv ℝ s (oddWaveSolution k (g p.1) (h p.1)) p.2) := by
  have hgc (a : A) : ContDiff ℝ (s + 1) (oddWavePotential k (g a)) :=
    contDiff_oddWavePotential k (s + 1) (hg a)
  have hgp (a : A) : ContDiff ℝ s (∂[0] (oddWavePotential k (g a))) :=
    PDE.contDiff_partialDeriv_of_succ (hgc a)
  have hhc (a : A) : ContDiff ℝ s (oddWavePotential k (h a)) := contDiff_oddWavePotential k s (hh a)
  have hDg := PDE.continuous_iteratedFDeriv_fderiv_apply_family
    (f := fun a ↦ oddWavePotential k (g a)) hgc
    (continuous_iteratedFDeriv_oddWavePotential_family k (s + 1) hg hgj)
    (EuclideanSpace.single 0 (1 : ℝ))
  have hDh := continuous_iteratedFDeriv_oddWavePotential_family k s hh hhj
  change Continuous (fun p : A × ℝ^(2 * k + 3 + 1) ↦ iteratedFDeriv ℝ s
    (fun q ↦ (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹ •
      ((∂[0] (oddWavePotential k (g p.1))) q + oddWavePotential k (h p.1) q)) p.2)
  simp_rw [iteratedFDeriv_const_smul_apply' ((hgp _).add (hhc _)).contDiffAt,
    fun_iteratedFDeriv_add_apply (hgp _).contDiffAt (hhc _).contDiffAt]
  exact (hDg.add hDh).const_smul (Nat.doubleFactorial (2 * k + 1) : ℝ)⁻¹

end WaveEquation
