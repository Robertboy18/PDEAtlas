/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.LpNorm
public import PDE.FDeriv.Calculus
public import PDE.Hyperbolic.Models.Wave.Strichartz.InitialEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Physical initial energy for real wave data

The Fourier input used by the wave estimates has exactly the energy of the
initial displacement gradient and velocity. Real-to-complex inclusion preserves
these norms, and the Fourier convention's factor of `2π` is already accounted
for by Plancherel. No norm of the displacement itself is needed.
-/

@[expose] public section
open MeasureTheory LineDeriv PDE
open scoped SchwartzMap

namespace WaveEquation.Strichartz

private theorem norm_lineDeriv_real_complex (g : 𝓢(ℝ^3, ℝ)) (i : Fin 3) (x : ℝ^3) :
    ‖∂_{EuclideanSpace.basisFun (Fin 3) ℝ i}
      (g.postcompCLM Complex.ofRealCLM) x‖ ^ 2 = (∂[i] (g : ℝ^3 → ℝ)) x ^ 2 := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, EuclideanSpace.basisFun_apply]
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (g.hasFDerivAt x)
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hd
  change ‖fderiv ℝ (fun y ↦ (g y : ℂ)) x (EuclideanSpace.single i 1)‖ ^ 2 = _
  rw [hd.fderiv]
  simp [ContinuousLinearMap.comp_apply, partialDeriv]

/-- For real initial data, the squared Fourier input norm is the sum of the
squared physical L² norms of the displacement gradient and velocity. -/
theorem norm_initialEnergyDatum_real_sq (g h : 𝓢(ℝ^3, ℝ)) :
    ‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM)‖ ^ 2 =
      lpNorm (fderiv ℝ g) 2 volume ^ 2 + lpNorm h 2 volume ^ 2 := by
  rw [norm_initialEnergyDatum_sq (EuclideanSpace.basisFun (Fin 3) ℝ)]
  have hi (i : Fin 3) (_ : i ∈ Finset.univ) :
      Integrable (fun x ↦ ‖∂_{EuclideanSpace.basisFun (Fin 3) ℝ i}
        (g.postcompCLM Complex.ofRealCLM) x‖ ^ 2) := ((∂_{EuclideanSpace.basisFun (Fin 3) ℝ i}
      (g.postcompCLM Complex.ofRealCLM)).memLp 2 volume).integrable_norm_pow (by norm_num)
  -- In Euclidean coordinates, the squared scalar differential norm is the
  -- sum of the squared coordinate derivatives.
  rw [← integral_finsetSum Finset.univ hi]
  have he : (fun x ↦ ∑ i : Fin 3, ‖∂_{EuclideanSpace.basisFun (Fin 3) ℝ i}
      (g.postcompCLM Complex.ofRealCLM) x‖ ^ 2) = fun x ↦ ‖fderiv ℝ g x‖ ^ 2 := by
    funext x
    simp only [norm_lineDeriv_real_complex]
    exact (norm_fderiv_sq_eq_sum_partialDeriv_sq g.differentiableAt).symm
  rw [he]
  have hd : MemLp (fderiv ℝ g) 2 volume := (SchwartzMap.fderivCLM ℝ (ℝ^3) ℝ g).memLp 2 volume
  have hg := hd.norm.integral_sq_eq_lpNorm_sq
  have hh := (h.memLp 2 volume).integral_sq_eq_lpNorm_sq
  simpa [lpNorm_norm hd.aestronglyMeasurable, SchwartzMap.postcompCLM_apply]
    using congrArg₂ (· + ·) hg hh

/-- The usual sum of the two physical initial-data norms bounds the Fourier
energy input used by the homogeneous and inhomogeneous wave estimates. -/
theorem norm_initialEnergyDatum_real_le (g h : 𝓢(ℝ^3, ℝ)) :
    ‖initialEnergyDatum (g.postcompCLM Complex.ofRealCLM) (h.postcompCLM Complex.ofRealCLM)‖ ≤
      lpNorm (fderiv ℝ g) 2 volume + lpNorm h 2 volume := by
  have hg : 0 ≤ lpNorm (fderiv ℝ g) 2 volume := lpNorm_nonneg
  have hh : 0 ≤ lpNorm h 2 volume := lpNorm_nonneg
  have hn := norm_nonneg (initialEnergyDatum (g.postcompCLM Complex.ofRealCLM)
    (h.postcompCLM Complex.ofRealCLM))
  nlinarith [norm_initialEnergyDatum_real_sq g h, mul_nonneg hg hh]

end WaveEquation.Strichartz
