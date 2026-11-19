/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution

/-!
# Restricting a Kirchhoff potential to a coordinate line

The three-dimensional wave equation also constructs one-dimensional equations
with a potential. If the transverse Laplacian of the initial velocity is the
velocity itself, restriction to a coordinate line gives `v_tt - v_yy - v = 0`.
Spherical averaging commutes with the spatial derivatives, so this reduction
needs no decay assumption or uniqueness theorem.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE PDE.Analysis PDE.Common MeasureTheory

/-- The Kirchhoff potential on a fixed coordinate line, with time first. -/
def kirchhoffLine (f : ℝ^3 → ℝ) (i : Fin 3) (x : ℝ^3) (t y : ℝ) : ℝ :=
  t * unitSphereAverage 3 f (coordinateLine i x y) t

/-- The line restriction has the joint finite regularity of its initial data. -/
theorem contDiff_kirchhoffLine {k : ℕ} {f : ℝ^3 → ℝ} (hf : ContDiff ℝ k f) (i : Fin 3) (x : ℝ^3) :
    ContDiff ℝ k (fun p : ℝ × ℝ ↦ kirchhoffLine f i x p.1 p.2) := by
  have hl : ContDiff ℝ k (coordinateLine i x) :=
    (contDiff_coordinateLine i x).of_le (by simp)
  exact contDiff_fst.mul ((contDiff_unitSphereAverage hf).comp
    ((hl.comp contDiff_snd).prodMk contDiff_fst))

/-- The initial displacement of the line restriction is zero. -/
@[simp]
theorem kirchhoffLine_initial (f : ℝ^3 → ℝ) (i : Fin 3) (x : ℝ^3) (y : ℝ) :
    kirchhoffLine f i x 0 y = 0 := by
  simp [kirchhoffLine]

/-- Its initial velocity is the restriction of the prescribed velocity data. -/
theorem deriv_kirchhoffLine_initial {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 1 f)
    (i : Fin 3) (x : ℝ^3) (y : ℝ) :
    deriv (fun t ↦ kirchhoffLine f i x t y) 0 = f (coordinateLine i x y) := by
  simpa [kirchhoffLine] using ((hasDerivAt_id (0 : ℝ)).fun_mul
    (hasDerivAt_unitSphereAverage f (coordinateLine i x y) 0 hf)).deriv

/-- Twice differentiating the line parameter averages the corresponding
second coordinate derivative of the initial data. -/
theorem secondDeriv_kirchhoffLine_space {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 2 f)
    (i : Fin 3) (x : ℝ^3) (t y : ℝ) :
    deriv (deriv (kirchhoffLine f i x t)) y =
      t * unitSphereAverage 3 (∂[i] (∂[i] f)) (coordinateLine i x y) t := by
  have hmean : ContDiff ℝ 2 (fun z ↦ unitSphereAverage 3 f z t) :=
    (contDiff_unitSphereAverage hf).comp (contDiff_id.prodMk contDiff_const)
  have hcoord := iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at i 2
    (x := coordinateLine i x y) hmean.contDiffAt
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply,
    iteratedDeriv_eq_iterate, Function.comp_def, coordinateLine_coordinateLine,
    coordinateLine_apply_same] at hcoord
  have hd : ContDiff ℝ 1 (∂[i] f) := contDiff_partialDeriv_of_succ (m := 1) hf
  simp_rw [partialDeriv_unitSphereAverage (hf.of_le (by norm_num)),
    partialDeriv_unitSphereAverage hd] at hcoord
  unfold kirchhoffLine
  rw [deriv_const_mul_field', deriv_const_mul_field, ← hcoord]

/-- A transverse eigenfunction in the initial data produces the
one-dimensional Klein–Gordon equation with negative mass squared. -/
theorem kleinGordon_kirchhoffLine {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3)
    (htransverse : ∀ z, laplacian f z = (∂[i] (∂[i] f)) z + f z) (x : ℝ^3) (y : ℝ) {t : ℝ}
    (ht : 0 < t) :
    deriv (deriv (fun s ↦ kirchhoffLine f i x s y)) t -
        deriv (deriv (kirchhoffLine f i x t)) y - kirchhoffLine f i x t y = 0 := by
  have hsecond : Continuous (∂[i] (∂[i] f)) := (contDiff_partialDeriv_of_succ (m := 0)
      (contDiff_partialDeriv_of_succ (m := 1) hf)).continuous
  have hint (g : ℝ^3 → ℝ) (hg : Continuous g) : Integrable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦
          g (coordinateLine i x y + t • (ω : ℝ^3))) (volume : Measure (ℝ^3)).toSphere :=
    (hg.comp (by fun_prop)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))
  rw [secondDeriv_kirchhoffLine_space hf]
  change deriv (deriv (fun s ↦ s * unitSphereAverage 3 f (coordinateLine i x y) s)) t -
      t * unitSphereAverage 3 (∂[i] (∂[i] f)) (coordinateLine i x y) t -
        t * unitSphereAverage 3 f (coordinateLine i x y) t = 0
  rw [secondDeriv_radius_mul_unitSphereAverage hf _ ht]
  simp_rw [unitSphereAverage, htransverse]
  rw [integral_add (hint _ hsecond) (hint _ hf.continuous), add_div]
  ring

end WaveEquation
