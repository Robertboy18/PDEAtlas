/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Radial.Average.Basic
public import PDE.Spaces.Sobolev.Weighted.PlanarReflection
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Finite mixed derivatives of radial averages

Each radial derivative adds one factor of the averaging parameter. Axial
derivatives leave that factor unchanged. The derivative families below come
from the actual finite coordinate derivatives of the source; no identities
for a separately supplied family are assumed.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Calculus

private theorem contDiff_radialAxialChart (m : ℕ) :
    ContDiff ℝ m (fun p : ℝ × ℝ ↦
      EuclideanSpace.single (0 : Fin 2) p.1 + EuclideanSpace.single 1 p.2) := by
  apply (contDiff_piLp 2).2
  intro i
  fin_cases i
  · simpa using (contDiff_fst : ContDiff ℝ m (fun p : ℝ × ℝ ↦ p.1))
  · simpa using (contDiff_snd : ContDiff ℝ m (fun p : ℝ × ℝ ↦ p.2))

private theorem iteratedDeriv_weightedRadialAverage_of_contDiff
    {f : ℝ → ℝ} (m n : ℕ) (hf : ContDiff ℝ m f) (r : ℝ) :
    iteratedDeriv m (weightedRadialAverage f n) r =
      weightedRadialAverage (iteratedDeriv m f) (n + m) r := by
  have hc := (contDiff_nat_iff_iteratedDeriv.mp hf).1
  have hd := (contDiff_nat_iff_iteratedDeriv.mp hf).2
  simpa only [iteratedDeriv_zero] using
    iteratedDeriv_weightedRadialAverage (fun j ↦ iteratedDeriv j f)
      (R := |r| + 1) m n
      (fun j hj ↦ (hc j hj).continuousOn)
      (fun j hj x _hx ↦ by
        simpa only [iteratedDeriv_succ] using (hd j hj x).hasDerivAt)
      m le_rfl (abs_lt.mp (lt_add_one |r|))

private theorem iteratedDeriv_weightedRadialAverage_axial
    {F : ℝ^2 → ℝ} (ell n : ℕ) (hF : ContDiff ℝ ell F) (r z : ℝ) :
    iteratedDeriv ell
        (fun y ↦ weightedRadialAverage
          (fun s ↦ F (EuclideanSpace.single 0 s + EuclideanSpace.single 1 y)) n r) z =
      weightedRadialAverage
        (fun s ↦ iteratedPartialDeriv (List.replicate ell (1 : Fin 2)) F
          (EuclideanSpace.single 0 s + EuclideanSpace.single 1 z)) n r := by
  let G : ℕ → ℝ → ℝ → ℝ := fun j s y ↦
    iteratedPartialDeriv (List.replicate j (1 : Fin 2)) F
      (EuclideanSpace.single 0 s + EuclideanSpace.single 1 y)
  have hreg (j : ℕ) (hj : j ≤ ell) :
      ContDiff ℝ ((ell - j : ℕ) : ℕ∞)
        (iteratedPartialDeriv (List.replicate j (1 : Fin 2)) F) := by
    simpa only [List.length_replicate] using
      contDiff_iteratedPartialDeriv_of_le hF (List.replicate j (1 : Fin 2))
        (by simpa only [List.length_replicate] using hj)
  have hcont (j : ℕ) (hj : j ≤ ell) :
      ContinuousOn (fun p : ℝ × ℝ ↦ G j p.1 p.2)
        (uIcc 0 r ×ˢ Ioo (z - 1) (z + 1)) :=
    ((hreg j hj).continuous.comp (contDiff_radialAxialChart (ell - j)).continuous).continuousOn
  have hderiv (j : ℕ) (hj : j < ell) (s : ℝ) (_hs : s ∈ uIcc 0 r)
      (y : ℝ) (_hy : y ∈ Ioo (z - 1) (z + 1)) :
      HasDerivAt (G j s) (G (j + 1) s y) y := by
    have hC1 : ContDiff ℝ 1
        (iteratedPartialDeriv (List.replicate j (1 : Fin 2)) F) :=
      (hreg j hj.le).of_le (by exact_mod_cast (show 1 ≤ ell - j by omega))
    have hline :
        coordinateLine 1 (EuclideanSpace.single (0 : Fin 2) s + EuclideanSpace.single 1 y) =
          fun a ↦ EuclideanSpace.single 0 s + EuclideanSpace.single 1 a := by
      funext a
      ext i
      fin_cases i <;> simp [coordinateLine]
    have hbase := ((hC1.differentiable one_ne_zero)
        (coordinateLine 1
          (EuclideanSpace.single (0 : Fin 2) s + EuclideanSpace.single 1 y) y)).hasFDerivAt
    have h := hbase.comp_hasDerivAt y (hasDerivAt_coordinateLine 1
        (EuclideanSpace.single 0 s + EuclideanSpace.single 1 y) y)
    rw [hline] at h
    simpa only [G, List.replicate_succ, iteratedPartialDeriv, partialDeriv,
      Function.comp_def] using h
  simpa only [G, List.replicate_zero, iteratedPartialDeriv] using
    iteratedDeriv_weightedRadialAverage_parameter G
      (r := r) (a := z - 1) (b := z + 1) ell n
      hcont hderiv ell le_rfl (show z ∈ Ioo (z - 1) (z + 1) by constructor <;> linarith)

/-- A finite mixed derivative passes through the radial average. The radial
count increments the power; the axial count does not. This includes negative
radii and the axis because the source is defined with finite regularity on
the whole plane. -/
theorem mixedIteratedDeriv2D_weightedRadialAverage
    (q ell n : ℕ) {F : ℝ^2 → ℝ} (hF : ContDiff ℝ (q + ell : ℕ) F) (r z : ℝ) :
    SobolevSpace.Weighted.mixedIteratedDeriv2D q ell
        (fun s y ↦ weightedRadialAverage
          (fun a ↦ F (EuclideanSpace.single 0 a + EuclideanSpace.single 1 y)) n s) r z =
      weightedRadialAverage
        (fun s ↦ iteratedPartialDeriv
          (List.replicate q (0 : Fin 2) ++ List.replicate ell (1 : Fin 2)) F
          (EuclideanSpace.single 0 s + EuclideanSpace.single 1 z)) (n + q) r := by
  have hFell : ContDiff ℝ ell F :=
    hF.of_le (by exact_mod_cast (show ell ≤ q + ell by omega))
  let H : ℝ^2 → ℝ := iteratedPartialDeriv (List.replicate ell (1 : Fin 2)) F
  have hH : ContDiff ℝ q H := by
    simpa only [H, List.length_replicate, Nat.add_sub_cancel_right,
      WithTop.coe_natCast] using
      contDiff_iteratedPartialDeriv_of_le hF (List.replicate ell (1 : Fin 2))
        (by simp)
  have hslice : ContDiff ℝ q
      (fun s ↦ H (EuclideanSpace.single 0 s + EuclideanSpace.single 1 z)) := by
    exact hH.comp ((contDiff_radialAxialChart q).comp
      (contDiff_id.prodMk contDiff_const))
  have haxial :
      (fun s ↦ iteratedDeriv ell
        (fun y ↦ weightedRadialAverage
          (fun a ↦ F (EuclideanSpace.single 0 a + EuclideanSpace.single 1 y)) n s) z) =
      weightedRadialAverage
        (fun a ↦ H (EuclideanSpace.single 0 a + EuclideanSpace.single 1 z)) n := by
    funext s
    exact iteratedDeriv_weightedRadialAverage_axial ell n hFell s z
  unfold SobolevSpace.Weighted.mixedIteratedDeriv2D
  rw [haxial, iteratedDeriv_weightedRadialAverage_of_contDiff q n hslice r]
  apply congrArg (fun f ↦ weightedRadialAverage f (n + q) r)
  funext s
  rw [iteratedPartialDeriv_append, iteratedPartialDeriv_replicate]
  have hline :
      coordinateLine 0 (EuclideanSpace.single (0 : Fin 2) s + EuclideanSpace.single 1 z) =
        fun a ↦ EuclideanSpace.single 0 a + EuclideanSpace.single 1 z := by
    funext a
    ext i
    fin_cases i <;> simp [coordinateLine]
  have hcoord :
      (EuclideanSpace.single (0 : Fin 2) s + EuclideanSpace.single 1 z : ℝ^2) 0 = s := by
    simp
  have hbridge :=
    (iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at 0 q
      (x := EuclideanSpace.single (0 : Fin 2) s + EuclideanSpace.single 1 z)
      hH.contDiffAt).symm
  rw [hline, hcoord] at hbridge
  exact hbridge

end PDE.Calculus
