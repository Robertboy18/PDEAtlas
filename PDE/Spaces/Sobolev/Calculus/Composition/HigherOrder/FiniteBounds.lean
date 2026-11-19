/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.SmoothBounds
public import PDE.Spaces.Sobolev.Calculus.Product.SmoothInterpolation

/-!
# Quantitative higher composition bounds for finite families

Coordinate interpolation controls the full derivative tensors of a finite
family. The general higher chain estimate then bounds smooth composition.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Composition

open GraphSpace GagliardoNirenberg

variable {n m : ℕ}

/-- The derivative tensor of a finite family is controlled by the sum of the
coordinate derivative tensor norms. -/
theorem norm_iteratedFDeriv_pi_le (j : ℕ) {u : ℝ^n → Fin m → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ j u x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y ↦ u y i) x‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have he := (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (hu.contDiffAt (x := x)) (i := j) (by simp)
  have hev := congrArg (fun T ↦ T v) he
  change iteratedFDeriv ℝ j (fun y ↦ u y i) x v = iteratedFDeriv ℝ j u x v i at hev
  rw [← hev]
  exact (iteratedFDeriv ℝ j (fun y ↦ u y i) x).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum
      (fun l _ ↦ norm_nonneg (iteratedFDeriv ℝ j (fun y ↦ u y l) x))
      (Finset.mem_univ i)) (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _))

/-- Coordinate tensor bounds give an interpolation bound for a finite family. -/
theorem lpNorm_iteratedFDeriv_pi_le (j : ℕ) {u : ℝ^n → Fin m → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) {A : ℝ}
    (hA : ∀ i, lpNorm (iteratedFDeriv ℝ j (fun y ↦ u y i)) p volume ≤ A) :
    lpNorm (iteratedFDeriv ℝ j u) p volume ≤ (m : ℝ) * A := by
  classical
  let g (i : Fin m) (x : ℝ^n) := ‖iteratedFDeriv ℝ j (fun y ↦ u y i) x‖
  have hui (i : Fin m) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ u y i) :=
    (contDiff_apply ℝ (fun _ ↦ ℝ) i).comp hu
  have hci (i : Fin m) : HasCompactSupport (fun y ↦ u y i) :=
    hc.comp_left (g := fun v : Fin m → ℝ ↦ v i) rfl
  have hg (i : Fin m) : MemLp (g i) p volume :=
    ((hui i).continuous_iteratedFDeriv (by simp)).norm.memLp_of_hasCompactSupport
      (((hci i).iteratedFDeriv j).comp_left (g := norm) norm_zero)
  have hs : MemLp (fun x ↦ ∑ i, g i x) p volume :=
    memLp_finsetSum Finset.univ (fun i _ ↦ hg i)
  calc
    _ ≤ lpNorm (fun x ↦ ∑ i, g i x) p volume :=
      lpNorm_mono_real hs (norm_iteratedFDeriv_pi_le j hu)
    _ ≤ ∑ i, lpNorm (g i) p volume := by
      simpa only [Finset.sum_fn] using lpNorm_sum_le (s := Finset.univ) (fun i _ ↦ hg i) hp
    _ ≤ ∑ _i : Fin m, A := Finset.sum_le_sum fun i _ ↦ by
      simpa only [g, lpNorm_norm
        ((hui i).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable p]
        using hA i
    _ = _ := by simp

end SobolevSpace.Composition
