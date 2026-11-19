/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.SmoothBounds
public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Weak

/-!
# Uniform composition bounds along bounded Sobolev approximations

The bounds depend on the reaction only on a fixed bounded interval containing
the values of the approximants. There is no restriction on the spatial dimension
and no global growth assumption on the reaction.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SobolevSpace.Composition

open GagliardoNirenberg

/-- A smooth scalar reaction has uniformly bounded derivatives through each
finite order on a bounded interval. -/
theorem exists_iteratedFDeriv_bound_on_Icc {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-B) B, ∀ j, j ≤ k →
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  classical
  have hb (i : Fin (k + 1)) :
      ∃ C : ℝ, ∀ x ∈ Icc (-B) B, ‖iteratedFDeriv ℝ i.val f x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn
      (hf.continuous_iteratedFDeriv (by simp)).continuousOn
  choose C hC using hb
  refine ⟨∑ i : Fin (k + 1), |C i|, Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), ?_⟩
  intro x hx j hj
  let i : Fin (k + 1) := ⟨j, by omega⟩
  exact (hC i x hx).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun l _ ↦ abs_nonneg (C l)) (Finset.mem_univ i)))

variable {n : ℕ} [NeZero n]

/-- A uniformly bounded smooth approximation with convergent top derivatives
has uniformly square-integrable derivatives after smooth scalar composition. -/
theorem exists_uniform_lpNorm_iteratedFDeriv_comp_bound {k : ℕ} (hk : 0 < k)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {v : ℕ → ℝ^n → ℝ} (hv : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j))
    (hvc : ∀ j, HasCompactSupport (v j)) {B : ℝ}
    (hvB : ∀ j x, ‖v j x‖ ≤ B)
    (hlim : ∀ α : List (Fin n), α.length = k →
      ∃ g : ℝ^n → ℝ, MemLp g 2 volume ∧
        Tendsto (fun j ↦ eLpNorm (iteratedPartialDeriv α (v j) - g) 2 volume)
          atTop (𝓝 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j,
      MemLp (iteratedFDeriv ℝ k (f ∘ v j)) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ k (f ∘ v j)) 2 volume ≤ C := by
  obtain ⟨T, hT, htop⟩ := exists_maxDerivativeLpNorm_bound hk hv hvc hlim
  obtain ⟨A, hA, hest⟩ := exists_constant_lpNorm_iteratedPartialDeriv_le (n := n) k
  obtain ⟨R, hR, hreact⟩ := exists_iteratedFDeriv_bound_on_Icc hf k (max B 0)
  have hbase (j : ℕ) : lpNorm (v j) ∞ volume ≤ max B 0 := by
    have he : eLpNorm (v j) ∞ volume ≤ ENNReal.ofReal (max B 0) := by
      rw [eLpNorm_exponent_top (hv j).continuous.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound
        (Eventually.of_forall fun x ↦ (hvB j x).trans (le_max_left _ _))
    simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal (le_max_right B 0)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  let M := A * (max B 0 + T)
  have hM : 0 ≤ M := mul_nonneg (by linarith) (add_nonneg (le_max_right _ _) hT)
  have hcoord (j : ℕ) (α : List (Fin n)) (hα : α.length ≤ k) :
      lpNorm (iteratedPartialDeriv α (v j)) (derivativeExponent k α.length) volume ≤ M :=
    (hest (v j) ((hv j).of_le (by simp)) (hvc j) α hα).trans
      (mul_le_mul_of_nonneg_left (add_le_add (hbase j) (htop j)) (by linarith))
  let D (i : Fin k) : ℝ := (n : ℝ) ^ (i.val + 1) * M
  let C := (k.factorial : ℝ) * R *
    (∑ i : Fin k, D i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ k
  refine ⟨C, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR)
    (pow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by positivity) _) _), ?_⟩
  intro j
  apply memLp_and_lpNorm_iteratedFDeriv_comp_le hk hf (hv j) (hvc j) hR
  · intro x l hl
    apply hreact (v j x) _ l hl
    apply abs_le.mp
    simpa only [Real.norm_eq_abs] using (hvB j x).trans (le_max_left B 0)
  · intro i
    apply lpNorm_iteratedFDeriv_le_of_coordinate_bounds (i.val + 1)
      (hv j) (hvc j) ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans
        (two_le_derivativeExponent (by omega)))
    intro α hα
    simpa only [hα] using hcoord j α (by omega)

end SobolevSpace.Composition
