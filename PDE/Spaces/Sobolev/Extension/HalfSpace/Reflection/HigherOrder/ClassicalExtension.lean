/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.ClassicalJets
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Extending finite classical regularity from a half-space

Weighted reflection extends a function without asking for values or derivatives on the
other side of the boundary. We extend the derivative coordinates inductively, then use
the reflection moments to match their jets. This lets equations posed only for forward
time use analytical results stated for globally smooth representatives.
-/

@[expose] public noncomputable section

open Set
open scoped Topology
open SobolevSpace.GraphSpace.HigherOrderReflection

namespace PDE.Analysis

variable {n : ℕ}

/-- Every finite-order smooth function on a closed coordinate half-space has
an equally smooth global representative agreeing on that half-space. -/
theorem exists_contDiff_extension_halfSpace (i : Fin n) (k : ℕ)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) :
    ∃ F : ℝ^n → ℝ, ContDiff ℝ k F ∧ EqOn F f {x | 0 ≤ x i} := by
  classical
  induction k generalizing f with
  | zero =>
    let P : ℝ^n → ℝ^n := fun x ↦ x + max 0 (-x i) • EuclideanSpace.single i 1
    have hP : Continuous P := continuous_id.add
      ((continuous_const.max (EuclideanSpace.proj i).continuous.neg).smul continuous_const)
    have hPi (x : ℝ^n) : 0 ≤ (P x) i := by
      have hi := le_max_right (0 : ℝ) (-x i)
      simp only [P, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
        ↓reduceIte, smul_eq_mul, mul_one]
      linarith
    have hPeq (x : ℝ^n) (hx : 0 ≤ x i) : P x = x := by
      simp [P, max_eq_left (neg_nonpos.mpr hx)]
    refine ⟨f ∘ P, contDiff_zero.mpr ?_, ?_⟩
    · exact hf.continuousOn.comp_continuous hP hPi
    · intro x hx
      exact congrArg f (hPeq x hx)
  | succ k ih =>
    let D := fderivWithin ℝ f {x : ℝ^n | 0 ≤ x i}
    have hD : ContDiffOn ℝ k D {x | 0 ≤ x i} :=
      hf.fderivWithin (uniqueDiffOn_coordinateHalfSpace i) (by simp)
    have hext (j : Fin n) : ∃ G : ℝ^n → ℝ, ContDiff ℝ k G ∧
        EqOn G (fun x ↦ D x (EuclideanSpace.single j 1)) {x | 0 ≤ x i} :=
      ih (hD.clm_apply contDiffOn_const)
    choose G hG hGeq using hext
    let L : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦ ∑ j, G j x • EuclideanSpace.proj j
    have hL : ContDiff ℝ k L := ContDiff.sum (fun j _ ↦ (hG j).smul_const _)
    have hLeq (x : ℝ^n) (hx : 0 ≤ x i) : L x = D x := by
      ext v
      have hv : v = ∑ j, v j • EuclideanSpace.single j 1 := by
        ext j
        simp [Pi.single_apply]
      change (∑ j, G j x • EuclideanSpace.proj j) v = D x v
      conv_rhs => rw [hv]
      simp only [sum_apply, smul_apply, EuclideanSpace.coe_proj, map_sum, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl (fun j _ ↦ by rw [hGeq j hx, mul_comm])
    refine ⟨weightedReflectionFun i (k + 1) f,
      contDiff_succ_weightedReflectionFun i k hL ?_, ?_⟩
    · intro x hx
      rw [hLeq x hx]
      exact (hf.differentiableOn (by simp) x hx).hasFDerivWithinAt
    · exact fun x hx ↦ weightedReflectionFun_eq_of_nonneg i (k + 1) f x hx

/-- A compactly supported function smooth on a closed coordinate half-space has
an equally smooth compactly supported global representative. A smooth cutoff equal
to one on the original support preserves agreement throughout the physical half-space. -/
theorem exists_contDiff_compact_extension_halfSpace (i : Fin n) (k : ℕ)
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ k f {x | 0 ≤ x i}) (hc : HasCompactSupport f) :
    ∃ F : ℝ^n → ℝ, ContDiff ℝ k F ∧ HasCompactSupport F ∧ EqOn F f {x | 0 ≤ x i} := by
  obtain ⟨F, hF, heq⟩ := exists_contDiff_extension_halfSpace i k hf
  obtain ⟨χ, _, hχone, _, _⟩ := TestFunction.exists_eq_one_on_compact
    (isOpen_univ : IsOpen (Set.univ : Set (ℝ^n))) hc.isCompact (Set.subset_univ (tsupport f))
  refine ⟨fun x ↦ χ.toFun x * F x,
    (χ.contDiff.of_le (by simp)).mul hF, χ.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  change χ.toFun x * F x = f x
  rw [heq hx]
  by_cases hfx : f x = 0
  · simp [hfx]
  · rw [hχone x (subset_tsupport f hfx), one_mul]

end PDE.Analysis
