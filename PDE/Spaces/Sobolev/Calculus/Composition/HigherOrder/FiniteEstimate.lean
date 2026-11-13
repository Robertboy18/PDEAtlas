/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteBounds
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.ReactionEnvelope
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# A continuous monotone bound for smooth Sobolev composition

The estimate uses a single bound on the Sobolev norms of the input coordinates.
It is uniform over their compact supports.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Composition

open GraphSpace GagliardoNirenberg

variable {n k m : ℕ} {f : (Fin m → ℝ) → ℝ}

/-- The interpolation and higher-chain-rule contribution at derivative order `d`. -/
def finiteChainBound (n m d : ℕ) (A R : ℝ) : ℝ :=
  (d.factorial : ℝ) * (∑ i : Fin d,
    ((m : ℝ) * (n : ℝ) ^ (i.val + 1) * A * max R 0) ^
      (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ d

/-- A uniform bound for the graph norm of a smooth composition. -/
def finiteCompositionBound (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n k : ℕ) (A R : ℝ) : ℝ :=
  ∑ a : DerivIndex n k, reactionDerivativeBound hf k (A * max R 0) *
    ((m : ℝ) * max R 0 + finiteChainBound n m a.toList.length A R)

theorem finiteChainBound_nonneg (n m d : ℕ) {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    0 ≤ finiteChainBound n m d A R := by
  unfold finiteChainBound
  positivity

theorem continuous_finiteChainBound (n m d : ℕ) (A : ℝ) :
    Continuous (finiteChainBound n m d A) := by
  apply continuous_const.mul
  apply Continuous.pow
  apply continuous_finsetSum
  intro i _
  exact (continuous_const.mul (continuous_id.max continuous_const)).rpow_const
    (fun _ ↦ Or.inr (by positivity))

theorem monotone_finiteChainBound (n m d : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    Monotone (finiteChainBound n m d A) := by
  intro R S hRS
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by positivity) _)
  apply Finset.sum_le_sum
  intro i _
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact mul_le_mul_of_nonneg_left (max_le_max_right 0 hRS) (by positivity)

theorem continuous_finiteCompositionBound (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n k : ℕ) (A : ℝ) : Continuous (finiteCompositionBound hf n k A) := by
  apply continuous_finsetSum
  intro a _
  exact ((continuous_reactionDerivativeBound hf k).comp
    (continuous_const.mul (continuous_id.max continuous_const))).mul
      ((continuous_const.mul (continuous_id.max continuous_const)).add
        (continuous_finiteChainBound n m a.toList.length A))

theorem monotone_finiteCompositionBound (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n k : ℕ) {A : ℝ} (hA : 0 ≤ A) : Monotone (finiteCompositionBound hf n k A) := by
  intro R S hRS
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul
  · exact monotone_reactionDerivativeBound hf k
      (mul_le_mul_of_nonneg_left (max_le_max_right 0 hRS) hA)
  · exact add_le_add (mul_le_mul_of_nonneg_left (max_le_max_right 0 hRS) (Nat.cast_nonneg _))
      (monotone_finiteChainBound n m a.toList.length hA hRS)
  · exact add_nonneg (by positivity) (finiteChainBound_nonneg n m _ hA R)
  · exact zero_le_one.trans (one_le_reactionDerivativeBound hf k _)

private theorem lpNorm_iteratedFDeriv_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {u : ℝ^n → E} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p : ℝ≥0∞) :
    lpNorm (iteratedFDeriv ℝ 0 u) p volume = lpNorm u p volume := by
  simp only [← toReal_eLpNorm]
  congr 1
  exact eLpNorm_congr_norm_ae
    (hu.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    hu.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := u) (x := x))

/-- Smooth compactly supported inputs satisfy the finite-family composition
bound, uniformly over the supports of their coordinates. -/
theorem norm_smooth_finite_composition_le (hk : (n : ℝ) < 2 * (k : ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {u : ℝ^n → Fin m → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) {A R : ℝ} (hA : 0 ≤ A)
    (hinterp : ∀ (v : ℝ^n → ℝ) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
      (hvc : HasCompactSupport v) (d : ℕ), d ≤ k → ∀ α : List (Fin n), α.length ≤ d →
      lpNorm (iteratedPartialDeriv α v) (derivativeExponent d α.length) volume ≤
        A * ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) v hv hvc‖)
    (hR : ∀ i, ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
      (fun x ↦ u x i) ((contDiff_apply ℝ (fun _ ↦ ℝ) i).comp hu)
      (hc.comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl)‖ ≤ max R 0) :
    ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
      (f ∘ u) (hf.comp hu) (hc.comp_left hf0)‖ ≤ finiteCompositionBound hf n k A R := by
  classical
  let ui (i : Fin m) (x : ℝ^n) := u x i
  have hui (i : Fin m) : ContDiff ℝ (⊤ : ℕ∞) (ui i) := (contDiff_apply ℝ (fun _ ↦ ℝ) i).comp hu
  have hci (i : Fin m) : HasCompactSupport (ui i) := hc.comp_left (g := fun y : Fin m → ℝ ↦ y i) rfl
  let U (i : Fin m) : W^{k,2}(ℝ^n) := mkWkpSpaceOnOfContDiff (ui i) (hui i) (hci i)
  have hcoord (i : Fin m) (d : ℕ) (hd : d ≤ k) (α : List (Fin n)) (hα : α.length ≤ d) :
      lpNorm (iteratedPartialDeriv α (ui i)) (derivativeExponent d α.length) volume ≤
        A * max R 0 :=
    (hinterp (ui i) (hui i) (hci i) d hd α hα).trans
      (mul_le_mul_of_nonneg_left (hR i) hA)
  have hux (x : ℝ^n) : ‖u x‖ ≤ A * max R 0 := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA (le_max_right _ _))).mpr
    intro i
    apply (Product.norm_le_lpNorm_top_of_continuous (hui i).continuous
      ((hui i).continuous.memLp_of_hasCompactSupport (hci i)) x).trans
    simpa only [List.length_nil, derivativeExponent_zero, iteratedPartialDeriv]
      using hcoord i 0 (Nat.zero_le k) [] (by simp)
  let C := reactionDerivativeBound hf k (A * max R 0)
  have hC : 0 ≤ C := zero_le_one.trans (one_le_reactionDerivativeBound hf k _)
  have hk1 : 1 ≤ k := by
    exact_mod_cast (show (0 : ℝ) < k by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hreact (x : ℝ^n) (j : ℕ) (hj : j ≤ k) : ‖iteratedFDeriv ℝ j f (u x)‖ ≤ C :=
    norm_iteratedFDeriv_le_reactionDerivativeBound hf k _ (hux x) hj
  have hpoint (x : ℝ^n) : ‖f (u x)‖ ≤ C * ‖u x‖ := by
    have h := (convex_closedBall (0 : Fin m → ℝ) (A * max R 0)).norm_image_sub_le_of_norm_fderiv_le
      (x := 0) (y := u x) (fun y _ ↦ hf.differentiable (by simp) y)
      (fun y hy ↦ by
        simpa only [norm_iteratedFDeriv_one] using
          norm_iteratedFDeriv_le_reactionDerivativeBound hf k (A * max R 0)
            (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy) hk1)
      (by simpa only [Metric.mem_closedBall, dist_self] using mul_nonneg hA (le_max_right R 0))
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hux x)
    simpa only [hf0, sub_zero] using h
  have hbasei (i : Fin m) : lpNorm (ui i) 2 volume ≤ max R 0 := by
    have he := wkpCoordinateCLM_norm_le (baseIndex n k) (U i)
    change ‖(mkWkpSpaceOnOfContDiff (ui i) (hui i) (hci i)).val (baseIndex n k)‖ ≤ ‖U i‖ at he
    rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal] at he
    simp only [domainMeasure, Measure.restrict_univ, baseIndex_toList,
      iteratedPartialDeriv, toReal_eLpNorm] at he
    exact he.trans (hR i)
  have hbaseu : lpNorm u 2 volume ≤ (m : ℝ) * max R 0 := by
    rw [← lpNorm_iteratedFDeriv_zero hu]
    refine lpNorm_iteratedFDeriv_pi_le 0 hu hc (by norm_num) fun i ↦ ?_
    change lpNorm (iteratedFDeriv ℝ 0 (ui i)) 2 volume ≤ _
    rw [lpNorm_iteratedFDeriv_zero (hui i)]
    exact hbasei i
  have hbase : lpNorm (f ∘ u) 2 volume ≤ C * ((m : ℝ) * max R 0) := by
    have hm : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
    calc
      _ ≤ lpNorm (fun x ↦ C * ‖u x‖) 2 volume :=
        lpNorm_mono_real (hm.norm.const_mul C) hpoint
      _ = C * lpNorm u 2 volume := by
        change lpNorm (C • (fun x ↦ ‖u x‖)) 2 volume = _
        rw [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hC,
          lpNorm_norm hm.aestronglyMeasurable]
      _ ≤ _ := mul_le_mul_of_nonneg_left hbaseu hC
  let W : W^{k,2}(ℝ^n) := mkWkpSpaceOnOfContDiff (f ∘ u) (hf.comp hu) (hc.comp_left hf0)
  refine (PiLp.norm_le_sum_norm W.val).trans (Finset.sum_le_sum fun a _ ↦ ?_)
  change ‖(mkWkpSpaceOnOfContDiff (f ∘ u) (hf.comp hu) (hc.comp_left hf0)).val a‖ ≤ _
  rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
  simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
  by_cases ha : a.toList.length = 0
  · simp only [List.length_eq_zero_iff.mp ha, iteratedPartialDeriv]
    exact hbase.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (finiteChainBound_nonneg n m _ hA R)) hC)
  · have hpos := Nat.pos_of_ne_zero ha
    have hbound := memLp_and_lpNorm_iteratedFDeriv_comp_le hpos hf hu hc hC
      (fun x j hj ↦ hreact x j (hj.trans a.toList_length_le))
      (fun i ↦ (m : ℝ) * (n : ℝ) ^ (i.val + 1) * A * max R 0) (fun i ↦ by
        apply (lpNorm_iteratedFDeriv_pi_le (i.val + 1) hu hc
          (A := (n : ℝ) ^ (i.val + 1) * (A * max R 0))
          ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans
            (two_le_derivativeExponent (by omega))) ?_).trans_eq (by ring)
        intro l
        apply lpNorm_iteratedFDeriv_le_of_coordinate_bounds (i.val + 1) (hui l) (hci l)
          ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_derivativeExponent (by omega)))
        intro α hα
        simpa only [hα] using hcoord l a.toList.length a.toList_length_le α (by omega))
    have hpartial := lpNorm_mono_real hbound.1.norm (fun x ↦
      PDE.norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
        ((hf.comp hu).of_le (by simp)).contDiffAt (x := x))
    rw [lpNorm_norm hbound.1.aestronglyMeasurable] at hpartial
    apply (hpartial.trans hbound.2).trans
    change (a.toList.length.factorial : ℝ) * C * _ ≤
      C * (_ + finiteChainBound n m a.toList.length A R)
    unfold finiteChainBound
    nlinarith [mul_nonneg hC (mul_nonneg (Nat.cast_nonneg m) (le_max_right R 0))]

end SobolevSpace.Composition
