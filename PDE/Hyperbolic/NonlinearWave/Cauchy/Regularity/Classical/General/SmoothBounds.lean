/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Composition
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SmoothData
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Composition bounds on smooth Sobolev norm balls

The constants use derivatives of the scalar reaction only on a bounded value
range. Gagliardo–Nirenberg interpolation controls the products in the higher
chain rule uniformly over smooth compactly supported inputs.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GagliardoNirenberg SobolevSpace.Composition
open scoped ENNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Positive-order chain-rule bounds use only positive-order reaction derivatives. -/
theorem norm_iteratedFDeriv_comp_le_of_derivative_bounds {n j : ℕ} (hj : 0 < j) {f : ℝ → ℝ}
    {u : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : ContDiff ℝ (⊤ : ℕ∞) u) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ y l, 0 < l → l ≤ j → ‖iteratedFDeriv ℝ l f y‖ ≤ D) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ j (f ∘ u) x‖ ≤ (j.factorial : ℝ) * D * higherChainGauge j u x ^ j := by
  let g : ℝ → ℝ := fun y ↦ f y - f (u x)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.sub contDiff_const
  have hshift {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {v : E → ℝ} (hv : ContDiff ℝ (⊤ : ℕ∞) v) (c : ℝ) {l : ℕ} (hl : 0 < l) (z : E) :
      iteratedFDeriv ℝ l (fun y ↦ v y - c) z = iteratedFDeriv ℝ l v z := by
    change iteratedFDeriv ℝ l (v - fun _ ↦ c) z = _
    rw [iteratedFDeriv_sub (hv.of_le (by simp)) contDiff_const]
    simp only [Pi.sub_apply, iteratedFDeriv_const_of_ne hl.ne', Pi.zero_apply, sub_zero]
  have he := norm_iteratedFDeriv_comp_le_higherChainGauge j hg hu x (C := D) (by
    intro l hl
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · simpa only [norm_iteratedFDeriv_zero, g, sub_self, norm_zero] using hD
    · rw [show iteratedFDeriv ℝ l g (u x) = iteratedFDeriv ℝ l f (u x) from hshift hf _ hl0 _]
      exact hb _ _ hl0 hl)
  have heq : iteratedFDeriv ℝ j (g ∘ u) x = iteratedFDeriv ℝ j (f ∘ u) x :=
    hshift (hf.comp hu) _ hj x
  rwa [heq] at he

/-- Derivative Lᵖ bounds control the L² norm of a positive-order scalar composition. -/
theorem lpNorm_iteratedFDeriv_comp_le_of_derivative_bounds {n j : ℕ} (hj : 0 < j) {f : ℝ → ℝ}
    {u : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ y l, 0 < l → l ≤ j → ‖iteratedFDeriv ℝ l f y‖ ≤ D) (A : Fin j → ℝ)
    (hA : ∀ i : Fin j, lpNorm (iteratedFDeriv ℝ (i.val + 1) u) (derivativeExponent j (i.val + 1))
      volume ≤ A i) :
    MemLp (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ∧
      lpNorm (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ≤ (j.factorial : ℝ) * D * (∑ i : Fin j,
        A i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ j := by
  let G := higherChainGauge j u
  have hG : Continuous G := continuous_higherChainGauge hu j
  have hcG : HasCompactSupport G := HasCompactSupport.higherChainGauge hc j
  have hm : MemLp (fun x ↦ (j.factorial : ℝ) * D * G x ^ j) 2 volume :=
    ((hG.pow j).memLp_of_hasCompactSupport
      (hcG.comp_left (g := fun s : ℝ ↦ s ^ j) (zero_pow hj.ne'))).const_mul _
  have hp (x : ℝ^n) : ‖iteratedFDeriv ℝ j (f ∘ u) x‖ ≤ (j.factorial : ℝ) * D * G x ^ j :=
    norm_iteratedFDeriv_comp_le_of_derivative_bounds hj hf hu hD hb x
  refine ⟨hm.mono' ((hf.comp hu).continuous_iteratedFDeriv (by simp)).aestronglyMeasurable
    (.of_forall hp), ?_⟩
  have hpower : lpNorm (fun x ↦ G x ^ j) 2 volume =
      lpNorm G (ENNReal.ofReal (2 * (j : ℝ))) volume ^ j := by
    have he := congrArg ENNReal.toReal (eLpNorm_norm_rpow G (μ := volume) hG.aestronglyMeasurable
        (show (0 : ℝ) < j by exact_mod_cast hj) (p := 2))
    have heq : (fun x ↦ ‖G x‖ ^ (j : ℝ)) = fun x ↦ G x ^ j := by
      ext x
      rw [Real.norm_of_nonneg (higherChainGauge_nonneg j u x), Real.rpow_natCast]
    rw [heq] at he
    have hexp : (2 : ℝ≥0∞) * ENNReal.ofReal (j : ℝ) =
        ENNReal.ofReal (2 * (j : ℝ)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    simpa only [hexp, ← ENNReal.toReal_rpow, Real.rpow_natCast, toReal_eLpNorm] using he
  calc
    _ ≤ lpNorm (fun x ↦ (j.factorial : ℝ) * D * G x ^ j) 2 volume := lpNorm_mono_real hm hp
    _ = (j.factorial : ℝ) * D * lpNorm (fun x ↦ G x ^ j) 2 volume := by
      change lpNorm (((j.factorial : ℝ) * D) • (fun x ↦ G x ^ j)) 2 volume = _
      rw [lpNorm_const_smul, coe_nnnorm, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hD)]
    _ ≤ _ := by
      rw [hpower]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ lpNorm_nonneg (lpNorm_higherChainGauge_le hj hu hc A hA) j)
        (mul_nonneg (Nat.cast_nonneg _) hD)

variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
/-- Each classical derivative in a smooth Sobolev graph is bounded by its
full graph norm. -/
theorem lpNorm_iteratedPartialDeriv_le_smoothGraph {u : ℝ^n → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) (α : List (Fin n)) (hα : α.length ≤ k) :
    lpNorm (iteratedPartialDeriv α u) 2 volume ≤ ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2)
      (Ω := univ) u hu hc‖ := by
  have h := PiLp.norm_apply_le (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc).val
    (derivIndexOfList α hα)
  rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal] at h
  rw [iteratedPartialDeriv_congr_perm_smooth hu (derivIndexOfList_toList_perm α hα)] at h
  simpa only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm, Submodule.norm_coe] using h

/-- Interpolation and the higher chain rule give a uniform positive-order
composition bound from a value bound and a Sobolev graph bound. -/
theorem exists_uniform_smooth_composition_derivative_bound {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) {B R : ℝ} (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      (∀ x, ‖u x‖ ≤ B) →
      ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      MemLp (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ∧
        lpNorm (iteratedFDeriv ℝ j (f ∘ u)) 2 volume ≤ C := by
  obtain ⟨A, hA, hest⟩ := exists_constant_lpNorm_iteratedPartialDeriv_le (n := n) j
  obtain ⟨D, hD, hreact⟩ := exists_iteratedFDeriv_bound_on_Icc hf j B
  let M := A * (B + R)
  let T (i : Fin j) : ℝ := (n : ℝ) ^ (i.val + 1) * M
  let C := (j.factorial : ℝ) * D * (∑ i : Fin j, T i ^ (((i.val + 1 : ℕ) : ℝ)⁻¹)) ^ j
  have hM : 0 ≤ M := mul_nonneg (by linarith) (add_nonneg hB hR)
  refine ⟨C, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD)
    (pow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (by positivity) _) _), ?_⟩
  intro u hu hc hub hur
  have hbase : lpNorm u ∞ volume ≤ B := by
    have he : eLpNorm u ∞ volume ≤ ENNReal.ofReal B := by
      rw [eLpNorm_exponent_top hu.continuous.aestronglyMeasurable]
      exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hub)
    simpa only [toReal_eLpNorm, ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have htop : maxDerivativeLpNorm j j u ≤ R := by
    apply Finset.sup'_le
    intro α _
    rw [derivativeExponent_self hj]
    exact (lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc (List.ofFn α)
      (by simpa using hjk)).trans hur
  have hcoord (α : List (Fin n)) (hα : α.length ≤ j) :
      lpNorm (iteratedPartialDeriv α u) (derivativeExponent j α.length) volume ≤ M :=
    (hest u (hu.of_le (by simp)) hc α hα).trans
      (mul_le_mul_of_nonneg_left (add_le_add hbase htop) (by linarith))
  apply memLp_and_lpNorm_iteratedFDeriv_comp_le hj hf hu hc hD
  · intro x l hl
    exact hreact (u x) (abs_le.mp (by simpa only [Real.norm_eq_abs] using hub x)) l hl
  · intro i
    apply lpNorm_iteratedFDeriv_le_of_coordinate_bounds (i.val + 1) hu hc
      ((by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_derivativeExponent (by omega)))
    intro α hα
    simpa only [hα] using hcoord α (by omega)

/-- Smooth compact inputs in a fixed Sobolev ball have uniformly bounded
composition graphs. The scalar reaction need only be smooth and fix zero. -/
theorem exists_uniform_smooth_composition_bound (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
      (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
      ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
      ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
        (f ∘ u) (hf.comp hu) (hc.comp_left hf0)‖ ≤ C := by
  classical
  let B := ‖classicalRepresentativeCLM hk‖ * R
  have hB : 0 ≤ B := mul_nonneg (classicalRepresentativeCLM hk).opNorm_nonneg hR
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  obtain ⟨K, hK⟩ := hf1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_Icc (-B) B) isCompact_Icc
  have hvalue (u : ℝ^n → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u)
      (hur : ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖ ≤ R)
      (x : ℝ^n) : ‖u x‖ ≤ B := by
    let U := mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc
    have he : u = (classicalRepresentativeCLM hk U : ℝ^n → ℝ) := by
      apply eq_classicalRepresentativeCLM_of_ae_eq hk U hu.continuous
      simpa only [U, baseRepresentative, wkpBaseCoordinateCLM_apply,
        domainMeasure, Measure.restrict_univ] using (wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae
          (k := k) (Ω := univ) hu hc).symm
    rw [he]
    exact ((classicalRepresentativeCLM hk U).norm_coe_le_norm x).trans
      (((classicalRepresentativeCLM hk).le_opNorm U).trans
        (mul_le_mul_of_nonneg_left hur (classicalRepresentativeCLM hk).opNorm_nonneg))
  have hcoord (a : DerivIndex n k) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ^n → ℝ)
        (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u),
        ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ) u hu hc‖ ≤ R →
        ‖(mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := univ)
          (f ∘ u) (hf.comp hu) (hc.comp_left hf0)).val a‖ ≤ C := by
    by_cases ha : a.toList.length = 0
    · refine ⟨K * R, mul_nonneg K.2 hR, ?_⟩
      intro u hu hc hur
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [List.length_eq_zero_iff.mp ha, iteratedPartialDeriv,
        domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      have hum : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hc
      have hp : ∀ x, ‖(f ∘ u) x‖ ≤ (K : ℝ) * ‖u x‖ := by
        intro x
        have hx : u x ∈ Icc (-B) B :=
          abs_le.mp (by simpa only [Real.norm_eq_abs] using hvalue u hu hc hur x)
        simpa only [Function.comp_apply, hf0, dist_zero_right] using
          hK.dist_le_mul (u x) hx 0 ⟨neg_nonpos.mpr hB, hB⟩
      have hm := lpNorm_mono_real (hum.norm.const_mul (K : ℝ)) hp
      have he :
          lpNorm (fun x ↦ (K : ℝ) * ‖u x‖) 2 volume = K * lpNorm u 2 volume := by
        change lpNorm ((K : ℝ) • fun x ↦ ‖u x‖) 2 volume = _
        rw [lpNorm_const_smul, coe_nnnorm]
        erw [Real.norm_of_nonneg K.2, lpNorm_norm hum.aestronglyMeasurable]
        rfl
      rw [he] at hm
      exact hm.trans (mul_le_mul_of_nonneg_left
        ((lpNorm_iteratedPartialDeriv_le_smoothGraph hu hc [] (by simp)).trans hur) K.2)
    · obtain ⟨C, hC, hest⟩ := exists_uniform_smooth_composition_derivative_bound (n := n)
        hf (Nat.pos_of_ne_zero ha) a.toList_length_le hB hR
      refine ⟨C, hC, ?_⟩
      intro u hu hc hur
      obtain ⟨hm, hb⟩ := hest u hu hc (hvalue u hu hc hur) hur
      rw [norm_mkWkpSpaceOnOfContDiff_coordinate_eq_eLpNorm_toReal]
      simp only [domainMeasure, Measure.restrict_univ, toReal_eLpNorm]
      exact (lpNorm_mono_real hm.norm (fun x ↦
        norm_iteratedPartialDeriv_le_norm_iteratedFDeriv a.toList
          ((hf.comp hu).of_le (by simp)).contDiffAt)).trans
        ((lpNorm_norm hm.aestronglyMeasurable 2).le.trans hb)
  choose C hC hest using hcoord
  refine ⟨∑ a, C a, Finset.sum_nonneg (fun a _ ↦ hC a), ?_⟩
  intro u hu hc hur
  exact (PiLp.norm_le_sum_norm _).trans (Finset.sum_le_sum fun a _ ↦ hest a u hu hc hur)

end PDE.Hyperbolic.NonlinearWave.Cauchy
