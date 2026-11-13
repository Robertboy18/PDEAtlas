/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Interpolation

/-!
# Finite products of Sobolev derivatives

Finite Hölder combines the interpolated derivative coordinates. The constant
is independent of the allocation of derivatives among the factors.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Product

open GraphSpace GagliardoNirenberg

private theorem eLpNorm_prod_le {ι X : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset ι) (f : ι → X → ℝ) (p : ι → ℝ≥0∞)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun x ↦ ∏ i ∈ s, f i x) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ ≤
      ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    simpa using eLpNorm_le_of_ae_bound (p := ∞) (μ := μ)
      (f := fun _ : X ↦ (1 : ℝ)) aestronglyMeasurable_const
      (Filter.Eventually.of_forall fun _ ↦ (by simp : ‖(1 : ℝ)‖ ≤ 1))
  | cons i s hi ih =>
    have : ENNReal.HolderTriple (p i) (∑ j ∈ s, (p j)⁻¹)⁻¹
        ((p i)⁻¹ + ∑ j ∈ s, (p j)⁻¹)⁻¹ := ⟨by simp⟩
    simp only [Finset.prod_cons, Finset.sum_cons]
    apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := p i) (q := (∑ j ∈ s, (p j)⁻¹)⁻¹) (fun a b : ℝ ↦ a * b) 1
      continuous_mul (hf i (Finset.mem_cons_self ..))
      (s.aestronglyMeasurable_fun_prod fun j hj ↦ hf j (Finset.mem_cons_of_mem hj))
      (Filter.Eventually.of_forall fun x ↦ by simp [norm_mul])).trans
    simp only [ENNReal.coe_one, one_mul]
    exact mul_le_mul_right (ih (fun j hj ↦ hf j (Finset.mem_cons_of_mem hj))) _

private theorem prod_memLp_and_lpNorm_le {ι X : Type*} [Fintype ι]
    [MeasurableSpace X] {μ : Measure X} (f : ι → X → ℝ) (p : ι → ℝ≥0∞)
    (hf : ∀ i, MemLp (f i) (p i) μ) (hp : ∑ i, (p i)⁻¹ = (2 : ℝ≥0∞)⁻¹)
    {C : ℝ} (R : ι → ℝ)
    (hbound : ∀ i, lpNorm (f i) (p i) μ ≤ C * R i) :
    MemLp (fun x ↦ ∏ i, f i x) 2 μ ∧
      lpNorm (fun x ↦ ∏ i, f i x) 2 μ ≤ C ^ Fintype.card ι * ∏ i, R i := by
  classical
  have hm := MemLp.fun_prod (s := Finset.univ) (fun i _ ↦ hf i)
  have he := eLpNorm_prod_le Finset.univ f p (fun i _ ↦ (hf i).aestronglyMeasurable)
  rw [hp, inv_inv] at hm he
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∏ i, lpNorm (f i) (p i) μ := by
      simpa only [toReal_eLpNorm, ENNReal.toReal_prod] using
        ENNReal.toReal_mono (ENNReal.prod_ne_top fun i _ ↦ (hf i).eLpNorm_ne_top) he
    _ ≤ ∏ i, (C * R i) := Finset.prod_le_prod₀ (fun _ _ ↦ lpNorm_nonneg)
      (fun i _ ↦ hbound i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- Finite products of weak derivatives satisfy the quantitative Sobolev
estimate at `n < 2k`. The same constant works for every derivative allocation
whose total order is at most `k`. A nonempty family is necessary on `ℝⁿ`. -/
theorem exists_constant_prod_derivatives_le {n k m : ℕ} [NeZero n] [NeZero m]
    (hk : (n : ℝ) < 2 * (k : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Fin m → DerivIndex n k),
      (∑ i, (a i).toList.length) ≤ k → ∀ u : Fin m → W^{k,2}(ℝ^n),
      MemLp (fun x ↦ ∏ i, (u i).val (a i) x) 2 (domainMeasure n univ) ∧
      lpNorm (fun x ↦ ∏ i, (u i).val (a i) x) 2 (domainMeasure n univ) ≤
        C * ∏ i, ‖u i‖ := by
  classical
  obtain ⟨A, hA, hbound⟩ := exists_coordinate_lpNorm_bound hk
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨A ^ m, pow_nonneg hA0 _, ?_⟩
  intro a ha u
  let d := ∑ i, (a i).toList.length
  have hid (i : Fin m) : (a i).toList.length ≤ d :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (a j).toList.length) (Finset.mem_univ i)
  by_cases hd : d = 0
  · have ha0 (i : Fin m) : a i = baseIndex n k := by
      apply DerivIndex.ext
      simp only [baseIndex_toList]
      exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (hd ▸ hid i))
    let p (i : Fin m) : ℝ≥0∞ := if i = 0 then 2 else ∞
    have hm (i : Fin m) : MemLp ((u i).val (a i)) (p i) (domainMeasure n univ) := by
      by_cases hi : i = 0
      · simpa [p, hi] using Lp.memLp ((u i).val (a i))
      · simpa [p, hi, ha0] using
          memLp_coordinate_derivativeExponent hk (Nat.zero_le k) (baseIndex n 0) (u i)
    have hb (i : Fin m) : lpNorm ((u i).val (a i)) (p i) (domainMeasure n univ) ≤
        A * ‖u i‖ := by
      by_cases hi : i = 0
      · simp only [p, ite_eq_left hi]
        exact (wkpCoordinateCLM_norm_le (a i) (u i)).trans
          (le_mul_of_one_le_left (norm_nonneg _) hA)
      · simpa [p, hi, ha0] using hbound 0 (Nat.zero_le k) (baseIndex n 0) (u i)
    simpa using prod_memLp_and_lpNorm_le (fun i ↦ (u i).val (a i)) p hm
      (by
        calc
          ∑ i, (p i)⁻¹ = (p 0)⁻¹ := Finset.sum_eq_single 0
            (by intro b _ hb; simp [p, hb]) (by simp)
          _ = _ := by simp [p]) (fun i ↦ ‖u i‖) hb
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    let b (i : Fin m) : DerivIndex n d :=
      ⟨⟨(a i).1.val, Nat.lt_succ_of_le (by simpa using hid i)⟩, (a i).2⟩
    have hb (i : Fin m) : (b i).castOrder ha = a i := rfl
    let p (i : Fin m) := derivativeExponent d (b i).toList.length
    have hp : ∑ i, (p i)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
      simp only [p, derivativeExponent, inv_inv]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity), ← Finset.sum_div]
      have he : ∑ i, ((b i).toList.length : ℝ) = (d : ℝ) := by
        simp only [b, DerivIndex.toList_length]
        exact_mod_cast (show ∑ i, (a i).1.val = d by simp only [d, DerivIndex.toList_length])
      rw [he]
      have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
      have hr : (d : ℝ) / (2 * d) = (2 : ℝ)⁻¹ := by field_simp
      rw [hr, ENNReal.ofReal_inv_of_pos (by norm_num)]; norm_num
    simpa only [hb, Fintype.card_fin] using prod_memLp_and_lpNorm_le
      (fun i ↦ (u i).val ((b i).castOrder ha)) p
      (fun i ↦ memLp_coordinate_derivativeExponent hk ha (b i) (u i)) hp
      (fun i ↦ ‖u i‖) (fun i ↦ hbound d ha (b i) (u i))

end SobolevSpace.Product
