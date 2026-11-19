/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Coordinates
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Multivariable coefficients as native analytic series

An exponent is represented by its multiset of coordinate factors. Choosing an
ordering of those factors realizes each monomial as a continuous multilinear
map with no increase in its coefficient norm. The choice of ordering affects
the multilinear map but not its diagonal values.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal

noncomputable section

namespace ContinuousMultilinearMap

variable {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

/-- A multilinear representative of the monomial with coordinate multiset `s`. -/
def symMonomial (s : Sym ι n) (z : G) : (ι → ℝ) [×n]→L[ℝ] G :=
  coordinateMonomial
    (fun j ↦ (s : Multiset ι).toList.get
      (Fin.cast ((Multiset.length_toList _).trans (Sym.card_coe (s := s))).symm j)) z

/-- Every ordering of a monomial has the same diagonal value. -/
theorem symMonomial_diag (s : Sym ι n) (z : G) (x : ι → ℝ) :
    symMonomial s z (fun _ ↦ x) = ((s : Multiset ι).map x).prod • z := by
  let w : Fin n → ι := fun j ↦ (s : Multiset ι).toList.get
    (Fin.cast ((Multiset.length_toList _).trans (Sym.card_coe (s := s))).symm j)
  have hw : List.ofFn w = (s : Multiset ι).toList := by
    dsimp only [w]
    rw [← List.ofFn_congr ((Multiset.length_toList _).trans (Sym.card_coe (s := s)))
      (s : Multiset ι).toList.get, List.ofFn_get]
  change (∏ j, x (w j)) • z = _
  rw [← List.prod_ofFn, List.ofFn_comp', hw, Multiset.prod_map_toList]

variable [Fintype ι]

/-- Realizing a multiset monomial introduces no coefficient norm loss. -/
theorem norm_symMonomial_le (s : Sym ι n) (z : G) :
    ‖symMonomial s z‖ ≤ ‖z‖ :=
  norm_coordinateMonomial_le _ z

variable [DecidableEq ι]

/-- Group the coordinate words of a multilinear map by their multiset of indices. -/
def symCoefficient (f : (ι → ℝ) [×n]→L[ℝ] G) (s : Sym ι n) : G :=
  ∑ w : Fin n → ι, if (List.ofFn w : Multiset ι) = s then
    f (fun j ↦ Pi.single (w j) 1) else 0

/-- Grouping coordinate words cannot increase the sum of their norms. -/
theorem sum_norm_symCoefficient_le (f : (ι → ℝ) [×n]→L[ℝ] G) :
    ∑ s : Sym ι n, ‖symCoefficient f s‖ ≤ (Fintype.card ι : ℝ) ^ n * ‖f‖ := by
  classical
  calc
    ∑ s : Sym ι n, ‖symCoefficient f s‖ ≤
        ∑ s : Sym ι n, ∑ w : Fin n → ι,
          if (List.ofFn w : Multiset ι) = s then ‖f (fun j ↦ Pi.single (w j) 1)‖ else 0 := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [symCoefficient, apply_ite, norm_zero] using
        norm_sum_le (s := Finset.univ)
          (fun w : Fin n → ι ↦
            if (List.ofFn w : Multiset ι) = s then f (fun j ↦ Pi.single (w j) 1) else 0)
    _ = ∑ w : Fin n → ι, ‖f (fun j ↦ Pi.single (w j) 1)‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      let s : Sym ι n := ⟨List.ofFn w, by simp⟩
      have h (t : Sym ι n) : (List.ofFn w : Multiset ι) = t ↔ s = t :=
        Sym.coe_inj (s₁ := s) (s₂ := t)
      simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ ≤ _ := sum_norm_apply_coordinate_vectors_le f

/-- Grouping words with the same coordinate monomial preserves diagonal evaluation. -/
theorem apply_diag_eq_sum_symCoefficient (f : (ι → ℝ) [×n]→L[ℝ] G) (x : ι → ℝ) :
    f (fun _ ↦ x) =
      ∑ s : Sym ι n, ((s : Multiset ι).map x).prod • symCoefficient f s := by
  classical
  have hf := congrArg (fun p : (ι → ℝ) [×n]→L[ℝ] G ↦ p (fun _ ↦ x))
    (eq_sum_coordinateMonomial f)
  simp only [sum_apply, coordinateMonomial_apply] at hf
  rw [hf]
  simp only [symCoefficient, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  let s : Sym ι n := ⟨List.ofFn w, by simp⟩
  have h (t : Sym ι n) : (List.ofFn w : Multiset ι) = t ↔ s = t := Sym.coe_inj (s₁ := s) (s₂ := t)
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  change (∏ j, x (w j)) = ((List.ofFn w : Multiset ι).map x).prod
  rw [Multiset.map_coe, Multiset.prod_coe, ← List.ofFn_comp', List.prod_ofFn]

end ContinuousMultilinearMap

namespace FormalMultilinearSeries

variable {ι G E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Realize multivariable coefficients as a native formal multilinear series. -/
def ofMultiindexCoefficients (a : (ι →₀ ℕ) → G) :
    FormalMultilinearSeries ℝ (ι → ℝ) G :=
  fun n ↦ ∑ s : Sym ι n,
    ContinuousMultilinearMap.symMonomial s (a (s : Multiset ι).toFinsupp)

/-- Diagonal evaluation is the usual homogeneous polynomial in the coordinates. -/
theorem ofMultiindexCoefficients_apply (a : (ι →₀ ℕ) → G) (n : ℕ) (x : ι → ℝ) :
    ofMultiindexCoefficients a n (fun _ ↦ x) =
      ∑ s : Sym ι n, ((s : Multiset ι).map x).prod • a (s : Multiset ι).toFinsupp := by
  simp [ofMultiindexCoefficients, ContinuousMultilinearMap.symMonomial_diag]

/-- The homogeneous operator norm is bounded by the sum of the coefficient norms. -/
theorem norm_ofMultiindexCoefficients_le (a : (ι →₀ ℕ) → G) (n : ℕ) :
    ‖ofMultiindexCoefficients a n‖ ≤ ∑ s : Sym ι n, ‖a (s : Multiset ι).toFinsupp‖ := by
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum fun s _ ↦
    ContinuousMultilinearMap.norm_symMonomial_le s (a (s : Multiset ι).toFinsupp)

/-- Geometric bounds on multivariable coefficients imply a positive analytic radius. -/
theorem radius_pos_of_multiindex_bound (a : (ι →₀ ℕ) → G)
    {C r : ℝ} (hr : 0 < r)
    (ha : ∀ n, ∑ s : Sym ι n, ‖a (s : Multiset ι).toFinsupp‖ ≤ C * r ^ n) :
    0 < (ofMultiindexCoefficients a).radius := by
  let s : ℝ≥0 := ⟨r⁻¹, le_of_lt (inv_pos.mpr hr)⟩
  have hs : 0 < (s : ℝ≥0∞) := ENNReal.coe_pos.mpr (inv_pos.mpr hr)
  apply hs.trans_le
  apply (ofMultiindexCoefficients a).le_radius_of_bound C (r := s)
  intro n
  calc
    ‖ofMultiindexCoefficients a n‖ * (s : ℝ) ^ n ≤ (C * r ^ n) * (s : ℝ) ^ n := by
      gcongr
      exact (norm_ofMultiindexCoefficients_le a n).trans (ha n)
    _ = C := by
      change (C * r ^ n) * (r⁻¹) ^ n = C
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hr.ne', one_pow, mul_one]

/-- Extract a commutative coefficient by collecting all coordinate words with that exponent. -/
def multiindexCoeff (p : FormalMultilinearSeries ℝ (ι → ℝ) G) (a : ι →₀ ℕ) : G :=
  (p (a.sum fun _ ↦ id)).symCoefficient
    ((Sym.equivNatSum ι _).symm ⟨a, rfl⟩)

/-- The coefficient extraction can be computed using any proof of the total degree. -/
theorem multiindexCoeff_eq (p : FormalMultilinearSeries ℝ (ι → ℝ) G)
    (a : ι →₀ ℕ) {n : ℕ} (h : a.sum (fun _ ↦ id) = n) :
    p.multiindexCoeff a =
      (p n).symCoefficient ((Sym.equivNatSum ι n).symm ⟨a, h⟩) := by
  subst n
  rfl

/-- At a multiset exponent, coefficient extraction is exactly the grouped word coefficient. -/
theorem multiindexCoeff_toFinsupp (p : FormalMultilinearSeries ℝ (ι → ℝ) G)
    {n : ℕ} (s : Sym ι n) :
    p.multiindexCoeff (s : Multiset ι).toFinsupp = (p n).symCoefficient s := by
  rw [multiindexCoeff_eq p _ (n := n) (by simp)]
  exact congrArg (ContinuousMultilinearMap.symCoefficient (p n))
    ((Sym.equivNatSum ι n).symm_apply_apply s)

/-- Passing to commutative coefficients preserves every homogeneous diagonal polynomial. -/
theorem ofMultiindexCoefficients_multiindexCoeff_apply
    (p : FormalMultilinearSeries ℝ (ι → ℝ) G) (n : ℕ) (x : ι → ℝ) :
    ofMultiindexCoefficients p.multiindexCoeff n (fun _ ↦ x) = p n (fun _ ↦ x) := by
  rw [ofMultiindexCoefficients_apply]
  simp only [multiindexCoeff_toFinsupp]
  exact (ContinuousMultilinearMap.apply_diag_eq_sum_symCoefficient (p n) x).symm

/-- Extracting commutative coefficients costs at most the number of coordinate words. -/
theorem sum_norm_multiindexCoeff_le (p : FormalMultilinearSeries ℝ (ι → ℝ) G) (n : ℕ) :
    ∑ s : Sym ι n, ‖p.multiindexCoeff (s : Multiset ι).toFinsupp‖ ≤
      (Fintype.card ι : ℝ) ^ n * ‖p n‖ := by
  simpa only [multiindexCoeff_toFinsupp] using
    ContinuousMultilinearMap.sum_norm_symCoefficient_le (p n)

/-- Commutative coefficient extraction preserves a positive convergence radius. -/
theorem radius_pos_ofMultiindexCoefficients_multiindexCoeff
    (p : FormalMultilinearSeries ℝ (ι → ℝ) G) (hp : 0 < p.radius) :
    0 < (ofMultiindexCoefficients p.multiindexCoeff).radius := by
  obtain ⟨C, r, hC, hr, hpr⟩ := p.le_mul_pow_of_radius_pos hp
  let K : ℝ := Fintype.card ι + 1
  have hK : 0 < K := by positivity
  apply radius_pos_of_multiindex_bound p.multiindexCoeff (C := C) (mul_pos hK hr)
  intro n
  calc
    ∑ s : Sym ι n, ‖p.multiindexCoeff (s : Multiset ι).toFinsupp‖ ≤
        (Fintype.card ι : ℝ) ^ n * ‖p n‖ := p.sum_norm_multiindexCoeff_le n
    _ ≤ K ^ n * ‖p n‖ := by gcongr; simp [K]
    _ ≤ K ^ n * (C * r ^ n) :=
      mul_le_mul_of_nonneg_left (hpr n) (pow_nonneg hK.le _)
    _ = C * (K * r) ^ n := by
      rw [mul_pow, ← mul_assoc, mul_comm (K ^ n) C, mul_assoc]

end FormalMultilinearSeries

/-- A native analytic expansion also has its canonical commutative-coefficient expansion.
The radius may shrink, but no extra convergence hypothesis is required. -/
theorem HasFPowerSeriesAt.ofMultiindexCoefficients
    {ι G : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : (ι → ℝ) → G} {p : FormalMultilinearSeries ℝ (ι → ℝ) G} {x : ι → ℝ}
    (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofMultiindexCoefficients p.multiindexCoeff) x := by
  obtain ⟨r, hf⟩ := hf
  let q := FormalMultilinearSeries.ofMultiindexCoefficients p.multiindexCoeff
  have hq := p.radius_pos_ofMultiindexCoefficients_multiindexCoeff hf.radius_pos
  refine ⟨min r q.radius, min_le_right _ _, lt_min hf.r_pos hq, ?_⟩
  intro y hy
  have hyr : y ∈ Metric.eball (0 : ι → ℝ) r :=
    Metric.mem_eball.mpr ((Metric.mem_eball.mp hy).trans_le (min_le_left _ _))
  simpa only [q, FormalMultilinearSeries.ofMultiindexCoefficients_multiindexCoeff_apply] using
    hf.hasSum hyr
