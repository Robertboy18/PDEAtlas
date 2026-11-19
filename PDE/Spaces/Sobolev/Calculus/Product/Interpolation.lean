/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.GagliardoNirenberg.Weak
public import PDE.Spaces.Sobolev.GraphSpace.Representatives.Bridge
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Analysis.MeasureTheory.Lp.ExponentLift
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import PDE.Spaces.Sobolev.Fractional.Integer.Reverse
import PDE.Analysis.Fourier.SobolevMoments
import PDE.Analysis.Fourier.L1Reconstruction
import PDE.DistributionTheory.TemperedDistribution.Representative.Uniqueness

/-!
# Bounded derivative coordinates above the Sobolev continuity threshold

Fourier reconstruction gives essential boundedness at `n < 2k`. Interpolation
and the closed graph theorem then give continuous linear derivative maps with
the exponents needed for finite products.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Product

open GraphSpace GagliardoNirenberg

variable {n k : ℕ} [NeZero n]

omit [NeZero n] in
/-- The sharp Sobolev continuity threshold gives an essentially bounded representative. -/
theorem exists_ae_bound_of_dimension_lt (hk : (n : ℝ) < 2 * (k : ℝ))
    (u : GlobalSobolevSpace n k 2) :
    ∃ B : ℝ, ∀ᵐ x ∂volume, ‖u.toFun x‖ ≤ B := by
  let U := ofRepresentative u
  let v := Fractional.ofWkpSpace U
  obtain ⟨g, hg, hmom⟩ :=
    PDE.Analysis.Fourier.exists_fourier_memL1_moments_of_memSobolev
      (r := 0) (by simpa using hk) v.memSobolev_toDistr
  obtain ⟨b, _, hbid⟩ :=
    PDE.Analysis.Fourier.exists_contDiff_representative_of_fourier_eq g hg hmom
  have hrep : (b : ℝ^n → ℂ) =ᵐ[volume] Fractional.toL2Fun (Nat.cast_nonneg k) v := by
    apply PDE.ae_eq_of_integral_schwartz_smul_eq b.continuous.locallyIntegrable
      ((Lp.memLp (Fractional.toL2Fun (Nat.cast_nonneg k) v)).locallyIntegrable
        (by norm_num))
    intro φ
    rw [hbid, Fractional.toDistr_eq_toL2Fun (Nat.cast_nonneg k),
      Lp.toTemperedDistribution_apply]
  have hbase : (fun x ↦ (b x).re) =ᵐ[volume] u.toFun := by
    have hu := ofRepresentative_base_ae u
    simp only [domainMeasure, Measure.restrict_univ] at hu
    filter_upwards [hrep, Fractional.reOfL2_toL2Fun_ofWkpSpace U, hu] with x hx hy hz
    exact (congrArg Complex.re hx).trans (hy.trans hz)
  refine ⟨‖b‖, ?_⟩
  filter_upwards [hbase] with x hx
  rw [← hx, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (b x)).trans (b.norm_coe_le_norm x)

/-- Every derivative of order at most `d ≤ k` has the interpolation exponent
`2d/j`, including infinity at order zero. -/
theorem memLp_coordinate_derivativeExponent (hk : (n : ℝ) < 2 * (k : ℝ))
    {d : ℕ} (hd : d ≤ k) (a : DerivIndex n d) (u : W^{k,2}(ℝ^n)) :
    MemLp (u.val (a.castOrder hd)) (derivativeExponent d a.toList.length)
      (domainMeasure n univ) := by
  obtain ⟨B, hB⟩ := exists_ae_bound_of_dimension_lt hk (toRepresentative u)
  let v : GlobalSobolevSpace n d 2 :=
    { toFun := (toRepresentative u).toFun
      memLp := (toRepresentative u).memLp
      weak_derivs_inLp := fun α hα ↦ (toRepresentative u).weak_derivs_inLp α (hα.trans hd) }
  obtain ⟨g, _, hg, hw⟩ := exists_memLp_weakDerivative_of_bounded d v hB
    a.toList a.toList_length_le
  have he := hw.unique_ae isOpen_univ (u.property (a.castOrder hd))
  simp only [domainMeasure, Measure.restrict_univ] at he ⊢
  exact hg.ae_eq he

instance {d : ℕ} (a : DerivIndex n d) :
    Fact (1 ≤ derivativeExponent d a.toList.length) :=
  ⟨(by norm_num : (1 : ℝ≥0∞) ≤ 2).trans (two_le_derivativeExponent a.toList_length_le)⟩

/-- A weak-derivative coordinate, with its integrability upgraded by interpolation. -/
def derivativeLpCLM (hk : (n : ℝ) < 2 * (k : ℝ))
    {d : ℕ} (hd : d ≤ k) (a : DerivIndex n d) :
    W^{k,2}(ℝ^n) →L[ℝ] Lp ℝ (derivativeExponent d a.toList.length)
      (domainMeasure n univ) :=
  (wkpCoordinateCLM (a.castOrder hd)).liftLpExponent
    (memLp_coordinate_derivativeExponent hk hd a)

/-- Exponent lifting retains the stored weak derivative almost everywhere. -/
theorem derivativeLpCLM_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    {d : ℕ} (hd : d ≤ k) (a : DerivIndex n d) (u : W^{k,2}(ℝ^n)) :
    derivativeLpCLM hk hd a u =ᵐ[domainMeasure n univ] u.val (a.castOrder hd) :=
  (memLp_coordinate_derivativeExponent hk hd a u).coeFn_toLp

/-- One interpolation constant works for all derivative orders and coordinates
through `k`. It also dominates the contractive `L²` coordinate bound. -/
theorem exists_coordinate_lpNorm_bound (hk : (n : ℝ) < 2 * (k : ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d : ℕ) (hd : d ≤ k) (a : DerivIndex n d)
      (u : W^{k,2}(ℝ^n)),
      lpNorm (u.val (a.castOrder hd)) (derivativeExponent d a.toList.length)
        (domainMeasure n univ) ≤ C * ‖u‖ := by
  classical
  let I := (d : Fin (k + 1)) × DerivIndex n d.val
  let A (i : I) := ‖derivativeLpCLM hk (Nat.le_of_lt_succ i.1.isLt) i.2‖
  let C := 1 + ∑ i : I, A i
  refine ⟨C, le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦
    norm_nonneg (derivativeLpCLM hk (Nat.le_of_lt_succ i.1.isLt) i.2)), ?_⟩
  intro d hd a u
  let i : I := ⟨⟨d, Nat.lt_succ_of_le hd⟩, a⟩
  have hA : ‖derivativeLpCLM hk hd a‖ ≤ C := by
    exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (derivativeLpCLM hk
      (Nat.le_of_lt_succ j.1.isLt) j.2)) (Finset.mem_univ i)).trans
      (le_add_of_nonneg_left zero_le_one)
  calc
    _ = ‖derivativeLpCLM hk hd a u‖ := by
      change lpNorm _ _ _ = ‖(memLp_coordinate_derivativeExponent hk hd a u).toLp _‖
      rw [Lp.norm_toLp, toReal_eLpNorm]
    _ ≤ ‖derivativeLpCLM hk hd a‖ * ‖u‖ := (derivativeLpCLM hk hd a).le_opNorm u
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)

end SobolevSpace.Product
