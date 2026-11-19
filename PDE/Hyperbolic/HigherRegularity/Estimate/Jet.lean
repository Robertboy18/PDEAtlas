/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HigherRegularity.Estimate.Symmetric
public import PDE.Hyperbolic.HigherRegularity.EllipticInduction.OrderOneTimeJet
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Norm sums along a Sobolev time jet

Splitting off the head makes the quantitative wave induction follow the
recursive derivative structure. At order one the two terms are controlled
directly by the energy estimate. Changing the time restriction from `(a,b]`
to `[a,b]` preserves the essential supremum.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 6, estimate (64).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The base-coordinate map contracts the time `L²` norm. -/
theorem norm_baseCoordinateTimeLp_le (f : Lp (W^{m,2}(Ω)) 2 (volume.restrict (Ioc a b))) :
    ‖baseCoordinateTimeLp f‖ ≤ ‖f‖ := by
  have hK : ‖wkpBaseCoordinateCLM (n := n) (m := m) (p := 2) (Ω := Ω)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro U
      simpa only [one_mul] using wkpBaseCoordinateCLM_norm_le U)
  exact (ContinuousLinearMap.norm_compLp_le _ f).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK (norm_nonneg f))

/-- Splitting the solution sum separates the new spatial lift from its
already constructed derivative jet. -/
theorem solutionSobolevNormSum_succ (U : SobolevTimeJet n (m + 2) Ω a b) (t : ℝ) :
    solutionSobolevNormSum U t = solutionSobolevNormSum U.timeDerivative t + ‖U.head t‖ := by
  unfold solutionSobolevNormSum
  rw [Fin.sum_univ_castSucc]
  simp only [SobolevTimeJet.iteratedTimeDerivative_castSucc,
    SobolevTimeJet.iteratedTimeDerivative_last]

/-- At order one the solution sum is exactly its velocity and displacement norms. -/
theorem solutionSobolevNormSum_one (U : SobolevTimeJet n 1 Ω a b) (t : ℝ) :
    solutionSobolevNormSum U t = ‖U.timeDerivative.head t‖ + ‖U.head t‖ := by
  unfold solutionSobolevNormSum
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_one, SobolevTimeJet.iteratedTimeDerivative_castSucc]
  have hz : (0 : Fin 1) = Fin.last 0 := rfl
  rw [hz, SobolevTimeJet.iteratedTimeDerivative_last, SobolevTimeJet.iteratedTimeDerivative_last]

/-- Every derivative norm is one nonnegative term of the whole sum. -/
theorem norm_solution_level_le (U : SobolevTimeJet n (m + 1) Ω a b) (r : Fin (m + 2)) (t : ℝ) :
    ‖(U.iteratedTimeDerivative r).head t‖ ≤ solutionSobolevNormSum U t := by
  unfold solutionSobolevNormSum
  exact Finset.single_le_sum
    (fun s _ ↦ norm_nonneg ((U.iteratedTimeDerivative s).head t)) (Finset.mem_univ r)

/-- In particular the head norm is bounded by the solution sum. -/
theorem norm_solution_head_le (U : SobolevTimeJet n (m + 1) Ω a b) (t : ℝ) :
    ‖U.head t‖ ≤ solutionSobolevNormSum U t := by
  simpa only [SobolevTimeJet.iteratedTimeDerivative_last] using
    norm_solution_level_le U (Fin.last (m + 1)) t

/-- The first derivative is also a term of the same solution sum. -/
theorem norm_solution_derivative_head_le (U : SobolevTimeJet n (m + 1) Ω a b) (t : ℝ) :
    ‖U.timeDerivative.head t‖ ≤ solutionSobolevNormSum U t := by
  simpa only [SobolevTimeJet.iteratedTimeDerivative_castSucc,
    SobolevTimeJet.iteratedTimeDerivative_last] using
    norm_solution_level_le U (Fin.last m).castSucc t

/-- An almost-everywhere sum bound gives the closed-interval form of Evans's estimate. -/
theorem eLpNormEssSup_solutionSobolevNormSum_Icc_le (U : SobolevTimeJet n (m + 1) Ω a b) {C : ℝ}
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum U t ≤ C) :
    eLpNormEssSup (solutionSobolevNormSum U) (volume.restrict (Icc a b)) ≤ ENNReal.ofReal C := by
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [hbound] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (solutionSobolevNormSum_nonneg U t)] using ht

/-- The energy-space jet has a quantitative sum bound, with a constant
depending only on the canonical order-zero identification. -/
theorem exists_orderOneSobolevTimeJet_norm_le (hopen : IsOpen Ω)
    (B : ℝ → H¹₀(Ω) →L[ℝ] StrongDual ℝ (H¹₀(Ω)))
    (ell : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b)))
    (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
    (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
    (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))) (q : H¹₀(Ω)) (p : DerivLp n 2 Ω)
    (hweak :
      Hyperbolic.Variational.IsGelfandWeakWaveSolution (h10L2GelfandTriple hopen) B ell u v w q p)
    (hu : MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)))
    (hv : MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b))) {C : ℝ}
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖u t‖ + ‖v t‖ ≤ C) :
    ∃ U : SobolevTimeJet n 1 Ω a b,
      (∀ᵐ t ∂volume.restrict (Ioc a b), U.head t = h10SubtypeL (u t)) ∧
      baseCoordinateTimeLp U.timeDerivative.head = v ∧
      U.IsEssentiallyBounded ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), solutionSobolevNormSum U t ≤
        (1 + ‖orderZeroSobolevCLM (n := n) (p := 2) (Omega := Ω)‖) * C := by
  obtain ⟨U, hU, hdU, htop⟩ :=
    exists_orderOneSobolevTimeJet_of_weakWave hopen B ell u v w q p hweak hu hv
  have hhead : ∀ᵐ t ∂volume.restrict (Ioc a b), U.head t = h10SubtypeL (u t) :=
    hU.mono fun _ h ↦ wkpBaseCoordinateCLM_injective hopen h
  refine ⟨U, hhead, hdU, htop, ?_⟩
  let K := orderZeroSobolevCLM (n := n) (p := 2) (Omega := Ω)
  have hd := baseCoordinateTimeLp_apply_ae U.timeDerivative.head
  rw [hdU] at hd
  filter_upwards [hhead, hd, hbound] with t ht hdt hb
  have heq : U.timeDerivative.head t = K (v t) := by
    apply wkpBaseCoordinateCLM_injective hopen
    rw [orderZeroSobolevCLM_base]
    exact hdt.symm
  rw [solutionSobolevNormSum_one, ht, heq]
  have hnorm : ‖h10SubtypeL (u t)‖ = ‖u t‖ := rfl
  rw [hnorm]
  have hdle := K.le_opNorm (v t)
  have hu0 := norm_nonneg (u t)
  have hv0 := norm_nonneg (v t)
  have hK0 := norm_nonneg K
  have hmult := mul_le_mul_of_nonneg_left hb hK0
  change _ ≤ (1 + ‖K‖) * C
  nlinarith only [hb, hdle, hu0, hv0, hmult, mul_nonneg hK0 hu0]

end Hyperbolic.HigherRegularity
