/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.Autonomous.ClassicalCoefficients

/-!
# The closed-interval energy estimate for every weak wave

The uniform energy construction and uniqueness give Evans, §7.2.3, Theorem 5(i), with the
estimate (50), for the full autonomous operator. The essential supremum is taken over the closed
interval, as in (50); the endpoint singletons are null sets.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.3, Theorem 5(i), estimate (50).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open MeasureTheory Set Hyperbolic.Variational
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Every original weak solution obeys the full sum energy estimate. The constant
precedes the forcing and both initial data, and neither drift nor potential needs
any sign condition. -/
theorem exists_classical_wave_energy_estimate (hn : 0 < n) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {a b : ℝ} (hab : a < b) {A : ℝ^n → Fin n → Fin n → ℝ}
    {B : Fin n → ℝ^n → ℝ} {C : ℝ^n → ℝ} (hA : ∀ i j, ContDiffUpToBoundary 1 (fun x ↦ A x i j) Ω)
    (hB : ∀ i, ContDiffUpToBoundary 1 (B i) Ω) (hC : ContDiffUpToBoundary 0 C Ω)
    (hsymm : ∀ x ∈ Ω, ∀ i j, A x i j = A x j i) {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, ∀ ξ : Fin n → ℝ, alpha * ∑ i, ξ i * ξ i ≤ ∑ i, ∑ j, A x i j * ξ j * ξ i) :
    let T := h10L2GelfandTriple hopen
    let F := classicalAutonomousWaveForm hopen hbounded hA hB hC
    ∃ K : ℝ, 0 < K ∧
      ∀ (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (g : H¹₀(Ω)) (h : DerivLp n 2 Ω)
        (u : Lp (H¹₀(Ω)) 2 (volume.restrict (Ioc a b)))
        (v : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b)))
        (w : Lp (StrongDual ℝ (H¹₀(Ω))) 2 (volume.restrict (Ioc a b))),
        IsGelfandWeakWaveSolution T (fun _ ↦ F)
          (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f) u v w g h →
        MemLp (fun t ↦ u t) ∞ (volume.restrict (Ioc a b)) ∧
        MemLp (fun t ↦ v t) ∞ (volume.restrict (Ioc a b)) ∧
        (eLpNormEssSup (fun t ↦ ‖u t‖ + ‖v t‖)
          (volume.restrict (Icc a b))).toReal ≤ K * (‖f‖ + ‖g‖ + ‖h‖) := by
  have he := exists_uniform_energy_bound_of_classical_autonomous_coefficients
    hn hopen hbounded hab hA hB hC hsymm halpha hell
  let K := he.choose
  have hK : 0 < K := he.choose_spec.1
  refine ⟨K, hK, fun f g h u v w hweak ↦ ?_⟩
  obtain ⟨hu, hv, hb⟩ := (he.choose_spec.2 f g h).2 u v w hweak
  refine ⟨hu, hv, ?_⟩
  have hm : volume.restrict (Icc a b) = volume.restrict (Ioc a b) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm
  rw [hm]
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc a b),
      ‖‖u t‖ + ‖v t‖‖ ≤ K * (‖f‖ + ‖g‖ + ‖h‖) := by
    filter_upwards [hb] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      using ht
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hbound)).trans_eq (ENNReal.toReal_ofReal (by positivity))

end SobolevSpace.GraphSpace
