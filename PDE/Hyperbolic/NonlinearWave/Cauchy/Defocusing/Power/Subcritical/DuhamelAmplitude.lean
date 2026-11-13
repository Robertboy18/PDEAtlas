/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.Amplitude
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.PotentialControl

/-!
# Amplitude bounds from the three-dimensional Duhamel formula

For every real `1 < p < 5`, a bounded family satisfying the retarded integral formula and a uniform
scaled H¹ trace bound has an amplitude bound independent of its original bound. The factor is
exactly `1 / (4 * π)`.

The family index and retarded evaluation map are abstract. The integral representation and the
Sobolev trace estimates are hypotheses. From these inputs the argument is that of the proof
of Theorem 3 of Evans, §12.3.3: the representation gives (19), the trace bound takes the place
of (22)-(24), and (20)-(21), (25) and step 3 close the estimate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.3, proof of Theorem 3, equations (19)-(25) and step 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Absolute power integrability gives signed source integrability, and controls
its integral by the positive power potential. -/
theorem integrable_signed_power_potential {p : ℝ} (hp : 0 < p) {μ : Measure (ℝ^3)} {f : ℝ^3 → ℝ}
    (hf : AEStronglyMeasurable f μ) (hi : Integrable (fun y ↦ |f y| ^ p / ‖y‖) μ) :
    Integrable (fun y ↦ Real.signedPower p (f y) / ‖y‖) μ ∧
      |∫ y, Real.signedPower p (f y) / ‖y‖ ∂μ| ≤ ∫ y, |f y| ^ p / ‖y‖ ∂μ := by
  have hnorm (y : ℝ^3) : ‖Real.signedPower p (f y) / ‖y‖‖ = |f y| ^ p / ‖y‖ := by
    rw [norm_div, Real.norm_signedPower hp, norm_norm, Real.norm_eq_abs]
  have hm := ((Real.continuous_signedPower hp).comp_aestronglyMeasurable hf).aemeasurable
  refine ⟨hi.mono' (hm.div continuous_norm.measurable.aemeasurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ (hnorm y).le), ?_⟩
  exact (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
    (Filter.Eventually.of_forall hnorm))

/-- The subcritical Duhamel estimate bounds amplitude independently of any
preliminary amplitude bound. The trace and representation hypotheses are explicit. -/
theorem exists_uniform_amplitude_bound_of_duhamel {p : ℝ}
    (hp : 1 < p) (hp5 : p < 5) (T E V : ℝ) (hE : 0 ≤ E) (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 < B ∧ ∀ {X : Type*} (u v : X → ℝ) (r : X → ℝ) (σ : X → ℝ^3 → X)
      (U : (x : X) → H¹(ball (0 : ℝ^3) (r x))),
      BddAbove (range fun x ↦ |u x|) →
      (∀ x, 0 < r x) → (∀ x, r x ≤ T) → (∀ x, |v x| ≤ V) →
      (∀ x, ‖∇ (U x)‖ ≤ E) → (∀ x, ‖wkpBaseCoordinateCLM (U x)‖ / r x ≤ E) →
      (∀ x, (baseRepresentative (U x)) =ᵐ[domainMeasure 3 (ball 0 (r x))]
        fun y ↦ u (σ x y)) →
      (∀ x, u x = v x - (1 / (4 * Real.pi)) *
        ∫ y in ball (0 : ℝ^3) (r x), Real.signedPower p (baseRepresentative (U x) y) / ‖y‖) →
      ∀ x, |u x| ≤ B := by
  obtain ⟨K, hK, hpotential⟩ := exists_power_potential_bound T E hE
  let κ := 1 / (4 * Real.pi)
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨B, hB, hscalar⟩ := exists_amplitude_bound hp5 (1 + V + κ * K)
  refine ⟨B, hB, ?_⟩
  intro X u v r σ U hbounded hr hrT hv hgrad hbase hrep hduhamel
  let A := sSup (insert 1 (range fun x ↦ |u x|))
  have hbdd : BddAbove (insert 1 (range fun x ↦ |u x|)) := hbounded.insert 1
  have hA : 1 ≤ A := le_csSup hbdd (mem_insert 1 _)
  have huA (x : X) : |u x| ≤ A := le_csSup hbdd (mem_insert_of_mem 1 (mem_range_self x))
  have hpoint (x : X) : |u x| ≤ V + κ * K * A ^ max (p - 4) 0 := by
    have hamp : ∀ᵐ y ∂domainMeasure 3 (ball 0 (r x)),
        |baseRepresentative (U x) y| ≤ A := by
      filter_upwards [hrep x] with y hy
      rw [hy]
      exact huA _
    obtain ⟨hi, hb⟩ := hpotential (r x) p A (hr x) (hrT x) hp.le hA (U x) (hgrad x) (hbase x) hamp
    have hsigned := integrable_signed_power_potential (zero_lt_one.trans hp)
      (Lp.aestronglyMeasurable (wkpBaseCoordinateCLM (U x))) hi
    rw [hduhamel x]
    calc
      _ ≤ |v x| + |κ * ∫ y in ball (0 : ℝ^3) (r x),
          Real.signedPower p (baseRepresentative (U x) y) / ‖y‖| := abs_sub _ _
      _ = |v x| + κ * |∫ y in ball (0 : ℝ^3) (r x),
          Real.signedPower p (baseRepresentative (U x) y) / ‖y‖| := by
        rw [abs_mul, abs_of_nonneg hκ]
      _ ≤ V + κ * (K * A ^ max (p - 4) 0) :=
        add_le_add (hv x) (mul_le_mul_of_nonneg_left (hsigned.2.trans hb) hκ)
      _ = _ := by ring
  have hfeedback : A ≤ 1 + V + κ * K * A ^ max (p - 4) 0 := by
    apply csSup_le (insert_nonempty 1 _)
    intro z hz
    rcases hz with rfl | ⟨x, rfl⟩
    · have hterm : 0 ≤ κ * K * A ^ max (p - 4) 0 := by positivity
      linarith
    · exact (hpoint x).trans (by linarith)
  have hq : 0 ≤ A ^ max (p - 4) 0 := Real.rpow_nonneg (zero_le_one.trans hA) _
  have hclosed : A ≤ (1 + V + κ * K) * (1 + A ^ max (p - 4) 0) := by
    nlinarith [mul_nonneg hκ hK, mul_nonneg hV hq]
  exact fun x ↦ (huA x).trans (hscalar A (zero_le_one.trans hA) hclosed)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
