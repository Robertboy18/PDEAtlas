/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Scalar.Characteristics.Transport

/-!
# Maximal classical lifespan and shock onset

The global characteristic solution exists at every positive time below
`conservationShockTime`. No classical continuation can cross that threshold:
transporting the initial values and differentiating in the initial label
would make a nonzero initial derivative equal to zero at a degenerate
characteristic. This argument uses the infimum of degeneracy times and does
not require its attainment.

When a finite first degeneracy is attained at an initial label, the
spatial derivative of the constructed solution tends in norm to infinity
along that characteristic as time approaches the threshold from below.

Evans notes that the condition `1 + t g'(x - tF'(u)) F''(u) ≠ 0` for the implicit formula (61)
of §3.2.5, Example 5, fails at some `t > 0` when `F'' > 0` and `g' < 0`, and that in §3.4.1,
Example 1, the method breaks down for `t ≥ 1` because the projected characteristics of Burgers'
equation cross. Neither the exact lifespan nor the blow-up of the spatial derivative is stated
there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.5, Example 5, equations (59)-(61); §3.4.1(a), Example 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set PDE.Common
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.Scalar

/-- The formal shock time is nonnegative, including the value `⊤`. -/
theorem zero_le_conservationShockTime (a u₀ : ℝ → ℝ) :
    (0 : WithTop ℝ) ≤ conservationShockTime a u₀ := by
  classical
  by_cases hne : (conservationShockSet a u₀).Nonempty
  · have hle : (0 : ℝ) ≤ sInf (conservationShockSet a u₀) := le_csInf hne fun _ hr ↦ hr.1
    simpa [conservationShockTime, hne] using (WithTop.coe_le_coe.mpr hle :
      ((0 : ℝ) : WithTop ℝ) ≤ ((sInf (conservationShockSet a u₀) : ℝ) : WithTop ℝ))
  · simp [conservationShockTime, hne]

/-- Every degeneracy time lies above the formal shock time. -/
theorem conservationShockTime_le_of_mem {a u₀ : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ conservationShockSet a u₀) :
    conservationShockTime a u₀ ≤ (t : WithTop ℝ) := by
  have hne : (conservationShockSet a u₀).Nonempty := ⟨t, ht⟩
  have hb : BddBelow (conservationShockSet a u₀) := ⟨0, fun _ hr ↦ hr.1⟩
  simpa [conservationShockTime, hne] using (WithTop.coe_le_coe.mpr (csInf_le hb ht) :
      ((sInf (conservationShockSet a u₀) : ℝ) : WithTop ℝ) ≤ t)

/-- No classical solution with the prescribed initial data has a lifespan
longer than the formal shock time, whether or not its infimum is attained.
The C¹ hypotheses are local at each point of the closed time strip. -/
theorem classical_lifespan_le_conservationShockTime {a u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : Differentiable ℝ u₀) {T : ℝ}
    (hu : ∀ p : ℝ^2, p 0 ∈ Icc 0 T → ContDiffAt ℝ 1 u p)
    (hpde : ∀ p : ℝ^2, p 0 ∈ Icc 0 T → (∂[(0 : Fin 2)] u) p + a (u p) * (∂[(1 : Fin 2)] u) p = 0)
    (hinit : ∀ x : ℝ, u !₂[0, x] = u₀ x) :
    (T : WithTop ℝ) ≤ conservationShockTime a u₀ := by
  classical
  by_cases hne : (conservationShockSet a u₀).Nonempty
  · have hle : T ≤ sInf (conservationShockSet a u₀) := by
      refine le_csInf hne fun r hr ↦ ?_
      by_contra hn
      have hrT : r ≤ T := (lt_of_not_ge hn).le
      obtain ⟨ξ, hz⟩ := hr.2
      have hj := classical_solution_spatial_jacobian ha hu₀ hr.1
        (fun p hp ↦ hu p ⟨hp.1, hp.2.trans hrT⟩) (fun p hp ↦ hpde p ⟨hp.1, hp.2.trans hrT⟩) hinit ξ
      rw [hz, mul_zero] at hj
      simp [← hj] at hz
    simpa [conservationShockTime, hne] using (WithTop.coe_le_coe.mpr hle :
      (T : WithTop ℝ) ≤ ((sInf (conservationShockSet a u₀) : ℝ) : WithTop ℝ))
  · simp [conservationShockTime, hne]

/-- The global pre-shock solution admits no C¹ continuation past its
shock time. It is enough that a proposed continuation agrees with it on one
positive pre-shock time slice. -/
theorem not_exists_classical_continuation {a u₀ : ℝ → ℝ}
    (ha : ContDiff ℝ 1 a) (hu₀ : ContDiff ℝ 1 u₀) {s T : ℝ}
    (hs0 : 0 < s) (hs : (s : WithTop ℝ) < conservationShockTime a u₀)
    (hT : conservationShockTime a u₀ < (T : WithTop ℝ)) :
    ¬ ∃ u : ℝ^2 → ℝ, (∀ p : ℝ^2, p 0 ∈ Icc s T → ContDiffAt ℝ 1 u p) ∧
      (∀ p : ℝ^2, p 0 ∈ Icc s T → (∂[(0 : Fin 2)] u) p + a (u p) * (∂[(1 : Fin 2)] u) p = 0) ∧
      (∀ x : ℝ, u !₂[s, x] = conservationClassicalSolution a u₀ !₂[s, x]) := by
  classical
  rintro ⟨u, hu, hpde, hinit⟩
  have hne : (conservationShockSet a u₀).Nonempty := by
    by_contra hn
    simp [conservationShockTime, hn] at hT
  have hinf : sInf (conservationShockSet a u₀) < T := by
    simpa [conservationShockTime, hne] using hT
  obtain ⟨r, hr, hrT⟩ := exists_lt_of_csInf_lt hne hinf
  have hsr : s ≤ r := (WithTop.coe_lt_coe.mp (hs.trans_le (conservationShockTime_le_of_mem hr))).le
  have heq : (fun ξ ↦ u !₂[r, conservationCharPosition a u₀ r ξ]) = u₀ := by
    funext ξ
    apply classical_solution_eq_along_characteristic ha ξ (u₀ ξ) hsr
    · exact fun z hz ↦ hu _ ⟨hz.1, hz.2.trans hrT.le⟩
    · exact fun z hz ↦ hpde _ ⟨hz.1, hz.2.trans hrT.le⟩
    · rw [hinit]
      exact conservationClassicalSolution_characteristic
        ha.differentiable_one hu₀.differentiable_one hs0.le hs ξ
  obtain ⟨ξ, hz⟩ := hr.2
  have hd := hasDerivAt_characteristic_label ha.differentiable_one hu₀.differentiable_one r ξ
    (hu _ ⟨hsr, hrT.le⟩).differentiableAt_one
  rw [heq, hz, mul_zero] at hd
  simp [hd.deriv] at hz

/-- At an attained finite first degeneracy, the norm of the solution's
spatial derivative tends to infinity along the corresponding characteristic.
Attainment is explicit because the infimum over an unbounded label line need
not be achieved. -/
theorem tendsto_norm_partialDeriv_space_at_shock {a u₀ : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hu₀ : ContDiff ℝ 1 u₀) {T : ℝ} (hT : conservationShockTime a u₀ = (T : WithTop ℝ)) (ξ : ℝ)
    (hzero : 1 + T * deriv a (u₀ ξ) * deriv u₀ ξ = 0) :
    Tendsto (fun t : ℝ ↦ ‖(∂[(1 : Fin 2)] (conservationClassicalSolution a u₀))
      !₂[t, conservationCharPosition a u₀ t ξ]‖) (𝓝[<] T) atTop := by
  have hTnonneg : 0 ≤ T := by
    have h := zero_le_conservationShockTime a u₀
    rw [hT] at h
    exact WithTop.coe_le_coe.mp h
  have hTne : T ≠ 0 := by
    intro h
    simp [h] at hzero
  have hTpos : 0 < T := lt_of_le_of_ne hTnonneg hTne.symm
  have hu₀ne : deriv u₀ ξ ≠ 0 := by
    intro h
    simp [h] at hzero
  let d : ℝ → ℝ := fun t ↦ 1 + t * deriv a (u₀ ξ) * deriv u₀ ξ
  have hd : Continuous d := by dsimp [d]; fun_prop
  have hevent : ∀ᶠ t in 𝓝[<] T, 0 < t ∧ t < T := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hTpos), self_mem_nhdsWithin]
      with t ht hlt using ⟨ht, hlt⟩
  have hdlimit : Tendsto d (𝓝[<] T) (𝓝 0) := by
    simpa only [show d T = 0 from hzero] using
      (hd.continuousAt (x := T)).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio T))
  have hdpos : ∀ᶠ t in 𝓝[<] T, d t ∈ Ioi 0 := by
    filter_upwards [hevent] with t ht using conservationCharDenom_pos_of_lt_shockTime a u₀ ht.1.le
      (by rw [hT]; exact WithTop.coe_lt_coe.mpr ht.2) ξ
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hdlimit, hdpos⟩).inv_tendsto_nhdsGT_zero
  apply (hinv.const_mul_atTop (norm_pos_iff.mpr hu₀ne)).congr'
  filter_upwards [hevent] with t ht
  have htpre : (t : WithTop ℝ) < conservationShockTime a u₀ := by
    rw [hT]
    exact WithTop.coe_lt_coe.mpr ht.2
  rw [partialDeriv_space_conservationClassicalSolution_characteristic ha hu₀ ht.1 htpre]
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos
      (conservationCharDenom_pos_of_lt_shockTime a u₀ ht.1.le htpre ξ)]
  rfl

end PDE.Hyperbolic.ConservationLaw.Scalar
