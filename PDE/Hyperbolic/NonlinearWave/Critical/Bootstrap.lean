/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.QuinticHolder
public import PDE.Analysis.MeasureTheory.Lp.TimeInterval
import CAS.ExactTactic

/-!
# Nonlinear critical Strichartz bootstrap

The quintic forcing satisfies the Hölder bound proved in `QuinticHolder`. The intermediate value
theorem excludes crossing the quartic barrier. Bounded prefix norms then give finite critical mixed
norm on the entire half-open band.

The linear Strichartz inequality and the small uniform L⁶ bound are hypotheses. The nonlinear
estimate, prefix continuity and terminal integrability are conclusions of the proof.

This is the derivation of (20) in step 4 of the proof of Evans, §12.4, Theorem 3, in an abstract
form with a fixed spatial measure; `memLp_four_twelve_cone_of_strichartz` applies it to backward
cones. With the linear estimate (21) and the bound `‖u⁵‖_{L²} ≤ ‖u‖_{L⁶} ‖u‖_{L¹²}⁴`, a small L⁶
norm gives `φ(τ) ≤ C₁ + εφ(τ)⁴` with `φ(s) = 0`, and `lt_two_mul_of_quartic_bound` gives
`φ(τ) < 2C₁`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Theorem 3, step 4 of its proof, equations (20)-(21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace WaveEquation.Critical

/-- A continuous function starting at zero cannot cross the forbidden quartic
barrier when the coefficient is small. -/
theorem lt_two_mul_of_quartic_bound {φ : ℝ → ℝ} {s t C ε : ℝ} (hφ : ContinuousOn φ (Icc s t))
    (hs : φ s = 0) (hC : 0 < C) (hsmall : ε * (2 * C) ^ 4 < C)
    (hbound : ∀ r ∈ Icc s t, φ r ≤ C + ε * φ r ^ 4) :
    ∀ r ∈ Icc s t, φ r < 2 * C := by
  intro r hr
  by_contra h
  have hrφ : 2 * C ≤ φ r := le_of_not_gt h
  have hsφ : φ s ≤ 2 * C := by rw [hs]; positivity
  obtain ⟨q, hq, heq⟩ := intermediate_value_Icc hr.1
    (hφ.mono (Icc_subset_Icc_right hr.2)) ⟨hsφ, hrφ⟩
  have hb := hbound q ⟨hq.1, hq.2.trans hr.2⟩
  rw [heq] at hb
  linarith


variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]
  {u : ℝ × X → ℝ} {s T C K M : ℝ}

/-- The nonlinear part of the critical Strichartz bootstrap. Only preterminal
prefixes are assumed to have finite mixed norm; the conclusion supplies the full band. -/
theorem memLp_four_twelve_of_quintic_strichartz_bound (hsT : s < T) (hu : Measurable u) (hC : 0 < C)
    (hK : 0 ≤ K) (hsmall : (K * M) * (2 * C) ^ 4 < C)
    (hu12 : ∀ t ∈ Ico s T, MemLp (fun x ↦ u (t, x)) 12 ν)
    (hu6 : ∀ t ∈ Ico s T, MemLp (fun x ↦ u (t, x)) 6 ν)
    (hM : ∀ t ∈ Ico s T, lpNorm (fun x ↦ u (t, x)) 6 ν ≤ M)
    (hlocal : ∀ t ∈ Ico s T,
      MemLp (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) 4 (volume.restrict (Icc s t)))
    (hlinear : ∀ t ∈ Ico s T, lpNorm (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) 4
      (volume.restrict (Icc s t)) ≤ C + K * ∫ r in Icc s t, lpNorm (fun x ↦ u (r, x) ^ 5) 2 ν) :
    MemLp (fun t ↦ lpNorm (fun x ↦ u (t, x)) 12 ν) 4 (volume.restrict (Ico s T)) := by
  have hmeas : Measurable (fun r ↦ lpNorm (fun x ↦ u (r, x)) 12 ν) :=
    (hu.eLpNorm_prod_right (by norm_num) (by norm_num)).ennreal_toReal
  refine memLp_four_Ico_of_prefix_bound hsT hmeas hlocal (B := 2 * C) fun t ht ↦ ?_
  apply le_of_lt
  apply lt_two_mul_of_quartic_bound (continuousOn_lpNorm_restrict_Icc_four hmeas (hlocal t ht))
    (by simp) hC hsmall _ t ⟨ht.1, le_rfl⟩
  intro r hr
  have hrT : r ∈ Ico s T := ⟨hr.1, hr.2.trans_lt ht.2⟩
  have hsub : Icc s r ⊆ Ico s T := fun q hq ↦ ⟨hq.1, hq.2.trans_lt hrT.2⟩
  have hh := integral_lpNorm_pow_four_smul_le (μ := volume.restrict (Icc s r))
    hu hu (ae_restrict_of_forall_mem measurableSet_Icc (fun q hq ↦ hu12 q (hsub hq)))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun q hq ↦ hu6 q (hsub hq)))
    (ae_restrict_of_forall_mem measurableSet_Icc (fun q hq ↦ hM q (hsub hq))) (hlocal r hrT)
  simp only [smul_eq_mul, ← pow_succ] at hh
  calc
    _ ≤ C + K * ∫ q in Icc s r, lpNorm (fun x ↦ u (q, x) ^ 5) 2 ν := hlinear r hrT
    _ ≤ C + K * (lpNorm (fun q ↦ lpNorm (fun x ↦ u (q, x)) 12 ν) 4
          (volume.restrict (Icc s r)) ^ 4 * M) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hh hK)
    _ = _ := by
      have hmul (z : ℝ) : K * (z * M) = (K * M) * z := by cas
      rw [hmul]

end WaveEquation.Critical
