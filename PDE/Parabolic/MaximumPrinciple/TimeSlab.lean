/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import CAS.ExactTactic

/-!
# Comparison on a closed time slab

On a slab `closure Ω × [s, t]`, a subsolution with nonnegative potential is bounded by any
nonnegative bound `M` of its lateral and initial values (`matrix_subsolution_le_on_timeSlab`). This
is Evans's §7.1.4(a), Theorem 9(i), with the differential inequality, the semidefiniteness of `a`,
the sign of `c` and the regularity of `u` assumed only at times strictly between `s` and `t`.

Time translation applies `matrix_subsolution_le_of_boundary_le` on each shorter slab, and continuity
then gives the terminal value. `matrix_comparison_on_timeSlab` compares a subsolution with a
supersolution in the same way; in particular a single fixed barrier can be carried to the terminal
time.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.4(a), Theorem 9 (Weak maximum principle for `c ≥ 0`),
  pp. 390-391.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open Set

variable {n : ℕ}

/-- Weak comparison on `[s,t]`, using differential inequalities only on `(s,t)`.
The terminal-time conclusion follows by continuity from shorter slabs. -/
theorem matrix_subsolution_le_on_timeSlab
    {Ω : Set (ℝ^n)} {s t M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hst : s < t) (hM : 0 ≤ M)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (ha : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, (a x r).PosSemidef)
    (hc : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, 0 ≤ c x r)
    (u : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closure Ω ×ˢ Icc s t))
    (huspace : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, ContDiffAt ℝ 2 (fun y ↦ u y r) x)
    (hutime : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, DifferentiableAt ℝ (u x) r)
    (hsub : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, matrixParabolicOperator a b c u x r ≤ 0)
    (hlateral : ∀ x ∈ frontier Ω, ∀ r ∈ Icc s t, u x r ≤ M)
    (hinitial : ∀ x ∈ closure Ω, u x s ≤ M) :
    ∀ x ∈ closure Ω, ∀ r ∈ Icc s t, u x r ≤ M := by
  have hinterior : ∀ x ∈ closure Ω, ∀ q ∈ Ioo s t, u x q ≤ M := by
    intro x hx q hq
    have htime {r : ℝ} (hr : r ∈ Ioc 0 (q - s)) : s + r ∈ Ioo s t := by
      constructor <;> cas
    have htimeClosed {r : ℝ} (hr : r ∈ Icc 0 (q - s)) : s + r ∈ Icc s t := by
      constructor <;> cas
    have hshiftcont : ContinuousOn
        (fun p : ℝ^n × ℝ ↦ u p.1 (s + p.2)) (closedCylinder Ω (q - s)) :=
      hucont.comp (continuous_fst.prodMk (continuous_const.add continuous_snd)).continuousOn
        (fun _ hp ↦ ⟨hp.1, htimeClosed hp.2⟩)
    have hshift := matrix_subsolution_le_of_boundary_le
      hΩopen hΩne hΩcompact (sub_pos.mpr hq.1) hM
      (fun y r ↦ a y (s + r)) (fun y r ↦ b y (s + r)) (fun y r ↦ c y (s + r))
      (fun y hy r hr ↦ ha y hy (s + r) (htime hr))
      (fun y hy r hr ↦ hc y hy (s + r) (htime hr))
      (fun y r ↦ u y (s + r)) hshiftcont
      (fun y hy r hr ↦ huspace y hy (s + r) (htime hr))
      (fun y hy r hr ↦
        ((hutime y hy (s + r) (htime hr)).hasDerivAt.comp_const_add s r).differentiableAt)
      (fun y hy r hr ↦ by
        simpa only [matrixParabolicOperator, deriv_comp_const_add] using
          hsub y hy (s + r) (htime hr))
      (fun p hp ↦ by
        rcases hp with hl | hi
        · exact hlateral p.1 hl.1 (s + p.2) (htimeClosed hl.2)
        · have hpzero : p.2 = 0 := hi.2
          simpa only [hpzero, add_zero] using hinitial p.1 hi.1)
    have hpoint := hshift (x, q - s) ⟨hx, (sub_pos.mpr hq.1).le, le_rfl⟩
    simpa only [add_sub_cancel] using hpoint
  intro x hx r hr
  have hcont : ContinuousOn (u x) (Icc s t) :=
    hucont.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hq ↦ ⟨hx, hq⟩)
  apply le_on_closure (hinterior x hx) _ continuousOn_const
  · rwa [closure_Ioo hst.ne]
  · rwa [closure_Ioo hst.ne]

/-- Comparison of a subsolution and supersolution on a closed slab. In particular,
a single fixed barrier can be carried to the terminal time by continuity. -/
theorem matrix_comparison_on_timeSlab
    {Ω : Set (ℝ^n)} {s t : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hst : s < t)
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    (ha : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, (a x r).PosSemidef)
    (hc : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, 0 ≤ c x r)
    (u v : ℝ^n → ℝ → ℝ)
    (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closure Ω ×ˢ Icc s t))
    (hvcont : ContinuousOn (fun p : ℝ^n × ℝ ↦ v p.1 p.2) (closure Ω ×ˢ Icc s t))
    (huspace : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, ContDiffAt ℝ 2 (fun y ↦ u y r) x)
    (hvspace : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, ContDiffAt ℝ 2 (fun y ↦ v y r) x)
    (hutime : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, DifferentiableAt ℝ (u x) r)
    (hvtime : ∀ x ∈ Ω, ∀ r ∈ Ioo s t, DifferentiableAt ℝ (v x) r)
    (hoperator : ∀ x ∈ Ω, ∀ r ∈ Ioo s t,
      matrixParabolicOperator a b c u x r ≤ matrixParabolicOperator a b c v x r)
    (hlateral : ∀ x ∈ frontier Ω, ∀ r ∈ Icc s t, u x r ≤ v x r)
    (hinitial : ∀ x ∈ closure Ω, u x s ≤ v x s) :
    ∀ x ∈ closure Ω, ∀ r ∈ Icc s t, u x r ≤ v x r := by
  have h := matrix_subsolution_le_on_timeSlab hΩopen hΩne hΩcompact hst le_rfl a b c ha hc
    (fun x r ↦ u x r - v x r) (hucont.sub hvcont)
    (fun x hx r hr ↦ (huspace x hx r hr).sub (hvspace x hx r hr))
    (fun x hx r hr ↦ (hutime x hx r hr).sub (hvtime x hx r hr))
    (fun x hx r hr ↦ by
      rw [matrixParabolicOperator_sub a b c
        (huspace x hx r hr) (hvspace x hx r hr) (hutime x hx r hr) (hvtime x hx r hr)]
      exact sub_nonpos.mpr (hoperator x hx r hr))
    (fun x hx r hr ↦ sub_nonpos.mpr (hlateral x hx r hr))
    (fun x hx ↦ sub_nonpos.mpr (hinitial x hx))
  exact fun x hx r hr ↦ sub_nonpos.mp (h x hx r hr)

end ParabolicMaximum
