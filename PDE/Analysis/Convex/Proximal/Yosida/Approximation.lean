/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Yosida.Basic
public import PDE.Analysis.Convex.Subdifferential.MinimalNorm

/-!
# Uniform Yosida bounds and approximation of the identity

At a point with a subgradient, monotonicity bounds the Yosida norm by the norm of every
subgradient. The minimum of these norms is attained, so the supremum over positive parameters
has the bound of Evans, §9.6.1, Theorem 2(v).

For Theorem 2(vi), the displacement estimate at domain points combines with nonexpansiveness
to give strong convergence at every point in the closure of the subdifferential domain.
The theorem permits any positive parameter family tending to zero; density of that domain
in the whole Hilbert space is not assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, Theorem 2(v)-(vi), p. 564, and steps 4 and 5 of
  its proof, pp. 564-565. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal} (hproper : IsProper I)
  (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)

/-- Every subgradient at the input bounds the norm of its Yosida approximation. -/
theorem norm_yosidaApproximation_le_of_mem_subdifferential
    {lambda : ℝ} (hlambda : 0 < lambda) {w v : H} (hv : v ∈ subdifferential I w) :
    ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda w‖ ≤ ‖v‖ := by
  let J := resolvent I hproper hconvex hlsc lambda hlambda w
  let A := yosidaApproximation I hproper hconvex hlsc lambda hlambda w
  have heq : J + lambda • A = w :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda w
  have hsub : w - J = lambda • A :=
    sub_eq_iff_eq_add.2 (by simpa only [add_comm] using heq.symm)
  have hmono : 0 ≤ inner ℝ (v - A) (w - J) :=
    subdifferential_monotone hproper hv
      (yosidaApproximation_mem_subdifferential hproper hconvex hlsc hlambda w)
  rw [hsub, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq] at hmono
  have hpair : ‖A‖ ^ 2 ≤ inner ℝ v A := by
    have := nonneg_of_mul_nonneg_right hmono hlambda
    linarith
  simpa only [inv_one, one_mul] using
    norm_le_of_mul_norm_sq_le_inner zero_lt_one (by simpa only [one_mul] using hpair)

/-- The resolvent displacement is bounded by the parameter times any subgradient norm. -/
theorem norm_resolvent_sub_self_le_of_mem_subdifferential
    {lambda : ℝ} (hlambda : 0 < lambda) {w v : H} (hv : v ∈ subdifferential I w) :
    ‖resolvent I hproper hconvex hlsc lambda hlambda w - w‖ ≤ lambda * ‖v‖ := by
  let J := resolvent I hproper hconvex hlsc lambda hlambda w
  let A := yosidaApproximation I hproper hconvex hlsc lambda hlambda w
  have heq : J + lambda • A = w :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda w
  have hsub : J - w = -(lambda • A) := by
    have h := congrArg (fun z ↦ J - z) heq
    simpa only [sub_add_cancel_left] using h.symm
  change ‖J - w‖ ≤ lambda * ‖v‖
  rw [hsub, norm_neg, norm_smul, Real.norm_of_nonneg hlambda.le]
  exact mul_le_mul_of_nonneg_left
    (norm_yosidaApproximation_le_of_mem_subdifferential hproper hconvex hlsc hlambda hv)
    hlambda.le

/-- The Yosida norms over all positive parameters have an attained least-subgradient bound.

The proof establishes boundedness and nonemptiness of the range before using its supremum. -/
theorem exists_minimal_subgradient_yosida_sup_bound {w : H}
    (hw : w ∈ subdifferentialDomain I) :
    ∃ v ∈ subdifferential I w, (∀ z ∈ subdifferential I w, ‖v‖ ≤ ‖z‖) ∧
      (⨆ p : {r : ℝ // 0 < r},
        ‖yosidaApproximation I hproper hconvex hlsc p.1 p.2 w‖) ≤ ‖v‖ := by
  obtain ⟨v, hv, hmin⟩ := exists_minimal_norm_subgradient hproper hw
  let f := fun p : {r : ℝ // 0 < r} ↦
    ‖yosidaApproximation I hproper hconvex hlsc p.1 p.2 w‖
  have hbound (p : {r : ℝ // 0 < r}) : f p ≤ ‖v‖ :=
    norm_yosidaApproximation_le_of_mem_subdifferential hproper hconvex hlsc p.2 hv
  have hbdd : BddAbove (range f) := ⟨‖v‖, by rintro _ ⟨p, rfl⟩; exact hbound p⟩
  have hne : (range f).Nonempty := ⟨f ⟨1, zero_lt_one⟩, ⟨⟨1, zero_lt_one⟩, rfl⟩⟩
  refine ⟨v, hv, hmin, ?_⟩
  exact (csSup_le_iff hbdd hne).2 (by rintro _ ⟨p, rfl⟩; exact hbound p)

/-- Approximation by a domain point controls the displacement at an arbitrary input. -/
theorem norm_resolvent_sub_self_le_of_near_domain
    {lambda : ℝ} (hlambda : 0 < lambda) (w : H) {y v : H}
    (hv : v ∈ subdifferential I y) :
    ‖resolvent I hproper hconvex hlsc lambda hlambda w - w‖ ≤
      2 * ‖w - y‖ + lambda * ‖v‖ := by
  let J := resolvent I hproper hconvex hlsc lambda hlambda
  have hdecomp : J w - w = (J w - J y) + (J y - y) + (y - w) := by abel
  change ‖J w - w‖ ≤ _
  calc
    ‖J w - w‖ ≤ ‖J w - J y‖ + ‖J y - y‖ + ‖y - w‖ := by
      rw [hdecomp]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖w - y‖ + lambda * ‖v‖ + ‖y - w‖ := by
      exact add_le_add
        (add_le_add (norm_resolvent_sub_le hproper hconvex hlsc hlambda w y)
          (norm_resolvent_sub_self_le_of_mem_subdifferential hproper hconvex hlsc hlambda hv))
        le_rfl
    _ = _ := by rw [norm_sub_rev y w]; ring

/-- The resolvent converges strongly to the identity on the closure of its subdifferential
domain along every positive parameter family tending to zero. -/
theorem tendsto_resolvent_of_mem_closure_domain {ι : Type*} {l : Filter ι}
    (lambda : ι → ℝ) (hlambda : ∀ i, 0 < lambda i)
    (hlimit : Tendsto lambda l (𝓝 0)) {w : H}
    (hw : w ∈ closure (subdifferentialDomain I)) :
    Tendsto (fun i ↦ resolvent I hproper hconvex hlsc (lambda i) (hlambda i) w) l (𝓝 w) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨y, hy, hwy⟩ := Metric.mem_closure_iff.1 hw (ε / 4) (by positivity)
  obtain ⟨v, hv⟩ := hy
  have hsmall : ∀ᶠ i in l, lambda i * ‖v‖ < ε / 2 := by
    have ht : Tendsto (fun i ↦ lambda i * ‖v‖) l (𝓝 (0 : ℝ)) := by
      simpa using hlimit.mul_const ‖v‖
    exact ht.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hsmall] with i hi
  have hb := norm_resolvent_sub_self_le_of_near_domain hproper hconvex hlsc (hlambda i) w hv
  rw [dist_eq_norm] at hwy ⊢
  linarith

end PDE.Analysis.Convex
