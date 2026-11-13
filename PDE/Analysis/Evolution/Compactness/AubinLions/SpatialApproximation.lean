/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Spatial approximation for Aubin–Lions compactness

The Hilbert-space proof of the Aubin–Lions lemma splits a bounded family of
trajectories `u ∈ L²(a, b; V)` with `u' ∈ L²(a, b; V*)` into a
finite-dimensional Galerkin part and a spatial tail. The tail is uniformly small.
For a stable trial system `(Pₙ)` in a Gelfand triple `V ↪ H ↪ V*`, the
pivot-space projections converge strongly to the identity on `H` and are
uniformly contractive, so they converge uniformly on compact subsets of `H`.
When the inclusion `ι : V ↪ H` is compact, the closed unit ball of `V` is
mapped into a compact set, and the approximation error `Pₙ ∘ ι - ι : V → H`
therefore tends to zero in operator norm.  Lifting pointwise to Bochner
spaces, one spatial cutoff makes `‖Pₙ u - u‖_{L^p(H)}` uniformly small on every
norm-bounded family of energy-space trajectories, with no control on the time
derivative.  The temporal half of the argument is in `TemporalCompactness`.

## Main results

* `StableTrialSystem.tendstoUniformlyOn_pivotProjection`: uniform convergence
  of `Pₙ` to the identity on compact subsets of `H`.
* `StableTrialSystem.tendsto_norm_inclusionApproximationError`: for a compact
  inclusion, `‖Pₙ ∘ ι - ι‖_{V → H} → 0`.
* `StableTrialSystem.tendsto_norm_inclusionApproximationErrorLp`,
  `StableTrialSystem.eventually_norm_inclusionApproximationErrorLp_apply_lt`:
  the same in Bochner `L^p`, uniformly on bounded families.

## References

* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
* J. Simon, "Compact sets in the space L^p(0,T;B)", *Ann. Mat. Pura Appl.* 146 (1986), 65-96.
  <https://doi.org/10.1007/BF01762360>
-/

@[expose] public section

noncomputable section


open Filter MeasureTheory Set
open scoped Topology InnerProductSpace

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

namespace StableTrialSystem

/-- The `n`th trial projection viewed as an operator on the pivot space. -/
def pivotProjection
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ) : H →L[ℝ] H :=
  (trials.projection n).pivotProjection

/-- The system pivot projection applies the bundled trial projection and then
includes the result into the pivot space. -/
@[simp]
theorem pivotProjection_apply
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ) (h : H) :
    trials.pivotProjection n h =
      T.inclusion ((trials.projection n).projection h : V) :=
  rfl

/-- Every system pivot projection has operator norm at most one. -/
theorem norm_pivotProjection_le
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ) :
    ‖trials.pivotProjection n‖ ≤ 1 :=
  (trials.projection n).norm_pivotProjection_le

/-- Stable trial-system projections converge strongly to the identity on the
pivot space. -/
theorem tendsto_pivotProjection
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (h : H) :
    Tendsto (fun n ↦ trials.pivotProjection n h) atTop (nhds h) := by
  simpa only [pivotProjection_apply] using
    StableTrialProjection.tendsto_inclusion_projection_of_eventually_approximable
      trials.projection trials.densePivot h

/-- Stable trial-system projections converge uniformly to the identity on
every compact subset of the pivot space. -/
theorem tendstoUniformlyOn_pivotProjection
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) {K : Set H} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n h ↦ trials.pivotProjection n h) id atTop K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  have hEq : Equicontinuous (fun n (x : K) ↦ trials.pivotProjection n x) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro x y n
    change dist (trials.pivotProjection n x) (trials.pivotProjection n y) ≤
      dist (x : H) (y : H)
    exact ((trials.pivotProjection n).lipschitzWith.dist_le_mul x y).trans (by
      simpa using mul_le_mul_of_nonneg_right (trials.norm_pivotProjection_le n)
        (dist_nonneg : 0 ≤ dist (x : H) y))
  exact UniformFun.tendsto_iff_tendstoUniformly.mp
    ((hEq.tendsto_uniformFun_iff_pi atTop _).mpr
      (tendsto_pi_nhds.mpr fun x ↦ trials.tendsto_pivotProjection x))

/-- If the energy-to-pivot inclusion is compact, stable trial projections
converge uniformly after inclusion on every closed energy-space ball. -/
theorem tendstoUniformlyOn_pivotProjection_inclusion_closedBall
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (hcompact : IsCompactOperator T.inclusion) (R : ℝ) :
    TendstoUniformlyOn
      (fun n v ↦ trials.pivotProjection n (T.inclusion v))
      T.inclusion atTop (Metric.closedBall (0 : V) R) := by
  obtain ⟨K, hKcompact, hKimage⟩ :=
    hcompact.image_closedBall_subset_compact R
  have huniform := trials.tendstoUniformlyOn_pivotProjection hKcompact
  have hsubset :
      Metric.closedBall (0 : V) R ⊆ T.inclusion ⁻¹' K := by
    intro v hv
    exact hKimage ⟨v, hv, rfl⟩
  simpa only [Function.comp_def, id_eq] using
    (huniform.comp T.inclusion).mono hsubset

/-- The error between the included energy vector and its pivot-space trial
projection, viewed as an operator from the energy space to the pivot space. -/
def inclusionApproximationError
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ) : V →L[ℝ] H :=
  (trials.pivotProjection n).comp T.inclusion - T.inclusion

/-- The inclusion approximation error is the projected inclusion minus the
original inclusion. -/
@[simp]
theorem inclusionApproximationError_apply
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ) (v : V) :
    trials.inclusionApproximationError n v =
      trials.pivotProjection n (T.inclusion v) - T.inclusion v :=
  rfl

/-- Compactness of the Gelfand inclusion upgrades strong trial-projection
convergence to convergence in operator norm after composition with the
inclusion. This is the spatial-tail estimate used in Aubin-Lions compactness. -/
theorem tendsto_norm_inclusionApproximationError
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (hcompact : IsCompactOperator T.inclusion) :
    Tendsto (fun n ↦ ‖trials.inclusionApproximationError n‖)
      atTop (nhds 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have huniform :=
    trials.tendstoUniformlyOn_pivotProjection_inclusion_closedBall
      hcompact 1
  have heventually :=
    (Metric.tendstoUniformlyOn_iff.mp huniform)
      (ε / 2) (half_pos hε)
  filter_upwards [heventually] with n hn
  have hop :
      ‖trials.inclusionApproximationError n‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (half_pos hε).le
    intro v hv
    have hvBall : v ∈ Metric.closedBall (0 : V) 1 := by
      simp [Metric.mem_closedBall, hv]
    have hvEstimate := hn v hvBall
    rw [inclusionApproximationError_apply, norm_sub_rev]
    simpa only [dist_eq_norm] using hvEstimate.le
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using
    hop.trans_lt (half_lt_self hε)

section Bochner

variable {α : Type*} [MeasurableSpace α]

/-- The spatial approximation error lifted pointwise to a Bochner `L^p`
space. -/
def inclusionApproximationErrorLp
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)] :
    Lp V p μ →L[ℝ] Lp H p μ :=
  (trials.inclusionApproximationError n).compLpL p μ

/-- Lifting the spatial approximation error to Bochner `L^p` does not
increase its operator norm. -/
theorem norm_inclusionApproximationErrorLp_le
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)] :
    ‖trials.inclusionApproximationErrorLp n p μ‖ ≤
      ‖trials.inclusionApproximationError n‖ :=
  ContinuousLinearMap.norm_compLpL_le _

/-- Compactness of the Gelfand inclusion makes the lifted spatial
approximation error converge to zero in Bochner-space operator norm. -/
theorem tendsto_norm_inclusionApproximationErrorLp
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (hcompact : IsCompactOperator T.inclusion)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)] :
    Tendsto
      (fun n ↦ ‖trials.inclusionApproximationErrorLp n p μ‖)
      atTop (nhds 0) :=
  squeeze_zero'
    (Eventually.of_forall fun n ↦
      norm_nonneg (trials.inclusionApproximationErrorLp n p μ))
    (Eventually.of_forall fun n ↦
      trials.norm_inclusionApproximationErrorLp_le n p μ)
    (trials.tendsto_norm_inclusionApproximationError hcompact)

/-- The Bochner `L^p` spatial tail is bounded by the energy-space trajectory
norm times the pointwise approximation-operator norm. -/
theorem norm_inclusionApproximationErrorLp_apply_le
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)]
    (u : Lp V p μ) :
    ‖trials.inclusionApproximationErrorLp n p μ u‖ ≤
      ‖trials.inclusionApproximationError n‖ * ‖u‖ := by
  calc
    ‖trials.inclusionApproximationErrorLp n p μ u‖ ≤
        ‖trials.inclusionApproximationErrorLp n p μ‖ * ‖u‖ :=
      (trials.inclusionApproximationErrorLp n p μ).le_opNorm u
    _ ≤ ‖trials.inclusionApproximationError n‖ * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (trials.norm_inclusionApproximationErrorLp_le n p μ)
        (norm_nonneg u)

/-- On every norm-bounded family of energy-space trajectories, one spatial
cutoff makes the Bochner spatial tail uniformly small. -/
theorem eventually_norm_inclusionApproximationErrorLp_apply_lt
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (hcompact : IsCompactOperator T.inclusion)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)]
    {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : Lp V p μ, ‖u‖ ≤ M →
      ‖trials.inclusionApproximationErrorLp n p μ u‖ < ε := by
  have hden : 0 < M + 1 := by linarith
  have hthreshold : 0 < ε / (M + 1) := div_pos hε hden
  have heventually :=
    (Metric.tendsto_nhds.mp
      (trials.tendsto_norm_inclusionApproximationErrorLp hcompact p μ))
      _ hthreshold
  filter_upwards [heventually] with n hn
  intro u hu
  have hop :
      ‖trials.inclusionApproximationErrorLp n p μ‖ <
        ε / (M + 1) := by
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg
        (norm_nonneg (trials.inclusionApproximationErrorLp n p μ))] at hn
    exact hn
  calc
    ‖trials.inclusionApproximationErrorLp n p μ u‖ ≤
        ‖trials.inclusionApproximationErrorLp n p μ‖ * ‖u‖ :=
      (trials.inclusionApproximationErrorLp n p μ).le_opNorm u
    _ ≤ ‖trials.inclusionApproximationErrorLp n p μ‖ * (M + 1) :=
      mul_le_mul_of_nonneg_left (hu.trans (by linarith))
        (norm_nonneg (trials.inclusionApproximationErrorLp n p μ))
    _ < (ε / (M + 1)) * (M + 1) :=
      mul_lt_mul_of_pos_right hop hden
    _ = ε := by field_simp

/-- The lifted inclusion error is the projected pivot trajectory minus the
included trajectory. -/
theorem inclusionApproximationErrorLp_apply_eq
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) (n : ℕ)
    (p : ENNReal) (μ : Measure α) [Fact (1 ≤ p)]
    (u : Lp V p μ) :
    trials.inclusionApproximationErrorLp n p μ u =
      (trials.pivotProjection n).compLpL p μ
          (T.inclusion.compLpL p μ u) -
        T.inclusion.compLpL p μ u := by
  change
    (trials.inclusionApproximationError n).compLpL p μ u =
      (trials.pivotProjection n).compLpL p μ
          (T.inclusion.compLpL p μ u) -
        T.inclusion.compLpL p μ u
  apply Lp.ext
  filter_upwards
      [(trials.inclusionApproximationError n).coeFn_compLpL u,
        (trials.pivotProjection n).coeFn_compLpL
          (T.inclusion.compLpL p μ u),
        T.inclusion.coeFn_compLpL u,
        Lp.coeFn_sub
          ((trials.pivotProjection n).compLpL p μ
            (T.inclusion.compLpL p μ u))
          (T.inclusion.compLpL p μ u)] with t herr hproj hinc hsub
  rw [herr, hsub]
  change
    trials.inclusionApproximationError n (u t) =
      ((trials.pivotProjection n).compLpL p μ
        (T.inclusion.compLpL p μ u)) t -
        (T.inclusion.compLpL p μ u) t
  rw [hproj, hinc]
  rfl

end Bochner

end StableTrialSystem

end PDE.Analysis.Evolution
