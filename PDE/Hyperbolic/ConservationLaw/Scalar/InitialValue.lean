/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.InitialValueWeakForm
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Initial-value weak solutions for one-dimensional conservation laws

We add the boundary term at `t = 0` that is absent from the interior
distributional predicate `PDE.Hyperbolic.ConservationLaw.Scalar.IsWeakSolution`.

For

`u_t + (f(u))_x = 0,    u(0, x) = u₀(x),`

the forward-half-space formulation is

`∫_{t > 0} (u φ_t + f(u) φ_x) dt dx + ∫ u₀(x) φ(0, x) dx = 0`.

The direct initial-boundary equation is the shared state-space-generic
`PDE.Hyperbolic.ConservationLaw.IsWeakInitialValueSolution`. We define
the standard strong initial trace in `L¹_loc(ℝ)` and the scalar weak and entropy
solution classes built from it. The trace state space may be any normed additive
commutative group.

## Main results

* `IsWeakInitialValueSolution.interior`: the half-space formulation with
  boundary term implies the interior weak equation on `t > 0`.
* `HasInitialTraceLocallyL1`: strong attainment of the datum,
  `∫_a^b ‖u(t, x) - u₀(x)‖ dx → 0` as `t ↓ 0` for every compact interval, with
  the integrability clauses needed to make the Bochner integrals meaningful.
* `HasInitialTraceLocallyL1.unique_ae`: a strong local `L¹` trace is unique up
  to a null set.
* `HasInitialTraceLocallyL1.tendsto_integral_smul_sub`: the trace is also
  attained weakly against continuous compactly supported test functions.
* `IsWeakSolutionWithInitialTrace`, `IsEntropySolutionWithInitialTrace`: an
  interior (entropy) weak solution together with the strong initial trace.
* `hasInitialTraceLocallyL1_of_dominated`: the trace from almost-everywhere
  pointwise convergence and a locally integrable dominator, by dominated
  convergence.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equations (2)-(4) and the definition of an integral
  solution; §11.4.3, definition of an entropy solution, p. 650.
  <https://doi.org/10.1090/gsm/019>
* S. N. Kružkov, *First order quasilinear equations in several independent variables*,
  Math. USSR-Sb. 10 (1970), 217-243, for generalized solutions of the Cauchy problem in the class of
  bounded measurable functions.
  <https://doi.org/10.1070/SM1970v010n02ABEH002156>
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.Scalar

noncomputable section

open Filter MeasureTheory Set
open PDE.Common TopologicalSpace
open scoped Distributions Topology

/-- A direct scalar weak solution, including the initial-boundary term, is an
interior weak solution on `t > 0`. -/
theorem IsWeakInitialValueSolution.interior {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakInitialValueSolution flux u₀ u) :
    IsWeakSolution flux forwardHalfSpace u := by
  exact
    { u_locallyIntegrable := hu.u_locallyIntegrable
      flux_locallyIntegrable := hu.flux_locallyIntegrable
      weak_eq := by
        intro φ
        simpa [weakIntegrand, PDE.Hyperbolic.ConservationLaw.InteriorWeakForm.integrand,
          mul_comm] using hu.interior_identity φ }

variable {E : Type*} [NormedAddCommGroup E]

/-- Strong attainment of locally integrable initial data in `L¹_loc(ℝ)` from positive times.

Both integrability clauses are essential. Local integrability of `u₀` makes it
an admissible initial datum. Eventual integrability of the trace error prevents
the Bochner integral's value `0` for non-integrable functions from making the
convergence condition hold vacuously.
-/
def HasInitialTraceLocallyL1
    (u : ℝ^2 → E) (u₀ : ℝ → E) : Prop :=
  LocallyIntegrable u₀ volume ∧
    ∀ a b : ℝ,
      (∀ᶠ t : ℝ in 𝓝[>] 0,
          IntegrableOn
            (fun x : ℝ ↦ u !₂[t, x] - u₀ x)
            (Icc a b) volume) ∧
        Tendsto
          (fun t : ℝ ↦
            ∫ x : ℝ in Icc a b, ‖u !₂[t, x] - u₀ x‖ ∂volume)
          (𝓝[>] 0) (𝓝 0)

/-- Initial data admitting a strong local `L¹` trace are locally integrable. -/
theorem HasInitialTraceLocallyL1.initial_locallyIntegrable {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) :
    LocallyIntegrable u₀ volume :=
  hu.1

/-- Near the initial time, the trace error is Bochner integrable on every
compact interval. -/
theorem HasInitialTraceLocallyL1.eventually_integrableOn_sub {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) (a b : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, IntegrableOn (fun x : ℝ ↦ u !₂[t, x] - u₀ x) (Icc a b) volume :=
  (hu.2 a b).1

/-- The local integral of the norm of the trace error tends to zero. -/
theorem HasInitialTraceLocallyL1.tendsto_setIntegral_norm_sub {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) (a b : ℝ) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ in Icc a b, ‖u !₂[t, x] - u₀ x‖ ∂volume) (𝓝[>] 0) (𝓝 0) :=
  (hu.2 a b).2

/-- A strong local `L¹` initial trace is unique up to almost-everywhere
equality.

On each compact interval, the distance between two candidate traces is
bounded by the sum of their errors from the same positive-time slice. Passing
this bound to the right-time limit makes that distance vanish in `L¹`; integer
intervals then cover the whole spatial line. -/
theorem HasInitialTraceLocallyL1.unique_ae {u : ℝ^2 → E} {u₀ v₀ : ℝ → E}
    (hu : HasInitialTraceLocallyL1 u u₀) (hv : HasInitialTraceLocallyL1 u v₀) :
    u₀ =ᵐ[volume] v₀ := by
  have hinterval (a b : ℝ) : u₀ =ᵐ[volume.restrict (Icc a b)] v₀ := by
    have htraceInt : IntegrableOn (fun x : ℝ ↦ u₀ x - v₀ x) (Icc a b) volume :=
      (hu.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc).sub
        (hv.initial_locallyIntegrable.integrableOn_isCompact isCompact_Icc)
    -- the distance of the two traces is bounded by the two errors of the same slice
    have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, (∫ x : ℝ in Icc a b, ‖u₀ x - v₀ x‖ ∂volume) ≤
        (∫ x : ℝ in Icc a b, ‖u !₂[t, x] - u₀ x‖ ∂volume) +
          ∫ x : ℝ in Icc a b, ‖u !₂[t, x] - v₀ x‖ ∂volume := by
      filter_upwards [hu.eventually_integrableOn_sub a b, hv.eventually_integrableOn_sub a b]
        with t huInt hvInt
      rw [← integral_add huInt.norm hvInt.norm]
      refine integral_mono htraceInt.norm (huInt.norm.add hvInt.norm) fun x ↦ ?_
      exact (norm_sub_le_norm_sub_add_norm_sub _ (u !₂[t, x]) _).trans_eq
        (by rw [norm_sub_rev (u₀ x)])
    have herr := (hu.tendsto_setIntegral_norm_sub a b).add (hv.tendsto_setIntegral_norm_sub a b)
    rw [add_zero] at herr
    have hzero := le_antisymm (ge_of_tendsto herr hbound) (integral_nonneg fun _ ↦ norm_nonneg _)
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun _ ↦ norm_nonneg _)
      htraceInt.norm).1 hzero] with x hx
    exact sub_eq_zero.mp (norm_eq_zero.mp hx)
  rw [← Measure.restrict_univ (μ := volume), ← iUnion_Icc_intCast ℝ,
    MeasureTheory.ae_eq_restrict_iUnion_iff]
  exact fun n ↦ hinterval n (n + 1)

/-- Strong local `L¹` convergence implies convergence against every continuous
compactly supported scalar test function.

Compact support places the test function in one interval. Its uniform norm
bound then reduces the pairing estimate to the defining local `L¹` error.
-/
theorem HasInitialTraceLocallyL1.tendsto_integral_smul_sub [NormedSpace ℝ E] {u : ℝ^2 → E}
    {u₀ : ℝ → E} (hu : HasInitialTraceLocallyL1 u u₀) {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, φ x • (u !₂[t, x] - u₀ x) ∂volume) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hsupport⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_zero_eq_Icc] at hsupport
  obtain ⟨C, hC⟩ := hφ.bounded_above_of_compact_support hφc
  have hintegral_eq (t : ℝ) : (∫ x : ℝ, φ x • (u !₂[t, x] - u₀ x) ∂volume) =
      ∫ x : ℝ in Icc (-R) R, φ x • (u !₂[t, x] - u₀ x) ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun hxφ ↦ hx (hsupport hxφ)]).symm
  refine squeeze_zero_norm' ?_ (by simpa using (hu.tendsto_setIntegral_norm_sub (-R) R).const_mul C)
  filter_upwards [hu.eventually_integrableOn_sub (-R) R] with t ht
  rw [hintegral_eq, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (ht.norm.const_mul C) (.of_forall fun x ↦ by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))

/-- An interior weak solution on `t > 0` together with strong local `L¹`
attainment of its initial data.

This is the trace formulation of the conservation-law IVP.  It is especially
convenient for entropy solutions, whose interior distributional identity and
initial trace are often established by different arguments.
-/
def IsWeakSolutionWithInitialTrace
    (flux : ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop :=
  IsWeakSolution flux forwardHalfSpace u ∧
    HasInitialTraceLocallyL1 u u₀

/-- The interior distributional solution carried by a weak solution with
initial trace. -/
theorem IsWeakSolutionWithInitialTrace.interior {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakSolutionWithInitialTrace flux u₀ u) :
    IsWeakSolution flux forwardHalfSpace u :=
  hu.1

/-- Strong local `L¹` attainment of the prescribed initial datum. -/
theorem IsWeakSolutionWithInitialTrace.initialTrace {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsWeakSolutionWithInitialTrace flux u₀ u) :
    HasInitialTraceLocallyL1 u u₀ :=
  hu.2

/-- An entropy weak solution on `t > 0` that attains the prescribed initial
datum strongly in `L¹_loc`.
-/
def IsEntropySolutionWithInitialTrace
    (flux : ℝ → ℝ) (u₀ : ℝ → ℝ) (u : ℝ^2 → ℝ) : Prop :=
  IsEntropyWeakSolution flux forwardHalfSpace u ∧
    HasInitialTraceLocallyL1 u u₀

/-- The interior entropy solution carried by an entropy solution with initial
trace. -/
theorem IsEntropySolutionWithInitialTrace.interior {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsEntropySolutionWithInitialTrace flux u₀ u) :
    IsEntropyWeakSolution flux forwardHalfSpace u :=
  hu.1

/-- Strong local `L¹` attainment of the prescribed initial datum. -/
theorem IsEntropySolutionWithInitialTrace.initialTrace {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsEntropySolutionWithInitialTrace flux u₀ u) :
    HasInitialTraceLocallyL1 u u₀ :=
  hu.2

/-- Forget the entropy inequalities while retaining the weak equation and initial trace. -/
theorem IsEntropySolutionWithInitialTrace.toWeak {flux : ℝ → ℝ} {u₀ : ℝ → ℝ} {u : ℝ^2 → ℝ}
    (hu : IsEntropySolutionWithInitialTrace flux u₀ u) :
    IsWeakSolutionWithInitialTrace flux u₀ u :=
  ⟨hu.interior.weak, hu.initialTrace⟩

/-- A dominated-convergence criterion for the local `L¹` initial trace.

This theorem is independent of any particular conservation law:
it passes from almost-everywhere pointwise right-time
convergence and a uniform local dominator to the strong local trace.
-/
theorem hasInitialTraceLocallyL1_of_dominated {u : ℝ^2 → E} {u₀ : ℝ → E}
    (hu₀ : LocallyIntegrable u₀ volume)
    (hMeas : ∀ a b : ℝ, ∀ᶠ t : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun x : ℝ ↦ u !₂[t, x] - u₀ x) (volume.restrict (Icc a b)))
    (hDom : ∀ a b : ℝ, ∃ g : ℝ → ℝ, Integrable g (volume.restrict (Icc a b)) ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ∀ᵐ x ∂volume.restrict (Icc a b), ‖u !₂[t, x] - u₀ x‖ ≤ g x)
    (hLim : ∀ᵐ x ∂volume, Tendsto (fun t : ℝ ↦ u !₂[t, x]) (𝓝[>] 0) (𝓝 (u₀ x))) :
    HasInitialTraceLocallyL1 u u₀ := by
  refine ⟨hu₀, fun a b ↦ ?_⟩
  obtain ⟨g, hg, hgDom⟩ := hDom a b
  refine ⟨by filter_upwards [hMeas a b, hgDom] with t htMeas htDom using hg.mono' htMeas htDom, ?_⟩
  simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Icc a b)) (f := fun _ ↦ (0 : ℝ)) g ((hMeas a b).mono fun t ht ↦ ht.norm)
      (hgDom.mono fun t ht ↦ ht.mono fun x hx ↦ by simpa using hx) hg
      (ae_restrict_of_ae (hLim.mono fun x hx ↦ by
        simpa using (hx.sub (tendsto_const_nhds (x := u₀ x))).norm))

end

end PDE.Hyperbolic.ConservationLaw.Scalar
