/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Viscosity
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Regularity
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Semigroup
import CAS.ExactTactic

/-!
# Hopf–Lax viscosity solutions in one space dimension

This is the one-dimensional case of Theorem 3 in Evans, §10.3.4, where the Hopf–Lax formula is
shown to be a viscosity solution.

The first lemmas transfer viscosity properties along equality on an open domain.
We then prove the Hopf–Lax subsolution and supersolution inequalities under
the stated convexity, coercivity, attainment, and regularity hypotheses. The
conclusion is `IsContinuousDifferentiableTestSolution` on positive time,
together with the initial trace for Lipschitz initial data.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.3.4, Theorem 3; §3.3.2(b), Lemma 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace HamiltonJacobi1D

noncomputable section

set_option linter.missingDocs true

open PDE.Common

open Filter
open scoped Topology

/-- Hopf–Lax spacetime profile, with coordinate `0` interpreted as time and
coordinate `1` as space. -/
noncomputable def hopfLaxSpacetime (H φ : ℝ → ℝ) : ℝ^2 → ℝ :=
  fun x ↦ HopfLax1D.hopfLax H φ (x 0) (x 1)

private theorem isAmbientDifferentiableTestSubsolution_congr_of_eqOn {H : ℝ → ℝ} {U : Set ℝ^2}
    (hU : IsOpen U) {u v : ℝ^2 → ℝ} (hEq : Set.EqOn u v U) :
    IsAmbientDifferentiableTestSubsolution H U u ↔ IsAmbientDifferentiableTestSubsolution H U v :=
  forall₂_congr fun _ hx ↦ forall_congr' fun ψ ↦ imp_congr_right fun _ ↦ imp_congr_left <|
    Filter.EventuallyEq.isLocalMax_iff <|
      (hU.eventually_mem hx).mono fun y hy ↦ congrArg (· - ψ y) (hEq hy)

private theorem isAmbientDifferentiableTestSupersolution_congr_of_eqOn {H : ℝ → ℝ} {U : Set ℝ^2}
    (hU : IsOpen U) {u v : ℝ^2 → ℝ} (hEq : Set.EqOn u v U) :
    IsAmbientDifferentiableTestSupersolution H U u ↔
      IsAmbientDifferentiableTestSupersolution H U v :=
  forall₂_congr fun _ hx ↦ forall_congr' fun ψ ↦ imp_congr_right fun _ ↦ imp_congr_left <|
    Filter.EventuallyEq.isLocalMin_iff <|
      (hU.eventually_mem hx).mono fun y hy ↦ congrArg (· - ψ y) (hEq hy)

/-- Differentiable-test solution inequalities are invariant under equality on the open
PDE domain. -/
theorem isAmbientDifferentiableTestSolution_congr_of_eqOn {H : ℝ → ℝ} {U : Set ℝ^2} (hU : IsOpen U)
    {u v : ℝ^2 → ℝ} (hEq : Set.EqOn u v U) :
    IsAmbientDifferentiableTestSolution H U u ↔ IsAmbientDifferentiableTestSolution H U v :=
  and_congr (isAmbientDifferentiableTestSubsolution_congr_of_eqOn hU hEq)
    (isAmbientDifferentiableTestSupersolution_congr_of_eqOn hU hEq)

/-!
## Transfer from a classical formula

If the Hopf–Lax profile agrees with a classical solution on an open set, then
it inherits the ambient-local viscosity inequalities there.
-/

/-- Transfer the classical characteristic solution to the Hopf–Lax profile on
an open subset where the two formulas agree. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSolution_of_eqOn {H φ : ℝ → ℝ} {U : Set ℝ^2}
    (hU : IsOpen U) {ξ : ℝ^2 → ℝ} (hH : Differentiable ℝ H) (hH' : Differentiable ℝ (deriv H))
    (hφ : Differentiable ℝ φ) (hφ' : Differentiable ℝ (deriv φ))
    (hξ : ∀ x ∈ U, DifferentiableAt ℝ ξ x) (hrel : IsFootpointOn H φ ξ U)
    (hEq : Set.EqOn (hopfLaxSpacetime H φ) (characteristicSolution H φ ξ) U) :
    IsAmbientDifferentiableTestSolution H U (hopfLaxSpacetime H φ) :=
  (isAmbientDifferentiableTestSolution_congr_of_eqOn hU hEq).2
    (characteristicSolution_isAmbientDifferentiableTestSolution hH hH' hφ hφ' hU hξ hrel)

/-!
## Hopf–Lax viscosity solution for the biconjugate Hamiltonian

The Hopf–Lax formula `u(t,x) = inf_y (φ(y) + t*L((x-y)/t))` solves
`u_t + H(u_x) = 0` in the viscosity sense under convexity/coercivity hypotheses on `H`.

The one-step dynamic-programming inequality proves the subsolution direction for the
biconjugate `H** := (H*)*`. An attained minimizing footpoint gives the reverse
inequality required for supersolutions. The two arguments therefore produce a
viscosity solution for `H**`; differentiable convex Hamiltonians are then recovered
from the proved biconjugacy identity `H** = H`. Both directions compare `u` with the test
function along the backward line `h ↦ x₀ - h • (1, q)`.
-/

/-- The backward line `h ↦ x₀ - h • (1, q)` in spacetime. -/
private def backwardLine (x0 : ℝ^2) (q h : ℝ) : ℝ^2 :=
  x0 - h • (EuclideanSpace.single 0 1 + q • EuclideanSpace.single 1 1)

/-- The backward line moves time back by `h` and space back by `h * q`. -/
private theorem backwardLine_apply (x0 : ℝ^2) (q h : ℝ) :
    backwardLine x0 q h 0 = x0 0 - h ∧ backwardLine x0 q h 1 = x0 1 - h * q := by
  simp [backwardLine]

/-- As `h ↓ 0`, the backward line tends to its base point `x₀`. -/
private theorem tendsto_backwardLine (x0 : ℝ^2) (q : ℝ) :
    Tendsto (backwardLine x0 q) (𝓝[>] 0) (𝓝 x0) :=
  ((continuous_const.sub (continuous_id.smul continuous_const)).tendsto' 0 x0
    (by simp)).mono_left nhdsWithin_le_nhds

/-- Right difference quotients of a differentiable test function along the backward line
converge to `ψₜ + q ψₓ`. -/
private theorem tendsto_backwardLine_slope {ψ : ℝ^2 → ℝ} {x0 : ℝ^2}
    (hψ : DifferentiableAt ℝ ψ x0) (q : ℝ) :
    Tendsto (fun h ↦ (ψ x0 - ψ (backwardLine x0 q h)) / h) (𝓝[>] 0)
      (𝓝 ((∂[(0 : Fin 2)] ψ) x0 + q * (∂[(1 : Fin 2)] ψ) x0)) := by
  set v : ℝ^2 := EuclideanSpace.single 0 1 + q • EuclideanSpace.single 1 1
  have h0 : backwardLine x0 q 0 = x0 := by simp [backwardLine]
  have hy : HasDerivAt (backwardLine x0 q) (-v) 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_sub x0).congr_deriv (by simp)
  have hv : fderiv ℝ ψ x0 v = (∂[(0 : Fin 2)] ψ) x0 + q * (∂[(1 : Fin 2)] ψ) x0 := by
    simp [v, partialDeriv]
  have h := (hψ.hasFDerivAt.comp_hasDerivAt_of_eq 0 hy h0.symm).tendsto_slope_zero_right.neg
  rw [map_neg, neg_neg, hv] at h
  refine h.congr fun h ↦ ?_
  rw [Function.comp_apply, Function.comp_apply, zero_add, h0, smul_eq_mul]
  ring

/-- The Hopf–Lax formula is a viscosity subsolution for the biconjugate
Hamiltonian whenever all positive-time infima are bounded below. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSubsolution_biconjugate {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H)
    (hbb : ∀ t > 0, ∀ x : ℝ, HopfLax1D.HopfLaxBddBelow H φ t x) :
    IsAmbientDifferentiableTestSubsolution (HopfLax1D.legendreTransform
      (HopfLax1D.legendreTransform H)) positiveTimeDomain (hopfLaxSpacetime H φ) := by
  intro x0 hx0 ψ hψ hmax
  have ht0 : 0 < x0 0 := hx0
  -- The one-step inequality along each slope `q` gives `ψₜ + q ψₓ ≤ H*(q)`.
  have hq (q : ℝ) : (∂[(0 : Fin 2)] ψ) x0 + q * (∂[(1 : Fin 2)] ψ) x0 ≤
      HopfLax1D.legendreTransform H q := by
    refine le_of_tendsto (tendsto_backwardLine_slope hψ q) ?_
    filter_upwards [Ioo_mem_nhdsGT ht0, (tendsto_backwardLine x0 q).eventually hmax] with h hh hloc
    have hs : 0 < x0 0 - h := sub_pos.2 hh.2
    have hHL := HopfLax1D.hopfLax_le_step hFin (z := x0 1 - h * q) hh.1 hs
      (by simpa using hbb _ ht0 (x0 1)) (hbb _ hs)
    rw [add_sub_cancel, sub_sub_cancel, mul_div_cancel_left₀ q hh.1.ne'] at hHL
    simp only [hopfLaxSpacetime, backwardLine_apply] at hloc
    rw [div_le_iff₀ hh.1]
    linarith
  -- Taking the supremum over `q` bounds the biconjugate Hamiltonian `H**`.
  have : HopfLax1D.legendreTransform (HopfLax1D.legendreTransform H) ((∂[(1 : Fin 2)] ψ) x0) ≤
      -(∂[(0 : Fin 2)] ψ) x0 :=
    csSup_le (Set.range_nonempty _) (Set.forall_mem_range.2 fun q ↦ by linarith [hq q])
  linarith

/-- If every positive-time Hopf–Lax infimum is attained, the profile is a
viscosity supersolution for the biconjugate Hamiltonian. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSupersolution_biconjugate_of_attains
    {H φ : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite H)
    (hbb : ∀ t > 0, ∀ x : ℝ, HopfLax1D.HopfLaxBddBelow H φ t x)
    (hatt : ∀ t > 0, ∀ x : ℝ, ∃ y : ℝ, HopfLax1D.hopfLax H φ t x =
      HopfLax1D.hopfLaxIntegrand H φ t x y) :
    IsAmbientDifferentiableTestSupersolution (HopfLax1D.legendreTransform
      (HopfLax1D.legendreTransform H)) positiveTimeDomain (hopfLaxSpacetime H φ) := by
  intro x0 hx0 ψ hψ hmin
  have ht0 : 0 < x0 0 := hx0
  -- Move backwards along the slope `q0` of an exact minimizer `y0` at `(t0, x0)`.
  obtain ⟨y0, hy0⟩ := hatt (x0 0) ht0 (x0 1)
  simp only [HopfLax1D.hopfLaxIntegrand] at hy0
  set q0 := (x0 1 - y0) / x0 0
  have hq0 : q0 * x0 0 = x0 1 - y0 := div_mul_cancel₀ _ ht0.ne'
  have hkey : HopfLax1D.legendreTransform H q0 ≤
      (∂[(0 : Fin 2)] ψ) x0 + q0 * (∂[(1 : Fin 2)] ψ) x0 := by
    refine ge_of_tendsto (tendsto_backwardLine_slope hψ q0) ?_
    filter_upwards [Ioo_mem_nhdsGT ht0, (tendsto_backwardLine x0 q0).eventually hmin] with h hh hloc
    have hs : 0 < x0 0 - h := sub_pos.2 hh.2
    -- The minimizing slope is unchanged along its backward characteristic.
    have hslope : (x0 1 - h * q0 - y0) / (x0 0 - h) = q0 := by
      rw [div_eq_iff hs.ne']
      linear_combination -hq0
    have hle := HopfLax1D.hopfLax_le_integrand (y := y0) (hbb _ hs (x0 1 - h * q0))
    simp only [HopfLax1D.hopfLaxIntegrand, hslope] at hle
    simp only [hopfLaxSpacetime, backwardLine_apply] at hloc
    rw [le_div_iff₀ hh.1]
    linarith
  -- Convert the `q0`-inequality into the supersolution inequality using `H**`.
  linarith [HopfLax1D.le_legendreTransform (p := q0) (hFin.legendreTransform
    ((∂[(1 : Fin 2)] ψ) x0))]

/-- If the Hopf–Lax infima are bounded below and attained, the profile is an
ambient-local viscosity solution for the biconjugate Hamiltonian. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_attains {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hbb : ∀ t > 0, ∀ x : ℝ, HopfLax1D.HopfLaxBddBelow H φ t x)
    (hatt : ∀ t > 0, ∀ x : ℝ, ∃ y : ℝ, HopfLax1D.hopfLax H φ t x =
      HopfLax1D.hopfLaxIntegrand H φ t x y) :
    IsAmbientDifferentiableTestSolution (HopfLax1D.legendreTransform
      (HopfLax1D.legendreTransform H)) positiveTimeDomain (hopfLaxSpacetime H φ) :=
  ⟨hopfLaxSpacetime_isAmbientDifferentiableTestSubsolution_biconjugate hFin hbb,
    hopfLaxSpacetime_isAmbientDifferentiableTestSupersolution_biconjugate_of_attains hFin hbb hatt⟩

/-- Domain-relative version of the Hopf–Lax biconjugate viscosity theorem, assuming
attainment of the Hopf–Lax infimum. -/
theorem hopfLaxSpacetime_isDifferentiableTestSolution_biconjugate_of_attains {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hbb : ∀ t > 0, ∀ x : ℝ, HopfLax1D.HopfLaxBddBelow H φ t x)
    (hatt : ∀ t > 0, ∀ x : ℝ, ∃ y : ℝ, HopfLax1D.hopfLax H φ t x =
      HopfLax1D.hopfLaxIntegrand H φ t x y) :
    IsDifferentiableTestSolution (HopfLax1D.legendreTransform (HopfLax1D.legendreTransform H))
      positiveTimeDomain (hopfLaxSpacetime H φ) :=
  (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_attains hFin hbb
    hatt).toSpatial isOpen_positiveTimeDomain

/-- Lipschitz initial data make every positive-time Hopf–Lax infimum finite
and attained, hence give an ambient-local viscosity solution for the
biconjugate Hamiltonian. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsAmbientDifferentiableTestSolution (HopfLax1D.legendreTransform
      (HopfLax1D.legendreTransform H)) positiveTimeDomain (hopfLaxSpacetime H φ) :=
  hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_attains hFin
    (fun _ ht _ ↦ HopfLax1D.hopfLaxBddBelow_of_lipschitz hFin hφ ht)
    fun _ ht _ ↦ by simpa using HopfLax1D.exists_hopfLax_eq_integrand_of_lipschitz hFin hφ ht

/-- Domain-relative Lipschitz-data Hopf–Lax theorem for the biconjugate Hamiltonian. -/
theorem hopfLaxSpacetime_isDifferentiableTestSolution_biconjugate_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsDifferentiableTestSolution (HopfLax1D.legendreTransform (HopfLax1D.legendreTransform H))
      positiveTimeDomain (hopfLaxSpacetime H φ) :=
  (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_lipschitz hFin
    hφ).toSpatial isOpen_positiveTimeDomain

/-- A convex differentiable Hamiltonian agrees with its biconjugate, so the
Lipschitz-data Hopf–Lax profile solves the original Hamilton–Jacobi equation
in the ambient-local viscosity sense. -/
theorem hopfLaxSpacetime_isAmbientDifferentiableTestSolution_of_lipschitz_convex {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsAmbientDifferentiableTestSolution H positiveTimeDomain (hopfLaxSpacetime H φ) := by
  have hbic := HopfLax1D.biconjugate_eq_of_convex_of_differentiable hFin hconv hH
  have hsol := hopfLaxSpacetime_isAmbientDifferentiableTestSolution_biconjugate_of_lipschitz hFin hφ
  exact ⟨fun x hx ψ hψ hmax ↦ hbic _ ▸ hsol.1 x hx ψ hψ hmax,
    fun x hx ψ hψ hmin ↦ hbic _ ▸ hsol.2 x hx ψ hψ hmin⟩

/-- The Hopf–Lax viscosity theorem relative to the forward-time domain, for a convex
differentiable Hamiltonian and Lipschitz initial data. -/
theorem hopfLaxSpacetime_isDifferentiableTestSolution_of_lipschitz_convex {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsDifferentiableTestSolution H positiveTimeDomain (hopfLaxSpacetime H φ) :=
  (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_of_lipschitz_convex hFin hconv hH
    hφ).toSpatial isOpen_positiveTimeDomain

/-- The Hopf–Lax spacetime profile is continuous on the forward-time domain for Lipschitz
initial data. -/
theorem hopfLaxSpacetime_continuousOn_of_lipschitz {H φ : ℝ → ℝ} (hFin : HopfLax1D.LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) :
    ContinuousOn (hopfLaxSpacetime H φ) positiveTimeDomain := by
  refine (LipschitzOnWith.of_dist_le' (K := (K : ℝ) + HopfLax1D.timeLipschitzConstant H K)
    fun p hp q hq ↦ ?_).continuousOn
  have hspace : |p 1 - q 1| ≤ dist p q := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p q (1 : Fin 2)
  have htime : |p 0 - q 0| ≤ dist p q := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p q (0 : Fin 2)
  rw [Real.dist_eq, add_mul]
  exact (HopfLax1D.abs_sub_hopfLax_le_lipschitz_spacetime hFin hφ hp hq).trans (add_le_add
    (mul_le_mul_of_nonneg_left hspace K.2)
    (mul_le_mul_of_nonneg_left htime (HopfLax1D.timeLipschitzConstant_nonneg H K)))

/-- The Hopf–Lax formula is a continuous viscosity solution on `t > 0` under the
standard convex differentiable Hamiltonian and Lipschitz initial-data hypotheses. -/
theorem hopfLaxSpacetime_isContinuousDifferentiableTestSolution_of_lipschitz_convex {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsContinuousDifferentiableTestSolution H positiveTimeDomain (hopfLaxSpacetime H φ) :=
  ⟨hopfLaxSpacetime_continuousOn_of_lipschitz hFin hφ,
    hopfLaxSpacetime_isDifferentiableTestSolution_of_lipschitz_convex hFin hconv hH hφ⟩

/-- The initial trace of Evans, §3.3.2(b), Lemma 2, in spacetime notation: for every fixed
spatial point `x`, the Hopf–Lax profile tends to the initial datum as `t ↓ 0`. -/
theorem hopfLaxSpacetime_initial_trace_of_lipschitz {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hφ : LipschitzWith K φ) (x : ℝ) :
    Filter.Tendsto (fun t : ℝ ↦ hopfLaxSpacetime H φ !₂[t, x]) (𝓝[>] (0 : ℝ)) (𝓝 (φ x)) := by
  simpa [hopfLaxSpacetime] using HopfLax1D.tendsto_hopfLax_initial_right hFin hφ x

/-- The continuous Hopf–Lax viscosity solution on `t > 0`, together with its
one-sided initial trace. -/
theorem hopfLaxSpacetime_isContinuousDifferentiableTestSolution_with_initial_trace {H φ : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hφ : LipschitzWith K φ) :
    IsContinuousDifferentiableTestSolution H positiveTimeDomain (hopfLaxSpacetime H φ) ∧ ∀ x : ℝ,
      Filter.Tendsto (fun t : ℝ ↦ hopfLaxSpacetime H φ !₂[t, x]) (𝓝[>] (0 : ℝ)) (𝓝 (φ x)) :=
  ⟨hopfLaxSpacetime_isContinuousDifferentiableTestSolution_of_lipschitz_convex hFin hconv hH hφ,
    hopfLaxSpacetime_initial_trace_of_lipschitz hFin hφ⟩

end

end HamiltonJacobi1D
