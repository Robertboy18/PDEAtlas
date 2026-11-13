/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.Riemann.Trace
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Oleinik.Uniqueness
import Mathlib.Analysis.Convex.Deriv
import PDE.Analysis.MeasureTheory.Lp.Continuous
import PDE.Analysis.MeasureTheory.SpaceTime
import PDE.Hyperbolic.ConservationLaw.InitialBoundary.SmoothTesting
import PDE.Hyperbolic.ConservationLaw.Scalar.InitialBoundaryCutoff
import PDE.Hyperbolic.ConservationLaw.Scalar.Riemann.Profile
import CAS.ExactTactic

/-!
# Oleinik uniqueness for scalar conservation laws

For a `C²` convex flux, two essentially bounded weak solutions of the initial-value problem with the
same datum that satisfy one-sided Oleinik bounds agree almost everywhere
(`IsWeakInitialValueSolution.ae_eq_of_oleinik`, the uniqueness theorem of Evans, §3.4.3, Theorem 3,
for a `C²` rather than smooth flux). `raw_smooth_testing_oleinik_unique` states it with the weak
formulation tested only against smooth compactly supported functions. For the affine flux `3r + 5`,
which is convex but not uniformly convex, the downward step from `1` to `-2` along `x = 3t` is the
unique such solution (`affine_downward_step_unique`), also after it is changed on countably many
time slices (`affine_countable_time_modification`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.3(b), definition of an entropy solution and
  Theorem 3 (Uniqueness of entropy solutions), p. 149.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal
open PDE.Hyperbolic.ConservationLaw
open PDE.Hyperbolic.ConservationLaw.Scalar

namespace PDE.Examples.ConservationLaw

/-- Uniqueness under Oleinik bounds, with the weak formulation tested against smooth
compactly supported functions. -/
theorem raw_smooth_testing_oleinik_unique
    {F g : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hconv : ConvexOn ℝ univ F)
    (hg : LocallyIntegrable g volume) {u v : ℝ^2 → ℝ}
    (hu : MemLp u ∞ (volume.restrict forwardHalfSpace))
    (hv : MemLp v ∞ (volume.restrict forwardHalfSpace))
    (huTest : ∀ φ : 𝓓((⊤ : Opens ℝ^2), ℝ),
      (∫ p in forwardHalfSpace,
        (∂[0] (φ : ℝ^2 → ℝ)) p * u p + (∂[1] (φ : ℝ^2 → ℝ)) p * F (u p)) +
        ∫ x : ℝ, φ !₂[0, x] * g x = 0)
    (hvTest : ∀ φ : 𝓓((⊤ : Opens ℝ^2), ℝ),
      (∫ p in forwardHalfSpace,
        (∂[0] (φ : ℝ^2 → ℝ)) p * v p + (∂[1] (φ : ℝ^2 → ℝ)) p * F (v p)) +
        ∫ x : ℝ, φ !₂[0, x] * g x = 0)
    (huSlope : ∃ C, HasOleinikBound u C) (hvSlope : ∃ C, HasOleinikBound v C) :
    u =ᵐ[volume.restrict forwardHalfSpace] v := by
  have native (w : ℝ^2 → ℝ) (hw : MemLp w ∞ (volume.restrict forwardHalfSpace))
      (hTest : ∀ φ : 𝓓((⊤ : Opens ℝ^2), ℝ),
        (∫ p in forwardHalfSpace,
          (∂[0] (φ : ℝ^2 → ℝ)) p * w p + (∂[1] (φ : ℝ^2 → ℝ)) p * F (w p)) +
          ∫ x : ℝ, φ !₂[0, x] * g x = 0) :
      IsWeakInitialValueSolution F g w := by
    have hwLoc := hw.locallyIntegrable le_top
    have hFLoc := (hF.continuous.comp_memLp_top hw).locallyIntegrable le_top
    refine
      { u_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hwLoc
        flux_locallyIntegrable := locallyIntegrableOn_of_locallyIntegrable_restrict hFLoc
        initial_locallyIntegrable := hg
        spacetime_integrable := ?_
        weak_initial_eq := ?_ }
    · intro φ
      exact (hwLoc.integrable_smul_left_of_hasCompactSupport
        (φ.continuous_partialDeriv 0) (φ.hasCompactSupport_partialDeriv 0)).add
          (hFLoc.integrable_smul_left_of_hasCompactSupport
            (φ.continuous_partialDeriv 1) (φ.hasCompactSupport_partialDeriv 1))
    · exact initialWeak_eq_zero_of_smooth hwLoc hFLoc hg hTest
  exact (native u hu huTest).ae_eq_of_oleinik hF hconv (native v hv hvTest)
    hu hv huSlope hvSlope

/-- The affine flux `3r + 5`. Its second derivative vanishes, so it is convex but not
uniformly convex. -/
def affineFlux (r : ℝ) : ℝ := 3 * r + 5

private theorem norm_affine_step_le (p : ℝ^2) :
    ‖planarShock (1 : ℝ) (-2) 3 p‖ ≤ 2 := by
  by_cases hp : p ∈ AffineInterface.leftHalfSpace 3
  · rw [planarShock_apply_of_mem hp]
    norm_num
  · rw [planarShock_apply_of_not_mem hp]
    norm_num

/-- The step from `1` to `-2` along `x = 3t` is a weak solution of the initial-value
problem with strong initial trace. -/
theorem affine_downward_step_initial_value :
    IsWeakInitialValueSolution affineFlux (riemannData 1 (-2)) (planarShock (1 : ℝ) (-2) 3) ∧
      HasInitialTraceLocallyL1 (planarShock (1 : ℝ) (-2) 3) (riemannData 1 (-2)) := by
  have hRH : RankineHugoniot affineFlux 1 (-2) 3 := by
    unfold RankineHugoniot affineFlux
    cas
  have htrace : HasInitialTraceLocallyL1
      (planarShock (1 : ℝ) (-2) 3) (riemannData 1 (-2)) := by
    apply hasInitialTraceLocallyL1_riemannData_of_finitePropagation
      (M := 3) (measurable_planarShock (1 : ℝ) (-2) 3)
      (fun p _ ↦ norm_affine_step_le p)
    · intro p ht hx
      apply planarShock_apply_of_mem
      change p 1 < 3 * p 0
      linarith
    · intro p _ hx
      exact planarShock_apply_of_not_mem (not_lt_of_ge hx)
  have hi : IsWeakSolutionWithInitialTrace affineFlux (riemannData 1 (-2))
      (planarShock (1 : ℝ) (-2) 3) :=
    ⟨hRH.isWeakSolution_planarShock.mono_domain le_top, htrace⟩
  exact ⟨hi.isWeakInitialValueSolution_of_locallyBounded
    (by unfold affineFlux; fun_prop)
    (fun _ _ ↦ ⟨2, fun p _ _ ↦ norm_affine_step_le p⟩), htrace⟩

/-- The downward step satisfies the Oleinik bound with constant `0`. -/
theorem affine_downward_step_oleinik :
    HasOleinikBound (planarShock (1 : ℝ) (-2) 3) 0 := by
  refine ⟨le_rfl, Filter.Eventually.of_forall ?_⟩
  intro p _ hz
  simp only [zero_mul]
  exact sub_nonpos.mpr
    (Riemann.antitone_planarShock_slice (by norm_num : (-2 : ℝ) ≤ 1) 3 p.1
      (le_add_of_nonneg_right hz.le))

/-- Every essentially bounded weak solution with the same datum and some Oleinik bound
equals the downward step almost everywhere. -/
theorem affine_downward_step_unique
    {v : ℝ^2 → ℝ}
    (hv : IsWeakInitialValueSolution affineFlux (riemannData 1 (-2)) v)
    (hvBdd : MemLp v ∞ (volume.restrict forwardHalfSpace))
    (hvSlope : ∃ C, HasOleinikBound v C) :
    v =ᵐ[volume.restrict forwardHalfSpace] planarShock (1 : ℝ) (-2) 3 := by
  have hF : ContDiff ℝ 2 affineFlux := by unfold affineFlux; fun_prop
  have hderiv : deriv affineFlux = fun _ ↦ (3 : ℝ) := by
    funext r
    cas
  have hconv : ConvexOn ℝ univ affineFlux :=
    Monotone.convexOn_univ_of_deriv (hF.differentiable (by norm_num))
      (by rw [hderiv]; exact monotone_const)
  have hb : MemLp (planarShock (1 : ℝ) (-2) 3) ∞ (volume.restrict forwardHalfSpace) :=
    memLp_top_of_bound (measurable_planarShock (1 : ℝ) (-2) 3).aestronglyMeasurable 2
      (Filter.Eventually.of_forall norm_affine_step_le)
  exact hv.ae_eq_of_oleinik hF hconv affine_downward_step_initial_value.1
    hvBdd hb hvSlope ⟨0, affine_downward_step_oleinik⟩

/-- Setting the step to zero on countably many time slices, which may accumulate at
`t = 0`, gives an essentially bounded weak solution with Oleinik bound `0` that equals
the step almost everywhere. -/
theorem affine_countable_time_modification (S : Set ℝ) (hS : S.Countable) :
    let u := {p : ℝ^2 | p 0 ∉ S}.indicator (planarShock (1 : ℝ) (-2) 3)
    IsWeakInitialValueSolution affineFlux (riemannData 1 (-2)) u ∧
      MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      HasOleinikBound u 0 ∧
      u =ᵐ[volume.restrict forwardHalfSpace] planarShock (1 : ℝ) (-2) 3 ∧
      (∀ t ∈ S, ∀ x : ℝ, u !₂[t, x] = 0) := by
  classical
  let u := {p : ℝ^2 | p 0 ∉ S}.indicator (planarShock (1 : ℝ) (-2) 3)
  have hprod : ∀ᵐ p : ℝ × ℝ^1 ∂volume, p.1 ∉ S := by
    rw [Measure.volume_eq_prod ℝ (ℝ^1)]
    exact Measure.quasiMeasurePreserving_fst.ae (hS.ae_notMem volume)
  have htime : ∀ᵐ p : ℝ^2 ∂volume, p 0 ∉ S :=
    (PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv
      (n := 1)).quasiMeasurePreserving.ae hprod
  have hEqGlobal : u =ᵐ[volume] planarShock (1 : ℝ) (-2) 3 := by
    filter_upwards [htime] with p hp
    exact indicator_of_mem hp _
  have hEq : u =ᵐ[volume.restrict forwardHalfSpace] planarShock (1 : ℝ) (-2) 3 :=
    ae_restrict_of_ae hEqGlobal
  have hi := affine_downward_step_initial_value.1
  have hflux := hEq.fun_comp affineFlux
  have htested (φ : InitialValueTestFunction) :
      InteriorWeakForm.integrand u (fun p ↦ affineFlux (u p)) φ
        =ᵐ[volume.restrict forwardHalfSpace]
      InteriorWeakForm.integrand (planarShock (1 : ℝ) (-2) 3)
        (fun p ↦ affineFlux (planarShock (1 : ℝ) (-2) 3 p)) φ := by
    filter_upwards [hEq] with p hp
    simp only [InteriorWeakForm.integrand, hp]
  have hw : IsWeakInitialValueSolution affineFlux (riemannData 1 (-2)) u :=
    { u_locallyIntegrable := hi.u_locallyIntegrable.congr hEq.symm
      flux_locallyIntegrable := hi.flux_locallyIntegrable.congr hflux.symm
      initial_locallyIntegrable := hi.initial_locallyIntegrable
      spacetime_integrable := fun φ ↦ (hi.spacetime_integrable φ).congr (htested φ).symm
      weak_initial_eq := fun φ ↦ by
        rw [integral_congr_ae (htested φ)]
        exact hi.weak_initial_eq φ }
  have hbase : MemLp (planarShock (1 : ℝ) (-2) 3) ∞
      (volume.restrict forwardHalfSpace) :=
    memLp_top_of_bound (measurable_planarShock (1 : ℝ) (-2) 3).aestronglyMeasurable 2
      (Filter.Eventually.of_forall norm_affine_step_le)
  have hb : MemLp u ∞ (volume.restrict forwardHalfSpace) :=
    (memLp_congr_ae hEq).mpr hbase
  have hs : HasOleinikBound u 0 := by
    refine ⟨le_rfl, Filter.Eventually.of_forall ?_⟩
    intro p _ hz
    simp only [zero_mul]
    by_cases hp : p.1 ∈ S
    · simp [u, hp]
    · simpa [u, hp] using sub_nonpos.mpr
        (Riemann.antitone_planarShock_slice (by norm_num : (-2 : ℝ) ≤ 1) 3 p.1
          (le_add_of_nonneg_right hz.le))
  refine ⟨hw, hb, hs, affine_downward_step_unique hw hb ⟨0, hs⟩, ?_⟩
  intro t ht x
  simp [ht]

end PDE.Examples.ConservationLaw
