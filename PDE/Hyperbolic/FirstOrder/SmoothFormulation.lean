/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.SmoothTimeTests
public import PDE.Hyperbolic.FirstOrder.TransportTestContinuity

/-!
# Density extension of the smooth transport identity

The scalar initial-value identity first extends the smooth time tests. The canonical
whole-space H¹ approximation then extends the spatial tests. Every spatial pairing is
measurable by `memLp_transportTestFunctional`; its uniform norm bound supplies the
dominator for the passage to the limit.

The hypothesis is the identity for smooth separated tests, which the spacetime
distribution formulation implies by testing with external tensor products.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal InnerProductSpace Topology Distributions ContDiff

namespace PDE.Hyperbolic.FirstOrder

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation

/-- Integrating linear observations against an L² weight gives a continuous functional
when their operator norms have an almost-everywhere L² majorant. -/
private theorem continuous_integral_linear_test_mul
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {a b : ℝ} (B : ℝ → W →L[ℝ] ℝ) {k θ : ℝ → ℝ}
    (hB : ∀ v, MemLp (fun t ↦ B t v) 2 (volume.restrict (Ioc a b)))
    (hk : MemLp k 2 (volume.restrict (Ioc a b)))
    (hθ : MemLp θ 2 (volume.restrict (Ioc a b)))
    (hk0 : ∀ᵐ t ∂volume.restrict (Ioc a b), 0 ≤ k t)
    (hbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ∀ v, ‖B t v‖ ≤ k t * ‖v‖) :
    Continuous (fun v ↦ ∫ t, B t v * θ t ∂volume.restrict (Ioc a b)) := by
  refine continuous_iff_continuousAt.2 fun v₀ ↦ continuousAt_of_dominated
    (bound := fun t ↦ (‖k t‖ * ‖θ t‖) * (‖v₀‖ + 1))
    (Eventually.of_forall fun v ↦ (hB v).aestronglyMeasurable.mul hθ.aestronglyMeasurable) ?_
    ((hk.norm.integrable_mul hθ.norm).mul_const _)
    (Eventually.of_forall fun t ↦ (B t).continuous.continuousAt.mul_const (θ t))
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds (lt_add_one ‖v₀‖))]
    with v hv
  filter_upwards [hk0, hbound] with t hkt ht
  rw [norm_mul, Real.norm_of_nonneg hkt, mul_right_comm]
  gcongr
  exact (ht v).trans (mul_le_mul_of_nonneg_left hv.le hkt)

open scoped SobolevSpace.WholeSpaceHilbert

variable {n m : ℕ} {a b : ℝ}

local notation "D" => DerivLp n 2 univ
local notation "H" => PiLp 2 (fun _ : Fin m ↦ D)
local notation "V" => PiLp 2 (fun _ : Fin m ↦ H¹(ℝ^n))
local notation "ν" => volume.restrict (Ioc a b)

/-- An L² state paired with an H¹ test and an L² time weight depends continuously
on the spatial test in its graph norm. -/
private theorem continuous_integral_inner_test_mul
    {v : ℝ → H} (hv : MemLp v 2 ν) {θ : ℝ → ℝ} (hθ : MemLp θ 2 ν) :
    Continuous (fun φ : V ↦
      ∫ t, inner ℝ (v t) (transportBaseCLM φ) * θ t ∂ν) := by
  let J : V →L[ℝ] H := transportBaseCLM
  exact continuous_integral_linear_test_mul (fun t ↦ (innerSL ℝ (v t)).comp J)
    (k := fun t ↦ ‖v t‖ * ‖J‖) (fun φ ↦ hv.inner_const (J φ)) (hv.norm.mul_const ‖J‖) hθ
    (ae_of_all _ fun _ ↦ by positivity) (ae_of_all _ fun t φ ↦
      (norm_inner_le_norm (v t) (J φ)).trans ((mul_le_mul_of_nonneg_left (J.le_opNorm φ)
        (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm))

/-- The smooth separated distribution identity extends to every H¹ spatial test and
every endpoint time test. The state and forcing are only Bochner L². The coefficient
base rows are continuous on Icc and the displayed spatial derivative rows are uniformly
bounded. Symmetry is not needed here. -/
theorem transport_timeTest_identity_of_smooth_tests
    (hab : a < b)
    (A : ℝ → Fin n → Fin m → Fin m → W^{1,∞}((univ : Set (ℝ^n))))
    (hA : ∀ j p q, ContinuousOn (fun t ↦
      (A t j p q : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (Icc a b))
    (L : ℝ≥0)
    (hL : ∀ t ∈ Icc a b, ∀ j p q,
      ‖(A t j p q : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L)
    {u f : ℝ → H} (hu : MemLp u 2 ν) (hf : MemLp f 2 ν) (x : H)
    (hweak : ∀ ψ : Fin m → 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      let φ : V := WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p))
      ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ Iio b →
      -(∫ t, inner ℝ (u t) (transportBaseCLM φ) * deriv ζ t ∂ν) =
        (∫ t, transportTestFunctional (A t) φ (u t) * ζ t ∂ν) +
        (∫ t, inner ℝ (f t) (transportBaseCLM φ) * ζ t ∂ν) +
        inner ℝ x (transportBaseCLM φ) * ζ a)
    (φ : V) (τ : TimeTest a b) :
    -(∫ t, inner ℝ (u t) (transportBaseCLM φ) * τ.derivFun t ∂ν) =
      (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
      (∫ t, inner ℝ (f t) (transportBaseCLM φ) * τ.toFun t ∂ν) +
      inner ℝ x (transportBaseCLM φ) * τ.toFun a := by
  have htime (ψ : Fin m → 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      let φ : V := WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (ψ p));
      -(∫ t, inner ℝ (u t) (transportBaseCLM φ) * τ.derivFun t ∂ν) =
        (∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) +
        (∫ t, inner ℝ (f t) (transportBaseCLM φ) * τ.toFun t ∂ν) +
        inner ℝ x (transportBaseCLM φ) * τ.toFun a := by
    intro φ
    have hB := memLp_transportTestFunctional hab.le A hA L hL hu φ
    have hfφ : MemLp (fun t ↦ inner ℝ (f t) (transportBaseCLM φ)) 2 ν :=
      hf.inner_const (transportBaseCLM φ)
    have hweak' : ∀ ζ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ Iio b →
        -(∫ t, inner ℝ (u t) (transportBaseCLM φ) * deriv ζ t ∂ν) =
          (∫ t, (transportTestFunctional (A t) φ (u t) +
            inner ℝ (f t) (transportBaseCLM φ)) * ζ t ∂ν) +
          inner ℝ x (transportBaseCLM φ) * ζ a := fun ζ hζ hζcs hζsupp ↦ by
      have hζLp : MemLp ζ 2 ν := memLp_restrict_Ioc_of_continuousOn hζ.continuous.continuousOn
      have hadd := integral_add (hB.integrable_mul hζLp) (hfφ.integrable_mul hζLp)
      simp only [Pi.mul_apply, ← add_mul] at hadd
      rw [hadd]
      exact hweak ψ ζ hζ hζcs hζsupp
    have h := timeTest_identity_of_smooth_initial_tests hab
      (hu.inner_const (transportBaseCLM φ)) (hB.add hfφ)
      (inner ℝ x (transportBaseCLM φ)) hweak' τ
    have hadd := integral_add (hB.integrable_mul τ.memLp) (hfφ.integrable_mul τ.memLp)
    simp only [Pi.add_apply, Pi.mul_apply, add_mul] at h hadd
    rwa [hadd] at h
  obtain ⟨ψ, hψ⟩ := exists_testFunctionProduct_tendsto_H1 φ
  have hleft := (continuous_integral_inner_test_mul hu τ.derivMemLp).neg
  have hload := continuous_integral_inner_test_mul hf τ.memLp
  have htrace : Continuous (fun φ : V ↦
      inner ℝ x (transportBaseCLM φ) * τ.toFun a) :=
    (continuous_const.inner transportBaseCLM.continuous).mul_const _
  obtain ⟨K, hK, hbound⟩ := exists_uniform_bound_transportTestFunctional A hA L hL
  have htransport : Continuous (fun φ : V ↦
      ∫ t, transportTestFunctional (A t) φ (u t) * τ.toFun t ∂ν) := by
    simp_rw [← transportTestInTestCLM_apply]
    apply continuous_integral_linear_test_mul
      (fun t ↦ transportTestInTestCLM (A t) (u t)) (k := fun t ↦ K * ‖u t‖)
    · intro φ
      simpa only [transportTestInTestCLM_apply] using
        memLp_transportTestFunctional hab.le A hA L hL hu φ
    · exact hu.norm.const_mul K
    · exact τ.memLp
    · exact Eventually.of_forall fun _ ↦ mul_nonneg hK (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht φ
      rw [transportTestInTestCLM_apply]
      exact ((transportTestFunctional (A t) φ).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (hbound t (Ioc_subset_Icc_self ht) φ)
          (norm_nonneg _)).trans_eq (mul_right_comm _ _ _))
  exact (isClosed_eq hleft ((htransport.add hload).add htrace)).mem_of_tendsto hψ
    (Eventually.of_forall fun k ↦ htime (ψ k))

end PDE.Hyperbolic.FirstOrder
