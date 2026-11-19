/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.NormBlowup.Jet
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.TraceCalculus
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Solution

/-!
# Classical observation of a higher mild prefix

Both Sobolev components are identified with the classical displacement
and its ordinary time derivative. The smooth scalar reaction need not be
globally Lipschitz. Zero initial displacement permits a regular backward jet
without imposing a backward PDE.
-/

@[expose] public noncomputable section

open PDE PDE.Common Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped NNReal Sobolev Laplacian

namespace WaveEquation.SmallData.Classical.NormBlowup

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- A higher mild prefix gives a jointly C² classical solution with exactly
the same displacement and velocity representatives throughout its forward strip. -/
theorem exists_classical_of_higher_mild (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (H : W^{k + 2,2}(ℝ^n)) {τ : ℝ≥0} (hτ : 0 < τ)
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hf hf0)
      (0, lowerOrderCLM (Nat.le_succ (k + 1)) H) τ V) :
    ∃ u : ℝ^(n + 1) → ℝ,
      IsSolutionBefore f (fun _ ↦ 0) (classicalRepresentativeCLM hq H) (τ : ℝ) u ∧
        ∀ t ∈ Ico 0 (τ : ℝ), ∀ x,
          u (timeSpaceCons t x) =
            classicalRepresentativeCLM hq (IccExtend τ.property V t).1 x ∧
          (∂[0] u) (timeSpaceCons t x) =
            classicalRepresentativeCLM hv (IccExtend τ.property V t).2 x := by
  obtain ⟨U, A, hU0, he, hQ, hV', hA⟩ := exists_jet_of_higher_mild hk hv hq hf hf0 H hτ V hV
  let Q : C(ℝ, BoundedContinuousFunction (ℝ^n) ℝ) := ⟨fun t ↦ classicalRepresentativeCLM hq (U t).1,
      (classicalRepresentativeCLM hq).continuous.comp U.continuous.fst⟩
  let u : ℝ^(n + 1) → ℝ := fun p ↦ Q (p 0) (spatialPart p)
  have hut (t : ℝ) (x : ℝ^n) : u (timeSpaceCons t x) = Q t x := by
    simp only [u, timeSpaceCons_zero, spatialPart_timeSpaceCons]
  have hreg : ContDiffOn ℝ 2 u {p | p 0 < (τ : ℝ)} := by
    apply (contDiffOn_two_higherWave hk hv hq U A isOpen_Iio hQ hV').comp
      (((EuclideanSpace.proj 0).contDiff.prodMk (spatialPartCLM n).contDiff).contDiffOn)
    exact fun p hp ↦ ⟨hp, mem_univ _⟩
  have hfirst (t : ℝ) (ht : t < (τ : ℝ)) (x : ℝ^n) : HasDerivAt (fun s ↦ u (timeSpaceCons s x))
        (classicalRepresentativeCLM hv (U t).2 x) t := by
    simp only [hut]
    exact hasDerivAt_classicalRepresentative_lowerOrder hv hq (Nat.le_succ (k + 1)) (hQ t ht) x
  have hsecond (t : ℝ) (ht : t < (τ : ℝ)) (x : ℝ^n) :=
    hasDerivAt_classicalRepresentative_lowerOrder hk hv (Nat.le_succ k) (hV' t ht) x
  refine ⟨u, ⟨show (0 : ℝ) < τ from hτ, hreg, ?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    have hw := waveOperator_eq_of_trace_derivatives hreg
      (fun t x ↦ classicalRepresentativeCLM hv (U t).2 x)
      (fun t x ↦ classicalRepresentativeCLM hk (A t) x) hfirst hsecond hp.2 (spatialPart p)
    rw [timeSpaceCons_spatialPart] at hw
    rw [hw, hA (p 0) hp, classicalRepresentative_higherSmoothAcceleration hk hf hf0 hq]
    simp only [hut]
    have hslice : ContDiffAt ℝ 2 (Q (p 0) : ℝ^n → ℝ) (spatialPart p) := by
      have hr := (contDiffAt_of_before hreg hp.2 (spatialPart p)).comp (spatialPart p)
        (contDiff_timeSpaceCons_spatial n (p 0) (m := 2)).contDiffAt
      simpa only [Function.comp_def, hut] using hr
    change Δ (Q (p 0) : ℝ^n → ℝ) (spatialPart p) - f (u p) -
      PDE.laplacian (Q (p 0)) (spatialPart p) = -f (u p)
    rw [← hslice.coordinate_laplacian_eq_laplacian]
    abel
  · intro x
    simp [hut, Q, hU0]
  · intro x
    rw [partialDeriv_eq_of_trace_derivative hreg (show (0 : ℝ) < τ from hτ) x (hfirst 0 hτ x), hU0]
    exact congrArg (fun v : BoundedContinuousFunction (ℝ^n) ℝ ↦ v x)
      (classicalRepresentativeCLM_lowerOrderCLM hv hq (Nat.le_succ (k + 1)) H)
  · intro t ht x
    constructor
    · change classicalRepresentativeCLM hq (U t).1 x = _
      rw [he t ht.1]
    · rw [partialDeriv_eq_of_trace_derivative hreg ht.2 x (hfirst t ht.2 x), he t ht.1]

end WaveEquation.SmallData.Classical.NormBlowup
