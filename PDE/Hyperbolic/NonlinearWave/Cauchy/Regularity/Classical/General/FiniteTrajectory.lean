/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Pointwise
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointRegularity

import PDE.Analysis.Calculus.LocalExtension.SmoothCutoff

/-!
# Classical representatives of finite higher Sobolev trajectories

A continuous higher Sobolev trajectory has bounded amplitude on every compact
time interval. A smooth cutoff of the scalar reaction therefore preserves its
mild equation on that interval. The globally Lipschitz energy theory
then supplies the strong time derivatives and the pointwise equation for the
original reaction.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped NNReal Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- A finite higher Sobolev mild trajectory also solves an equation with a smooth,
globally Lipschitz reaction agreeing with the original reaction along the trajectory.
The amplitude bound and the cutoff are constructed from continuity in time. -/
theorem exists_lipschitz_truncation_higherSmooth_trajectory (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hq : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {τ : ℝ≥0} {x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)}
    (U : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)))
    (hU : (higherLinearSemigroup n k).IsMildSolutionOn (higherSmoothMap hk hs hf0) x τ U) :
    ∃ (F : ℝ → ℝ) (K : ℝ≥0) (hFs : ContDiff ℝ (⊤ : ℕ∞) F)
      (_ : LipschitzWith K F) (hF0 : F 0 = 0),
      (higherLinearSemigroup n k).IsMildSolutionOn
        (higherSmoothMap hk hFs hF0) x τ U ∧
      ∀ t : Icc (0 : ℝ) (τ : ℝ), ∀ y : ℝ^n,
        F (classicalRepresentativeCLM hq (U t).1 y) =
          f (classicalRepresentativeCLM hq (U t).1 y) := by
  let Q := fun t : Icc (0 : ℝ) (τ : ℝ) ↦ classicalRepresentativeCLM hq (U t).1
  have hQ : Continuous Q := (classicalRepresentativeCLM hq).continuous.comp U.continuous.fst
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hQ.continuousOn
  let R := max B 0 + 1
  have hR : 0 < R := add_pos_of_nonneg_of_pos (le_max_right B 0) zero_lt_one
  obtain ⟨F, K, hFs, _, hF, hFeq⟩ :=
    hs.exists_lipschitzWith_compactSupport_eqOn_closedBall (by simp) 0 hR
  have hF0 : F 0 = 0 := (hFeq (Metric.mem_closedBall_self hR.le)).trans hf0
  have heq (t : Icc (0 : ℝ) (τ : ℝ)) (y : ℝ^n) : F (classicalRepresentativeCLM hq (U t).1 y) =
        f (classicalRepresentativeCLM hq (U t).1 y) := by
    apply hFeq
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ((Q t).norm_coe_le_norm y).trans ((hB t (mem_univ t)).trans
      ((le_max_left B 0).trans (le_add_of_nonneg_right zero_le_one)))
  have hmap (t : Icc (0 : ℝ) (τ : ℝ)) :
      higherSmoothMap hk hFs hF0 (U t) = higherSmoothMap hk hs hf0 (U t) := by
    apply Prod.ext
    · rfl
    change _ - higherComposition hk hFs hF0 _ = _ - higherComposition hk hs hf0 _
    congr 1
    apply classicalRepresentativeCLM_injective hk
    apply BoundedContinuousFunction.ext
    intro y
    rw [classicalRepresentative_higherComposition, classicalRepresentative_higherComposition,
      classicalRepresentativeCLM_lowerOrderCLM hk hq]
    exact heq t y
  refine ⟨F, K, hFs, hF, hF0, ?_, heq⟩
  intro t
  rw [hU t]
  congr 1
  apply (higherLinearSemigroup n k).duhamel_congr t.property.1
  intro s hst
  change higherSmoothMap hk hs hf0 (IccExtend τ.property U s) =
    higherSmoothMap hk hFs hF0 (IccExtend τ.property U s)
  rw [IccExtend_of_mem τ.property U ⟨hst.1, hst.2.trans t.property.2⟩]
  exact (hmap ⟨s, ⟨hst.1, hst.2.trans t.property.2⟩⟩).symm

/-- The mild equation of a finite higher Sobolev trajectory gives its two strong
time derivatives, including one-sided derivatives at the initial and final times.
Only smoothness of the original reaction is required. -/
theorem hasDerivWithinAt_higherSmooth_trajectory (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0)
    {τ : ℝ≥0} {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hs hf0) x τ V)
    {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) :
    let U := IccExtend τ.property V
    HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ (k + 1)) (U s).1)
        (U t).2 (Icc 0 (τ : ℝ)) t ∧
      HasDerivWithinAt (fun s ↦ lowerOrderCLM (Nat.le_succ k) (U s).2)
        (higherSmoothAcceleration hk hs hf0 (U t).1) (Icc 0 (τ : ℝ)) t := by
  have hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1) := by
    push_cast at hv ⊢
    linarith
  obtain ⟨F, K, hFs, hF, hF0, hVF, hFeq⟩ :=
    exists_lipschitz_truncation_higherSmooth_trajectory hv hq hs hf0 V hV
  obtain ⟨e, he⟩ := exists_energySolution hF hF0
    (lowerOrderCLM (by omega : 1 ≤ k + 2) x.1, wkpBaseCoordinateCLM x.2)
  let U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  have hU₀ : U 0 = x := (IccExtend_of_mem τ.property V ⟨le_rfl, τ.property⟩).trans hV.initial_value
  have hproj := he.eq_higherSmooth_mild_projection hv hFs hF hF0 x V hVF
  have hd := he.hasDerivWithinAt_higherOrder_smoothReaction hk hFs hF hF0 x U hU₀ hproj ht
  refine ⟨hd.1, ?_⟩
  have hacc : higherSmoothAcceleration hk hFs hF0 (U t).1 =
      higherSmoothAcceleration hk hs hf0 (U t).1 := by
    apply classicalRepresentativeCLM_injective hk
    apply BoundedContinuousFunction.ext
    intro y
    rw [classicalRepresentative_higherSmoothAcceleration hk hFs hF0 hq,
      classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq]
    congr 1
    change F (classicalRepresentativeCLM hq (IccExtend τ.property V t).1 y) =
      f (classicalRepresentativeCLM hq (IccExtend τ.property V t).1 y)
    rw [IccExtend_of_mem τ.property V ht]
    exact hFeq ⟨t, ht⟩ y
  rw [hacc] at hd
  exact hd.2

/-- Every finite mild trajectory for a smooth scalar reaction has a jointly C²
canonical representative in the interior of its time interval. -/
theorem contDiffOn_two_higherSmooth_trajectory (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {τ : ℝ≥0} {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hs hf0) x τ V) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ^n ↦ classicalRepresentativeCLM hq (IccExtend τ.property V p.1).1
      p.2) (Ioo 0 (τ : ℝ) ×ˢ univ) := by
  let U : C(ℝ, W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)) :=
    ⟨IccExtend τ.property V, V.continuous.Icc_extend'⟩
  apply contDiffOn_two_higherWave hk hv hq U
    ⟨_, (continuous_higherSmoothAcceleration hk hs hf0).comp U.continuous.fst⟩ isOpen_Ioo
  · intro t ht
    exact (hasDerivWithinAt_higherSmooth_trajectory hk hv hs hf0 V hV
      ⟨ht.1.le, ht.2.le⟩).1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  · intro t ht
    exact (hasDerivWithinAt_higherSmooth_trajectory hk hv hs hf0 V hV
      ⟨ht.1.le, ht.2.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- Evaluation of a finite higher Sobolev mild trajectory gives the classical
velocity and acceleration, with one-sided time derivatives at both endpoints. -/
theorem hasDerivWithinAt_classical_higherSmooth_trajectory (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {τ : ℝ≥0} {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hs hf0) x τ V)
    {t : ℝ} (ht : t ∈ Icc 0 (τ : ℝ)) (y : ℝ^n) :
    let U := IccExtend τ.property V
    let q := fun s z ↦ classicalRepresentativeCLM hq (U s).1 z
    let v := fun s z ↦ classicalRepresentativeCLM hv (U s).2 z
    HasDerivWithinAt (fun s ↦ q s y) (v t y) (Icc 0 (τ : ℝ)) t ∧
      HasDerivWithinAt (fun s ↦ v s y) (Δ (q t) y - f (q t y)) (Icc 0 (τ : ℝ)) t := by
  have hd := hasDerivWithinAt_higherSmooth_trajectory hk hv hs hf0 V hV ht
  refine ⟨hasDerivWithinAt_classicalRepresentative_lowerOrder hv hq
    (Nat.le_succ (k + 1)) hd.1 y, ?_⟩
  have hv' := hasDerivWithinAt_classicalRepresentative_lowerOrder hk hv (Nat.le_succ k) hd.2 y
  rwa [classicalRepresentative_higherSmoothAcceleration hk hs hf0 hq] at hv'

/-- The canonical representative of a finite higher Sobolev mild trajectory
satisfies the original nonlinear wave equation pointwise in the interior. -/
theorem higherSmooth_trajectory_wave_equation (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {τ : ℝ≥0} {x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)}
    (V : C(Icc (0 : ℝ) (τ : ℝ), W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n)))
    (hV : (higherLinearSemigroup n (k + 1)).IsMildSolutionOn (higherSmoothMap hv hs hf0) x τ V)
    {t : ℝ} (ht : t ∈ Ioo 0 (τ : ℝ)) (y : ℝ^n) :
    let q := fun s z ↦ classicalRepresentativeCLM hq (IccExtend τ.property V s).1 z; deriv
      (fun s ↦ deriv (fun r ↦ q r y) s) t - Δ (q t) y + f (q t y) = 0 := by
  let q := fun s z ↦ classicalRepresentativeCLM hq (IccExtend τ.property V s).1 z
  let v := fun s z ↦ classicalRepresentativeCLM hv (IccExtend τ.property V s).2 z
  have hd (s : ℝ) (hs' : s ∈ Icc 0 (τ : ℝ)) :=
    hasDerivWithinAt_classical_higherSmooth_trajectory hk hv hq hs hf0 V hV hs' y
  have hv' : HasDerivAt (fun s ↦ v s y) (Δ (q t) y - f (q t y)) t :=
    (hd t ⟨ht.1.le, ht.2.le⟩).2.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hdd : deriv (fun s ↦ deriv (fun r ↦ q r y) s) t = Δ (q t) y - f (q t y) := by
    apply HasDerivAt.deriv
    apply hv'.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs'
    exact ((hd s ⟨hs'.1.le, hs'.2.le⟩).1.hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)).deriv
  change deriv (fun s ↦ deriv (fun r ↦ q r y) s) t - Δ (q t) y + f (q t y) = 0
  rw [hdd]
  abel

end PDE.Hyperbolic.NonlinearWave.Cauchy
