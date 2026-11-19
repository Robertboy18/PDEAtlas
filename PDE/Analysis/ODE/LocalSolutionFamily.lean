/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Local solution families for autonomous ODEs

A time-independent `C¹` vector field `f : E → E` has a local family `α : E × ℝ → E` of
integral curves anchored at a common time `t₀`, with the expected joint space-time Fréchet
derivative at the basepoint `(x₀, t₀)`:

`Dα(x₀, t₀) (v, τ) = v + τ • f x₀`.

No two-time cocycle law is proved, which is why `α` is called a local solution family
rather than a local flow.

Existence and continuity of the family come from Mathlib's Picard–Lindelöf
(Cauchy–Lipschitz) theorem,
`IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn`, whose
hypotheses follow from `C¹` regularity of `f` at `x₀` by `IsPicardLindelof.of_contDiffAt_one`.
For the
derivative formula, the mean value inequality applied to `s ↦ α (x, s) - s • f x₀`, whose
derivative `f (α (x, s)) - f x₀` is small near the basepoint by continuity of the velocity
`f ∘ α` at `(x₀, t₀)`, shows that the remainder is `o(‖(x, t) - (x₀, t₀)‖)`.

## Main results

* `exists_local_solution_family_hasFDerivAt_of_contDiffAt`: for `f` of class `C¹` at `x₀`, there
  are `ε, r > 0` and `α : E × ℝ → E` with `α (x, t₀) = x`, continuous on
  `closedBall x₀ r × [t₀ - ε, t₀ + ε]`, solving `∂ₜ α (x, t) = f (α (x, t))` there, and
  Fréchet differentiable at `(x₀, t₀)` with derivative `(v, τ) ↦ v + τ • f x₀`.
-/

@[expose] public section

namespace PDE.Analysis.ODE

open scoped Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Construct a local family of integral curves based at the common time
`t₀`, and compute its joint space-time Fréchet derivative at `(x₀, t₀)`.

Neither a two-time cocycle law nor differentiability away from the basepoint
is proved here. -/
theorem exists_local_solution_family_hasFDerivAt_of_contDiffAt
    {f : E → E} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) (t₀ : ℝ) :
    ∃ (ε : ℝ) (_hε : 0 < ε) (r : ℝ) (_hr : 0 < r) (α : E × ℝ → E),
      (∀ x ∈ Metric.closedBall x₀ r, α (x, t₀) = x) ∧
      ContinuousOn α (Metric.closedBall x₀ r ×ˢ Set.Icc (t₀ - ε) (t₀ + ε)) ∧
      (∀ x ∈ Metric.closedBall x₀ r,
        ∀ t ∈ Set.Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt (fun s : ℝ ↦ α (x, s)) (f (α (x, t)))
            (Set.Icc (t₀ - ε) (t₀ + ε)) t) ∧
      HasFDerivAt α
        ((ContinuousLinearMap.fst ℝ E ℝ) +
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight (f x₀))
        (x₀, t₀) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ := IsPicardLindelof.of_contDiffAt_one (f := f) hf
  obtain ⟨α, hα, hαc⟩ :=
    IsPicardLindelof.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn (f := fun _ ↦ f)
      (tmin := t₀ - ε) (tmax := t₀ + ε) (t₀ := ⟨t₀, by simp [le_of_lt hε]⟩) (hPL t₀)
  have hr' : (0 : ℝ) < r := hr
  have hinit (x : E) (hx : x ∈ Metric.closedBall x₀ r) : α (x, t₀) = x := (hα x hx).1
  have hderiv (x : E) (hx : x ∈ Metric.closedBall x₀ r) (t : ℝ)
      (ht : t ∈ Set.Icc (t₀ - ε) (t₀ + ε)) :
      HasDerivWithinAt (fun s : ℝ ↦ α (x, s)) (f (α (x, t))) (Set.Icc (t₀ - ε) (t₀ + ε)) t :=
    (hα x hx).2 t ht
  have hx₀ : α (x₀, t₀) = x₀ := hinit x₀ (Metric.mem_closedBall_self hr'.le)
  refine ⟨ε, hε, r, hr', α, hinit, hαc, hderiv, ?_⟩
  -- the velocity `f ∘ α` is continuous at the basepoint
  have hbox : Metric.closedBall x₀ r ×ˢ Set.Icc (t₀ - ε) (t₀ + ε) ∈ 𝓝 (x₀, t₀) :=
    prod_mem_nhds (Metric.closedBall_mem_nhds x₀ hr') (Icc_mem_nhds (by linarith) (by linarith))
  have hvel : ContinuousAt (fun p ↦ f (α p)) (x₀, t₀) :=
    hf.continuousAt.comp_of_eq (hαc.continuousAt hbox) hx₀
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro δ hδ
  obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem hbox (hvel (Metric.ball_mem_nhds _ hδ)))
  filter_upwards [Metric.ball_mem_nhds (x₀, t₀) hη] with ⟨x, t⟩ hxt
  -- the segment from `(x, t₀)` to `(x, t)` stays in the ball of radius `η`
  have hseg (s : ℝ) (hs : s ∈ Set.uIcc t₀ t) :
      (x, s) ∈ Metric.closedBall x₀ r ×ˢ Set.Icc (t₀ - ε) (t₀ + ε) ∧
        dist (f (α (x, s))) (f (α (x₀, t₀))) < δ := by
    refine hηsub (Metric.mem_ball.2 (lt_of_le_of_lt ?_ (Metric.mem_ball.1 hxt)))
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_le_max le_rfl
      ((Real.dist_le_of_mem_uIcc hs Set.left_mem_uIcc).trans_eq (dist_comm _ _))
  have hx := (hseg t₀ Set.left_mem_uIcc).1.1
  -- the mean value inequality for `s ↦ α (x, s) - s • f x₀`
  have hmv := (convex_uIcc t₀ t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s ↦ α (x, s) - s • f x₀) (f' := fun s ↦ f (α (x, s)) - f x₀) (C := δ)
    (fun s hs ↦ ((hderiv x hx s (hseg s hs).1.2).mono fun u hu ↦ (hseg u hu).1.2).sub
      (by simpa using (hasDerivWithinAt_id s _).smul_const (f x₀)))
    (fun s hs ↦ by simpa [hx₀, dist_eq_norm] using (hseg s hs).2.le)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hrem : α (x, t) - α (x₀, t₀) - ((ContinuousLinearMap.fst ℝ E ℝ) +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (f x₀)) ((x, t) - (x₀, t₀)) =
      (α (x, t) - t • f x₀) - (α (x, t₀) - t₀ • f x₀) := by
    simp only [add_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd', Prod.fst_sub,
      Prod.snd_sub, hx₀, hinit x hx, sub_smul]
    abel
  rw [hrem]
  refine hmv.trans (mul_le_mul_of_nonneg_left ?_ hδ.le)
  simpa only [Prod.norm_def, Prod.snd_sub, Real.norm_eq_abs] using
    norm_snd_le ((x, t) - (x₀, t₀))

end

end PDE.Analysis.ODE
