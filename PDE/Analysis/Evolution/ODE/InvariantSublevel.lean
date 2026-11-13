/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Evolution.ODE.CommonTime
import CAS.ExactTactic

/-!
# Finite-dimensional evolution inside a strict energy barrier

If the energy derivative points strictly inward on the boundary of a ball, a
trajectory starting inside cannot leave. Compactness supplies a common local
existence time for states in that ball. Gluing finitely many such trajectories
reaches any requested finite endpoint while preserving the same energy bound.
Uniqueness on the ball makes these solutions agree on overlapping intervals,
giving one trajectory defined for all future time.

The vector field need only be continuously differentiable, and the inward
estimate is needed only on the energy boundary.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology
open scoped InnerProductSpace

namespace PDE.Analysis.Evolution

/-- A strict inward work estimate on an energy sphere constructs a trajectory
on every requested compact interval and keeps it in the enclosed ball. The
initial state may lie on the boundary. The hypotheses are consistent only for `0 < B`:
at `B = 0` the work estimate at `x = 0` would read `0 < 0`. -/
theorem exists_ode_solution_Icc_of_inner_neg_on_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E}
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) (x₀ : E)
    {a b B : ℝ} (hab : a ≤ b)
    (hwork : ∀ x : E, (1 / 2 : ℝ) * ‖x‖ ^ 2 = B → inner ℝ (f x) x < 0)
    (hinit : (1 / 2 : ℝ) * ‖x₀‖ ^ 2 ≤ B) :
    ∃ u : ℝ → E, u a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b, (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤ B := by
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_time_on_isCompact
    (isCompact_closedBall (0 : E) (2 * B + 1)) hf
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((b - a) / ε) 0)
  have hNpos : 0 < (N : ℝ) := (le_max_right _ _).trans_lt hN
  have hNnat : 0 < N := Nat.cast_pos.mp hNpos
  let d : ℝ := (b - a) / N
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hab) hNpos.le
  have hdε : d < ε := by
    apply (div_lt_iff₀ hNpos).mpr
    have := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hN)
    nlinarith
  have hendpoint : a + (N : ℝ) * d = b := by
    dsimp [d]
    cas using hNpos
  apply exists_ode_solution_Icc_of_partition_of_energyEnvelope
    (fun _ ↦ f) (fun _ x ↦ (1 / 2 : ℝ) * ‖x‖ ^ 2)
    (fun _ _ ↦ B) hd N hNnat hendpoint x₀ hinit
  intro n _ x hx
  have hxball : x ∈ Metric.closedBall (0 : E) (2 * B + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  obtain ⟨u, hu, hdu⟩ := hlocal x hxball (a + (n : ℝ) * d)
  have hderiv (t : ℝ) (ht : t ∈ Icc (a + (n : ℝ) * d)
      (a + ((n + 1 : ℕ) : ℝ) * d)) : HasDerivAt u (f (u t)) t := by
    apply hdu t
    constructor
    · linarith [ht.1]
    · have := ht.2
      push_cast at this
      nlinarith
  refine ⟨u, hu, fun t ht ↦ (hderiv t ht).hasDerivWithinAt, ?_⟩
  have he (t : ℝ) (ht : t ∈ Icc (a + (n : ℝ) * d)
      (a + ((n + 1 : ℕ) : ℝ) * d)) :
      HasDerivAt (fun r ↦ (1 / 2 : ℝ) * ‖u r‖ ^ 2) (inner ℝ (f (u t)) (u t)) t :=
    hasDerivAt_half_norm_sq (hderiv t ht)
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun t ht ↦ (he t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (he t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (by simpa only [hu] using hx)
    (fun t ↦ hasDerivAt_const t B)
  intro t _ ht
  exact hwork (u t) ht

/-- A strict inward energy barrier yields one trajectory for all future time.
Uniqueness on the common energy ball makes the finite-interval solutions agree,
so their union is differentiable even where a different interval was chosen. As in the
compact-interval version, the hypotheses are consistent only for `0 < B`. -/
theorem exists_ode_solution_Ici_of_inner_neg_on_boundary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E}
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) (x₀ : E) (a : ℝ)
    {B : ℝ}
    (hwork : ∀ x : E, (1 / 2 : ℝ) * ‖x‖ ^ 2 = B → inner ℝ (f x) x < 0)
    (hinit : (1 / 2 : ℝ) * ‖x₀‖ ^ 2 ≤ B) :
    ∃ u : ℝ → E, u a = x₀ ∧
      (∀ t ∈ Ici a, HasDerivWithinAt u (f (u t)) (Ici a) t) ∧
      ∀ t ∈ Ici a, (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤ B := by
  classical
  let b (t : ℝ) := max a t + 1
  have hb (t : ℝ) : a < b t := by dsimp only [b]; linarith [le_max_left a t]
  have htb (t : ℝ) : t < b t := by dsimp only [b]; linarith [le_max_right a t]
  choose v hv hd he using fun t : ℝ ↦
    exists_ode_solution_Icc_of_inner_neg_on_boundary hf x₀ (hb t).le hwork hinit
  let ball := Metric.closedBall (0 : E) (2 * B + 1)
  have hball (x : E) (hx : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ B) : x ∈ ball := by
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hC1 : ContDiff ℝ 1 f := contDiff_iff_contDiffAt.2 hf
  obtain ⟨K, hK⟩ := hC1.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : E) (2 * B + 1)) (isCompact_closedBall _ _)
  have hright (s t : ℝ) (hat : a ≤ t) (htb : t < b s) :
      HasDerivWithinAt (v s) (f (v s t)) (Ici t) t := by
    apply (hasDerivWithinAt_inter (Iio_mem_nhds htb)).mp
    exact (hd s t ⟨hat, htb.le⟩).mono (fun y hy ↦ ⟨hat.trans hy.1, hy.2.le⟩)
  have hagree (s t x : ℝ) (hax : a ≤ x) (hxs : x ≤ b s) (hxt : x ≤ b t) :
      v s x = v t x := by
    have hscont : ContinuousOn (v s) (Icc a x) :=
      (HasDerivWithinAt.continuousOn (hd s)).mono (Icc_subset_Icc_right hxs)
    have htcont : ContinuousOn (v t) (Icc a x) :=
      (HasDerivWithinAt.continuousOn (hd t)).mono (Icc_subset_Icc_right hxt)
    have hsame := ODE_solution_unique_of_mem_Icc_right
      (v := fun _ ↦ f) (s := fun _ ↦ ball) (K := K)
      (fun _ _ ↦ hK) hscont
      (fun r hr ↦ hright s r hr.1 (hr.2.trans_le hxs))
      (fun r hr ↦ hball _ (he s r ⟨hr.1, hr.2.le.trans hxs⟩)) htcont
      (fun r hr ↦ hright t r hr.1 (hr.2.trans_le hxt))
      (fun r hr ↦ hball _ (he t r ⟨hr.1, hr.2.le.trans hxt⟩))
      ((hv s).trans (hv t).symm)
    exact hsame ⟨hax, le_rfl⟩
  let u : ℝ → E := fun t ↦ v t t
  have hlocal (t : ℝ) : EqOn u (v t) (Icc a (b t)) := by
    intro s hs
    exact hagree s t s hs.1 (htb s).le hs.2
  refine ⟨u, hv a, ?_, fun t ht ↦ he t t ⟨ht, (htb t).le⟩⟩
  intro t ht
  have htmem : t ∈ Icc a (b t) := ⟨ht, (htb t).le⟩
  have hderiv : HasDerivWithinAt u (f (u t)) (Icc a (b t)) t :=
    (hd t t htmem).congr_of_mem (hlocal t) htmem
  apply (hasDerivWithinAt_inter (Iio_mem_nhds (htb t))).mp
  exact hderiv.mono (fun s hs ↦ ⟨hs.1, hs.2.le⟩)

end PDE.Analysis.Evolution
