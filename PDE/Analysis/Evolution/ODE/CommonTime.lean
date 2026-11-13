/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Core.EnergyBarrier
public import PDE.Analysis.Evolution.Core.EnergyIdentity
public import PDE.Analysis.Evolution.ODE.FiniteContinuation
public import Mathlib.Analysis.ODE.ExistUnique
import CAS.ExactTactic

/-!
# Common-time existence from an energy sublevel bound

Compactness gives a common local existence time for initial states in a bounded
finite-dimensional energy sublevel. A first-contact estimate keeps each local
trajectory under the same affine energy envelope. Finite gluing then constructs
a solution on the whole requested interval, without global Lipschitzness of the
vector field.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace PDE.Analysis.Evolution

/-- A continuously differentiable autonomous vector field has a uniform local
existence time for initial states in a compact set. The initial time is arbitrary. -/
theorem exists_uniform_time_on_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {s : Set E} (hs : IsCompact s)
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) :
    ∃ ε > (0 : ℝ), ∀ x ∈ s, ∀ a : ℝ, ∃ u : ℝ → E,
      u a = x ∧ ∀ t ∈ Ioo (a - ε) (a + ε), HasDerivAt u (f (u t)) t := by
  classical
  choose r hr ε hε hlocal using fun x ↦
    (hf x).exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt 0
  obtain ⟨c, _, hc⟩ := hs.elim_nhds_subcover (fun x ↦ Metric.closedBall x (r x))
    (fun x _ ↦ Metric.closedBall_mem_nhds x (hr x))
  have hmin : ∀ c : Finset E, ∃ δ > (0 : ℝ), ∀ x ∈ c, δ ≤ ε x := by
    intro c
    induction c using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x c _ ih =>
      obtain ⟨δ, hδ, hcδ⟩ := ih
      refine ⟨min δ (ε x), lt_min hδ (hε x), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hcδ y hy)
  obtain ⟨δ, hδ, hcδ⟩ := hmin c
  refine ⟨δ, hδ, ?_⟩
  intro x hx a
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hc hx)
  obtain ⟨u, hu, hdu⟩ := hlocal y x hxy
  refine ⟨fun t ↦ u (t - a), by simpa using hu, ?_⟩
  intro t ht
  have htime : t - a ∈ Ioo (0 - ε y) (0 + ε y) := by
    have := hcδ y hy
    constructor <;> linarith [ht.1, ht.2]
  simpa [Function.comp_def] using (hdu (t - a) htime).scomp t ((hasDerivAt_id t).sub_const a)

/-- In finite dimension, let `f` be `C¹` with `⟪f x, x⟫ ≤ K` whenever `½ ‖x‖² ≤ B`, and
let `½ ‖x₀‖² + K (b - a) < B`. Then `u' = f(u)`, `u(a) = x₀` has a solution on
`[a, b]` with `½ ‖u(t)‖² ≤ ½ ‖x₀‖² + K (t - a)`. -/
theorem exists_ode_solution_Icc_of_inner_le_on_sublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E}
    (hf : ∀ x : E, ContDiffAt ℝ 1 f x) (x₀ : E)
    {a b K B : ℝ} (hab : a ≤ b) (hK : 0 ≤ K)
    (hwork : ∀ x : E, (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ B → inner ℝ (f x) x ≤ K)
    (hmargin : (1 / 2 : ℝ) * ‖x₀‖ ^ 2 + K * (b - a) < B) :
    ∃ u : ℝ → E, u a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t) ∧
      ∀ t ∈ Icc a b,
        (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖x₀‖ ^ 2 + K * (t - a) := by
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
    (fun t _ ↦ (1 / 2 : ℝ) * ‖x₀‖ ^ 2 + K * (t - a))
    hd N hNnat hendpoint x₀ (by simp)
  intro n hn x hx
  have hcell : a + (n : ℝ) * d ≤ a + ((n + 1 : ℕ) : ℝ) * d := by
    push_cast
    nlinarith
  have hright : a + ((n + 1 : ℕ) : ℝ) * d ≤ b := by
    rw [← hendpoint]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt hn) hd)
  have hprefix : (1 / 2 : ℝ) * ‖x₀‖ ^ 2 + K * ((a + (n : ℝ) * d) - a) < B := by
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hcell.trans hright) a) hK
    linarith
  have hxB : (1 / 2 : ℝ) * ‖x‖ ^ 2 ≤ B := hx.trans hprefix.le
  have hxball : x ∈ Metric.closedBall (0 : E) (2 * B + 1) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖x‖ - 1)]
  obtain ⟨u, hu, hdu⟩ := hlocal x hxball (a + (n : ℝ) * d)
  have hderiv (t : ℝ) (ht : t ∈ Icc (a + (n : ℝ) * d)
      (a + ((n + 1 : ℕ) : ℝ) * d)) :
      HasDerivWithinAt u (f (u t))
        (Icc (a + (n : ℝ) * d) (a + ((n + 1 : ℕ) : ℝ) * d)) t := by
    apply (hdu t ?_).hasDerivWithinAt
    constructor
    · linarith [ht.1]
    · have := ht.2
      push_cast at this
      nlinarith
  refine ⟨u, hu, hderiv, ?_⟩
  have hcellmargin : (1 / 2 : ℝ) * ‖u (a + (n : ℝ) * d)‖ ^ 2 +
      K * ((a + ((n + 1 : ℕ) : ℝ) * d) - (a + (n : ℝ) * d)) < B := by
    rw [hu]
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right hright a) hK
    nlinarith
  have henergy := le_affine_of_hasDerivWithinAt_le_on_sublevel hcell hK
    (fun t ht ↦ hasDerivWithinAt_half_norm_sq (hderiv t ht))
    (fun t _ ↦ hwork (u t)) hcellmargin
  intro t ht
  have := henergy t ht
  rw [hu] at this
  nlinarith

end PDE.Analysis.Evolution
