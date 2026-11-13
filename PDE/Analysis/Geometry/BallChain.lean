/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.Positivity

/-!
# Uniform comparison by chains of interior balls

This is the ball-chain argument of the harmonic Harnack theorem, stated
without an equation and in any dimension. Connectedness
gives finite paths, and compactness bounds their lengths uniformly. A radius
cap and an arbitrary enlargement factor support local estimates at bounded
scales.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Set Metric
open scoped Topology

variable {E : Type*} [PseudoMetricSpace E]

/-- Two points share a comparison scale whose enlarged balls stay in the domain. -/
def BallChainLinked (U : Set E) (L ρ : ℝ) (x y : U) : Prop :=
  ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ dist x.1 y.1 ≤ r ∧
    closedBall x.1 (L * r) ⊆ U ∧ closedBall y.1 (L * r) ⊆ U

/-- An admissible ball link is symmetric in its two endpoints. -/
theorem ballChainLinked_symm {U : Set E} {L ρ : ℝ} {x y : U}
    (h : BallChainLinked U L ρ x y) : BallChainLinked U L ρ y x := by
  rcases h with ⟨r, hr, hrρ, hdist, hx, hy⟩
  exact ⟨r, hr, hrρ, by simpa only [dist_comm] using hdist, hy, hx⟩

/-- The simple graph on `U` whose edges are the admissible ball links. -/
def ballChainGraph (U : Set E) (L ρ : ℝ) : SimpleGraph U :=
  SimpleGraph.fromRel (BallChainLinked U L ρ)

/-- Every point of an open set has a capped admissible comparison scale. -/
theorem exists_ballChain_radius {U : Set E} (hU : IsOpen U)
    {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) (x : U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ closedBall x.1 ((L + 1) * r) ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x.1 x.2
  let r := min (ε / (2 * (L + 1))) ρ
  have hden : 0 < 2 * (L + 1) := by positivity
  have hr : 0 < r := lt_min (div_pos hε hden) hρ
  have hrε : r * (2 * (L + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_left _ _)
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  exact (closedBall_subset_ball (by nlinarith : (L + 1) * r < ε)).trans hεU

/-- Points in a smaller ball are linked through the enlarged interior ball. -/
theorem ballChainLinked_of_mem_ball {U : Set E} {L ρ : ℝ}
    {x y : U} {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (hball : closedBall x.1 ((L + 1) * r) ⊆ U)
    (hy : y.1 ∈ ball x.1 r) : BallChainLinked U L ρ x y := by
  have hxy : dist x.1 y.1 < r := by simpa only [mem_ball, dist_comm] using hy
  refine ⟨r, hr, hrρ, hxy.le, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by nlinarith : L * r ≤ (L + 1) * r)).trans hball
  · intro z hz
    apply hball
    have hd : dist z y.1 ≤ L * r := hz
    have htri := dist_triangle z y.1 x.1
    have hyx : dist y.1 x.1 < r := hy
    change dist z x.1 ≤ (L + 1) * r
    nlinarith

/-- Topological connectedness makes the interior-ball graph connected. -/
theorem ballChainGraph_reachable {U : Set E} (hU : IsOpen U)
    (hconn : IsPreconnected U) {L ρ : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) (x y : U) :
    (ballChainGraph U L ρ).Reachable x y := by
  let hUspace : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  refine @PreconnectedSpace.induction₂' U inferInstance hUspace
    (ballChainGraph U L ρ).Reachable ?_ ?_ x y
  · intro p
    obtain ⟨r, hr, hrρ, hball⟩ := exists_ballChain_radius hU hL hρ p
    filter_upwards [Metric.ball_mem_nhds p hr] with q hq
    by_cases hpq : p = q
    · subst q
      exact ⟨SimpleGraph.Reachable.rfl, SimpleGraph.Reachable.rfl⟩
    · have hlinked : BallChainLinked U L ρ p q :=
        ballChainLinked_of_mem_ball hr hrρ hball hq
      have hadj : (ballChainGraph U L ρ).Adj p q :=
        (SimpleGraph.fromRel_adj _ p q).mpr ⟨hpq, Or.inl hlinked⟩
      exact ⟨hadj.reachable, hadj.symm.reachable⟩
  · exact ⟨fun _ _ _ hpq hqz ↦ hpq.trans hqz⟩

/-- Multiplicative edge comparisons compose along a finite walk. -/
theorem le_pow_mul_of_walk {X : Type*} {G : SimpleGraph X} {u : X → ℝ} {A : ℝ}
    (hA : 0 ≤ A) (hlocal : ∀ x y, G.Adj x y → u x ≤ A * u y)
    {x y : X} (w : G.Walk x y) : u x ≤ A ^ w.length * u y := by
  induction w with
  | nil => simp
  | cons h w ih =>
      calc
        u _ ≤ A * u _ := hlocal _ _ h
        _ ≤ A * (A ^ w.length * u _) := mul_le_mul_of_nonneg_left ih hA
        _ = A ^ (SimpleGraph.Walk.cons h w).length * u _ := by
          simp only [SimpleGraph.Walk.length_cons, pow_succ]
          ring

/-- Compactness turns a uniform local comparison into a uniform comparison
on a compact subset of a connected open set. The constant precedes the field. -/
theorem exists_comparison_constant_of_ballChain
    {U K : Set E} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    {L ρ A : ℝ} (hL : 0 ≤ L) (hρ : 0 < ρ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, (∀ x ∈ U, 0 ≤ u x) →
      (∀ x y : U, BallChainLinked U L ρ x y → u x.1 ≤ A * u y.1) →
      ∀ x ∈ K, ∀ y ∈ K, u x ≤ C * u y := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, zero_lt_one, by simp⟩
  obtain ⟨b, hbK⟩ := hKne
  let base : U := ⟨b, hKU hbK⟩
  let G := ballChainGraph U L ρ
  have hreach (q : U) : G.Reachable base q := ballChainGraph_reachable hU hconn hL hρ base q
  let path (q : U) : G.Walk base q := Classical.choice (hreach q)
  have hlocal : ∀ q : U, ∃ r : ℝ, 0 < r ∧ r ≤ ρ ∧ closedBall q.1 ((L + 1) * r) ⊆ U :=
    fun q ↦ exists_ballChain_radius hU hL hρ q
  choose radius hradius hcap hclosed using hlocal
  have hcover : K ⊆ ⋃ q : U, ball q.1 (radius q) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hKU hz⟩, mem_ball_self (hradius ⟨z, hKU hz⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun q : U ↦ ball q.1 (radius q)) (fun _ ↦ isOpen_ball) hcover
  let N : ℕ := (∑ q ∈ t, (path q).length) + 1
  have hbounded (z : K) : ∃ w : G.Walk base ⟨z.1, hKU z.2⟩, w.length ≤ N := by
    obtain ⟨q, hqt, hzq⟩ := mem_iUnion₂.mp (ht z.2)
    have hqN : (path q).length + 1 ≤ N :=
      Nat.add_le_add_right (Finset.single_le_sum
        (f := fun q : U ↦ (path q).length) (fun _ _ ↦ Nat.zero_le _) hqt) 1
    let zU : U := ⟨z.1, hKU z.2⟩
    have hlinked : BallChainLinked U L ρ q zU :=
      ballChainLinked_of_mem_ball (hradius q) (hcap q) (hclosed q) hzq
    by_cases hqz : q = zU
    · subst q
      exact ⟨path zU, (Nat.le_succ _).trans hqN⟩
    · have hadj : G.Adj q zU :=
        (SimpleGraph.fromRel_adj _ q zU).mpr ⟨hqz, Or.inl hlinked⟩
      exact ⟨(path q).concat hadj, by simpa using hqN⟩
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨A ^ (2 * N), pow_pos hApos _, ?_⟩
  intro u hnonneg hlinks x hx y hy
  have hadj : ∀ p q : U, G.Adj p q → u p.1 ≤ A * u q.1 := by
    intro p q hpq
    rcases ((SimpleGraph.fromRel_adj _ p q).mp hpq).2 with h | h
    · exact hlinks p q h
    · exact hlinks p q (ballChainLinked_symm h)
  obtain ⟨wx, hwx⟩ := hbounded ⟨x, hx⟩
  obtain ⟨wy, hwy⟩ := hbounded ⟨y, hy⟩
  have hxbase : u x ≤ A ^ N * u base.1 :=
    (le_pow_mul_of_walk hApos.le hadj wx.reverse).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA (by simpa using hwx)) (hnonneg base.1 base.2))
  have hbasey : u base.1 ≤ A ^ N * u y :=
    (le_pow_mul_of_walk hApos.le hadj wy).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hwy) (hnonneg y (hKU hy)))
  calc
    u x ≤ A ^ N * u base.1 := hxbase
    _ ≤ A ^ N * (A ^ N * u y) := mul_le_mul_of_nonneg_left hbasey (pow_nonneg hApos.le N)
    _ = A ^ (2 * N) * u y := by simp [two_mul, pow_add, mul_assoc]

end PDE.Analysis
