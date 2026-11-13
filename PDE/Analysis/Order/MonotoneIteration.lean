/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

/-!
# Monotone iteration on order intervals

The order-theoretic core of the subsolution and supersolution method. If a
monotone map sends a lower barrier upward and an
upper barrier downward, all iterates remain in the corresponding closed
interval. Lower iterates lie below every fixed point in the interval, while
upper iterates lie above every such fixed point. More strongly, every lower
iterate lies below every upper iterate, even when the iteration indices
differ.

When one of these iterate sequences converges and the map is continuous at
the limit, the limit is respectively the least or greatest fixed point in
the interval. The final results derive this convergence from compactness of
the orbit. The argument uses compactness to obtain a cluster point and the
closedness of the order relation to prove that a monotone sequence has at
most one cluster point.

Everything here is purely order-theoretic and topological: `α` is a partial
order with an `OrderClosedTopology`, `T : α → α` is monotone, and the barriers
are elements `lower ≤ T lower` and `T upper ≤ upper`. In the PDE application
`α` is a function space ordered pointwise, `T` is the solution operator of a
linearised problem, and the barriers are a subsolution and a supersolution;
the analytic input (monotonicity of `T`, compactness of the orbit) is proved
separately and fed in as hypotheses.

## Main results

* `iterate_mem_Icc`: all iterates `T^[n] x` of a point of `[lower, upper]`
  stay in `[lower, upper]`.
* `iterate_lower_le_iterate_upper`: `T^[m] lower ≤ T^[n] upper` for all `m, n`.
* `iterate_le_fixedPoint`, `fixedPoint_le_iterate`: lower iterates lie below,
  and upper iterates above, every fixed point in the interval.
* `isLeast_fixedPoint_Icc_of_tendsto_iterate`,
  `isGreatest_fixedPoint_Icc_of_tendsto_iterate`: a convergent lower (upper)
  orbit converges to the least (greatest) fixed point in the interval, provided
  `T` is continuous at the limit.
* `exists_least_fixed_point_Icc_of_compact_iterates`,
  `exists_greatest_fixed_point_Icc_of_compact_iterates`: the same conclusions
  with convergence derived from compactness of the orbit.
* `exists_tendsto_of_monotone_of_isCompact`: a monotone sequence in a compact
  set converges (to a point of the set).

## How it works

The scheme is the monotone iteration in the proof of Evans, §9.3, Theorem 1, where `T` sends
`u_k` to the weak solution `u_{k+1}` of the linear problem (7), and steps 2 and 3 prove (8) and
(13), hence (15): `lower ≤ u_k ≤ u_{k+1} ≤ upper`. `iterate_mem_Icc` and
`iterate_lower_le_iterate_upper` are the order part of this; they need only the monotonicity of
`T`, which in Evans comes from the choice (6) of `λ` and an integration by parts. Evans gets
convergence from the almost-everywhere monotone limit and the Dominated Convergence Theorem,
(16); we assume instead that the orbit is compact and use
`exists_tendsto_of_monotone_of_isCompact`, and continuity of `T` at the limit replaces step 5
of his proof. That the limits are the least and greatest fixed points in the interval is not
part of his theorem; it follows from `iterate_le_fixedPoint` and `fixedPoint_le_iterate`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.3, Theorem 1, p. 544, and steps 1-5 of its proof,
  (6)-(16), pp. 544-546. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Function Set
open scoped Topology

namespace PDE.OrderInterval

variable {α : Type*}

/-- A monotone sequence in a space with closed order has at most one cluster
point. -/
theorem mapClusterPt_eq_of_monotone
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : ℕ → α} (hf : Monotone f) {u v : α}
    (hu : MapClusterPt u atTop f) (hv : MapClusterPt v atTop f) :
    u = v := by
  apply le_antisymm
  · have hle (n : ℕ) : f n ≤ v := by
      exact isClosed_Ici.mem_of_mapClusterPt hv <|
        (eventually_ge_atTop n).mono fun m hnm ↦ hf hnm
    exact isClosed_Iic.mem_of_mapClusterPt hu (Eventually.of_forall hle)
  · have hle (n : ℕ) : f n ≤ u := by
      exact isClosed_Ici.mem_of_mapClusterPt hu <|
        (eventually_ge_atTop n).mono fun m hnm ↦ hf hnm
    exact isClosed_Iic.mem_of_mapClusterPt hv (Eventually.of_forall hle)

/-- An antitone sequence in a space with closed order has at most one cluster
point. -/
theorem mapClusterPt_eq_of_antitone
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : ℕ → α} (hf : Antitone f) {u v : α}
    (hu : MapClusterPt u atTop f) (hv : MapClusterPt v atTop f) :
    u = v := by
  exact mapClusterPt_eq_of_monotone (α := αᵒᵈ) hf hu hv

/-- A monotone sequence contained in a compact set converges to a point of
that set. -/
theorem exists_tendsto_of_monotone_of_isCompact
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : ℕ → α} (hf : Monotone f) {K : Set α}
    (hK : IsCompact K) (hmem : ∀ n, f n ∈ K) :
    ∃ u ∈ K, Tendsto f atTop (𝓝 u) := by
  have heventually : ∀ᶠ n in atTop, f n ∈ K := Eventually.of_forall hmem
  obtain ⟨u, huK, hu⟩ :=
    hK.exists_mapClusterPt_of_frequently heventually.frequently
  refine ⟨u, huK, hK.tendsto_nhds_of_unique_mapClusterPt heventually ?_⟩
  intro v _hvK hv
  exact mapClusterPt_eq_of_monotone hf hv hu

/-- An antitone sequence contained in a compact set converges to a point of
that set. -/
theorem exists_tendsto_of_antitone_of_isCompact
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : ℕ → α} (hf : Antitone f) {K : Set α}
    (hK : IsCompact K) (hmem : ∀ n, f n ∈ K) :
    ∃ u ∈ K, Tendsto f atTop (𝓝 u) := by
  exact exists_tendsto_of_monotone_of_isCompact (α := αᵒᵈ) hf hK hmem

/-- Every iterate of a monotone map remains between invariant lower and
upper barriers. -/
theorem iterate_mem_Icc
    [Preorder α]
    (T : α → α) (hT : Monotone T)
    {lower upper x : α}
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (hx : x ∈ Icc lower upper) (n : ℕ) :
    T^[n] x ∈ Icc lower upper := by
  apply (show MapsTo T (Icc lower upper) (Icc lower upper) from ?_).iterate n hx
  intro y hy
  exact ⟨hlower.trans (hT hy.1), (hT hy.2).trans hupper⟩

/-- Every iterate from the lower barrier lies below every iterate from the
upper barrier. -/
theorem iterate_lower_le_iterate_upper
    [Preorder α]
    (T : α → α) (hT : Monotone T)
    {lower upper : α} (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (m n : ℕ) :
    T^[m] lower ≤ T^[n] upper := by
  have hlower_mono : Monotone (fun k : ℕ ↦ T^[k] lower) :=
    hT.monotone_iterate_of_le_map hlower
  have hupper_anti : Antitone (fun k : ℕ ↦ T^[k] upper) :=
    hT.antitone_iterate_of_map_le hupper
  calc
    T^[m] lower ≤ T^[max m n] lower := hlower_mono (Nat.le_max_left m n)
    _ ≤ T^[max m n] upper := hT.iterate (max m n) hlowerupper
    _ ≤ T^[n] upper := hupper_anti (Nat.le_max_right m n)

/-- Lower iterates of a monotone map lie below every fixed point above the
initial lower barrier. -/
theorem iterate_le_fixedPoint
    [Preorder α]
    (T : α → α) (hT : Monotone T)
    {lower u : α} (hlower : lower ≤ u)
    (hu : IsFixedPt T u) (n : ℕ) :
    T^[n] lower ≤ u := by
  induction n with
  | zero =>
      simpa
  | succ n ih =>
      rw [iterate_succ_apply']
      exact (hT ih).trans_eq hu

/-- Upper iterates of a monotone map lie above every fixed point below the
initial upper barrier. -/
theorem fixedPoint_le_iterate
    [Preorder α]
    (T : α → α) (hT : Monotone T)
    {upper u : α} (hupper : u ≤ upper)
    (hu : IsFixedPt T u) (n : ℕ) :
    u ≤ T^[n] upper := by
  induction n with
  | zero =>
      simpa
  | succ n ih =>
      rw [iterate_succ_apply']
      calc
        u = T u := hu.symm
        _ ≤ T (T^[n] upper) := hT ih

/-- If the lower iterates converge, their limit is the least fixed point in
the invariant interval. -/
theorem isLeast_fixedPoint_Icc_of_tendsto_iterate
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    (T : α → α) (hT : Monotone T)
    {lower upper u : α}
    (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (hcontinuous : ContinuousAt T u)
    (hu : Tendsto (fun n : ℕ ↦ T^[n] lower) atTop (𝓝 u)) :
    IsLeast {w | w ∈ Icc lower upper ∧ IsFixedPt T w} u := by
  have hmem : ∀ n : ℕ, T^[n] lower ∈ Icc lower upper := fun n ↦
    iterate_mem_Icc T hT hlower hupper ⟨le_rfl, hlowerupper⟩ n
  have huIcc : u ∈ Icc lower upper :=
    isClosed_Icc.mem_of_tendsto hu (Eventually.of_forall hmem)
  have hufixed : IsFixedPt T u :=
    _root_.isFixedPt_of_tendsto_iterate hu hcontinuous
  refine ⟨⟨huIcc, hufixed⟩, ?_⟩
  intro w hw
  exact le_of_tendsto' hu fun n ↦
    iterate_le_fixedPoint T hT hw.1.1 hw.2 n

/-- If the upper iterates converge, their limit is the greatest fixed point
in the invariant interval. -/
theorem isGreatest_fixedPoint_Icc_of_tendsto_iterate
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    (T : α → α) (hT : Monotone T)
    {lower upper u : α}
    (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (hcontinuous : ContinuousAt T u)
    (hu : Tendsto (fun n : ℕ ↦ T^[n] upper) atTop (𝓝 u)) :
    IsGreatest {w | w ∈ Icc lower upper ∧ IsFixedPt T w} u := by
  have hmem : ∀ n : ℕ, T^[n] upper ∈ Icc lower upper := fun n ↦
    iterate_mem_Icc T hT hlower hupper ⟨hlowerupper, le_rfl⟩ n
  have huIcc : u ∈ Icc lower upper :=
    isClosed_Icc.mem_of_tendsto hu (Eventually.of_forall hmem)
  have hufixed : IsFixedPt T u :=
    _root_.isFixedPt_of_tendsto_iterate hu hcontinuous
  refine ⟨⟨huIcc, hufixed⟩, ?_⟩
  intro w hw
  exact ge_of_tendsto' hu fun n ↦
    fixedPoint_le_iterate T hT hw.1.2 hw.2 n

/-- Compactness of the lower orbit produces the least fixed point in the
invariant interval. -/
theorem exists_least_fixed_point_Icc_of_compact_iterates
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    (T : α → α) (hT : Monotone T)
    {lower upper : α}
    (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (hcontinuous : Continuous T)
    {K : Set α} (hK : IsCompact K)
    (hiterates : ∀ n : ℕ, T^[n] lower ∈ K) :
    ∃ u ∈ K, IsLeast {w | w ∈ Icc lower upper ∧ IsFixedPt T w} u := by
  obtain ⟨u, huK, hu⟩ :=
    exists_tendsto_of_monotone_of_isCompact
      (hT.monotone_iterate_of_le_map hlower) hK hiterates
  exact
    ⟨u, huK,
      isLeast_fixedPoint_Icc_of_tendsto_iterate
        T hT hlowerupper hlower hupper hcontinuous.continuousAt hu⟩

/-- Compactness of the upper orbit produces the greatest fixed point in the
invariant interval. -/
theorem exists_greatest_fixed_point_Icc_of_compact_iterates
    [PartialOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    (T : α → α) (hT : Monotone T)
    {lower upper : α}
    (hlowerupper : lower ≤ upper)
    (hlower : lower ≤ T lower) (hupper : T upper ≤ upper)
    (hcontinuous : Continuous T)
    {K : Set α} (hK : IsCompact K)
    (hiterates : ∀ n : ℕ, T^[n] upper ∈ K) :
    ∃ u ∈ K, IsGreatest {w | w ∈ Icc lower upper ∧ IsFixedPt T w} u := by
  obtain ⟨u, huK, hu⟩ :=
    exists_tendsto_of_antitone_of_isCompact
      (hT.antitone_iterate_of_map_le hupper) hK hiterates
  exact
    ⟨u, huK,
      isGreatest_fixedPoint_Icc_of_tendsto_iterate
        T hT hlowerupper hlower hupper hcontinuous.continuousAt hu⟩

end PDE.OrderInterval
