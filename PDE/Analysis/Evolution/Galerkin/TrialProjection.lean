/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.Triple
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Stable Galerkin trial projections

Let `V ↪ H` be a Gelfand triple with inclusion `ι`. A stable trial projection onto a subspace
`S ⊆ V` is a continuous linear map `P : H → S` that fixes `S`, whose error `h - ι(P h)` is
pivot-orthogonal to `ι(S)`, and whose restriction to `V` satisfies `‖P(ι v)‖_V ≤ K ‖v‖_V`.
Such a projection is contractive and a best approximation in the pivot norm. If the trial
spaces eventually approximate every vector of `H`, the projections converge strongly in `H`.
If they eventually approximate every vector of `V` and `K` is uniform, the energy projections
`P ∘ ι` converge strongly in `V`. The trial spaces need not be nested.

A stable trial system is a sequence of finite-dimensional trial spaces with stable projections
of one constant `K`, eventually dense in `V`. Eventual density in `H` follows from density of
`ι`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, equations (12), (13) and (15) (a basis
  orthogonal in `H¹₀(U)` and orthonormal in `L²(U)`, with `d_m^k(0) = (g, w_k)`).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section Galerkin
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A pivot-orthogonal projection `P : H → S` onto a Galerkin trial space `S ⊆ V` with
energy bound `‖P(ι v)‖_V ≤ K ‖v‖_V`. Evans uses a basis orthogonal in both the pivot and
energy spaces (§7.1.2, equations (12) and (13)), for which `K = 1`. -/
structure StableTrialProjection
    (T : GelfandTriple (V := V) (H := H)) (S : Submodule ℝ V) (K : NNReal) where
  /-- Orthogonal projection from the pivot space onto the included trial
  space, with values recorded in `S`. -/
  projection : H →L[ℝ] S
  /-- The projection fixes every vector already lying in the trial space. -/
  fixes : ∀ w : S, projection (T.inclusion (w : V)) = w
  /-- The projection error is pivot-orthogonal to the included trial space. -/
  pivotOrthogonal : ∀ (w : S) (h : H),
    inner ℝ (T.inclusion (w : V))
      (h - T.inclusion (projection h : V)) = 0
  /-- Uniform stability of the pivot projection when restricted to `V`. -/
  norm_le : ∀ v : V, ‖projection (T.inclusion v)‖ ≤ (K : ℝ) * ‖v‖

namespace StableTrialProjection

/-- Restriction of the pivot projection to the energy space. -/
def energyProjection
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) : V →L[ℝ] S :=
  P.projection.comp T.inclusion

/-- The energy projection is the pivot projection after inclusion into the pivot space. -/
@[simp]
theorem energyProjection_apply
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (v : V) :
    P.energyProjection v = P.projection (T.inclusion v) :=
  rfl

/-- The energy projection fixes every vector in the trial space. -/
theorem energyProjection_fixes
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (w : S) :
    P.energyProjection (w : V) = w :=
  P.fixes w

/-- The trial projection viewed as an operator on the pivot space. -/
def pivotProjection
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) : H →L[ℝ] H :=
  (T.inclusion.comp S.subtypeL).comp P.projection

/-- The pivot projection applies the bundled trial projection and then includes
the result into the pivot space. -/
@[simp]
theorem pivotProjection_apply
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (h : H) :
    P.pivotProjection h = T.inclusion (P.projection h : V) :=
  rfl

/-- A pivot-orthogonal trial projection is contractive in the pivot norm:
`‖ι(P h)‖_H ≤ ‖h‖_H`. -/
theorem norm_inclusion_projection_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (h : H) :
    ‖T.inclusion (P.projection h : V)‖ ≤ ‖h‖ := by
  have hdecomp : h =
      T.inclusion (P.projection h : V) +
        (h - T.inclusion (P.projection h : V)) := by
    abel
  have hpyth : ‖h‖ ^ 2 =
      ‖T.inclusion (P.projection h : V)‖ ^ 2 +
        ‖h - T.inclusion (P.projection h : V)‖ ^ 2 := by
    calc
      ‖h‖ ^ 2 = ‖T.inclusion (P.projection h : V) +
          (h - T.inclusion (P.projection h : V))‖ ^ 2 :=
        congrArg (fun z : H ↦ ‖z‖ ^ 2) hdecomp
      _ = ‖T.inclusion (P.projection h : V)‖ ^ 2 +
          ‖h - T.inclusion (P.projection h : V)‖ ^ 2 := by
        simpa only [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_real
            (P.pivotOrthogonal (P.projection h) h)
  have hsq : ‖T.inclusion (P.projection h : V)‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- The pivot-space projection is contractive. -/
theorem norm_pivotProjection_apply_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (h : H) :
    ‖P.pivotProjection h‖ ≤ ‖h‖ := by
  simpa using P.norm_inclusion_projection_le h

/-- The pivot-space projection has operator norm at most one. -/
theorem norm_pivotProjection_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) :
    ‖P.pivotProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simpa using P.norm_pivotProjection_apply_le h

/-- The pivot-orthogonal projection is a best approximation in the pivot norm:
`‖h - ι(P h)‖_H ≤ ‖h - ι w‖_H` for every `w ∈ S`. -/
theorem norm_sub_inclusion_projection_le
    {T : GelfandTriple (V := V) (H := H)} {S : Submodule ℝ V} {K : NNReal}
    (P : StableTrialProjection T S K) (h : H) (w : S) :
    ‖h - T.inclusion (P.projection h : V)‖ ≤
      ‖h - T.inclusion (w : V)‖ := by
  let r : H := h - T.inclusion (P.projection h : V)
  let d : H := T.inclusion ((P.projection h - w : S) : V)
  have hord : inner ℝ d r = 0 := by
    simpa only [d, r] using P.pivotOrthogonal (P.projection h - w) h
  have hdecomp : h - T.inclusion (w : V) = d + r := by
    dsimp [d, r]
    rw [map_sub]
    abel
  have hpyth : ‖h - T.inclusion (w : V)‖ ^ 2 = ‖d‖ ^ 2 + ‖r‖ ^ 2 := by
    calc
      ‖h - T.inclusion (w : V)‖ ^ 2 = ‖d + r‖ ^ 2 :=
        congrArg (fun z : H ↦ ‖z‖ ^ 2) hdecomp
      _ = ‖d‖ ^ 2 + ‖r‖ ^ 2 := by
        simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real hord
  have hsq : ‖r‖ ^ 2 ≤ ‖h - T.inclusion (w : V)‖ ^ 2 := by
    rw [hpyth]
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by simpa only [r] using hsq)

/-- If every `h ∈ H` is eventually approximated by `ι(S n)`, then `ι(Pₙ h) → h` in `H`.
The trial spaces need not be nested, so finite-element families are covered. -/
theorem tendsto_inclusion_projection_of_eventually_approximable
    {T : GelfandTriple (V := V) (H := H)}
    {S : ℕ → Submodule ℝ V} {K : NNReal}
    (P : ∀ n, StableTrialProjection T (S n) K)
    (hdense : ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop,
        ∃ w : S n, ‖h - T.inclusion (w : V)‖ < ε) :
    ∀ h : H, Filter.Tendsto
      (fun n ↦ T.inclusion ((P n).projection h : V))
      Filter.atTop (nhds h) := by
  intro h
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  filter_upwards [hdense h ε hε] with n hn
  obtain ⟨w, hw⟩ := hn
  rw [dist_eq_norm, norm_sub_rev]
  exact ((P n).norm_sub_inclusion_projection_le h w).trans_lt hw

/-- If every `v ∈ V` is eventually approximated by `S n` and the projections share one
energy bound `K`, then `Pₙ(ι v) → v` in `V`. The trial spaces need not be nested. -/
theorem tendsto_energyProjection_of_eventually_approximable
    {T : GelfandTriple (V := V) (H := H)}
    {S : ℕ → Submodule ℝ V} {K : NNReal}
    (P : ∀ n, StableTrialProjection T (S n) K)
    (hdense : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop, ∃ w : S n, ‖v - (w : V)‖ < ε) :
    ∀ v : V, Filter.Tendsto
      (fun n ↦ ((P n).energyProjection v : V))
      Filter.atTop (nhds v) := by
  intro v
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have hK : 0 < (K : ℝ) + 1 := by positivity
  filter_upwards [hdense v (ε / ((K : ℝ) + 1)) (div_pos hε hK)] with n hn
  obtain ⟨w, hw⟩ := hn
  rw [dist_eq_norm]
  have hsplit : ((P n).energyProjection v : V) - v =
      ((P n).energyProjection (v - (w : V)) : V) + ((w : V) - v) := by
    simp only [map_sub, (P n).energyProjection_fixes, Submodule.coe_sub]
    abel
  calc
    ‖((P n).energyProjection v : V) - v‖ =
        ‖((P n).energyProjection (v - (w : V)) : V) + ((w : V) - v)‖ :=
      congrArg norm hsplit
    _ ≤ ‖((P n).energyProjection (v - (w : V)) : V)‖ + ‖(w : V) - v‖ :=
      norm_add_le _ _
    _ ≤ (K : ℝ) * ‖v - (w : V)‖ + ‖(w : V) - v‖ := by
      gcongr
      exact (P n).norm_le (v - (w : V))
    _ = ((K : ℝ) + 1) * ‖v - (w : V)‖ := by
      rw [norm_sub_rev]
      ring
    _ < ((K : ℝ) + 1) * (ε / ((K : ℝ) + 1)) := mul_lt_mul_of_pos_left hw hK
    _ = ε := by field_simp

end StableTrialProjection

/-! ## Transfer of density to the pivot space -/

/-- Eventual approximation in the energy norm, together with density of the
Gelfand inclusion, implies eventual approximation in the pivot norm. -/
theorem eventually_approximable_pivot_of_energy
    (T : GelfandTriple (V := V) (H := H))
    (S : ℕ → Submodule ℝ V)
    (hdenseEnergy : ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ w : S n, ‖v - (w : V)‖ < ε) :
    ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ w : S n, ‖h - T.inclusion (w : V)‖ < ε := by
  intro h ε hε
  obtain ⟨v, hv⟩ :=
    T.denseRange.exists_dist_lt h (half_pos hε)
  have hden : 0 < 2 * (‖T.inclusion‖ + 1) := by positivity
  filter_upwards [
    hdenseEnergy v (ε / (2 * (‖T.inclusion‖ + 1)))
      (div_pos hε hden)] with n hn
  obtain ⟨w, hw⟩ := hn
  refine ⟨w, ?_⟩
  have hJ :
      ‖T.inclusion (v - (w : V))‖ < ε / 2 := by
    have hop := T.inclusion.le_opNorm (v - (w : V))
    have hscale :
        ‖T.inclusion‖ * ‖v - (w : V)‖ < ε / 2 := by
      have hbound :
          ‖T.inclusion‖ < ‖T.inclusion‖ + 1 :=
        lt_add_one _
      have heq :
          (‖T.inclusion‖ + 1) *
              (ε / (2 * (‖T.inclusion‖ + 1))) =
            ε / 2 := by
        field_simp
      calc
        ‖T.inclusion‖ * ‖v - (w : V)‖ <
            (‖T.inclusion‖ + 1) *
              (ε / (2 * (‖T.inclusion‖ + 1))) := by
          exact
            (mul_le_mul_of_nonneg_right hbound.le (norm_nonneg _)).trans_lt
              (mul_lt_mul_of_pos_left hw (by positivity))
        _ = ε / 2 := heq
    exact lt_of_le_of_lt hop hscale
  rw [dist_eq_norm] at hv
  calc
    ‖h - T.inclusion (w : V)‖ =
        ‖(h - T.inclusion v) +
          T.inclusion (v - (w : V))‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖h - T.inclusion v‖ +
        ‖T.inclusion (v - (w : V))‖ :=
      norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hv hJ
    _ = ε := by ring

/-- A uniformly stable finite-dimensional trial family that is eventually
dense in the energy space. -/
structure StableTrialSystem
    (T : GelfandTriple (V := V) (H := H)) where
  /-- The finite-dimensional energy subspaces, not necessarily nested. -/
  space : ℕ → Submodule ℝ V
  /-- Every trial space is finite-dimensional. -/
  finiteDimensional : ∀ k, FiniteDimensional ℝ (space k)
  /-- One nonnegative energy-norm stability constant valid for the entire trial family. -/
  stabilityConstant : NNReal
  /-- Pivot-orthogonal, energy-stable projection onto each trial space. -/
  projection : ∀ k,
    StableTrialProjection T (space k) stabilityConstant
  /-- Every energy-space vector is eventually approximated by vectors in the trial spaces. -/
  denseEnergy :
    ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in Filter.atTop,
        ∃ w : space k, ‖v - (w : V)‖ < ε

namespace StableTrialSystem

/-- Every pivot-space vector is eventually approximated by included trial vectors. -/
theorem densePivot
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T) :
    ∀ h : H, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k in Filter.atTop,
        ∃ w : trials.space k, ‖h - T.inclusion (w : V)‖ < ε :=
  eventually_approximable_pivot_of_energy T trials.space trials.denseEnergy

end StableTrialSystem

end Galerkin

end PDE.Analysis.Evolution
