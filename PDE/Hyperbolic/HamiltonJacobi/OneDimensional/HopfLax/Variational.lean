/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax
public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Path.Hamiltonian

/-!
# The path-space variational formula behind Hopf–Lax

We specialize the finite-dimensional path and action formalism to the
one-dimensional Hamiltonian conventions of Evans, §3.3.2(b),
Theorem 4: the value function in formula (17) equals the Hopf–Lax
formula (21). For positive time, the pointwise formula

`inf_y (φ(y) + t L((x - y) / t))`

equals the infimum of

`φ(γ(0)) + integral_0^t L(γ'(s)) ds`

over absolutely continuous paths with `γ(t) = x`. Evans takes the infimum in (17) over `C¹`
paths.

The action is real-valued, so the path type records that
`L (deriv γ)` is integrable. This is the finite-action part of
the usual extended-real variational problem: paths with infinite action do
not affect its infimum. The lower bound is Jensen's inequality combined
with the fundamental theorem of calculus for absolutely continuous
functions. The reverse bound is attained, for each initial point, by the
constant-speed straight path.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), definition (17) and Theorem 4.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HopfLax1D

noncomputable section

open MeasureTheory Set

/-- An absolutely continuous path ending at `x` at time `t`, with finite
Lagrangian action. -/
structure AdmissiblePath (H : ℝ → ℝ) (t x : ℝ) where
  /-- The path, defined on all of `ℝ` and used on `[0,t]`. -/
  curve : ℝ → ℝ
  /-- Absolute continuity on the time interval. -/
  absolutelyContinuous : AbsolutelyContinuousOnInterval curve 0 t
  /-- The prescribed terminal point. -/
  terminal : curve t = x
  /-- Finiteness of the Lagrangian action. -/
  actionIntegrable :
    IntervalIntegrable (fun s ↦ legendreTransform H (deriv curve s)) volume 0 t

/-- View a scalar Hamiltonian path in the general Lagrangian path space. -/
def AdmissiblePath.toPath {H : ℝ → ℝ} {t x : ℝ} (γ : AdmissiblePath H t x) :
    HamiltonJacobi.HopfLax.AdmissiblePath (legendreTransform H) t x where
  curve := γ.curve
  absolutelyContinuous := γ.absolutelyContinuous
  terminal := γ.terminal
  actionIntegrable := γ.actionIntegrable

/-- The action of an admissible path, including the initial cost. -/
noncomputable def pathCost (H φ : ℝ → ℝ) {t x : ℝ}
    (γ : AdmissiblePath H t x) : ℝ :=
  φ (γ.curve 0) +
    ∫ s in (0 : ℝ)..t, legendreTransform H (deriv γ.curve s)

/-- The variational problem (17) of Evans, over absolutely continuous paths in place of `C¹`
paths. -/
noncomputable def variationalValue (H φ : ℝ → ℝ) (t x : ℝ) : ℝ :=
  sInf (Set.range (pathCost H φ : AdmissiblePath H t x → ℝ))

/-- The constant-speed path from `y` at time zero to `x` at time `t`. -/
noncomputable def straightPath (H : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) (y : ℝ) :
    AdmissiblePath H t x :=
  let γ := HamiltonJacobi.HopfLax.straightPath (legendreTransform H) (x := x) ht y
  ⟨γ.curve, γ.absolutelyContinuous, γ.terminal, γ.actionIntegrable⟩

/-- The straight path is the affine curve `s ↦ y + s (x - y) / t`. -/
@[simp]
theorem straightPath_curve (H : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) (y s : ℝ) :
    (straightPath H (x := x) ht y).curve s = y + s * ((x - y) / t) := by
  simp only [straightPath, HamiltonJacobi.HopfLax.straightPath_curve, smul_eq_mul, div_eq_inv_mul]

/-- The straight path starts at `y`. -/
theorem straightPath_start (H : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) (y : ℝ) :
    (straightPath H (x := x) ht y).curve 0 = y := by
  simp [straightPath]

/-- The straight path has constant velocity `(x - y) / t`. -/
theorem deriv_straightPath (H : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) (y s : ℝ) :
    deriv (straightPath H (x := x) ht y).curve s = (x - y) / t := by
  simpa only [straightPath, smul_eq_mul, div_eq_inv_mul] using
    HamiltonJacobi.HopfLax.deriv_straightPath (legendreTransform H) (x := x) ht y s

/-- The action of the straight path from `y` is exactly the Hopf–Lax integrand
`φ(y) + t L((x - y) / t)`. This is the competitor showing that the path-space
infimum is at most the Hopf–Lax infimum. -/
theorem pathCost_straightPath (H φ : ℝ → ℝ) {t x : ℝ} (ht : 0 < t) (y : ℝ) :
    pathCost H φ (straightPath H (x := x) ht y) = hopfLaxIntegrand H φ t x y := by
  simpa only [pathCost, straightPath, hopfLaxIntegrand,
    HamiltonJacobi.HopfLax.pathCost, smul_eq_mul, div_eq_inv_mul] using
    HamiltonJacobi.HopfLax.pathCost_straightPath (legendreTransform H) φ (x := x) ht y

/-- Jensen's inequality for the velocity of an absolutely continuous path.
The mean velocity is fixed by the two endpoints. -/
theorem lagrangian_displacement_le_action {H : ℝ → ℝ} (hFin : LegendreFinite H) {t x : ℝ}
    (ht : 0 < t) (γ : AdmissiblePath H t x) :
    t * legendreTransform H ((x - γ.curve 0) / t) ≤
      ∫ s in (0 : ℝ)..t, legendreTransform H (deriv γ.curve s) := by
  simpa only [AdmissiblePath.toPath, smul_eq_mul, div_eq_inv_mul] using
    HamiltonJacobi.HopfLax.lagrangian_displacement_le_action
      (convexOn_legendreTransform hFin) (continuous_legendreTransform hFin) ht γ.toPath

/-- Every finite-action absolutely continuous path has cost at least the
Hopf–Lax value. -/
theorem hopfLax_le_pathCost {H φ : ℝ → ℝ} {t x : ℝ} (hFin : LegendreFinite H) (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) (γ : AdmissiblePath H t x) :
    hopfLax H φ t x ≤ pathCost H φ γ :=
  (hopfLax_le_integrand hbb).trans (by
    unfold hopfLaxIntegrand pathCost
    gcongr
    exact lagrangian_displacement_le_action hFin ht γ)

/-- A straight path from a minimizing Hopf–Lax footpoint minimizes the
path-space cost among all admissible paths. -/
theorem isMinOn_pathCost_straightPath_of_hopfLax_eq_integrand {H φ : ℝ → ℝ} {t x y : ℝ}
    (hFin : LegendreFinite H) (ht : 0 < t) (hbb : HopfLaxBddBelow H φ t x)
    (hy : hopfLax H φ t x = hopfLaxIntegrand H φ t x y) :
    IsMinOn (pathCost H φ : AdmissiblePath H t x → ℝ) Set.univ (straightPath H (x := x) ht y) := by
  intro γ _
  rw [pathCost_straightPath, ← hy]
  exact hopfLax_le_pathCost hFin ht hbb γ

/-- The path-cost range is bounded below whenever the pointwise Hopf–Lax
integrand is bounded below. -/
theorem pathCost_bddBelow {H φ : ℝ → ℝ} {t x : ℝ} (hFin : LegendreFinite H) (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) :
    BddBelow (Set.range (pathCost H φ : AdmissiblePath H t x → ℝ)) :=
  ⟨hopfLax H φ t x, Set.forall_mem_range.2 (hopfLax_le_pathCost hFin ht hbb)⟩

/-- A global minimizer of the path cost attains the infimum defining the
variational value. -/
theorem pathCost_eq_variationalValue_of_isMinOn {H φ : ℝ → ℝ} {t x : ℝ} {γ : AdmissiblePath H t x}
    (hγ : IsMinOn (pathCost H φ : AdmissiblePath H t x → ℝ) Set.univ γ) :
    pathCost H φ γ = variationalValue H φ t x :=
  Eq.symm (IsLeast.csInf_eq ⟨⟨γ, rfl⟩, Set.forall_mem_range.2 fun η ↦ hγ (Set.mem_univ η)⟩)

/-- Evans, §3.3.2(b), Theorem 4 in one space dimension: the
pointwise Hopf–Lax formula (21) is exactly the absolutely-continuous-path
variational problem (17). -/
theorem hopfLax_eq_variationalValue {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {t x : ℝ} (ht : 0 < t)
    (hbb : HopfLaxBddBelow H φ t x) :
    hopfLax H φ t x = variationalValue H φ t x := by
  refine le_antisymm (le_csInf ⟨_, straightPath H (x := x) ht x, rfl⟩
    (Set.forall_mem_range.2 (hopfLax_le_pathCost hFin ht hbb)))
    (le_csInf (Set.range_nonempty _) (Set.forall_mem_range.2 fun y ↦ ?_))
  exact (csInf_le (pathCost_bddBelow hFin ht hbb) ⟨straightPath H (x := x) ht y, rfl⟩).trans_eq
    (pathCost_straightPath H φ ht y)

/-- Any path attaining the variational value starts at a minimizing
footpoint for the pointwise Hopf–Lax formula. -/
theorem hopfLax_eq_integrand_of_pathCost_eq_variationalValue {H φ : ℝ → ℝ} {t x : ℝ}
    (hFin : LegendreFinite H) (ht : 0 < t) (hbb : HopfLaxBddBelow H φ t x)
    (γ : AdmissiblePath H t x) (hγ : pathCost H φ γ = variationalValue H φ t x) :
    hopfLax H φ t x = hopfLaxIntegrand H φ t x (γ.curve 0) := by
  refine le_antisymm (hopfLax_le_integrand hbb) ?_
  rw [hopfLax_eq_variationalValue hFin ht hbb, ← hγ]
  unfold hopfLaxIntegrand pathCost
  gcongr
  exact lagrangian_displacement_le_action hFin ht γ

/-- The initial point of any globally minimizing path is a minimizing
footpoint for the pointwise Hopf–Lax formula. -/
theorem hopfLax_eq_integrand_of_isMinOn_pathCost {H φ : ℝ → ℝ} {t x : ℝ} (hFin : LegendreFinite H)
    (ht : 0 < t) (hbb : HopfLaxBddBelow H φ t x) (γ : AdmissiblePath H t x)
    (hγ : IsMinOn (pathCost H φ : AdmissiblePath H t x → ℝ) Set.univ γ) :
    hopfLax H φ t x = hopfLaxIntegrand H φ t x (γ.curve 0) :=
  hopfLax_eq_integrand_of_pathCost_eq_variationalValue hFin ht hbb γ
      (pathCost_eq_variationalValue_of_isMinOn hγ)

/-- The form for Lipschitz initial data, as in Evans's Theorem 4. Finiteness of the
Legendre transform supplies the coercive lower bound needed to make the
pointwise and path-space infima real-valued. -/
theorem hopfLax_eq_variationalValue_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    hopfLax H φ t x = variationalValue H φ t x :=
  hopfLax_eq_variationalValue hFin ht (hopfLaxBddBelow_of_lipschitz hFin hφ ht)

/-- For Lipschitz initial data, the path-space variational problem has a
global minimizer at every positive time and terminal point. -/
theorem exists_isMinOn_pathCost_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H) {K : NNReal}
    (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ γ : AdmissiblePath H t x, IsMinOn (pathCost H φ : AdmissiblePath H t x → ℝ) Set.univ γ := by
  obtain ⟨y, hy⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x) hFin hφ ht
  exact ⟨straightPath H (x := x) ht y, isMinOn_pathCost_straightPath_of_hopfLax_eq_integrand
    hFin ht (hopfLaxBddBelow_of_lipschitz hFin hφ ht) hy⟩

/-- For Lipschitz initial data, the infimum defining the path-space
variational value is attained by an admissible path. -/
theorem exists_variationalValue_eq_pathCost_of_lipschitz {H φ : ℝ → ℝ} (hFin : LegendreFinite H)
    {K : NNReal} (hφ : LipschitzWith K φ) {t x : ℝ} (ht : 0 < t) :
    ∃ γ : AdmissiblePath H t x, variationalValue H φ t x = pathCost H φ γ := by
  obtain ⟨y, hy⟩ := exists_hopfLax_eq_integrand_of_lipschitz (x := x) hFin hφ ht
  exact ⟨straightPath H (x := x) ht y, ((hopfLax_eq_variationalValue_of_lipschitz hFin hφ
    ht).symm.trans hy).trans (pathCost_straightPath H φ ht y).symm⟩

end

end HopfLax1D
