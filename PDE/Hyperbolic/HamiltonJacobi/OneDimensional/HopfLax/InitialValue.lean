/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.InitialValue
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Viscosity
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Regularity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Comparison

/-!
# Hopf–Lax solutions of the Hamilton–Jacobi initial-value problem

The closed-time Hopf–Lax operator solves the viscosity initial-value problem of Evans, §10.1.1,
in the form of `OneDimensional.InitialValue`. This is Theorem 3 of Evans, §10.3.4, in one space
dimension. The profile is the Hopf–Lax formula (21) of Evans, §3.3.2(b), Theorem 4, with the
initial datum at time zero, and `hopfLaxEvolutionSpacetime_dynamic_programming` is the functional
identity (22) of Lemma 1 there.

The positive-time viscosity theorem only requires Lipschitz initial data.
The solution class also needs bounded initial data, since it asks that the image of every slab
`[0, T] × ℝ` be bounded.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Theorem 4, formula (21), and Lemma 1,
  equation (22); §10.1.1, definition of viscosity solution; §10.3.4, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HamiltonJacobi1D

noncomputable section

open PDE.Common

/-- The Hopf–Lax profile on closed forward spacetime, with the initial datum
inserted at time zero. -/
noncomputable def hopfLaxEvolutionSpacetime (H phi : ℝ → ℝ) : ℝ^2 → ℝ :=
  fun z ↦ HopfLax1D.hopfLaxEvolution H phi (z 0) (z 1)

/-- On positive time, the closed-time profile agrees with the usual Hopf–Lax
profile. -/
theorem hopfLaxEvolutionSpacetime_eq_hopfLaxSpacetime
    {H phi : ℝ → ℝ} {z : ℝ^2} (hz : z ∈ positiveTimeDomain) :
    hopfLaxEvolutionSpacetime H phi z = hopfLaxSpacetime H phi z := by
  have ht : z 0 ≠ 0 := ne_of_gt hz
  simp [hopfLaxEvolutionSpacetime, hopfLaxSpacetime, HopfLax1D.hopfLaxEvolution, ht]

/-- Pointwise order between initial data is preserved at every point of closed
forward spacetime. -/
theorem hopfLaxEvolutionSpacetime_le_of_initial_le {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {z : ℝ^2}
    (hz : 0 ≤ z 0) (hphiPsi : ∀ x, phi x ≤ psi x) :
    hopfLaxEvolutionSpacetime H phi z ≤ hopfLaxEvolutionSpacetime H psi z :=
  HopfLax1D.hopfLaxEvolution_mono_phi_of_lipschitz hFin hphi hz hphiPsi

/-- The closed-time Hopf–Lax evolution does not increase a pointwise uniform
distance bound between two initial data. -/
theorem dist_hopfLaxEvolutionSpacetime_le_of_initial_dist_le {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {C : ℝ}
    (hphiPsi : ∀ x, dist (phi x) (psi x) ≤ C) {z : ℝ^2} (hz : 0 ≤ z 0) :
    dist (hopfLaxEvolutionSpacetime H phi z) (hopfLaxEvolutionSpacetime H psi z) ≤ C :=
  HopfLax1D.dist_hopfLaxEvolution_le_of_lipschitz hFin hphi hz hphiPsi

/-- Restart the closed-time Hopf–Lax profile from any intermediate
nonnegative time. This is the dynamic-programming identity in spacetime
notation. -/
theorem hopfLaxEvolutionSpacetime_dynamic_programming {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {s : ℝ} {z : ℝ^2}
    (hs : 0 ≤ s) (hsz : s ≤ z 0) :
    hopfLaxEvolutionSpacetime H phi z = HopfLax1D.hopfLaxEvolution H
      (fun x ↦ hopfLaxEvolutionSpacetime H phi !₂[s, x]) (z 0 - s) (z 1) := by
  simpa [hopfLaxEvolutionSpacetime] using
    HopfLax1D.hopfLaxEvolution_dynamic_programming_of_lipschitz hFin hphi hs hsz (x := z 1)

/-- Pointwise order on one nonnegative time slice propagates to every later
point of the two canonical Hopf–Lax profiles. -/
theorem hopfLaxEvolutionSpacetime_le_of_le_at_time {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {Kphi Kpsi : NNReal} (hphi : LipschitzWith Kphi phi)
    (hpsi : LipschitzWith Kpsi psi) {s : ℝ} {z : ℝ^2} (hs : 0 ≤ s) (hsz : s ≤ z 0)
    (hcompare : ∀ x, hopfLaxEvolutionSpacetime H phi !₂[s, x] ≤
      hopfLaxEvolutionSpacetime H psi !₂[s, x]) :
    hopfLaxEvolutionSpacetime H phi z ≤ hopfLaxEvolutionSpacetime H psi z := by
  simpa [hopfLaxEvolutionSpacetime] using
    HopfLax1D.hopfLaxEvolution_le_hopfLaxEvolution_of_le_at_time hFin hphi hpsi hs hsz hcompare

/-- A pointwise uniform-distance bound on one nonnegative time slice
propagates unchanged to every later point of the canonical Hopf–Lax
profiles. -/
theorem dist_hopfLaxEvolutionSpacetime_le_of_dist_at_time {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {Kphi Kpsi : NNReal} (hphi : LipschitzWith Kphi phi)
    (hpsi : LipschitzWith Kpsi psi) {C s : ℝ} {z : ℝ^2} (hs : 0 ≤ s) (hsz : s ≤ z 0)
    (hbound : ∀ x, dist (hopfLaxEvolutionSpacetime H phi !₂[s, x])
      (hopfLaxEvolutionSpacetime H psi !₂[s, x]) ≤ C) :
    dist (hopfLaxEvolutionSpacetime H phi z) (hopfLaxEvolutionSpacetime H psi z) ≤ C := by
  simpa [hopfLaxEvolutionSpacetime] using
    HopfLax1D.dist_hopfLaxEvolution_le_of_dist_at_time hFin hphi hpsi hs hsz hbound

/-- A uniform-distance bound on the time slab `s ≤ t ≤ T` is equivalent to
the same bound on its initial slice.

This is a comparison theorem for the canonical Hopf–Lax semigroup. -/
theorem dist_hopfLaxEvolutionSpacetime_le_on_time_interval_iff {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {Kphi Kpsi : NNReal} (hphi : LipschitzWith Kphi phi)
    (hpsi : LipschitzWith Kpsi psi) {C s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∀ z ∈ {z : ℝ^2 | s ≤ z 0 ∧ z 0 ≤ T}, dist (hopfLaxEvolutionSpacetime H phi z)
      (hopfLaxEvolutionSpacetime H psi z) ≤ C) ↔ ∀ x, dist
      (hopfLaxEvolutionSpacetime H phi !₂[s, x]) (hopfLaxEvolutionSpacetime H psi !₂[s, x]) ≤ C :=
  ⟨fun hdist x ↦ hdist !₂[s, x] ⟨le_rfl, hsT⟩, fun hdist _ hz ↦
    dist_hopfLaxEvolutionSpacetime_le_of_dist_at_time hFin hphi hpsi hs hz.1 hdist⟩

/-- Equality on one nonnegative time slice determines both canonical
Hopf–Lax profiles at every later time. -/
theorem eqOn_hopfLaxEvolutionSpacetime_of_eq_on_time_slice {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {Kphi Kpsi : NNReal} (hphi : LipschitzWith Kphi phi)
    (hpsi : LipschitzWith Kpsi psi) {s : ℝ} (hs : 0 ≤ s)
    (hslice : ∀ x, hopfLaxEvolutionSpacetime H phi !₂[s, x] =
      hopfLaxEvolutionSpacetime H psi !₂[s, x]) :
    Set.EqOn (hopfLaxEvolutionSpacetime H phi) (hopfLaxEvolutionSpacetime H psi)
      {z : ℝ^2 | s ≤ z 0} :=
  fun _ hz ↦ le_antisymm
    (hopfLaxEvolutionSpacetime_le_of_le_at_time hFin hphi hpsi hs hz fun x ↦ (hslice x).le)
    (hopfLaxEvolutionSpacetime_le_of_le_at_time hFin hpsi hphi hs hz fun x ↦ (hslice x).ge)

/-- A uniform distance bound on a nonempty closed time slab is equivalent to
the same bound on the initial data.

The forward implication is the Hopf–Lax contraction estimate. The converse
uses the copy of the initial datum at time zero, which belongs to the slab
when `0 ≤ T`. Thus this statement concerns the canonical Hopf–Lax evolution,
not arbitrary viscosity solutions. -/
theorem dist_hopfLaxEvolutionSpacetime_le_on_closedTimeSlab_iff {H phi psi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {C T : ℝ}
    (hT : 0 ≤ T) :
    (∀ z ∈ closedTimeSlab T, dist (hopfLaxEvolutionSpacetime H phi z)
      (hopfLaxEvolutionSpacetime H psi z) ≤ C) ↔ ∀ x, dist (phi x) (psi x) ≤ C :=
  ⟨fun hdist x ↦ by simpa [hopfLaxEvolutionSpacetime] using hdist !₂[0, x] ⟨le_rfl, hT⟩,
    fun hdist z hz ↦ dist_hopfLaxEvolutionSpacetime_le_of_initial_dist_le hFin hphi hdist hz.1⟩

/-- The closed-time Hopf–Lax solution operator remembers its initial datum.

This injectivity comes from evaluating the profile at time zero; it makes no
claim that the positive-time Hopf–Lax operator is injective. -/
theorem hopfLaxEvolutionSpacetime_injective (H : ℝ → ℝ) :
    Function.Injective (hopfLaxEvolutionSpacetime H) :=
  fun phi psi hprofiles ↦ funext fun x ↦ by
    simpa [hopfLaxEvolutionSpacetime] using congrFun hprofiles !₂[0, x]

/-- Two canonical closed-time Hopf–Lax profiles agree exactly when their
initial data agree. -/
theorem hopfLaxEvolutionSpacetime_eq_iff {H phi psi : ℝ → ℝ} :
    hopfLaxEvolutionSpacetime H phi = hopfLaxEvolutionSpacetime H psi ↔ phi = psi :=
  (hopfLaxEvolutionSpacetime_injective H).eq_iff

/-- The closed-time Hopf–Lax profile is Lipschitz on every forward time slab.

The estimate is independent of the slab endpoint; only nonnegativity of the
two time coordinates enters the Hopf–Lax spacetime estimate. -/
theorem hopfLaxEvolutionSpacetime_lipschitzOnWith_closedTimeSlab {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) (T : ℝ) :
    LipschitzOnWith (Real.toNNReal ((K : ℝ) + HopfLax1D.timeLipschitzConstant H K))
      (hopfLaxEvolutionSpacetime H phi) (closedTimeSlab T) := by
  refine LipschitzOnWith.of_dist_le' fun p hp q hq ↦ ?_
  have hspace : |p 1 - q 1| ≤ dist p q := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p q (1 : Fin 2)
  have htime : |p 0 - q 0| ≤ dist p q := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p q (0 : Fin 2)
  have h := HopfLax1D.abs_sub_hopfLaxEvolution_le_lipschitz_spacetime (t := p 0) (s := q 0)
    (x := p 1) (y := q 1) hFin hphi hp.1 hq.1
  rw [Real.dist_eq]
  dsimp only [hopfLaxEvolutionSpacetime]
  linarith [mul_le_mul_of_nonneg_left hspace K.coe_nonneg,
    mul_le_mul_of_nonneg_left htime (HopfLax1D.timeLipschitzConstant_nonneg H K)]

/-- A uniform bound on the initial datum grows at most linearly on every
closed forward time slab. -/
theorem hopfLaxEvolutionSpacetime_image_closedTimeSlab_isBounded {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {C : ℝ}
    (hphiBound : ∀ x, |phi x| ≤ C) (T : ℝ) :
    Bornology.IsBounded (hopfLaxEvolutionSpacetime H phi '' closedTimeSlab T) := by
  refine (Metric.isBounded_of_abs_le (C + HopfLax1D.timeLipschitzConstant H K * T)).subset ?_
  rintro y ⟨z, hz, rfl⟩
  have hz0 : 0 ≤ z 0 := hz.1
  have hzT : z 0 ≤ T := hz.2
  change |HopfLax1D.hopfLaxEvolution H phi (z 0) (z 1)| ≤ _
  linarith [HopfLax1D.abs_hopfLaxEvolution_le_add_time hFin hphi hz0 hphiBound (x := z 1),
    mul_le_mul_of_nonneg_left hzT (HopfLax1D.timeLipschitzConstant_nonneg H K)]

/-- Bounded Lipschitz initial data produce a profile that is bounded and
uniformly continuous on every finite forward time slab. -/
theorem hopfLaxEvolutionSpacetime_isBoundedUniformContinuousOnSlabs {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) {K : NNReal} (hphi : LipschitzWith K phi) {C : ℝ}
    (hphiBound : ∀ x, |phi x| ≤ C) :
    HamiltonJacobi.IsBoundedUniformContinuousOnSlabs
      (hopfLaxEvolutionSpacetime H phi ∘ scalarSpaceTimeEquiv.symm) := by
  refine fun T _ ↦ ⟨?_, ?_⟩
  · rw [Set.image_comp, scalarSpaceTimeEquiv.image_symm_eq_preimage]
    exact hopfLaxEvolutionSpacetime_image_closedTimeSlab_isBounded hFin hphi hphiBound T
  · refine (hopfLaxEvolutionSpacetime_lipschitzOnWith_closedTimeSlab hFin hphi T
      ).uniformContinuousOn.comp
      scalarSpaceTimeEquiv.symm.toContinuousLinearMap.uniformContinuous.uniformContinuousOn
      fun z hz ↦ ?_
    simpa [closedTimeSlab, HamiltonJacobi.closedTimeSlab] using hz

/-- Under the standard convexity hypotheses, the closed-time Hopf–Lax profile
satisfies the Hamilton–Jacobi viscosity equation on positive time. -/
theorem hopfLaxEvolutionSpacetime_isSpatialDifferentiableTestSolution {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hphi : LipschitzWith K phi) :
    IsSpatialDifferentiableTestSolution
      (fun p _x ↦ H p) positiveTimeDomain (hopfLaxEvolutionSpacetime H phi) :=
  IsAmbientDifferentiableTestSolution.toSpatial isOpen_positiveTimeDomain
    ((isAmbientDifferentiableTestSolution_congr_of_eqOn isOpen_positiveTimeDomain
      fun _ hz ↦ hopfLaxEvolutionSpacetime_eq_hopfLaxSpacetime hz).2
      (hopfLaxSpacetime_isAmbientDifferentiableTestSolution_of_lipschitz_convex hFin hconv hH hphi))

/-- Bounded Lipschitz data yield a viscosity solution of the complete
Hamilton–Jacobi initial-value problem, as in Evans, §10.3.4, Theorem 3.

The profile need not stay uniformly bounded for all time. The quantitative
Hopf–Lax regularity estimate gives the finite-slab boundedness required by the
solution predicate, with at most linear growth in the slab endpoint. -/
theorem hopfLaxEvolutionSpacetime_isDifferentiableTestInitialSolution {H phi : ℝ → ℝ}
    (hFin : HopfLax1D.LegendreFinite H) (hconv : ConvexOn ℝ (Set.univ : Set ℝ) H)
    (hH : Differentiable ℝ H) {K : NNReal} (hphi : LipschitzWith K phi) {C : ℝ}
    (hphiBound : ∀ x, |phi x| ≤ C) :
    IsDifferentiableTestInitialSolution (fun p _x ↦ H p) phi (hopfLaxEvolutionSpacetime H phi) :=
  ⟨hopfLaxEvolutionSpacetime_isBoundedUniformContinuousOnSlabs hFin hphi hphiBound,
    hopfLaxEvolutionSpacetime_isSpatialDifferentiableTestSolution hFin hconv hH hphi,
    fun x ↦ by simp [hopfLaxEvolutionSpacetime]⟩

end

end HamiltonJacobi1D
