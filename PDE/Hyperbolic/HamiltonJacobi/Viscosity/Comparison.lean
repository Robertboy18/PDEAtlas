/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.Viscosity.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Doubled-variable contact inequalities for viscosity comparison

To compare a subsolution `u` with a supersolution `v`, consider a local maximum
of `u(z) - v(w) - Ψ(z, w)`. Fixing `w` gives a test touching `u` from above;
fixing `z` gives a test touching `v` from below. Neither solution needs to be
differentiable. Applying their viscosity inequalities bounds the sum of the
two time derivatives of `Ψ` by a difference of Hamiltonians.

For a penalty `Ψ(z, w) = P(z - w) + c * zₜ`, the spatial test derivatives
agree, while the time derivatives sum to `c`. Thus a positive `c` rules out
an interior local maximum when both equations have the same autonomous
Hamiltonian. The argument works for every penalty locally `C¹` at `z - w`,
including the quadratic penalties used in doubling variables.

This is the local contact step of comparison for arbitrary viscosity
subsolutions and supersolutions, independently of the Hopf–Lax formula. It is step 5 and the
subtraction (14) of step 6 in Evans's proof of Theorem 1 in §10.2, where the time penalty
`λ(t+s)` of (5) plays the role of `c * zₜ`.
Initial-value comparison additionally needs maximum attainment, exclusion
of initial contact, and control at spatial infinity. Those steps are proved
in `LocalizedMaximum` and `FiniteHorizon.Autonomous`. The contact argument works in a real
Hilbert space, without finite dimensionality. Only local `C¹` regularity of the
touching tests is used.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.2, proof of Theorem 1, equations (5) and (12)-(14).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

namespace HamiltonJacobi

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open Set
open scoped Topology

/-- A joint local maximum gives the two touching tests used in viscosity
comparison, and hence an inequality between their time derivatives and
Hamiltonians.

The two equations may have different, position-dependent Hamiltonians.
Only the two slices of the penalty need be `C¹` near their contact points. -/
theorem IsSpatialViscositySubsolution.doubling_inequality {H K : E → E → ℝ} {U V : Set (E × ℝ)}
    {u v : (E × ℝ) → ℝ} {z w : (E × ℝ)} (hu : IsSpatialViscositySubsolution H U u)
    (hv : IsSpatialViscositySupersolution K V v) (hz : z ∈ U) (hw : w ∈ V)
    {Ψ : (E × ℝ) → (E × ℝ) → ℝ} (hleft : ContDiffAt ℝ 1 (fun x ↦ Ψ x w) z)
    (hright : ContDiffAt ℝ 1 (Ψ z) w)
    (hmax : IsLocalMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 - Ψ q.1 q.2) (U ×ˢ V) (z, w)) :
    fderiv ℝ (fun x ↦ Ψ x w) z (0, 1) + fderiv ℝ (Ψ z) w (0, 1) ≤
      K (-∇ (fun x ↦ Ψ z (x, w.2)) w.1) w.1 - H (∇ (fun x ↦ Ψ (x, z.2) w) z.1) z.1 := by
  have hleftMax : IsLocalMaxOn (fun x ↦ u x - Ψ x w) U z := by
    have hslice := hmax.comp_continuousOn (g := fun x : (E × ℝ) ↦ (x, w))
      (fun x hx ↦ show (x, w) ∈ U ×ˢ V from ⟨hx, hw⟩)
      (continuous_id.prodMk continuous_const).continuousOn hz
    change ∀ᶠ x in 𝓝[U] z, u x - Ψ x w ≤ u z - Ψ z w
    filter_upwards [hslice] with x hx
    dsimp at hx
    linarith
  have hrightMin : IsLocalMinOn (fun x ↦ v x - -Ψ z x) V w := by
    have hslice := hmax.comp_continuousOn (g := fun x : (E × ℝ) ↦ (z, x))
      (fun x hx ↦ show (z, x) ∈ U ×ˢ V from ⟨hz, hx⟩)
      (continuous_const.prodMk continuous_id).continuousOn hw
    change ∀ᶠ x in 𝓝[V] w, v w - -Ψ z w ≤ v x - -Ψ z x
    filter_upwards [hslice] with x hx
    dsimp at hx
    linarith
  have hsub := hu.2 z hz (fun x ↦ Ψ x w) hleft hleftMax
  have hsuper := hv.2 w hw (fun x ↦ -Ψ z x) hright.neg hrightMin
  have hrightDiff := hright.differentiableAt_one
  have hgrad : ∇ (fun x ↦ -Ψ z (x, w.2)) w.1 =
      -∇ (fun x ↦ Ψ z (x, w.2)) w.1 := by
    change ∇ (fun x ↦ (-Ψ z) (x, w.2)) w.1 = -∇ (fun x ↦ Ψ z (x, w.2)) w.1
    rw [gradient_spaceSlice_eq hrightDiff.neg, gradient_spaceSlice_eq hrightDiff]
    simp only [hrightDiff.hasFDerivAt.neg.fderiv, ContinuousLinearMap.neg_comp, map_neg]
  change 0 ≤ fderiv ℝ (-Ψ z) w (0, 1) + K (∇ (fun x ↦ -Ψ z (x, w.2)) w.1) w.1 at hsuper
  rw [hrightDiff.hasFDerivAt.neg.fderiv, neg_apply, hgrad] at hsuper
  linarith

/-- A penalty depending on the difference of the contact points gives the
same spatial momentum in both equations. A linear time penalty leaves its
coefficient on the left side of the contact inequality. -/
theorem IsSpatialViscositySubsolution.le_hamiltonian_sub_of_isLocalMaxOn_sub_penalty
    {H K : E → E → ℝ} {U V : Set (E × ℝ)} {u v P : E × ℝ → ℝ} {z w : E × ℝ} {c : ℝ}
    (hu : IsSpatialViscositySubsolution H U u) (hv : IsSpatialViscositySupersolution K V v)
    (hz : z ∈ U) (hw : w ∈ V) (hP : ContDiffAt ℝ 1 P (z - w))
    (hmax : IsLocalMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 - (P (q.1 - q.2) + c * q.1.2))
      (U ×ˢ V) (z, w)) :
    c ≤ K (∇ (fun x ↦ P (x, z.2 - w.2)) (z.1 - w.1)) w.1 -
      H (∇ (fun x ↦ P (x, z.2 - w.2)) (z.1 - w.1)) z.1 := by
  let L := fderiv ℝ P (z - w)
  have hPdiff := hP.differentiableAt_one
  have hleftP : HasFDerivAt (fun x ↦ P (x - w)) L z :=
    (hasFDerivAt_comp_sub w).mpr hPdiff.hasFDerivAt
  have hrightP : HasFDerivAt (fun x ↦ P (z - x)) (-L) w := by
    convert! hPdiff.hasFDerivAt.comp w ((hasFDerivAt_id w).const_sub z) using 1
    simp only [L, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]
  have htime : HasFDerivAt (fun x : E × ℝ ↦ c * x.2) (c • ContinuousLinearMap.snd ℝ E ℝ) z :=
    (c • ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hleft := hleftP.add htime
  have hright := hrightP.add_const (c * z.2)
  have hleftC1 : ContDiffAt ℝ 1 (fun x ↦ P (x - w) + c * x.2) z :=
    (hP.comp z (contDiffAt_id.sub contDiffAt_const)).add (contDiffAt_const.mul contDiffAt_snd)
  have hrightC1 : ContDiffAt ℝ 1 (fun x ↦ P (z - x) + c * z.2) w :=
    (hP.comp w (contDiffAt_const.sub contDiffAt_id)).add contDiffAt_const
  have hlt : fderiv ℝ (fun x ↦ P (x - w) + c * x.2) z (0, 1) =
      L (0, 1) + c := by
    change fderiv ℝ ((fun x : E × ℝ ↦ P (x - w)) + fun x ↦ c * x.2) z (0, 1) = L (0, 1) + c
    simp [hleft.fderiv]
  have hrt : fderiv ℝ (fun x ↦ P (z - x) + c * z.2) w (0, 1) =
      -L (0, 1) := by
    simp [hright.fderiv]
  have hlx : ∇ (fun x ↦ P ((x, z.2) - w) + c * z.2) z.1 =
      ∇ (fun x ↦ P (x, z.2 - w.2)) (z.1 - w.1) := by
    change ∇ (fun x ↦ ((fun y : E × ℝ ↦ P (y - w)) + fun y : E × ℝ ↦ c * y.2) (x, z.2)) z.1 =
        ∇ (fun x ↦ P (x, (z - w).2)) (z - w).1
    rw [gradient_spaceSlice_eq hleft.differentiableAt, gradient_spaceSlice_eq hPdiff]
    congr 1
    ext x
    simp [hleft.fderiv, L]
  have hrx : ∇ (fun x ↦ P (z - (x, w.2)) + c * z.2) w.1 =
      -∇ (fun x ↦ P (x, z.2 - w.2)) (z.1 - w.1) := by
    change ∇ (fun x ↦ P (z - (x, w.2)) + c * z.2) w.1 = -∇ (fun x ↦ P (x, (z - w).2)) (z - w).1
    rw [gradient_spaceSlice_eq hright.differentiableAt, gradient_spaceSlice_eq hPdiff, ← map_neg]
    congr 1
    ext x
    simp [hright.fderiv, L]
  have h := hu.doubling_inequality hv hz hw (Ψ := fun x y ↦ P (x - y) + c * x.2)
    hleftC1 hrightC1 hmax
  rw [hlt, hrt, hlx, hrx, neg_neg] at h
  linarith only [h]

/-- A positive linear time penalty rules out an interior doubled maximum
for the same autonomous Hamiltonian, with no regularity assumption on `H`. -/
theorem IsSpatialViscositySubsolution.not_isLocalMaxOn_sub_penalty {H : E → ℝ} {U V : Set (E × ℝ)}
    {u v P : E × ℝ → ℝ} {z w : E × ℝ} {c : ℝ}
    (hu : IsSpatialViscositySubsolution (fun p _ ↦ H p) U u)
    (hv : IsSpatialViscositySupersolution (fun p _ ↦ H p) V v) (hz : z ∈ U) (hw : w ∈ V)
    (hP : ContDiffAt ℝ 1 P (z - w)) (hc : 0 < c) :
    ¬IsLocalMaxOn (fun q : (E × ℝ) × (E × ℝ) ↦ u q.1 - v q.2 - (P (q.1 - q.2) + c * q.1.2)) (U ×ˢ V)
      (z, w) := by
  intro hmax
  have h := hu.le_hamiltonian_sub_of_isLocalMaxOn_sub_penalty hv hz hw hP hmax
  exact hc.not_ge (by simpa only [sub_self] using h)

end

end HamiltonJacobi
