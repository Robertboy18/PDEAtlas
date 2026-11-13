/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.InitialValue
public import PDE.Examples.Hyperbolic.ConservationLaw.System.Riemann

/-!
# Coupled rarefactions on arbitrary prescribed segments

The first characteristic family of the flux `(a²/2, (a+1)b)` has the rarefaction curve
`(s, exp(-s))`. For all states `A < B` on this curve,
`exists_continuous_rarefaction_of_integralCurve` gives the fan `(ξ, exp(-ξ))` with
`ξ = max A (min B (x/t))` (`exists_coupled_rarefaction`), with no smallness condition.
Rescaling the eigenvector by any `d ≠ 0` gives the same fan
(`exists_coupled_segment_rarefaction`). The flux and its Jacobian are those of
`PDE.Examples.Hyperbolic.ConservationLaw.System.Riemann`.
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.Rarefaction

open PDE.Common PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.System
open PDE.Hyperbolic.ConservationLaw.Scalar
open PDE.Examples.Hyperbolic.ConservationLaw.System.Riemann
open MeasureTheory Set
open scoped ENNReal

/-- A constant rescaling of the first characteristic eigenfield. -/
def coupledField (d : ℝ) (hd : d ≠ 0) : CharacteristicField coupledFlux where
  flux_differentiable := contDiff_coupledFlux.differentiable (by simp)
  speed q := q 0
  rightEigenvector q := d • !₂[1, -q 1]
  eigenvector q := by
    constructor
    · apply Module.End.mem_eigenspace_iff.mpr
      rw [map_smul]
      change d • fderiv ℝ coupledFlux q !₂[1, -q 1] =
        q 0 • d • (!₂[1, -q 1] : ℝ^2)
      have he : fderiv ℝ coupledFlux q !₂[1, -q 1] =
          q 0 • (!₂[1, -q 1] : ℝ^2) := by
        rw [fderiv_coupledFlux]
        ext i
        fin_cases i <;> simp
        ring
      rw [he, smul_comm]
    · apply smul_ne_zero hd
      intro h
      have h0 := congrArg (fun z : ℝ^2 ↦ z 0) h
      norm_num at h0

/-- The speed of the rescaled field is the first characteristic speed. -/
theorem coupledField_speed (d : ℝ) (hd : d ≠ 0) :
    (coupledField d hd).speed = characteristicSpeed coupledFlux 0 := by
  rw [characteristicSpeed_coupledFlux]
  funext q
  simp [coupledField]

/-- The rarefaction curve `s ↦ (d s, exp(-d s))`. -/
def coupledCurve (d : ℝ) (s : ℝ) : ℝ^2 := !₂[d * s, Real.exp (-(d * s))]

/-- The curve is a global integral curve for each nonzero rescaling. -/
theorem isIntegralCurve_coupledCurve (d : ℝ) (hd : d ≠ 0) :
    IsIntegralCurve (coupledCurve d) (coupledField d hd).vectorField := by
  intro s
  exact (hasDerivAt_coupled_rarefaction (d * s)).scomp s
    (by simpa using (hasDerivAt_id s).const_mul d)

/-- For `d a < d b`, the fan between `coupledCurve d a` and `coupledCurve d b` is an
explicit bounded continuous weak solution with strong initial trace. -/
theorem exists_coupled_segment_rarefaction
    (d : ℝ) (a b : ℝ) (hab : d * a < d * b) :
    ∃ K : ℝ, ∃ u : ℝ^2 → ℝ^2,
      IsWeakInitialValueSolution coupledFlux
        (riemannData (coupledCurve d a) (coupledCurve d b)) u ∧
      HasInitialTraceLocallyL1 u (riemannData (coupledCurve d a) (coupledCurve d b)) ∧
      ContinuousOn u forwardHalfSpace ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      Set.range (fun x : ℝ ↦ u !₂[1, x]) = coupledCurve d '' uIcc a b ∧
      (∀ p : ℝ^2, 0 < p 0 →
        let ξ := max (d * a) (min (d * b) (similarityVariable p))
        u p = !₂[ξ, Real.exp (-ξ)]) := by
  have hd : d ≠ 0 := by aesop
  let C := coupledField d hd
  have hv := (isIntegralCurve_coupledCurve d hd).isIntegralCurveOn (Set.univ : Set ℝ)
  obtain ⟨l, r, K, u, hsegment, _hclosure, _hprofile, _hinverse,
    hu, ht, _hm, hc, hL, hbound, _hray, hformula, _hsimple,
    hrange, _hphase, _hoff, _hae, _htests⟩ :=
    exists_continuous_rarefaction_of_integralCurve 0
      (contDiff_coupledFlux.of_le (by simp)) isStrictlyHyperbolicAt_coupledFlux
      isGenuinelyNonlinearFamily_coupledFlux_zero C (coupledField_speed d hd)
      isOpen_univ ordConnected_univ hv (mem_univ a) (mem_univ b) hab
  refine ⟨K, u, hu, ht, hc, hL, hbound, hrange, ?_⟩
  have hvD := (isIntegralCurve_coupledCurve d hd).isIntegralCurveOn (Ioo l r)
  have hC := (isGenuinelyNonlinearFamily_iff isStrictlyHyperbolicAt_coupledFlux 0
    C (coupledField_speed d hd)).mp isGenuinelyNonlinearFamily_coupledFlux_zero
  have haD := hsegment (left_mem_uIcc : a ∈ uIcc a b)
  have hbD := hsegment (right_mem_uIcc : b ∈ uIcc a b)
  intro p hp
  rw [hformula p hp]
  let ξ := max (d * a) (min (d * b) (similarityVariable p))
  have hξ : ξ ∈ (C.speed ∘ coupledCurve d) '' Ioo l r := by
    apply image_mono hsegment
    rw [C.speed_image_uIcc hvD hC haD hbD hab.le]
    exact ⟨le_max_left _ _, max_le hab.le (min_le_left _ _)⟩
  have heq := (C.speedInverse_mem_and_eq hξ).2
  change d * C.speedInverse (coupledCurve d) l r ξ = ξ at heq
  change (!₂[d * C.speedInverse (coupledCurve d) l r ξ,
    Real.exp (-(d * C.speedInverse (coupledCurve d) l r ξ))] : ℝ^2) =
      !₂[ξ, Real.exp (-ξ)]
  rw [heq]

/-- For all `A < B`, the fan from `(A, exp(-A))` to `(B, exp(-B))` is `(ξ, exp(-ξ))` with
`ξ = max A (min B (x/t))`. -/
theorem exists_coupled_rarefaction (A B : ℝ) (hAB : A < B) :
    ∃ K : ℝ, ∃ u : ℝ^2 → ℝ^2,
      IsWeakInitialValueSolution coupledFlux
        (riemannData !₂[A, Real.exp (-A)] !₂[B, Real.exp (-B)]) u ∧
      HasInitialTraceLocallyL1 u
        (riemannData !₂[A, Real.exp (-A)] !₂[B, Real.exp (-B)]) ∧
      ContinuousOn u forwardHalfSpace ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      Set.range (fun x : ℝ ↦ u !₂[1, x]) =
        (fun s ↦ (!₂[s, Real.exp (-s)] : ℝ^2)) '' uIcc A B ∧
      (∀ p : ℝ^2, 0 < p 0 →
        let ξ := max A (min B (similarityVariable p))
        u p = !₂[ξ, Real.exp (-ξ)]) := by
  have hv : coupledCurve 1 = fun s ↦ (!₂[s, Real.exp (-s)] : ℝ^2) := by
    funext s
    simp [coupledCurve]
  simpa only [hv, one_mul] using
    exists_coupled_segment_rarefaction 1 A B (by simpa using hAB)

end PDE.Examples.Hyperbolic.ConservationLaw.System.Rarefaction
