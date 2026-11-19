/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannInvariant
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Diagonal form of the one-dimensional p-system

For the p-system

`vₜ - wₓ = 0`, `wₜ - p'(v)vₓ = 0`,

write `c(v) = √p'(v)` and let `A' = c`. The Riemann coordinates

`R₀ = w - A(v)`, `R₁ = w + A(v)`

satisfy the diagonal equations

`(R₀)ₜ + c(v)(R₀)ₓ = 0`, `(R₁)ₜ - c(v)(R₁)ₓ = 0`.

The families appear exchanged:
`R₀` is constant along the zero-family state-space curves, so its spacetime
transport speed is the other eigenvalue `c`; similarly, `R₁` travels with
speed `-c`. We prove the pointwise chain rule, extract the two
scalar p-system equations from the quasilinear residual, and prove that the
two diagonal transport laws are equivalent to the original system wherever
`p' > 0`.

The coordinates are the Riemann invariants of Evans, §11.3.1, for the p-system of Example 1 in
§11.1, and the diagonal equations are (6) of Theorem 1 there, in which each invariant is
transported with the eigenvalue of the other family. The constancy along characteristics is
Remark (i), (7)-(8). Evans proves only that solutions satisfy (6); the converse for `p' > 0` is
ours. His worked example in §11.3.1 is barotropic gas dynamics, (12)-(26), not the p-system.

## Main results

* `partialDeriv_riemannInvariant_comp`: the chain rule for `R_k ∘ u`.
* `quasilinearResidual_eq_zero_iff_strain_velocity_equations`: the vector
  quasilinear residual vanishes exactly when the two scalar p-system equations
  hold.
* `riemannInvariant_transport`, `riemannInvariant_zero_transport`,
  `riemannInvariant_one_transport`: the diagonal transport equations at points
  where `p' ≥ 0`.
* `quasilinearResidual_eq_zero_iff_riemannInvariant_transport`: for `p' > 0`,
  the system is equivalent to the pair of transport equations.
* `riemannInvariant_eq_on_characteristic`: a Riemann invariant of a classical
  solution is constant along the corresponding spacetime characteristic.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1, Example 1, equations (6)-(7); §11.3.1, definition
  of Riemann invariants, Theorem 1 and Remark (i), equations (2)-(8).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

/-- Coordinate chain rule for a p-system Riemann invariant composed with a
differentiable spacetime state. -/
theorem partialDeriv_riemannInvariant_comp {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (base : ℝ) (k : Fin 2) {u : ℝ^2 → ℝ^2} {p : ℝ^2} (hu : DifferentiableAt ℝ u p) (i : Fin 2) :
    (∂[i] (riemannInvariant stress base k ∘ u)) p = if k = 0 then ((∂[i] u) p) 1 -
      soundSpeed stress (u p 0) * ((∂[i] u) p) 0 else ((∂[i] u) p) 1 + soundSpeed stress (u p 0) *
      ((∂[i] u) p) 0 := by
  unfold partialDeriv
  rw [fderiv_comp p ((differentiable_riemannInvariant hstress base k) (u p)) hu,
    ContinuousLinearMap.comp_apply, fderiv_riemannInvariant_apply hstress]

/-- The p-system quasilinear residual vanishes exactly when its strain and
velocity equations hold:

`vₜ - wₓ = 0`, `wₜ - p'(v)vₓ = 0`. -/
theorem quasilinearResidual_eq_zero_iff_strain_velocity_equations {stress : ℝ → ℝ} {u : ℝ^2 → ℝ^2}
    {p : ℝ^2} (hstress : DifferentiableAt ℝ stress (u p 0)) :
    quasilinearResidual (flux stress) u p = 0 ↔ ((∂[0] u) p) 0 - ((∂[1] u) p) 1 = 0 ∧
      ((∂[0] u) p) 1 - deriv stress (u p 0) * ((∂[1] u) p) 0 = 0 := by
  constructor
  · intro hpde
    constructor
    · have hcomponent := congrArg (fun state : ℝ^2 ↦ state 0) hpde
      rw [quasilinearResidual, fderiv_flux_apply hstress] at hcomponent
      simpa [sub_eq_add_neg] using hcomponent
    · have hcomponent := congrArg (fun state : ℝ^2 ↦ state 1) hpde
      rw [quasilinearResidual, fderiv_flux_apply hstress] at hcomponent
      simpa [sub_eq_add_neg] using hcomponent
  · rintro ⟨hstrain, hvelocity⟩
    rw [quasilinearResidual, fderiv_flux_apply hstress]
    ext i
    fin_cases i
    · simpa [sub_eq_add_neg] using hstrain
    · simpa [sub_eq_add_neg] using hvelocity

/-- Unified diagonal transport equation for either p-system Riemann
invariant. The transport speed is the negative of the corresponding
state-space characteristic speed. -/
theorem riemannInvariant_transport {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    (k : Fin 2) {u : ℝ^2 → ℝ^2} {p : ℝ^2} (hnonnegative : 0 ≤ deriv stress (u p 0))
    (hu : DifferentiableAt ℝ u p) (hpde : quasilinearResidual (flux stress) u p = 0) :
    (∂[0] (riemannInvariant stress base k ∘ u)) p - characteristicSpeed (soundSpeed stress (u p 0))
      k * (∂[1] (riemannInvariant stress base k ∘ u)) p = 0 := by
  obtain ⟨hstrain, hvelocity⟩ := (quasilinearResidual_eq_zero_iff_strain_velocity_equations
      (hstress.differentiable one_ne_zero (u p 0))).mp hpde
  have hstrainEq : ((∂[0] u) p) 0 = ((∂[1] u) p) 1 := sub_eq_zero.mp hstrain
  have hvelocityEq : ((∂[0] u) p) 1 = deriv stress (u p 0) * ((∂[1] u) p) 0 :=
    sub_eq_zero.mp hvelocity
  have hsoundSq : soundSpeed stress (u p 0) ^ 2 = deriv stress (u p 0) := Real.sq_sqrt hnonnegative
  by_cases hk : k = 0
  · subst k
    rw [partialDeriv_riemannInvariant_comp hstress base 0 hu,
      partialDeriv_riemannInvariant_comp hstress base 0 hu]
    simp only [ite_eq_left, characteristicSpeed]
    rw [hstrainEq, hvelocityEq, ← hsoundSq]
    ring
  · have hkone : k = 1 := Fin.eq_one_of_ne_zero k hk
    subst k
    rw [partialDeriv_riemannInvariant_comp hstress base 1 hu,
      partialDeriv_riemannInvariant_comp hstress base 1 hu]
    norm_num [characteristicSpeed]
    rw [hstrainEq, hvelocityEq, ← hsoundSq]
    ring

/-- The zero-family Riemann invariant obeys transport with speed `c(v)`. -/
theorem riemannInvariant_zero_transport {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    {u : ℝ^2 → ℝ^2} {p : ℝ^2} (hnonnegative : 0 ≤ deriv stress (u p 0))
    (hu : DifferentiableAt ℝ u p) (hpde : quasilinearResidual (flux stress) u p = 0) :
    (∂[0] (riemannInvariant stress base 0 ∘ u)) p + soundSpeed stress (u p 0) *
      (∂[1] (riemannInvariant stress base 0 ∘ u)) p = 0 := by
  simpa [characteristicSpeed] using riemannInvariant_transport hstress base 0 hnonnegative hu hpde

/-- The one-family Riemann invariant obeys transport with speed `-c(v)`. -/
theorem riemannInvariant_one_transport {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    {u : ℝ^2 → ℝ^2} {p : ℝ^2} (hnonnegative : 0 ≤ deriv stress (u p 0))
    (hu : DifferentiableAt ℝ u p) (hpde : quasilinearResidual (flux stress) u p = 0) :
    (∂[0] (riemannInvariant stress base 1 ∘ u)) p - soundSpeed stress (u p 0) *
      (∂[1] (riemannInvariant stress base 1 ∘ u)) p = 0 := by
  simpa [characteristicSpeed] using riemannInvariant_transport hstress base 1 hnonnegative hu hpde

/-- In the strictly hyperbolic regime, the two Riemann-invariant transport
equations reconstruct the p-system quasilinear equation. Strict positivity
is needed to cancel the sound speed when recovering `vₜ - wₓ = 0`. -/
theorem quasilinearResidual_eq_zero_of_riemannInvariant_transport {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (base : ℝ) {u : ℝ^2 → ℝ^2} {p : ℝ^2}
    (hpositive : 0 < deriv stress (u p 0)) (hu : DifferentiableAt ℝ u p)
    (htransport : ∀ k : Fin 2, (∂[0] (riemannInvariant stress base k ∘ u)) p - characteristicSpeed
      (soundSpeed stress (u p 0)) k * (∂[1] (riemannInvariant stress base k ∘ u)) p = 0) :
    quasilinearResidual (flux stress) u p = 0 := by
  have hzero : (∂[0] (riemannInvariant stress base 0 ∘ u)) p + soundSpeed stress (u p 0) *
            (∂[1] (riemannInvariant stress base 0 ∘ u)) p =
        0 := by
    simpa [characteristicSpeed] using htransport 0
  have hone : (∂[0] (riemannInvariant stress base 1 ∘ u)) p - soundSpeed stress (u p 0) *
            (∂[1] (riemannInvariant stress base 1 ∘ u)) p =
        0 := by
    simpa [characteristicSpeed] using htransport 1
  rw [partialDeriv_riemannInvariant_comp hstress base 0 hu,
    partialDeriv_riemannInvariant_comp hstress base 0 hu] at hzero
  simp only [ite_eq_left] at hzero
  rw [partialDeriv_riemannInvariant_comp hstress base 1 hu,
    partialDeriv_riemannInvariant_comp hstress base 1 hu] at hone
  norm_num at hone
  have hsoundPos : 0 < soundSpeed stress (u p 0) := soundSpeed_pos hpositive
  have hsoundSq : soundSpeed stress (u p 0) ^ 2 = deriv stress (u p 0) := Real.sq_sqrt hpositive.le
  -- Subtracting the diagonal equations isolates `c(v) * (vₜ - wₓ)`.
  have hscaledStrain : soundSpeed stress (u p 0) * (((∂[0] u) p) 0 - ((∂[1] u) p) 1) = 0 := by
    nlinarith [hzero, hone]
  have hstrain : ((∂[0] u) p) 0 - ((∂[1] u) p) 1 = 0 :=
    (mul_eq_zero.mp hscaledStrain).resolve_left (ne_of_gt hsoundPos)
  -- Adding the equations gives `wₜ - c(v)^2 vₓ = 0`, and `c(v)^2 = p'(v)`.
  have hvelocitySound : ((∂[0] u) p) 1 - soundSpeed stress (u p 0) ^ 2 * ((∂[1] u) p) 0 = 0 := by
    nlinarith [hzero, hone]
  have hvelocity : ((∂[0] u) p) 1 - deriv stress (u p 0) * ((∂[1] u) p) 0 = 0 := by
    simpa only [hsoundSq] using hvelocitySound
  exact (quasilinearResidual_eq_zero_iff_strain_velocity_equations
      (hstress.differentiable one_ne_zero (u p 0))).mpr ⟨hstrain, hvelocity⟩

/-- Pointwise diagonalization of the strictly hyperbolic p-system: the
vector quasilinear equation is equivalent to the transport equation for
each Riemann invariant. -/
theorem quasilinearResidual_eq_zero_iff_riemannInvariant_transport {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (base : ℝ) {u : ℝ^2 → ℝ^2} {p : ℝ^2}
    (hpositive : 0 < deriv stress (u p 0)) (hu : DifferentiableAt ℝ u p) :
    quasilinearResidual (flux stress) u p = 0 ↔ ∀ k : Fin 2,
      (∂[0] (riemannInvariant stress base k ∘ u)) p - characteristicSpeed
      (soundSpeed stress (u p 0)) k * (∂[1] (riemannInvariant stress base k ∘ u)) p = 0 := by
  constructor
  · exact fun hpde k ↦ riemannInvariant_transport hstress base k hpositive.le hu hpde
  · exact quasilinearResidual_eq_zero_of_riemannInvariant_transport hstress base hpositive hu

/-- A classical p-system solution satisfies the diagonal transport equation
at every point where the stress derivative is nonnegative. -/
theorem riemannInvariant_transport_of_isClassicalSolutionOn {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (base : ℝ) (k : Fin 2) {U : Set ℝ^2} {u : ℝ^2 → ℝ^2}
    (hsolution : IsClassicalSolutionOn (flux stress) U u) {p : ℝ^2} (hp : p ∈ U)
    (hnonnegative : 0 ≤ deriv stress (u p 0)) :
    (∂[0] (riemannInvariant stress base k ∘ u)) p - characteristicSpeed (soundSpeed stress (u p 0))
      k * (∂[1] (riemannInvariant stress base k ∘ u)) p = 0 :=
  riemannInvariant_transport hstress base k hnonnegative (hsolution.differentiableAt p hp)
    (hsolution.quasilinearResidual_eq_zero hp)

/-- Along a spacetime characteristic with tangent `(1, -λₖ)`, the `k`th
Riemann invariant has zero derivative. The sign agrees with the diagonal
equation `Rₜ - λₖ Rₓ = 0`. -/
theorem hasDerivAt_riemannInvariant_along_characteristic {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (base : ℝ) (k : Fin 2) {U : Set ℝ^2} {u : ℝ^2 → ℝ^2}
    (hsolution : IsClassicalSolutionOn (flux stress) U u) {curve : ℝ → ℝ^2} {t : ℝ}
    (hcurve : HasDerivAt curve ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2) -
      characteristicSpeed (soundSpeed stress (u (curve t) 0)) k •
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) t)
    (ht : curve t ∈ U) (hnonnegative : 0 ≤ deriv stress (u (curve t) 0)) :
    HasDerivAt (fun s ↦ riemannInvariant stress base k (u (curve s))) 0 t := by
  let invariant : ℝ^2 → ℝ := riemannInvariant stress base k ∘ u
  have hinvariant : DifferentiableAt ℝ invariant (curve t) :=
    (differentiable_riemannInvariant hstress base k (u (curve t))).comp (curve t)
        (hsolution.differentiableAt (curve t) ht)
  have hvalue : fderiv ℝ invariant (curve t) ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2) -
            characteristicSpeed (soundSpeed stress (u (curve t) 0)) k •
              EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) =
        0 := by
    rw [map_sub, map_smul]
    simpa only [partialDeriv, smul_eq_mul] using riemannInvariant_transport_of_isClassicalSolutionOn
        hstress base k hsolution ht hnonnegative
  have halongDifferentiable : DifferentiableAt ℝ (invariant ∘ curve) t :=
    hinvariant.comp t hcurve.differentiableAt
  have halongDeriv : deriv (invariant ∘ curve) t = 0 := by
    rw [fderiv_comp_deriv t hinvariant hcurve.differentiableAt, hcurve.deriv]
    exact hvalue
  change HasDerivAt (invariant ∘ curve) 0 t
  rw [← halongDeriv]
  exact halongDifferentiable.hasDerivAt

/-- A p-system Riemann invariant is constant along a characteristic on any
open preconnected time interval on which the classical solution and the
nonnegative stress-derivative condition are available. -/
theorem riemannInvariant_eq_on_characteristic {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (base : ℝ) (k : Fin 2) {U : Set ℝ^2} {u : ℝ^2 → ℝ^2}
    (hsolution : IsClassicalSolutionOn (flux stress) U u) {I : Set ℝ} (hIopen : IsOpen I)
    (hIpreconnected : IsPreconnected I) {curve : ℝ → ℝ^2} (hcurveMapsTo : Set.MapsTo curve I U)
    (hcurve : ∀ t ∈ I, HasDerivAt curve ((EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : ℝ^2) -
      characteristicSpeed (soundSpeed stress (u (curve t) 0)) k •
      EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) t)
    (hnonnegative : ∀ t ∈ I, 0 ≤ deriv stress (u (curve t) 0)) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    riemannInvariant stress base k (u (curve s)) =
      riemannInvariant stress base k (u (curve t)) := by
  let along : ℝ → ℝ := fun r ↦ riemannInvariant stress base k (u (curve r))
  have halong : ∀ r ∈ I, HasDerivAt along 0 r := by
    intro r hr
    simpa only [along] using hasDerivAt_riemannInvariant_along_characteristic
        hstress base k hsolution (hcurve r hr) (hcurveMapsTo hr) (hnonnegative r hr)
  have halongDifferentiable : DifferentiableOn ℝ along I :=
    fun r hr ↦ (halong r hr).differentiableAt.differentiableWithinAt
  have halongDeriv : I.EqOn (deriv along) 0 := by
    intro r hr
    simpa using (halong r hr).deriv
  simpa only [along] using hIopen.is_const_of_deriv_eq_zero hIpreconnected
      halongDifferentiable halongDeriv hs ht

end PDE.Hyperbolic.ConservationLaw.System.PSystem
