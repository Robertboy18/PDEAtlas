/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.IntegralCurveFamily
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannInvariant
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.Hyperbolic.ConservationLaw.System.Riemann
import CAS.ExactTactic

/-!
# Characteristic curves for the one-dimensional p-system

The p-system characteristic ODEs can be solved explicitly. If

`A(v) = ∫ x in 0..v, √p'(x)`,

then a wave of strength `s` through `(v, w)` has strain `v + s` and velocity

* `w + A(v + s) - A(v)` in family zero;
* `w - A(v + s) + A(v)` in family one.

These formulas define global characteristic flows. We assemble the two
flows into the `LocalWaveFamily` used by the local
Riemann inverse theorem, and specialize that theorem to the p-system
eigenbasis. Admissible orientations of these curves are proved separately in
`PSystem.WaveGeometry`.

The strain coordinate is the natural parameter: along either curve it moves
at unit rate, and the velocity coordinate changes by the acoustic
displacement `A(v + s) - A(v)`, whose derivative in `s` is the sound speed
`c(v + s) = √p'(v + s)`. This is why the tangent is the right eigenvector
`(1, ±c)` and why the corresponding Riemann invariant `w ∓ A(v)` is constant
along the curve.

In the notation of Evans, the paths of these curves are the rarefaction curves `Rₖ` of §11.2.1,
the solutions of (6) for the p-system eigenvectors of §11.1.2, Example 1 (continued); our
families zero and one have the eigenvalues `-c` and `c`, his `λ₁` and `λ₂`. The invariants are
Riemann invariants in the sense of §11.3.1, constant along the curves as in (3). The two-wave map
is the map `Φ` of the proof of Theorem 4 in §11.2.4 with each wave curve `Tₖ` replaced by the
rarefaction curve, and the inverse-function step uses the same derivative (49) at zero. Chapter 17
of Smoller's book treats the Riemann problem for systems of conservation laws.

## Main results

* `acousticDisplacement`, `hasDerivAt_acousticDisplacement`: `A(v + s) - A(v)`
  and its derivative `c(v + s)` in the strength.
* `characteristicCurve`, `hasDerivAt_characteristicCurve`,
  `isIntegralCurve_characteristicCurve`: the explicit curves are integral
  curves of the right eigenvector fields.
* `characteristicFlow`: the curves form a global flow (`characteristicCurve_add`).
* `riemannInvariant_characteristicCurve`,
  `existsUnique_characteristicCurve_strength`: the `k`th Riemann invariant is
  constant along the `k`th curve, and two states with equal `k`th invariant are
  joined by a unique strength.
* `existsUnique_characteristicWaveMap_strength`: when `p' > 0` everywhere, the
  composed two-wave map gives local coordinates near strength zero, the
  inverse-function step of the Riemann construction.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1, Example 1, equation (7); §11.1.2, Example 1
  (continued); §11.2.1, equation (6); §11.2.4, proof of Theorem 4, equations (44)-(49);
  §11.3.1, equations (2')-(3).
  <https://doi.org/10.1090/gsm/019>
* J. Smoller, *Shock Waves and Reaction–Diffusion Equations*, Grundlehren der mathematischen
  Wissenschaften, Springer, 1994, Chapter 17.
  <https://doi.org/10.1007/978-1-4612-0873-0>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

/-- Acoustic distance traversed when the strain changes from `v` to `v + s`.

Writing the displacement as a difference of one fixed primitive makes its
dependence on both the base strain and the strength transparent. -/
def acousticDisplacement
    (stress : ℝ → ℝ) (v s : ℝ) : ℝ :=
  acousticPrimitive stress 0 (v + s) - acousticPrimitive stress 0 v

/-- A strain change of zero traverses no acoustic distance. -/
@[simp]
theorem acousticDisplacement_zero (stress : ℝ → ℝ) (v : ℝ) :
    acousticDisplacement stress v 0 = 0 := by
  simp [acousticDisplacement]

/-- Acoustic displacement is additive under consecutive strain changes. -/
theorem acousticDisplacement_add (stress : ℝ → ℝ) (v s t : ℝ) :
    acousticDisplacement stress v (s + t) =
      acousticDisplacement stress v t + acousticDisplacement stress (v + t) s := by
  simp only [acousticDisplacement]
  ring_nf

/-- The acoustic displacement is independent of the normalization chosen for
the acoustic primitive. -/
theorem acousticPrimitive_sub_eq_acousticDisplacement {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 1 stress) (base v s : ℝ) :
    acousticPrimitive stress base (v + s) - acousticPrimitive stress base v =
      acousticDisplacement stress v s := by
  have hsound := continuous_soundSpeed hstress
  unfold acousticDisplacement acousticPrimitive
  rw [intervalIntegral.integral_interval_sub_left (hsound.intervalIntegrable base (v + s))
    (hsound.intervalIntegrable base v)]
  rw [intervalIntegral.integral_interval_sub_left (hsound.intervalIntegrable 0 (v + s))
    (hsound.intervalIntegrable 0 v)]

/-- The derivative with respect to wave strength is the sound speed at the
current strain. -/
theorem hasDerivAt_acousticDisplacement {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (v s : ℝ) :
    HasDerivAt (acousticDisplacement stress v) (soundSpeed stress (v + s)) s := by
  have hargument : HasDerivAt (fun r : ℝ ↦ v + r) 1 s := by
    cas
  change HasDerivAt (fun r ↦ acousticPrimitive stress 0 (v + r) - acousticPrimitive stress 0 v)
    (soundSpeed stress (v + s)) s
  simpa only [Function.comp_apply, mul_one] using
    ((hasDerivAt_acousticPrimitive hstress 0 (v + s)).comp
      s hargument).sub_const (acousticPrimitive stress 0 v)

/-- Acoustic displacement depends `C¹`-smoothly on strength and base strain. -/
theorem contDiff_acousticDisplacement {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ acousticDisplacement stress p.2 p.1) := by
  have hprimitive := contDiff_acousticPrimitive hstress 0
  change ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ acousticPrimitive stress 0 (p.2 + p.1) -
        acousticPrimitive stress 0 p.2)
  exact (hprimitive.comp (contDiff_snd.add contDiff_fst)).sub (hprimitive.comp contDiff_snd)

/-- State reached after following the `k`th characteristic field for
strength `s`. -/
def characteristicCurve
    (stress : ℝ → ℝ) (k : Fin 2)
    (s : ℝ) (state : ℝ^2) : ℝ^2 :=
  !₂[state 0 + s, state 1 + if k = 0 then acousticDisplacement stress (state 0) s else
        -acousticDisplacement stress (state 0) s]

/-- Strength zero leaves the state unchanged, so each characteristic curve passes through its
initial state. -/
@[simp]
theorem characteristicCurve_zero (stress : ℝ → ℝ) (k : Fin 2) (state : ℝ^2) :
    characteristicCurve stress k 0 state = state := by
  ext i
  fin_cases i <;> simp [characteristicCurve]

/-- The strain coordinate along either characteristic curve is `v + s`. -/
@[simp]
theorem characteristicCurve_apply_zero (stress : ℝ → ℝ) (k : Fin 2) (s : ℝ) (state : ℝ^2) :
    characteristicCurve stress k s state 0 = state 0 + s := by
  simp [characteristicCurve]

/-- The velocity coordinate along the characteristic curve is `w ± (A(v + s) - A(v))`, with
the plus sign in family zero and the minus sign in family one. -/
@[simp]
theorem characteristicCurve_apply_one (stress : ℝ → ℝ) (k : Fin 2) (s : ℝ) (state : ℝ^2) :
    characteristicCurve stress k s state 1 = state 1 + if k = 0 then acousticDisplacement stress
      (state 0) s else -acousticDisplacement stress (state 0) s := by
  simp [characteristicCurve]

/-- Apply the family-zero characteristic curve and then the family-one
characteristic curve.

This is the concrete two-wave coordinate map used in the inverse-function
argument. It is not the physical p-system Riemann solver: in compressive
directions the characteristic curve must be replaced by the corresponding
Lax shock curve. -/
def characteristicWaveMap
    (stress : ℝ → ℝ) (left strength : ℝ^2) : ℝ^2 :=
  characteristicCurve stress 1 (strength 1) (characteristicCurve stress 0 (strength 0) left)

/-- The strain after a family-zero wave of strength `s₀` followed by a family-one wave of
strength `s₁` is `v + s₀ + s₁`. -/
@[simp]
theorem characteristicWaveMap_apply_zero (stress : ℝ → ℝ) (left strength : ℝ^2) :
    characteristicWaveMap stress left strength 0 = left 0 + strength 0 + strength 1 := by
  simp [characteristicWaveMap]

/-- The velocity after the two waves: the family-zero step adds the acoustic displacement from
`v` by `s₀`, and the family-one step subtracts the displacement from `v + s₀` by `s₁`. -/
@[simp]
theorem characteristicWaveMap_apply_one (stress : ℝ → ℝ) (left strength : ℝ^2) :
    characteristicWaveMap stress left strength 1 = left 1 + acousticDisplacement stress (left 0)
      (strength 0) - acousticDisplacement stress (left 0 + strength 0) (strength 1) := by
  simp [characteristicWaveMap, sub_eq_add_neg]

/-- Characteristic steps compose by addition of their strengths. -/
theorem characteristicCurve_add (stress : ℝ → ℝ) (k : Fin 2) (s t : ℝ) (state : ℝ^2) :
    characteristicCurve stress k (s + t) state =
      characteristicCurve stress k s (characteristicCurve stress k t state) := by
  ext i
  fin_cases i
  · simp only [characteristicCurve, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  · fin_cases k <;> simp [characteristicCurve, acousticDisplacement_add] <;> ring

/-- Wave strength is uniquely determined by the state on a characteristic
curve. This follows already from the strain coordinate `v + s`. -/
theorem characteristicCurve_injective (stress : ℝ → ℝ) (k : Fin 2) (state : ℝ^2) :
    Function.Injective (fun s ↦ characteristicCurve stress k s state) := by
  intro s t hstate
  have hstrain := congrArg (fun current : ℝ^2 ↦ current 0) hstate
  simp only [characteristicCurve_apply_zero] at hstrain
  exact add_left_cancel hstrain

/-- Following a characteristic curve by `s` and then by `-s` returns to the
initial state. -/
@[simp]
theorem characteristicCurve_neg_left (stress : ℝ → ℝ) (k : Fin 2) (s : ℝ) (state : ℝ^2) :
    characteristicCurve stress k (-s) (characteristicCurve stress k s state) = state := by
  rw [← characteristicCurve_add]
  simp

/-- Following a characteristic curve by `-s` and then by `s` returns to the
initial state. -/
@[simp]
theorem characteristicCurve_neg_right (stress : ℝ → ℝ) (k : Fin 2) (s : ℝ) (state : ℝ^2) :
    characteristicCurve stress k s (characteristicCurve stress k (-s) state) = state := by
  rw [← characteristicCurve_add]
  simp

/-- The explicit characteristic curve has the selected right eigenvector as
its derivative. -/
theorem hasDerivAt_characteristicCurve {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (k : Fin 2)
    (state : ℝ^2) (s : ℝ) :
    HasDerivAt (fun r ↦ characteristicCurve stress k r state)
      (rightEigenvector (soundSpeed stress (characteristicCurve stress k s state 0)) k) s := by
  have hstrain : HasDerivAt (fun r : ℝ ↦ state 0 + r) 1 s := by
    cas
  have hacoustic := hasDerivAt_acousticDisplacement hstress (state 0) s
  let coordinates := EuclideanSpace.equiv (Fin 2) ℝ
  fin_cases k
  · have hcoordinates : HasDerivAt (fun r : ℝ ↦ ![state 0 + r,
              state 1 + acousticDisplacement stress (state 0) r])
          ![1, soundSpeed stress (state 0 + s)] s := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · simpa using hstrain
      · simpa using hacoustic.const_add (state 1)
    have hcurve := coordinates.symm.hasFDerivAt.comp_hasDerivAt s hcoordinates
    simpa [coordinates, characteristicCurve, rightEigenvector, Function.comp_def] using hcurve
  · have hcoordinates : HasDerivAt (fun r : ℝ ↦ ![state 0 + r,
              state 1 + -acousticDisplacement stress (state 0) r])
          ![1, -soundSpeed stress (state 0 + s)] s := by
      rw [hasDerivAt_pi]
      intro i
      fin_cases i
      · simpa using hstrain
      · simpa using hacoustic.neg.const_add (state 1)
    have hcurve := coordinates.symm.hasFDerivAt.comp_hasDerivAt s hcoordinates
    simpa [coordinates, characteristicCurve, rightEigenvector, Function.comp_def] using hcurve

/-- The explicit formula is a global integral curve of the selected
characteristic vector field. -/
theorem isIntegralCurve_characteristicCurve {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (k : Fin 2) (state : ℝ^2) :
    IsIntegralCurve (fun s ↦ characteristicCurve stress k s state)
      (fun _ current ↦ rightEigenvector (soundSpeed stress (current 0)) k) :=
  fun s ↦ hasDerivAt_characteristicCurve hstress k state s

/-- The explicit characteristic state is jointly `C¹` in strength and
initial state. -/
theorem contDiff_characteristicCurve {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (k : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ characteristicCurve stress k p.1 p.2) := by
  have hstrain : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ p.2 0) := by
    fun_prop
  have hvelocity : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ p.2 1) := by
    fun_prop
  have hacoustic : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ acousticDisplacement stress (p.2 0) p.1) :=
    (contDiff_acousticDisplacement hstress).comp (contDiff_fst.prodMk hstrain)
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa [characteristicCurve] using hstrain.add contDiff_fst
  · fin_cases k
    · simpa [characteristicCurve] using hvelocity.add hacoustic
    · simpa [characteristicCurve, sub_eq_add_neg] using hvelocity.sub hacoustic

/-- At zero strength, the joint strength-state derivative of a
characteristic step has the right eigenvector as its strength column and the
identity as its state block. -/
theorem hasFDerivAt_characteristicCurve_zero {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (k : Fin 2) (state : ℝ^2) :
    HasFDerivAt (fun p : ℝ × ℝ^2 ↦ characteristicCurve stress k p.1 p.2)
      (waveStepDerivative (rightEigenvector (soundSpeed stress (state 0)) k)) (0, state) := by
  apply hasFDerivAt_waveStep_zero
  · exact characteristicCurve_zero stress k
  · exact (contDiff_characteristicCurve hstress k).differentiable one_ne_zero (0, state)
  · simpa using hasDerivAt_characteristicCurve hstress k state 0

/-- The explicit p-system characteristic curves form a global flow. -/
def characteristicFlow
    (stress : ℝ → ℝ) (hstress : ContDiff ℝ 1 stress)
    (k : Fin 2) :
    Flow ℝ (ℝ^2) where
  toFun := characteristicCurve stress k
  cont' := (contDiff_characteristicCurve hstress k).continuous
  map_add' := characteristicCurve_add stress k
  map_zero' := characteristicCurve_zero stress k

/-- The flow map is the explicit characteristic curve; this holds by definition. -/
@[simp]
theorem characteristicFlow_apply (stress : ℝ → ℝ) (hstress : ContDiff ℝ 1 stress) (k : Fin 2)
    (s : ℝ) (state : ℝ^2) :
    characteristicFlow stress hstress k s state = characteristicCurve stress k s state :=
  rfl

/-- Each explicit flow line solves the ODE of the corresponding p-system
characteristic field. -/
theorem isIntegralCurve_characteristicFlow {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (state : ℝ^2) :
    IsIntegralCurve (fun s ↦ characteristicFlow stress hstress k s state)
      (characteristicField stress (hstress.differentiable one_ne_zero)
        hpositive k).vectorField := by
  intro s
  simpa [CharacteristicField.vectorField, characteristicField, characteristicFlow_apply] using
    hasDerivAt_characteristicCurve hstress k state s

/-- The Riemann invariant associated with a characteristic family is constant
along its explicit characteristic curve. -/
theorem riemannInvariant_characteristicCurve {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (base : ℝ) (k : Fin 2) (state : ℝ^2) (s : ℝ) :
    riemannInvariant stress base k (characteristicCurve stress k s state) =
      riemannInvariant stress base k state := by
  by_cases hk : k = 0
  · simp only [riemannInvariant, characteristicCurve_apply_zero,
      characteristicCurve_apply_one, hk, ite_eq_left]
    rw [← acousticPrimitive_sub_eq_acousticDisplacement hstress base (state 0) s]
    ring
  · simp only [riemannInvariant, characteristicCurve_apply_zero,
      characteristicCurve_apply_one, hk, ite_false]
    rw [← acousticPrimitive_sub_eq_acousticDisplacement hstress base (state 0) s]
    ring

/-- Two states with the same `k`th Riemann invariant are joined by a unique
`k`th characteristic strength. -/
theorem existsUnique_characteristicCurve_strength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (base : ℝ) (k : Fin 2) (state target : ℝ^2)
    (hinvariant : riemannInvariant stress base k target = riemannInvariant stress base k state) :
    ∃! s : ℝ, characteristicCurve stress k s state = target := by
  let s := target 0 - state 0
  have hstrain : characteristicCurve stress k s state 0 = target 0 := by
    simp [s]
  have hinvariant' : riemannInvariant stress base k (characteristicCurve stress k s state) =
        riemannInvariant stress base k target :=
    (riemannInvariant_characteristicCurve hstress base k state s).trans hinvariant.symm
  have hvelocity : characteristicCurve stress k s state 1 = target 1 := by
    unfold riemannInvariant at hinvariant'
    split_ifs at hinvariant' <;> rw [hstrain] at hinvariant' <;> linarith
  have hstate : characteristicCurve stress k s state = target := by
    ext i
    fin_cases i
    · exact hstrain
    · exact hvelocity
  refine ⟨s, hstate, fun t ht ↦ ?_⟩
  exact characteristicCurve_injective stress k state (ht.trans hstate.symm)

/-- The two explicit characteristic flows, viewed as the wave family used
by the local Riemann parameterization. -/
def characteristicWaveFamily
    (stress : ℝ → ℝ) (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) :
    LocalWaveFamily (flux stress)
      (fun k ↦ characteristicField stress
        (hstress.differentiable one_ne_zero) hpositive k) :=
  LocalWaveFamily.ofCharacteristicFlows (fun k ↦ characteristicFlow stress hstress k) (fun k state ↦
      (contDiff_characteristicCurve hstress k).contDiffAt (x := (0, state)))
    (fun k state ↦ (isIntegralCurve_characteristicFlow
        hstress hpositive k state).isIntegralCurveAt 0)

/-- The generic ordered wave map of the two characteristic flows is the
explicit p-system characteristic wave map. -/
theorem characteristicWaveFamily_composedWaveMap {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left strength : ℝ^2) :
    (characteristicWaveFamily stress hstress hpositive |>.composedWaveMap left) strength =
      characteristicWaveMap stress left strength := by
  change characteristicCurve stress 1 (strength 1)
        (characteristicCurve stress 0 (strength 0) left) =
      characteristicWaveMap stress left strength
  rfl

/-- The p-system characteristic wave map gives local coordinates around
every strictly hyperbolic state.

The theorem is the analytic inverse-function stage of the Riemann
construction. -/
theorem existsUnique_characteristicWaveMap_strength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (left : ℝ^2) :
    ∃ source target : Set (ℝ^2), IsOpen source ∧ IsOpen target ∧ 0 ∈ source ∧ left ∈ target ∧
      ∀ right ∈ target, ∃! strength : ℝ^2, strength ∈ source ∧
      characteristicWaveMap stress left strength = right := by
  let sound := soundSpeed stress (left 0)
  let basis := eigenbasis sound (soundSpeed_pos (hpositive (left 0)))
  simpa only [characteristicWaveFamily_composedWaveMap hstress hpositive] using
    (characteristicWaveFamily stress hstress hpositive
      |>.existsUnique_localRiemann_strength left (Set.mem_univ left) basis)
      (fun k ↦ by
        change rightEigenvector (soundSpeed stress (left 0)) k = eigenbasis sound
              (soundSpeed_pos (hpositive (left 0))) k
        exact (eigenbasis_apply sound (soundSpeed_pos (hpositive (left 0))) k).symm)

end PDE.Hyperbolic.ConservationLaw.System.PSystem
