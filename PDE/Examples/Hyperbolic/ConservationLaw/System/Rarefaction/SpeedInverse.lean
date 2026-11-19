/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Rarefaction.InitialValue
public import PDE.Examples.Hyperbolic.ConservationLaw.System.OneComponent
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives

/-!
# A rarefaction whose speed image is only the positive half-line

For the one-component flux `exp`, the rarefaction curve is the identity and the
characteristic speed is `exp`. The speed maps onto the positive half-line only, and its
derivative has no positive lower bound. The interval inverse of the speed is the
logarithm (`exponential_speedInverse_eq_log`), and the fan from `A` to `B` is
`log (max (exp A) (min (exp B) (x/t)))` (`exists_exponential_rarefaction`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.Rarefaction

open PDE.Common PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.System
open PDE.Hyperbolic.ConservationLaw.Scalar
open MeasureTheory Set
open scoped ContDiff ENNReal

/-- Exponential flux on the one-component Euclidean state space. -/
def exponentialFlux (q : ℝ^1) : ℝ^1 := WithLp.toLp 2 ![Real.exp (q 0)]

/-- The exponential flux is smooth. -/
theorem contDiff_exponentialFlux : ContDiff ℝ ∞ exponentialFlux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  change ContDiff ℝ ∞ (fun q : ℝ^1 ↦ Real.exp (q 0))
  cas

/-- The Jacobian acts by multiplication by the positive exponential. -/
theorem fderiv_exponentialFlux (q v : ℝ^1) :
    fderiv ℝ exponentialFlux q v = Real.exp (q 0) • v := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  fin_cases i
  simp only [Fin.sum_univ_one, PiLp.smul_apply, smul_eq_mul]
  have hd : (∂[0] exponentialFlux) q 0 = Real.exp (q 0) := by
    rw [partialDeriv_apply 0 0 (contDiff_exponentialFlux.differentiable (by simp) q)]
    change (∂[0] (fun y : ℝ^1 ↦ Real.exp (y 0))) q = Real.exp (q 0)
    cas
  change v 0 * (∂[0] exponentialFlux) q 0 = Real.exp (q 0) * v 0
  rw [hd, mul_comm]

/-- The exponential flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_exponentialFlux (q : ℝ^1) :
    IsStrictlyHyperbolicAt exponentialFlux q :=
  OneComponent.isStrictlyHyperbolicAt_of_fderiv_eq_smul
    (contDiff_exponentialFlux.differentiable (by simp) q) (fderiv_exponentialFlux q)

/-- The canonical characteristic speed is the exponential of the state. -/
theorem characteristicSpeed_exponentialFlux (k : Fin 1) :
    characteristicSpeed exponentialFlux k = fun q ↦ Real.exp (q 0) := by
  funext q
  exact OneComponent.characteristicSpeed_eq_of_fderiv_eq_smul (fderiv_exponentialFlux q) k

/-- The family of the exponential flux is genuinely nonlinear. -/
theorem isGenuinelyNonlinearFamily_exponentialFlux (k : Fin 1) :
    IsGenuinelyNonlinearFamily exponentialFlux k := by
  intro q
  rw [characteristicSpeed_exponentialFlux]
  constructor
  · cas
  intro v hv
  have hD : fderiv ℝ (fun y : ℝ^1 ↦ Real.exp (y 0)) q v =
      Real.exp (q 0) * v 0 := by
    rw [fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_one]
    have h : (∂[0] (fun y : ℝ^1 ↦ Real.exp (y 0))) q = Real.exp (q 0) := by
      cas
    rw [h]
  rw [hD]
  apply mul_ne_zero (Real.exp_ne_zero _)
  intro hz
  apply hv.2
  ext i
  fin_cases i
  exact hz

/-- A constant, smooth eigenvector selection for the exponential flux. -/
def exponentialField : CharacteristicField exponentialFlux where
  flux_differentiable := contDiff_exponentialFlux.differentiable (by simp)
  speed q := Real.exp (q 0)
  rightEigenvector _ := WithLp.toLp 2 ![1]
  eigenvector q := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr (fderiv_exponentialFlux q _), ?_⟩
    intro h
    have h0 := congrArg (fun z : ℝ^1 ↦ z 0) h
    norm_num at h0

/-- The rarefaction curve `s ↦ s` in `ℝ¹`. -/
def exponentialCurve (s : ℝ) : ℝ^1 := s • WithLp.toLp 2 ![1]

/-- The curve is a global integral curve of the eigenvector field. -/
theorem isIntegralCurve_exponentialCurve :
    IsIntegralCurve exponentialCurve exponentialField.vectorField := by
  intro s
  change HasDerivAt (fun t : ℝ ↦ t • (WithLp.toLp 2 ![1] : ℝ^1))
    (WithLp.toLp 2 ![1]) s
  simpa only [id_eq, one_smul] using
    (hasDerivAt_id s).smul_const (WithLp.toLp 2 ![1] : ℝ^1)

/-- The speed image of the curve is the positive half-line. -/
theorem range_exponentialCurve_speed :
    Set.range (exponentialField.speed ∘ exponentialCurve) = Ioi 0 := by
  change Set.range (fun s : ℝ ↦ Real.exp (s * 1)) = Ioi 0
  simpa only [mul_one] using Real.range_exp

/-- The chosen interval inverse agrees with logarithm on its domain. -/
theorem exponential_speedInverse_eq_log {l r ξ : ℝ}
    (hξ : ξ ∈ (exponentialField.speed ∘ exponentialCurve) '' Ioo l r) :
    exponentialField.speedInverse exponentialCurve l r ξ = Real.log ξ := by
  have heq := (exponentialField.speedInverse_mem_and_eq hξ).2
  change Real.exp (exponentialField.speedInverse exponentialCurve l r ξ * 1) = ξ at heq
  simpa only [Real.log_exp, mul_one] using congrArg Real.log heq

/-- The speed inverse is `C¹` on the speed image. -/
theorem contDiffOn_exponential_speedInverse (l r : ℝ) :
    ContDiffOn ℝ 1 (exponentialField.speedInverse exponentialCurve l r)
      ((exponentialField.speed ∘ exponentialCurve) '' Ioo l r) := by
  apply exponentialField.contDiffOn_speedInverse_of_continuousOn
    (contDiff_exponentialFlux.of_le (by simp)) isStrictlyHyperbolicAt_exponentialFlux
    (isGenuinelyNonlinearFamily_exponentialFlux 0)
    (characteristicSpeed_exponentialFlux 0).symm
    (isIntegralCurve_exponentialCurve.isIntegralCurveOn (Ioo l r))
  exact continuousOn_const

/-- For `A < B` the fan is `log (max (exp A) (min (exp B) (x/t)))`, a bounded continuous
weak solution with strong initial trace. -/
theorem exists_exponential_rarefaction (A B : ℝ) (hAB : A < B) :
    ∃ K : ℝ, ∃ u : ℝ^2 → ℝ^1,
      IsWeakInitialValueSolution exponentialFlux
        (riemannData (exponentialCurve A) (exponentialCurve B)) u ∧
      HasInitialTraceLocallyL1 u
        (riemannData (exponentialCurve A) (exponentialCurve B)) ∧
      ContinuousOn u forwardHalfSpace ∧ MemLp u ∞ (volume.restrict forwardHalfSpace) ∧
      (∀ p : ℝ^2, 0 < p 0 → ‖u p‖ ≤ K) ∧
      Set.range (fun x : ℝ ↦ u !₂[1, x]) = exponentialCurve '' uIcc A B ∧
      (∀ p : ℝ^2, 0 < p 0 →
        u p = exponentialCurve
          (Real.log (max (Real.exp A) (min (Real.exp B) (similarityVariable p))))) := by
  have hspeed : exponentialField.speed = characteristicSpeed exponentialFlux 0 :=
    (characteristicSpeed_exponentialFlux 0).symm
  have hexpands : exponentialField.speed (exponentialCurve A) <
      exponentialField.speed (exponentialCurve B) := by
    simpa only [exponentialField, exponentialCurve, PiLp.smul_apply,
      WithLp.ofLp_toLp, Matrix.cons_val_zero, smul_eq_mul, mul_one] using
      Real.exp_lt_exp.mpr hAB
  obtain ⟨l, r, K, u, hsegment, _hclosure, _hprofile, _hinverse,
    hu, ht, _hm, hc, hL, hbound, _hray, hformula, _hsimple,
    hrange, _hphase, _hoff, _hae, _htests⟩ :=
    exists_continuous_rarefaction_of_integralCurve 0
      (contDiff_exponentialFlux.of_le (by simp)) isStrictlyHyperbolicAt_exponentialFlux
      (isGenuinelyNonlinearFamily_exponentialFlux 0) exponentialField hspeed
      isOpen_univ ordConnected_univ
      (isIntegralCurve_exponentialCurve.isIntegralCurveOn univ)
      (mem_univ A) (mem_univ B) hexpands
  refine ⟨K, u, hu, ht, hc, hL, hbound, hrange, ?_⟩
  have hvD := isIntegralCurve_exponentialCurve.isIntegralCurveOn (Ioo l r)
  have hC := (isGenuinelyNonlinearFamily_iff isStrictlyHyperbolicAt_exponentialFlux 0
    exponentialField hspeed).mp (isGenuinelyNonlinearFamily_exponentialFlux 0)
  intro p hp
  rw [hformula p hp]
  let ξ := max (exponentialField.speed (exponentialCurve A))
    (min (exponentialField.speed (exponentialCurve B)) (similarityVariable p))
  have hξ : ξ ∈ (exponentialField.speed ∘ exponentialCurve) '' Ioo l r := by
    apply image_mono hsegment
    rw [exponentialField.speed_image_uIcc hvD hC
      (hsegment left_mem_uIcc) (hsegment right_mem_uIcc) hexpands.le]
    exact ⟨le_max_left _ _, max_le hexpands.le (min_le_left _ _)⟩
  change exponentialCurve (exponentialField.speedInverse exponentialCurve l r ξ) = _
  rw [exponential_speedInverse_eq_log hξ]
  congr 2
  simp only [ξ, exponentialField, exponentialCurve, PiLp.smul_apply,
    Matrix.cons_val_zero, smul_eq_mul, mul_one]

end PDE.Examples.Hyperbolic.ConservationLaw.System.Rarefaction
