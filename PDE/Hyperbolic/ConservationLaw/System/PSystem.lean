/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

-- Supplies `StrictMono.strictConvexOn_univ_of_deriv` for mechanical entropy.
public import Mathlib.Analysis.Convex.Deriv
public import PDE.Hyperbolic.ConservationLaw.System.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic

/-!
# The one-dimensional p-system

We study the two-component elasticity p-system

`vₜ - wₓ = 0`, `wₜ - p(v)ₓ = 0`,

in conservation form with flux `F(v, w) = (-w, -p(v))`, where `v` is
strain, `w` is velocity, and `p` is the stress law. We prove:

* the exact action of the flux Jacobian;
* strict hyperbolicity wherever `p' > 0`, with speeds `-√p'` and `√p'`;
* the mechanical entropy `w² / 2 + P(v)` and entropy flux `-p(v)w`
  when `P' = p`;
* convexity of the mechanical entropy when the stress law is monotone.

The flux is (7) of Evans, §11.1, Example 1, and the speeds and the condition `p' > 0` are
those of Example 1 (continued) in §11.1.2, equation (41). The entropy pair is Example 2 of
§11.4.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1, Example 1, equations (6)-(8); §11.1.2, Example 1
  (continued), equation (41); §11.4.2, Example 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Common

/-- The p-system flux `F(v, w) = (-w, -p(v))`. -/
def flux (stress : ℝ → ℝ) (state : ℝ^2) : ℝ^2 :=
  !₂[-state 1, -stress (state 0)]

/-- The first flux component is minus the velocity, encoding `vₜ - wₓ = 0`. -/
@[simp]
theorem flux_zero (stress : ℝ → ℝ) (state : ℝ^2) :
    flux stress state 0 = -state 1 := by
  simp [flux]

/-- The second flux component is minus the stress, encoding `wₜ - p(v)ₓ = 0`. -/
@[simp]
theorem flux_one (stress : ℝ → ℝ) (state : ℝ^2) :
    flux stress state 1 = -stress (state 0) := by
  simp [flux]

/-- The p-system flux is differentiable at a state whenever the stress law
is differentiable at its strain coordinate. -/
theorem differentiableAt_flux {stress : ℝ → ℝ} {state : ℝ^2}
    (hstress : DifferentiableAt ℝ stress (state 0)) :
    DifferentiableAt ℝ (flux stress) state := by
  rw [differentiableAt_piLp]
  intro i
  fin_cases i
  · exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (1 : Fin 2)).differentiableAt.neg
  · change DifferentiableAt ℝ (fun y : ℝ^2 ↦ -stress (y 0)) state
    exact (hstress.comp state (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state
            (0 : Fin 2)).differentiableAt).neg

/-- The p-system flux has the same differentiability order as its stress
law. -/
theorem contDiff_flux {stress : ℝ → ℝ} {n : WithTop ℕ∞} (hstress : ContDiff ℝ n stress) :
    ContDiff ℝ n (flux stress) := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun state : ℝ^2 ↦ -state 1)
    fun_prop
  · change ContDiff ℝ n (fun state : ℝ^2 ↦ -stress (state 0))
    have hcoordinate : ContDiff ℝ n (fun state : ℝ^2 ↦ state 0) := by
      cas
    exact (hstress.comp hcoordinate).neg

/-- The action of the p-system flux Jacobian. -/
theorem fderiv_flux_apply {stress : ℝ → ℝ} {state direction : ℝ^2}
    (hstress : DifferentiableAt ℝ stress (state 0)) :
    fderiv ℝ (flux stress) state direction =
      !₂[-direction 1, -(deriv stress (state 0) * direction 0)] := by
  have hflux := differentiableAt_flux hstress
  ext i
  have hcoordinate : fderiv ℝ (fun y : ℝ^2 ↦ flux stress y i) state direction =
        fderiv ℝ (flux stress) state direction i := by
    have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction)
      (((hasFDerivWithinAt_piLp (2 : ENNReal)).mp (hasFDerivWithinAt_univ.mpr hflux.hasFDerivAt) i
          |>.hasFDerivAt_of_univ).fderiv)
    simpa [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using h
  rw [← hcoordinate]
  fin_cases i
  · change fderiv ℝ (fun y : ℝ^2 ↦ -y 1) state direction = -direction 1
    rw [fderiv_fun_neg]
    have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (2 : ENNReal) state (1 : Fin 2)).fderiv
    simpa [EuclideanSpace.proj] using congrArg Neg.neg h
  · change fderiv ℝ (fun y : ℝ^2 ↦ -stress (y 0)) state direction =
        -(deriv stress (state 0) * direction 0)
    rw [fderiv_fun_neg]
    have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (hstress.hasFDerivAt.comp state
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (0 : Fin 2))).fderiv
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply,
      fderiv_eq_smul_deriv, EuclideanSpace.proj, smul_eq_mul, mul_comm] using congrArg Neg.neg h

/-- Right eigenvectors of the p-system Jacobian for a positive sound speed. -/
def rightEigenvector (sound : ℝ) (k : Fin 2) : ℝ^2 :=
  !₂[1, if k = 0 then sound else -sound]

/-- The corresponding ordered characteristic speeds. -/
def characteristicSpeed (sound : ℝ) (k : Fin 2) : ℝ :=
  if k = 0 then -sound else sound

/-- Positive sound speed gives two linearly independent characteristic directions. -/
theorem rightEigenvector_linearIndependent {sound : ℝ} (hsound : 0 < sound) :
    LinearIndependent ℝ (rightEigenvector sound) := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have := congrArg (fun v : ℝ^2 ↦ v 0) hzero
    norm_num [rightEigenvector] at this
  · intro a heq
    have hzero := congrArg (fun v : ℝ^2 ↦ v 0) heq
    have hone := congrArg (fun v : ℝ^2 ↦ v 1) heq
    norm_num [rightEigenvector] at hzero hone
    nlinarith

/-- The two p-system eigenvectors form a basis when the sound speed is
positive. -/
def eigenbasis (sound : ℝ) (hsound : 0 < sound) :
    Module.Basis (Fin 2) ℝ (ℝ^2) :=
  basisOfLinearIndependentOfCardEqFinrank (rightEigenvector_linearIndependent hsound) (by simp)

/-- The `k`th vector of the eigenbasis is the `k`th right eigenvector `(1, ±c)`. -/
@[simp]
theorem eigenbasis_apply (sound : ℝ) (hsound : 0 < sound) (k : Fin 2) :
    eigenbasis sound hsound k = rightEigenvector sound k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-- The explicit eigenpair of the p-system flux Jacobian when `p' ≥ 0`. -/
theorem hasEigenvector_fderiv_flux {stress : ℝ → ℝ} {state : ℝ^2}
    (hstress : DifferentiableAt ℝ stress (state 0)) (hnonnegative : 0 ≤ deriv stress (state 0))
    (k : Fin 2) :
    Module.End.HasEigenvector (fderiv ℝ (flux stress) state).toLinearMap
      (characteristicSpeed (√(deriv stress (state 0))) k)
      (rightEigenvector (√(deriv stress (state 0))) k) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · change fderiv ℝ (flux stress) state (rightEigenvector (√(deriv stress (state 0))) k) =
        characteristicSpeed (√(deriv stress (state 0))) k •
          rightEigenvector (√(deriv stress (state 0))) k
    rw [fderiv_flux_apply hstress]
    have hsq : (√(deriv stress (state 0))) ^ 2 = deriv stress (state 0) := Real.sq_sqrt hnonnegative
    ext i
    fin_cases k <;> fin_cases i <;> simp [rightEigenvector, characteristicSpeed, smul_eq_mul] <;>
      nlinarith
  · intro hzero
    have := congrArg (fun v : ℝ^2 ↦ v 0) hzero
    norm_num [rightEigenvector] at this

/-- The p-system is strictly hyperbolic at every state where `p' > 0`. -/
theorem isStrictlyHyperbolicAt {stress : ℝ → ℝ} {state : ℝ^2}
    (hstress : DifferentiableAt ℝ stress (state 0)) (hpositive : 0 < deriv stress (state 0)) :
    IsStrictlyHyperbolicAt (flux stress) state := by
  let sound := √(deriv stress (state 0))
  have hsound : 0 < sound := Real.sqrt_pos.2 hpositive
  refine ⟨differentiableAt_flux hstress, eigenbasis sound hsound, characteristicSpeed sound, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp [characteristicSpeed] at hij ⊢ <;> linarith
  · intro k
    simpa [sound] using hasEigenvector_fderiv_flux hstress hpositive.le k

/-- Mechanical energy `w²/2 + P(v)` for the p-system. -/
def mechanicalEntropy (potential : ℝ → ℝ) (state : ℝ^2) : ℝ :=
  state 1 ^ 2 / 2 + potential (state 0)

/-- Mechanical energy flux `-p(v)w` for the p-system. -/
def mechanicalEntropyFlux
    (stress : ℝ → ℝ) (state : ℝ^2) : ℝ :=
  -stress (state 0) * state 1

/-- Differential of the p-system mechanical entropy. -/
theorem fderiv_mechanicalEntropy_apply {potential : ℝ → ℝ} {state direction : ℝ^2}
    (hpotential : DifferentiableAt ℝ potential (state 0)) :
    fderiv ℝ (mechanicalEntropy potential) state direction =
      state 1 * direction 1 + deriv potential (state 0) * direction 0 := by
  have hkinetic :=
    (((PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (1 : Fin 2)).pow 2).const_mul
        (1 / 2 : ℝ))
  have hpotentialComp := hpotential.hasFDerivAt.comp state (PiLp.hasFDerivAt_apply
        (𝕜 := ℝ) (2 : ENNReal) state (0 : Fin 2))
  have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (hkinetic.add hpotentialComp).fderiv
  have hbase : ((fun y : ℝ^2 ↦ (1 / 2 : ℝ) * y 1 ^ 2) + (potential ∘ fun y : ℝ^2 ↦ y 0)) =
        fun y : ℝ^2 ↦ (1 / 2 : ℝ) * y 1 ^ 2 + potential (y 0) := by
    rfl
  rw [hbase] at h
  have h' : fderiv ℝ (fun y : ℝ^2 ↦ (1 / 2 : ℝ) * y 1 ^ 2 + potential (y 0)) state direction =
        (1 / 2 : ℝ) * (2 * state 1 * direction 1) + direction 0 * deriv potential (state 0) := by
    simpa [fderiv_eq_smul_deriv, EuclideanSpace.proj, smul_eq_mul] using h
  have hfun : (fun y : ℝ^2 ↦ (1 / 2 : ℝ) * y 1 ^ 2 + potential (y 0)) =
        mechanicalEntropy potential := by
    funext y
    simp only [Fin.isValue, one_div, mechanicalEntropy, add_left_inj]
    ring
  rw [hfun] at h'
  convert h' using 1
  all_goals ring

/-- Differential of the p-system mechanical entropy flux. -/
theorem fderiv_mechanicalEntropyFlux_apply {stress : ℝ → ℝ} {state direction : ℝ^2}
    (hstress : DifferentiableAt ℝ stress (state 0)) :
    fderiv ℝ (mechanicalEntropyFlux stress) state direction =
      -(deriv stress (state 0) * direction 0 * state 1) - stress (state 0) * direction 1 := by
  have hstressComp :=
    hstress.hasFDerivAt.comp state (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (0 : Fin 2))
  have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (hstressComp.neg.mul
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (1 : Fin 2))).fderiv
  have hbase : ((-(stress ∘ fun y : ℝ^2 ↦ y 0)) * fun y : ℝ^2 ↦ y 1) =
        fun y : ℝ^2 ↦ -stress (y 0) * y 1 := by
    rfl
  rw [hbase] at h
  have h' : fderiv ℝ (fun y : ℝ^2 ↦ -stress (y 0) * y 1) state direction =
        -(stress (state 0) * direction 1) - state 1 * (direction 0 * deriv stress (state 0)) := by
    simpa [fderiv_eq_smul_deriv, EuclideanSpace.proj, smul_eq_mul, sub_eq_add_neg] using h
  change fderiv ℝ (fun y : ℝ^2 ↦ -stress (y 0) * y 1) state direction =
      -(deriv stress (state 0) * direction 0 * state 1) - stress (state 0) * direction 1
  convert h' using 1
  all_goals ring

/-- The mechanical energy and energy flux form an entropy pair whenever
`P' = p`. -/
def mechanicalEntropyPair
    (stress potential : ℝ → ℝ)
    (hstress : ContDiff ℝ 1 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x) :
    EntropyPair (flux stress) where
  flux_differentiable := fun state ↦
    differentiableAt_flux
      (hstress.differentiable one_ne_zero (state 0))
  entropy := mechanicalEntropy potential
  entropyFlux := mechanicalEntropyFlux stress
  entropy_contDiff := by
    apply ContDiff.add
    · simpa only [EuclideanSpace.coe_proj] using
        ((((EuclideanSpace.proj (1 : Fin 2) :
          ℝ^2 →L[ℝ] ℝ).contDiff (n := 1)).pow 2).div_const 2)
    · exact hpotential.comp
        (by
          simpa only [EuclideanSpace.coe_proj] using
            (EuclideanSpace.proj (0 : Fin 2) :
              ℝ^2 →L[ℝ] ℝ).contDiff (n := 1))
  entropyFlux_contDiff := by
    exact (hstress.comp
      (by
        simpa only [EuclideanSpace.coe_proj] using
          (EuclideanSpace.proj (0 : Fin 2) :
            ℝ^2 →L[ℝ] ℝ).contDiff (n := 1))).neg.mul
        (by
          simpa only [EuclideanSpace.coe_proj] using
            (EuclideanSpace.proj (1 : Fin 2) :
              ℝ^2 →L[ℝ] ℝ).contDiff (n := 1))
  compatibility := by
    intro state
    apply ContinuousLinearMap.ext
    intro direction
    rw [fderiv_mechanicalEntropyFlux_apply
      (hstress.differentiable one_ne_zero (state 0))]
    simp only [ContinuousLinearMap.comp_apply]
    rw [fderiv_flux_apply
      (hstress.differentiable one_ne_zero (state 0))]
    rw [fderiv_mechanicalEntropy_apply
      (hpotential.differentiable one_ne_zero (state 0))]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_neg, hderiv,
      Matrix.cons_val_zero]
    ring

/-- A convex stored-energy potential makes the mechanical entropy convex. -/
theorem mechanicalEntropy_convex {potential : ℝ → ℝ} (hpotential : ConvexOn ℝ Set.univ potential) :
    ConvexOn ℝ Set.univ (mechanicalEntropy potential) := by
  have hkinetic : ConvexOn ℝ Set.univ (fun state : ℝ^2 ↦ state 1 ^ 2 / 2) := by
    have hsquare : ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2) :=
      Even.convexOn_pow (𝕜 := ℝ) (by norm_num : Even (2 : ℕ))
    have hcomp := hsquare.comp_linearMap (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).toLinearMap
    have hscaled := hcomp.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    simpa [Function.comp_def, EuclideanSpace.proj, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using hscaled
  have hstored : ConvexOn ℝ Set.univ (fun state : ℝ^2 ↦ potential (state 0)) := by
    simpa [Function.comp_def, EuclideanSpace.proj] using hpotential.comp_linearMap
        (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).toLinearMap
  change ConvexOn ℝ Set.univ ((fun state : ℝ^2 ↦ state 1 ^ 2 / 2) + fun state ↦ potential (state 0))
  exact hkinetic.add hstored

/-- The mechanical pair as a convex entropy pair. -/
def mechanicalConvexEntropyPair
    (stress potential : ℝ → ℝ)
    (hstress : ContDiff ℝ 1 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hconvex : ConvexOn ℝ Set.univ potential) :
    ConvexEntropyPair (flux stress) where
  toEntropyPair :=
    mechanicalEntropyPair stress potential hstress hpotential hderiv
  entropy_convex := mechanicalEntropy_convex hconvex

/-- Positive stress derivative makes the mechanical entropy convex. -/
def mechanicalConvexEntropyPairOfDerivPositive
    (stress potential : ℝ → ℝ)
    (hstress : ContDiff ℝ 1 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ x, 0 < deriv stress x) :
    ConvexEntropyPair (flux stress) := by
  apply mechanicalConvexEntropyPair stress potential hstress hpotential hderiv
  have hmono : StrictMono stress :=
    strictMono_of_deriv_pos hpositive
  have hderivMono : StrictMono (deriv potential) := by
    rw [funext hderiv]
    exact hmono
  exact (hderivMono.strictConvexOn_univ_of_deriv hpotential.continuous).convexOn

end PDE.Hyperbolic.ConservationLaw.System.PSystem
