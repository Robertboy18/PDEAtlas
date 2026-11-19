/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Bounded smooth multipliers for support-controlled approximation

A smooth function with bounded value and first derivatives acts continuously on
`W^{1,p}`. Compact support of the multiplier is unnecessary. This allows a fixed
cutoff in the normal direction to turn whole-space smooth approximants into
functions supported away from the boundary of a half-space.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}
variable {ψ : ℝ^n → ℝ}
variable (hψ : MemLp ψ ∞ (domainMeasure n Ω))
variable (hdψ : ∀ i : Fin n, MemLp (iteratedPartialDeriv [i] ψ) ∞ (domainMeasure n Ω))

/-- The coordinatewise bounded multiplier, before imposing weak derivative identities. -/
def boundedMultiplierAmbient :
    WkpAmbientOn n 1 p Ω →L[ℝ] WkpAmbientOn n 1 p Ω :=
  let P (a : DerivIndex n 1) :=
    PiLp.proj (𝕜 := ℝ) (p := p) (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω) a
  let M := mulLpLeft (p := p) (hψ.toLp ψ)
  let D (i : Fin n) := mulLpLeft (p := p) ((hdψ i).toLp (iteratedPartialDeriv [i] ψ))
  let e := PiLp.continuousLinearEquiv (𝕜 := ℝ) (p := p)
    (β := fun _ : DerivIndex n 1 ↦ DerivLp n p Ω)
  e.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (firstOrderRows
      (M.comp (P (baseIndex n 1)))
      (fun i ↦ M.comp (P (singleDerivIndex n i)) + (D i).comp (P (baseIndex n 1)))))

private theorem boundedMultiplierAmbient_base_ae (U : WkpAmbientOn n 1 p Ω) :
    (boundedMultiplierAmbient hψ hdψ U (baseIndex n 1) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ x * U (baseIndex n 1) x := by
  have hmul := mulLpLeft_apply_ae (p := p) (hψ.toLp ψ) (U (baseIndex n 1))
  filter_upwards [hmul, hψ.coeFn_toLp] with x hx hψx
  simpa [boundedMultiplierAmbient, hψx] using hx

private theorem boundedMultiplierAmbient_deriv_ae
    (U : WkpAmbientOn n 1 p Ω) (i : Fin n) :
    (boundedMultiplierAmbient hψ hdψ U (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ x * U (singleDerivIndex n i) x +
        iteratedPartialDeriv [i] ψ x * U (baseIndex n 1) x := by
  have h₁ := mulLpLeft_apply_ae (p := p) (hψ.toLp ψ) (U (singleDerivIndex n i))
  have h₂ := mulLpLeft_apply_ae (p := p)
    ((hdψ i).toLp (iteratedPartialDeriv [i] ψ)) (U (baseIndex n 1))
  have hadd := Lp.coeFn_add
    (mulLpLeft (p := p) (hψ.toLp ψ) (U (singleDerivIndex n i)))
    (mulLpLeft (p := p) ((hdψ i).toLp (iteratedPartialDeriv [i] ψ)) (U (baseIndex n 1)))
  filter_upwards [h₁, h₂, hadd, hψ.coeFn_toLp, (hdψ i).coeFn_toLp]
    with x hx₁ hx₂ hxadd hψx hdψx
  have hpoint := hxadd.trans (congrArg₂ (· + ·) hx₁ hx₂)
  rw [hψx, hdψx] at hpoint
  simpa [boundedMultiplierAmbient] using hpoint

/-- The smooth Leibniz rule shows that the coordinate multiplier preserves the graph. -/
theorem boundedMultiplierAmbient_mem (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (U : W^{1,p}(Ω)) :
    boundedMultiplierAmbient hψ hdψ U.val ∈ wkpSubmoduleOn n 1 p Ω := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨i, ha⟩
  · subst a
    simpa only [baseIndex_toList] using
      hasWeakDerivativeOn_nil
        (memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out)
  · subst a
    have hweak : HasWeakDerivativeOn Ω [i]
        (U.val (baseIndex n 1)) (U.val (singleDerivIndex n i)) := by
      simpa only [firstDerivIndex_one] using
        U.property.hasWeakDerivativeOn_first (by norm_num) i
    simpa only [singleDerivIndex_toList] using (hasWeakDerivativeOn_congr_ae (α := [i])
      (boundedMultiplierAmbient_base_ae hψ hdψ U.val)
      (boundedMultiplierAmbient_deriv_ae hψ hdψ U.val i)).mpr
      (hasWeakDerivativeOn_mul_contDiff_first
        (Lp.memLp _) (Lp.memLp _) hsm hψ (hdψ i) hweak)

/-- A bounded smooth function with bounded first derivatives is a continuous
multiplier on the first-order Sobolev graph space. -/
def boundedMultiplierCLM (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    W^{1,p}(Ω) →L[ℝ] W^{1,p}(Ω) :=
  ContinuousLinearMap.codRestrict
    ((boundedMultiplierAmbient hψ hdψ).comp
      (Submodule.subtypeL (wkpSubmoduleOn n 1 p Ω)))
    (wkpSubmoduleOn n 1 p Ω)
    (boundedMultiplierAmbient_mem hψ hdψ hsm)

/-- The multiplier acts on the base representative by pointwise multiplication. -/
theorem boundedMultiplierCLM_base_ae (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (U : W^{1,p}(Ω)) :
    baseRepresentative (boundedMultiplierCLM hψ hdψ hsm U)
      =ᵐ[domainMeasure n Ω] fun x ↦ ψ x * baseRepresentative U x :=
  boundedMultiplierAmbient_base_ae hψ hdψ U.val

/-- Its first derivative coordinates obey the weak Leibniz rule. -/
theorem boundedMultiplierCLM_deriv_ae (hsm : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (U : W^{1,p}(Ω)) (i : Fin n) :
    (wkpCoordinateCLM (singleDerivIndex n i) (boundedMultiplierCLM hψ hdψ hsm U) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        ψ x * wkpCoordinateCLM (singleDerivIndex n i) U x +
          iteratedPartialDeriv [i] ψ x * baseRepresentative U x :=
  boundedMultiplierAmbient_deriv_ae hψ hdψ U.val i

end SobolevSpace.GraphSpace
