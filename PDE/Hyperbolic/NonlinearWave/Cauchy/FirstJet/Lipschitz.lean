/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Products
public import PDE.Hyperbolic.NonlinearWave.Cauchy.EnergySolution

/-!
# First-derivative-dependent wave forcing on the energy space

The weak gradient, velocity and displacement assemble into one L² field with
values in `ℝ^n × ℝ × ℝ`. Mathlib's Lipschitz composition operator then constructs
`f(Du, v, u)` for arbitrary energy data. The source `u - f(Du, v, u)` cancels
the mass in the wave generator.

This is the whole-space energy construction needed for Theorem 1 of Evans, §12.2.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.2.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- The spatial weak gradient, time velocity and displacement, in that order,
assembled as a single L² field. -/
def firstJetCLM : (H¹(ℝ^n) × DerivLp n 2 univ) →L[ℝ]
    Lp (ℝ^n × ℝ × ℝ) 2 (domainMeasure n univ) :=
  (ContinuousLinearMap.id ℝ (ℝ^n × ℝ × ℝ)).compLpPair.comp
    ((wkpGradientCLM.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).compLpPair.comp
        ((ContinuousLinearMap.snd ℝ _ _).prod
          ((energyTriple n).inclusion.comp (ContinuousLinearMap.fst ℝ _ _)))))

/-- Assembly preserves the pointwise first jet almost everywhere. -/
theorem firstJetCLM_apply_ae (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (firstJetCLM z : ℝ^n → ℝ^n × ℝ × ℝ) =ᵐ[domainMeasure n univ]
      fun x ↦ (∇ z.1 x, z.2 x, (energyTriple n).inclusion z.1 x) := by
  have hpair := (ContinuousLinearMap.id ℝ (ℝ × ℝ)).coeFn_compLpPair
    z.2 ((energyTriple n).inclusion z.1)
  have hjet := (ContinuousLinearMap.id ℝ (ℝ^n × ℝ × ℝ)).coeFn_compLpPair
    (∇ z.1) ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).compLpPair (z.2, (energyTriple n).inclusion z.1))
  filter_upwards [hpair, hjet] with x hx hy
  simpa only [firstJetCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.id_apply, hx] using hy

/-- The first-derivative reaction in spatial L². -/
def reaction (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) : DerivLp n 2 univ :=
  hf.compLp hf0 (firstJetCLM z)

/-- The reaction is the expression `f(Du, v, u)`, with Sobolev weak
spatial derivatives and the velocity component. -/
theorem reaction_apply_ae (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    (reaction hf hf0 z : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
      fun x ↦ f (∇ z.1 x, z.2 x, (energyTriple n).inclusion z.1 x) := by
  filter_upwards [hf.coeFn_compLp hf0 (firstJetCLM z), firstJetCLM_apply_ae z] with x hx hy
  exact hx.trans (congrArg f hy)

/-- First-derivative dependence remains globally Lipschitz in the natural
energy norm. No second spatial derivative is needed. -/
theorem reaction_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    LipschitzWith (L * ‖firstJetCLM (n := n)‖₊) (reaction hf hf0) :=
  (hf.lipschitzWith_compLp hf0).comp firstJetCLM.lipschitzWith

/-- The mass-canceling source in the massive wave evolution. -/
def source (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : H¹(ℝ^n) × DerivLp n 2 univ) : DerivLp n 2 univ :=
  (energyTriple n).inclusion z.1 - reaction hf hf0 z

/-- A global Lipschitz bound for the mass-canceling first-jet source. -/
theorem source_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    LipschitzWith (‖(energyTriple n).inclusion‖₊ + L * ‖firstJetCLM (n := n)‖₊)
      (source hf hf0) := by
  have h := ((energyTriple n).inclusion.lipschitzWith.comp
    LipschitzWith.prod_fst).sub (reaction_lipschitz hf hf0)
  apply h.weaken
  exact le_of_eq (congrArg (fun K ↦ K + L * ‖firstJetCLM (n := n)‖₊)
    (mul_one ‖(energyTriple n).inclusion‖₊))

/-- The first-jet vector field in the energy Hilbert coordinates. -/
def nonlinearMap (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    C(EnergyState n, EnergyState n) where
  toFun z := (C).symm (0, source hf hf0 (C z))
  continuous_toFun := (C).symm.continuous.comp
    (continuous_const.prodMk ((source_lipschitz hf hf0).continuous.comp (C).continuous))

/-- Global Lipschitz forcing allows the semigroup iteration and
infinite-lifetime theorem to be used without a regularity loss. -/
theorem nonlinearMap_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    ∃ K : NNReal, LipschitzWith K (nonlinearMap hf hf0) := by
  have h := (C).symm.toContinuousLinearMap.lipschitzWith.comp
    ((LipschitzWith.const (0 : H¹(ℝ^n))).prodMk
      ((source_lipschitz hf hf0).comp (C).toContinuousLinearMap.lipschitzWith))
  exact ⟨_, h⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
