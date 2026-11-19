/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Lipschitz
public import PDE.Spaces.Sobolev.Calculus.Composition.VectorValued.Nemytskii
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Continuity of the wave source in H¹

The weak chain rule and continuity of superposition on finite-exponent `Lp`
spaces give continuity of composition on `W^{1,p}`. In particular, a `C¹`,
globally Lipschitz scalar nonlinearity fixing zero preserves whole-space H¹.
The resulting lift of the wave source agrees with the L² source.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Φ : E → F} {C : ℝ≥0}

/-- Bounded, continuous derivatives give a continuous composition operator
on first-order Sobolev spaces at every finite normed exponent. -/
theorem continuous_composition (hp : p ≠ ∞) (hΦ : ContDiff ℝ 1 Φ)
    (hzero : Φ 0 = 0) (hbound : ∀ z, ‖fderiv ℝ Φ z‖ ≤ C) :
    Continuous (composition (Ω := Ω) (p := p) hΦ hzero hbound) := by
  apply continuous_induced_rng.mpr
  apply (PiLp.homeomorph p (fun _ : DerivIndex n 1 ↦
    Lp F p (domainMeasure n Ω))).symm.continuous.comp
  refine continuous_pi fun a ↦ ?_
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · have h := (continuous_valueSuperposition (μ := domainMeasure n Ω)
      hp hΦ hzero hbound).comp (coordinateCLM (baseIndex n 1)).continuous
    refine h.congr fun U ↦ ?_
    apply Lp.ext
    exact (Lp.coeFn_superposition _ _ _).trans (composition_base_ae hΦ hzero hbound U).symm
  · have h := (continuous_chainSuperposition (μ := domainMeasure n Ω)
      hp hΦ hbound).comp (valueDerivativeCLM i).continuous
    refine h.congr fun U ↦ ?_
    apply Lp.ext
    filter_upwards [Lp.coeFn_superposition (fun _ : ℝ^n ↦ chainIntegrand Φ)
      (memLp_chainIntegrand (p := p) (μ := domainMeasure n Ω) hΦ hbound) (valueDerivativeCLM i U),
      valueDerivativeCLM_apply_ae U i,
      composition_derivative_ae hΦ hzero hbound U i] with x hx hpair hderiv
    exact hx.trans ((congrArg (chainIntegrand Φ) hpair).trans hderiv.symm)

end SobolevSpace.VectorValued

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : ℝ → ℝ} {L : NNReal}

/-- The scalar nonlinearity lifted to H¹ by the weak chain rule. -/
def compositionH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u : H¹(ℝ^n)) : H¹(ℝ^n) :=
  VectorValued.scalarEquiv (Ω := ⊤) (VectorValued.composition hreg hf0
    (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hf)
    ((VectorValued.scalarEquiv (Ω := ⊤)).symm u))

/-- The H¹ lift varies continuously with the displacement. -/
theorem continuous_compositionH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0) (hreg : ContDiff ℝ 1 f) :
    Continuous (compositionH1 (n := n) hf hf0 hreg) :=
  (VectorValued.scalarEquiv (Ω := ⊤)).continuous.comp
    ((VectorValued.continuous_composition (p := 2) (Ω := ⊤) (by simp) hreg hf0
      (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hf)).comp
      (VectorValued.scalarEquiv (Ω := ⊤)).symm.continuous)

/-- The H¹ construction has exactly the L² composition used by the energy equation. -/
theorem inclusion_compositionH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u : H¹(ℝ^n)) :
    (energyTriple n).inclusion (compositionH1 hf hf0 hreg u) =
      hf.compLp hf0 ((energyTriple n).inclusion u) := by
  apply Lp.ext
  exact (VectorValued.composition_base_ae hreg hf0 (fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hf)
      ((VectorValued.scalarEquiv (Ω := ⊤)).symm u)).trans
      (hf.coeFn_compLp hf0 ((energyTriple n).inclusion u)).symm

/-- The mass-canceling source as an H¹ function. -/
def sourceH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u : H¹(ℝ^n)) : H¹(ℝ^n) :=
  u - compositionH1 hf hf0 hreg u

/-- The lifted source is continuous in H¹. -/
theorem continuous_sourceH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0) (hreg : ContDiff ℝ 1 f) :
    Continuous (sourceH1 (n := n) hf hf0 hreg) :=
  continuous_id.sub (continuous_compositionH1 hf hf0 hreg)

/-- Forgetting one derivative recovers the original energy-space source. -/
theorem inclusion_sourceH1 (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hreg : ContDiff ℝ 1 f) (u : H¹(ℝ^n)) :
    (energyTriple n).inclusion (sourceH1 hf hf0 hreg u) = source hf hf0 u := by
  rw [sourceH1, map_sub, inclusion_compositionH1]
  rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy
