/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalState

/-!
# First-jet reactions on local energy spaces

The same Lipschitz composition constructs the reaction on each spatial
subdomain. Restriction commutes with the reaction and the weak Laplacian,
so the local H² equation retains its first-derivative dependence.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

/-- Assemble the spatial weak gradient, velocity and displacement on a subdomain. -/
def localFirstJetCLM : (W^{1,2}(Ω) × DerivLp n 2 Ω) →L[ℝ]
    Lp (ℝ^n × ℝ × ℝ) 2 (domainMeasure n Ω) :=
  (ContinuousLinearMap.id ℝ (ℝ^n × ℝ × ℝ)).compLpPair.comp
    ((wkpGradientCLM.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).compLpPair.comp
        ((ContinuousLinearMap.snd ℝ _ _).prod
          (wkpBaseCoordinateCLM.comp (ContinuousLinearMap.fst ℝ _ _)))))

/-- The assembled local jet has the expected representatives almost everywhere. -/
theorem localFirstJetCLM_apply_ae (z : W^{1,2}(Ω) × DerivLp n 2 Ω) :
    (localFirstJetCLM z : ℝ^n → ℝ^n × ℝ × ℝ) =ᵐ[domainMeasure n Ω]
      fun y ↦ (∇ z.1 y, z.2 y, baseRepresentative z.1 y) := by
  change (localFirstJetCLM z : ℝ^n → ℝ^n × ℝ × ℝ) =ᵐ[domainMeasure n Ω]
    fun y ↦ (∇ z.1 y, z.2 y, wkpBaseCoordinateCLM z.1 y)
  have hpair := (ContinuousLinearMap.id ℝ (ℝ × ℝ)).coeFn_compLpPair z.2 (wkpBaseCoordinateCLM z.1)
  have hjet := (ContinuousLinearMap.id ℝ (ℝ^n × ℝ × ℝ)).coeFn_compLpPair
    (∇ z.1) ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).compLpPair (z.2, wkpBaseCoordinateCLM z.1))
  filter_upwards [hpair, hjet] with y hy hz
  simpa only [localFirstJetCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.id_apply, hy] using hz

/-- The first-jet reaction in the local spatial L² space. -/
def localReaction (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : W^{1,2}(Ω) × DerivLp n 2 Ω) : DerivLp n 2 Ω :=
  hf.compLp hf0 (localFirstJetCLM z)

/-- Pointwise identification of the local nonlinear load. -/
theorem localReaction_apply_ae (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (z : W^{1,2}(Ω) × DerivLp n 2 Ω) :
    (localReaction hf hf0 z : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun y ↦ f (∇ z.1 y, z.2 y, baseRepresentative z.1 y) := by
  filter_upwards [hf.coeFn_compLp hf0 (localFirstJetCLM z),
    localFirstJetCLM_apply_ae z] with y hy hz
  exact hy.trans (congrArg f hz)

/-- The local reaction remains Lipschitz on the natural local energy space. -/
theorem localReaction_lipschitz (hf : LipschitzWith L f) (hf0 : f 0 = 0) :
    LipschitzWith (L * ‖localFirstJetCLM (n := n) (Ω := Ω)‖₊) (localReaction (Ω := Ω) hf hf0) :=
  (hf.lipschitzWith_compLp hf0).comp (localFirstJetCLM (n := n) (Ω := Ω)).lipschitzWith

/-- Restriction of a weak gradient preserves its vector representative. -/
theorem gradient_restrict_ae (hΩ : MeasurableSet Ω) (U : H¹(ℝ^n)) :
    (∇ (restrictCLM hΩ (subset_univ Ω) U) : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] (∇ U : ℝ^n → ℝ^n) := by
  have hbig := (wkpGradientCLM_apply_ae U).filter_mono (ae_mono (domainMeasure_le (subset_univ Ω)))
  have hcoord := ae_all_iff.mpr (fun i : Fin n ↦
    restrictCLM_apply_ae hΩ (subset_univ Ω) U (singleDerivIndex n i))
  filter_upwards [wkpGradientCLM_apply_ae (restrictCLM hΩ (subset_univ Ω) U),
    hbig, hcoord] with y hy hz hc
  exact PiLp.ext fun i ↦ (hy i).trans ((hc i).trans (hz i).symm)

/-- Restricting a solution restricts its first-jet reaction. -/
theorem localReaction_restrict (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (hΩ : MeasurableSet Ω) (z : H¹(ℝ^n) × DerivLp n 2 univ) :
    localReaction hf hf0 (restrictStateCLM hΩ z) =
      restrictDerivLp (subset_univ Ω) (reaction hf hf0 z) := by
  apply Lp.ext
  have hr := (reaction_apply_ae hf hf0 z).filter_mono (ae_mono (domainMeasure_le (subset_univ Ω)))
  filter_upwards [localReaction_apply_ae hf hf0 (restrictStateCLM hΩ z),
    restrictDerivLp_apply_ae (subset_univ Ω) (reaction hf hf0 z), hr,
    gradient_restrict_ae hΩ z.1, restrictDerivLp_apply_ae (subset_univ Ω) z.2,
    restrictCLM_apply_ae hΩ (subset_univ Ω) z.1 (baseIndex n 1)] with y hy hz hload hg hv hq
  exact hy.trans ((congrArg f (Prod.ext hg (Prod.ext hv hq))).trans (hload.symm.trans hz.symm))

/-- The local weak Laplacian is the restriction of the whole-space one. -/
theorem laplacian_restrict (hΩ : MeasurableSet Ω) (U : W^{2,2}(ℝ^n)) :
    wkpLaplacianCLM (restrictCLM hΩ (subset_univ Ω) U) =
      restrictDerivLp (subset_univ Ω) (wkpLaplacianCLM U) := by
  simp only [wkpLaplacianCLM_apply, map_sum]
  rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
