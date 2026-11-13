/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.KernelEnergy
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Derivatives
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.Cutoff.LpBound

/-!
# Derivative bounds for the mollified extension

The tangential derivatives are zero-mean kernel fields multiplied by the
cutoff. The normal derivative also contains the derivative of the cutoff.
The fractional boundary norm controls the kernel fields, and its function
coordinate controls this extra term. Together they give an `Lᵖ`
bound for every first partial derivative.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Trace.HalfSpace

open Approximation Fractional

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem cutoff_smul_bound {q : ℝ≥0∞} {f : ℝ^(n + 1) → F}
    (hf : MemLp f q (volume.restrict ℝ^(n + 1)₊)) :
    MemLp (fun z ↦ heightCutoff (splitTangentialNormal z).2 • f z)
        q (volume.restrict ℝ^(n + 1)₊) ∧
      eLpNorm (fun z ↦ heightCutoff (splitTangentialNormal z).2 • f z)
        q (volume.restrict ℝ^(n + 1)₊) ≤ eLpNorm f q (volume.restrict ℝ^(n + 1)₊) := by
  have hc : Continuous (fun z : ℝ^(n + 1) ↦ heightCutoff (splitTangentialNormal z).2) :=
    contDiff_heightCutoff.continuous.comp
      tangentialNormalContinuousLinearEquiv.continuous.snd
  have hbound := eLpNorm_mono_ae (p := q)
    (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z ↦ show
      ‖heightCutoff (splitTangentialNormal z).2 • f z‖ ≤ ‖f z‖ by
        rw [norm_smul, Real.norm_of_nonneg (heightCutoff_nonneg _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (heightCutoff_le_one _))
  exact ⟨hbound.trans_lt hf, hbound⟩

omit [CompleteSpace F] in
/-- The boundary coordinate of fractional data is an `Lᵖ` function on the whole boundary. -/
theorem boundary_memLp
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    MemLp (GagliardoSpace.toLp n (1 - 1 / p) univ g) (ENNReal.ofReal p) volume := by
  simpa only [Measure.restrict_univ] using
    Lp.memLp (GagliardoSpace.toLp n (1 - 1 / p) univ g)

omit [CompleteSpace F] in
private theorem boundary_eLpNorm_le
    (g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F)) :
    eLpNorm (GagliardoSpace.toLp n (1 - 1 / p) univ g) (ENNReal.ofReal p) volume ≤ ‖g‖ₑ := by
  have h : ‖GagliardoSpace.toLp n (1 - 1 / p) univ g‖ₑ ≤ ‖g‖ₑ :=
    WithLp.enorm_fst_le _ g.val
  simpa only [Lp.enorm_def, Measure.restrict_univ] using h

/-- Each first partial of the extension has a uniform bound in terms of the
fractional boundary norm. This includes the normal derivative and dimension zero. -/
theorem exists_pos_partialDeriv_mollifiedExtension_bound (hp : 1 < p)
    (μ : Mollifier n) :
    ∃ C : Fin (n + 1) → ℝ, (∀ i, 0 < C i) ∧
      ∀ g : GagliardoSpace n (1 - 1 / p) univ (p := ENNReal.ofReal p) (F := F),
        ∀ i : Fin (n + 1),
          MemLp (∂[i] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)))
              (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ∧
            eLpNorm (∂[i]
              (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g)))
              (ENNReal.ofReal p) (volume.restrict ℝ^(n + 1)₊) ≤ ENNReal.ofReal (C i) * ‖g‖ₑ := by
  choose B hB hspatial using fun i : Fin n ↦
    exists_pos_spatialDerivativeProfile_bound (F := F) hp μ i
  obtain ⟨D, hD, hnormal⟩ := exists_pos_normalDerivativeProfile_bound (F := F) hp μ
  obtain ⟨A, hA, hcutoff⟩ := exists_pos_deriv_heightCutoff_mollifyVector_bound
    (F := F) (p := ENNReal.ofReal p) μ ENNReal.ofReal_ne_top
  refine ⟨Fin.lastCases (A + D) B, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using add_pos hA hD
    · simpa using hB j
  · intro g i
    have hg := (boundary_memLp g).locallyIntegrable (Fact.out : 1 ≤ ENNReal.ofReal p)
    have hupper := ae_restrict_mem (μ := volume) (HalfSpace.measurableSet_upper (n + 1))
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · obtain ⟨hcut, hcutbound⟩ := hcutoff _ (boundary_memLp g)
      obtain ⟨hfield, hfieldbound⟩ := hnormal g
      obtain ⟨hmul, hmulbound⟩ := cutoff_smul_bound hfield
      have hae :
          ∂[Fin.last n] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            =ᵐ[volume.restrict ℝ^(n + 1)₊]
              (fun z ↦ deriv heightCutoff (splitTangentialNormal z).2 •
                mollifyVector μ (splitTangentialNormal z).2
                  (GagliardoSpace.toLp n (1 - 1 / p) univ g) (splitTangentialNormal z).1) +
              (fun z ↦ heightCutoff (splitTangentialNormal z).2 •
                signedKernelField μ.normalDerivativeProfile
                  (GagliardoSpace.toLp n (1 - 1 / p) univ g) z) := by
        filter_upwards [hupper] with z hz
        have ht : 0 < (splitTangentialNormal z).2 := by
          rw [upper_eq_preimage_split_snd_Ioi] at hz
          exact hz.2
        simpa only [Prod.mk.eta, join_splitTangentialNormal, Pi.add_apply, signedKernelField] using
          partialDeriv_mollifiedExtension_last μ hg ht (splitTangentialNormal z).1
      refine ⟨(memLp_congr_ae hae).2 (hcut.add hmul), ?_⟩
      rw [eLpNorm_congr_ae hae]
      calc
        _ ≤ _ + _ := eLpNorm_add_le (Fact.out : 1 ≤ ENNReal.ofReal p)
        _ ≤ ENNReal.ofReal A * ‖g‖ₑ + ENNReal.ofReal D * ‖g‖ₑ :=
          add_le_add (hcutbound.trans (mul_le_mul' le_rfl (boundary_eLpNorm_le g)))
            (hmulbound.trans hfieldbound)
        _ = _ := by rw [← add_mul, ← ENNReal.ofReal_add hA.le hD.le]; simp
    · obtain ⟨hfield, hfieldbound⟩ := hspatial j g
      obtain ⟨hmul, hmulbound⟩ := cutoff_smul_bound hfield
      have hae :
          ∂[j.castSucc] (mollifiedExtension μ (GagliardoSpace.toLp n (1 - 1 / p) univ g))
            =ᵐ[volume.restrict ℝ^(n + 1)₊] fun z ↦
              heightCutoff (splitTangentialNormal z).2 •
                signedKernelField (μ.spatialDerivativeProfile j)
                  (GagliardoSpace.toLp n (1 - 1 / p) univ g) z := by
        filter_upwards [hupper] with z hz
        have ht : 0 < (splitTangentialNormal z).2 := by
          rw [upper_eq_preimage_split_snd_Ioi] at hz
          exact hz.2
        simpa only [Prod.mk.eta, join_splitTangentialNormal, signedKernelField] using
          partialDeriv_mollifiedExtension_castSucc μ hg ht j (splitTangentialNormal z).1
      refine ⟨(memLp_congr_ae hae).2 hmul, ?_⟩
      rw [eLpNorm_congr_ae hae]
      simpa using hmulbound.trans hfieldbound

end SobolevSpace.Trace.HalfSpace
