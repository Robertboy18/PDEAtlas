/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.WeakDerivative
public import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
public import PDE.Spaces.Sobolev.Fractional.Integer.Reverse
import PDE.Analysis.Evolution.Time.WeakDerivative.Euclidean
import PDE.DistributionTheory.TemperedDistribution.Pushforward

/-!
# Real weak derivatives as tempered-distribution derivatives

The smooth-density theorem for Sobolev graph spaces identifies their derivative
rows with Fourier multipliers. Transporting that identity along the
measure-preserving identification of `ℝ¹` and `ℝ` connects the real weak-derivative
predicate `Evolution.HasWeakTimeDerivativeOn` to tempered-distribution
differentiation.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution FourierTransform
open scoped BesselPotentialSpace SchwartzMap LineDeriv Sobolev

namespace PDE.Analysis

open Evolution SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Fractional

private theorem pushforward_l2_realLine
    (A : (ℝ^1) ≃L[ℝ] ℝ)
    (hA : MeasurePreserving A (volume : Measure (ℝ^1)) volume)
    (u : Lp ℂ 2 (volume : Measure (ℝ^1))) (v : ComplexL2)
    (huv : (u : ℝ^1 → ℂ) =ᵐ[volume] fun x ↦ v (A x)) :
    pushforwardCLM A (u : 𝓢'(ℝ^1, ℂ)) = (v : 𝓢'(ℝ, ℂ)) := by
  ext φ
  simp only [pushforwardCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  rw [← hA.integral_comp A.toHomeomorph.measurableEmbedding (fun x ↦ φ x • v x)]
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  simp [hx]

private theorem pushforward_cxL2_realLine {f : ℝ^1 → ℝ} {g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hfg : f =ᵐ[volume] oneDimensionalPullback g) :
    pushforwardCLM (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) (cxL2 hf : 𝓢'(ℝ^1, ℂ)) =
      (hg.ofReal.toLp (fun x ↦ (g x : ℂ)) : 𝓢'(ℝ, ℂ)) := by
  let e := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm
  have hmp : MeasurePreserving (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))
      (volume : Measure (ℝ^1)) volume :=
    MeasurePreserving.symm e.toHomeomorph.toMeasurableEquiv
      ((PiLp.volume_preserving_toLp (Fin 1)).comp
        ((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _))
  have hfC : MemLp (fun x ↦ (f x : ℂ)) 2 volume := hf.ofReal
  have hgC : MemLp (fun x ↦ (g x : ℂ)) 2 volume := hg.ofReal
  apply pushforward_l2_realLine _ hmp
  filter_upwards [hfC.coeFn_toLp, hfg,
    hmp.quasiMeasurePreserving.ae_eq_comp hgC.coeFn_toLp] with x hx hfgx hgx
  change (hfC.toLp _) x = (hgC.toLp _) ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x)
  change (hgC.toLp _) ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x) =
    (g ((PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) x) : ℂ) at hgx
  rw [hx, hgx, hfgx]
  rfl

/-- A real `L²` weak-derivative pair gives the same derivative after
complexification into tempered distributions. The proof uses smooth density in
Sobolev graph spaces and their Fourier characterization. -/
theorem lineDeriv_toLp_of_hasWeakTimeDerivativeOn {f g : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
    (hw : HasWeakTimeDerivativeOn Set.univ f g) :
    ∂_{(1 : ℝ)} (hf.ofReal.toLp (fun x ↦ (f x : ℂ)) : 𝓢'(ℝ, ℂ)) =
      (hg.ofReal.toLp (fun x ↦ (g x : ℂ)) : 𝓢'(ℝ, ℂ)) := by
  have hrows : ∀ a, HasWeakDerivativeOn (n := 1) Set.univ a.toList
      (oneDimensionalPullback f) (w11Rows f g a) := by
    have hfirst := hw.to_hasWeakDerivativeOn (ContinuousLinearMap.id ℝ ℝ)
    change HasWeakDerivativeOn (n := 1) Set.univ [0]
      (oneDimensionalPullback f) (oneDimensionalPullback g) at hfirst
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · have hlocal := (memLp_oneDimensionalPullback hf).locallyIntegrable
        (by norm_num) |>.locallyIntegrableOn Set.univ
      simpa [w11Rows] using hasWeakDerivativeOn_nil hlocal
    · have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      simpa only [w11Rows, singleDerivIndex_toList, List.cons_ne_nil, ite_false] using hfirst
  let U : W^{1,2}(ℝ^1) :=
    mkWkpSpaceOnOfWeakDerivatives (oneDimensionalPullback f) (w11Rows f g)
      (w11Rows_base f g) (w11Rows_memLp_of_memLp hf hg) hrows
  have hrow (a : DerivIndex 1 1) : coordFun U a =ᵐ[volume] w11Rows f g a := by
    simpa [U, coordFun, domainMeasure] using
      mkWkpSpaceOnOfWeakDerivatives_apply_ae (oneDimensionalPullback f) (w11Rows f g)
        (w11Rows_base f g) (w11Rows_memLp_of_memLp hf hg) hrows a
  have hbase : pushforwardCLM (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)) (baseL2 U : 𝓢'(ℝ^1, ℂ)) =
      (hf.ofReal.toLp (fun x ↦ (f x : ℂ)) : 𝓢'(ℝ, ℂ)) := by
    apply pushforward_cxL2_realLine (memLp_coordFun U _) hf
    simpa [w11Rows] using hrow (baseIndex 1 1)
  have hderiv : pushforwardCLM (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ))
      (pureDerivL2 U 0 : 𝓢'(ℝ^1, ℂ)) =
        (hg.ofReal.toLp (fun x ↦ (g x : ℂ)) : 𝓢'(ℝ, ℂ)) := by
    apply pushforward_cxL2_realLine (memLp_coordFun U _) hg
    simpa [w11Rows] using hrow (topPureDerivIndex 1 1 0)
  have hunit : (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm (1 : ℝ) =
      EuclideanSpace.single (0 : Fin 1) (1 : ℝ) := by
    apply (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).injective
    simp
  rw [← hbase, lineDerivOp_pushforwardCLM, hunit, lineDeriv_baseL2]
  exact hderiv

/-- The real weak-derivative predicate determines the derivative of any complex
`L²` representatives of the input pair. -/
theorem lineDeriv_of_hasWeakTimeDerivativeOn {f g : ℝ → ℝ} {F G : ComplexL2}
    (hw : HasWeakTimeDerivativeOn Set.univ f g)
    (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F)
    (hG : (fun x ↦ (g x : ℂ)) =ᵐ[volume] G) :
    ∂_{(1 : ℝ)} (F : 𝓢'(ℝ, ℂ)) = (G : 𝓢'(ℝ, ℂ)) := by
  have hf : MemLp f 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.comp_memLp' ((Lp.memLp F).ae_eq hF.symm)
  have hg : MemLp g 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.comp_memLp' ((Lp.memLp G).ae_eq hG.symm)
  have hfC : MemLp (fun x ↦ (f x : ℂ)) 2 volume := hf.ofReal
  have hgC : MemLp (fun x ↦ (g x : ℂ)) 2 volume := hg.ofReal
  have hFeq : hfC.toLp _ = F := Lp.ext (hfC.coeFn_toLp.trans hF)
  have hGeq : hgC.toLp _ = G := Lp.ext (hgC.coeFn_toLp.trans hG)
  have h := lineDeriv_toLp_of_hasWeakTimeDerivativeOn hf hg hw
  rwa [hFeq, hGeq] at h

/-- The real parts of the spectral Hilbert transforms of a real `L²` weak pair
again form a real weak pair. No regularity of either Hilbert output is assumed. -/
theorem hasWeakTimeDerivativeOn_re_hilbertTransform_of_weak
    {f g : ℝ → ℝ} {F G : ComplexL2}
    (hw : HasWeakTimeDerivativeOn Set.univ f g)
    (hF : (fun x ↦ (f x : ℂ)) =ᵐ[volume] F)
    (hG : (fun x ↦ (g x : ℂ)) =ᵐ[volume] G) :
    HasWeakTimeDerivativeOn Set.univ
      (fun x ↦ (hilbertTransform F x).re) (fun x ↦ (hilbertTransform G x).re) :=
  hasWeakTimeDerivativeOn_re_hilbertTransform
    (lineDeriv_of_hasWeakTimeDerivativeOn hw hF hG)

end PDE.Analysis
