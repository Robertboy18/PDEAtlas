/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Variation.RetainedEvent

/-!
# Second-jet cancellation on separate branch intervals

The outgoing and incoming branches retain their own closed time intervals and
anchor sections. Both meet the same transverse section at time `e`. Applying the
retained response theorem separately gives corrected families for the same field
`f + P - μ • id`; only their speed neighborhoods are intersected.

Each response uses a supplied propagator for `Df(q)` on its own interval. The
outgoing signed integral cancels the retained old mismatch, and the incoming
Hessian contraction vanishes on the segment from the event to its own anchor.
The section equations then recover full vector cancellation.

All old families, events, intervals, and propagators precede the single correction
`P`. The common-interval theorem at the end is a specialization of this result.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Cancel the actual second jet of two moving-event branches on their own time intervals.

The old event equations place `e` in the interior of each interval. The outgoing
anchor lies at or before `e`, and the incoming anchor lies at or after it. Each
anchor belongs to its own interval; no common slab containing both is needed.

The outgoing Hessian integral has target exactly the negative projected old
second mismatch. Its incoming counterpart uses the retained incoming variation
and vanishes by the supplied contraction identity on `[e, cIn]`. Both entire
initial speed sections, both reference restrictions, and both first speed
variations are preserved. The output mismatch has zero value and two actual zero
speed derivatives. The corrected ODEs hold only on their respective time intervals. -/
theorem exists_two_branch_second_jet_cancellation_on_two_intervals
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {loOut hiOut loIn hiIn cOut e cIn sOut sIn : ℝ}
    (hloOut : loOut ≤ cOut) (hOut : cOut ≤ e)
    (hIn : e ≤ cIn) (hhiIn : cIn ≤ hiIn)
    (Fout Fin : ℝ → ℝ → E)
    (hFout : ContDiff ℝ ∞ Fout.uncurry) (hFin : ContDiff ℝ ∞ Fin.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFoutBase : EqOn (fun t ↦ Fout t 0) q (Icc loOut hiOut))
    (hFinBase : EqOn (fun t ↦ Fin t 0) q (Icc loIn hiIn))
    (hFoutOde : ∀ μ ∈ I₀, ∀ t ∈ Icc loOut hiOut,
      HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t)
    (hFinOde : ∀ μ ∈ I₀, ∀ t ∈ Icc loIn hiIn,
      HasDerivAt (fun s ↦ Fin s μ) (f (Fin t μ) - μ • Fin t μ) t)
    (τout τin : ℝ → ℝ)
    (hτout : ContDiffOn ℝ 2 τout I₀) (hτin : ContDiffOn ℝ 2 τin I₀)
    (hτout0 : τout 0 = e) (hτin0 : τin 0 = e)
    (ell : E →L[ℝ] ℝ)
    (hτoutSection : ∀ μ ∈ I₀,
      τout μ ∈ Ioo loOut hiOut ∧ ell (Fout (τout μ) μ) = ell (q e))
    (hτinSection : ∀ μ ∈ I₀,
      τin μ ∈ Ioo loIn hiIn ∧ ell (Fin (τin μ) μ) = ell (q e))
    (htransverse : ell (f (q e)) ≠ 0)
    (Sout : FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) sOut (Icc loOut hiOut))
    (Sin : FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) sIn (Icc loIn hiIn))
    (L : E →L[ℝ] V)
    (hker : LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (q e)} : Set E))
    (hfirst : HasDerivAt (fun μ ↦ Fout (τout μ) μ - Fin (τin μ) μ) 0 0)
    (P : E → E) (hP : ContDiff ℝ ∞ P)
    (hPzero : ∀ t, P (q t) = 0) (hDPzero : ∀ t, fderiv ℝ P (q t) = 0)
    (houtgoing : (∫ s in cOut..e, L (Sout.propagator e s
      (fderiv ℝ (fderiv ℝ P) (q s) (deriv (Fout s) 0) (deriv (Fout s) 0)))) =
        -L (deriv (deriv (fun μ ↦ Fout (τout μ) μ - Fin (τin μ) μ)) 0))
    (hincoming : ∀ s ∈ Icc e cIn,
      fderiv ℝ (fderiv ℝ P) (q s) (deriv (Fin s) 0) (deriv (Fin s) 0) = 0) :
    ∃ (Gout Gin : ℝ → ℝ → E) (υout υin : ℝ → ℝ) (I : Set ℝ),
      let M : ℝ → E := fun μ ↦ Gout (υout μ) μ - Gin (υin μ) μ
      ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
      IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
      (∀ μ, Gout cOut μ = Fout cOut μ ∧ Gin cIn μ = Fin cIn μ) ∧
      EqOn (fun t ↦ Gout t 0) q (Icc loOut hiOut) ∧
      EqOn (fun t ↦ Gin t 0) q (Icc loIn hiIn) ∧
      (∀ μ ∈ I,
        (∀ t ∈ Icc loOut hiOut,
          HasDerivAt (fun s ↦ Gout s μ)
            (f (Gout t μ) + P (Gout t μ) - μ • Gout t μ) t) ∧
        (∀ t ∈ Icc loIn hiIn,
          HasDerivAt (fun s ↦ Gin s μ)
            (f (Gin t μ) + P (Gin t μ) - μ • Gin t μ) t)) ∧
      ContDiffOn ℝ ∞ υout I ∧ ContDiffOn ℝ ∞ υin I ∧
      υout 0 = e ∧ υin 0 = e ∧
      (∀ μ ∈ I,
        (υout μ ∈ Ioo loOut hiOut ∧ ell (Gout (υout μ) μ) = ell (q e)) ∧
        (υin μ ∈ Ioo loIn hiIn ∧ ell (Gin (υin μ) μ) = ell (q e))) ∧
      EqOn (fun t ↦ deriv (Gout t) 0) (fun t ↦ deriv (Fout t) 0) (Icc loOut hiOut) ∧
      EqOn (fun t ↦ deriv (Gin t) 0) (fun t ↦ deriv (Fin t) 0) (Icc loIn hiIn) ∧
      deriv υout 0 = deriv τout 0 ∧ deriv υin 0 = deriv τin 0 ∧
      M 0 = 0 ∧ HasDerivAt M 0 0 ∧ HasDerivAt (deriv M) 0 0 := by
  -- Each old event gives an interior point in its own native time interval.
  have heOutOpen : e ∈ Ioo loOut hiOut := by
    simpa only [hτout0] using (hτoutSection 0 h0I₀).1
  have heInOpen : e ∈ Ioo loIn hiIn := by
    simpa only [hτin0] using (hτinSection 0 h0I₀).1
  have heOut : e ∈ Icc loOut hiOut := Ioo_subset_Icc_self heOutOpen
  have heIn : e ∈ Icc loIn hiIn := Ioo_subset_Icc_self heInOpen
  have hLv : L (f (q e)) = 0 :=
    LinearMap.mem_ker.mp (hker ▸ Submodule.mem_span_singleton_self _)
  obtain ⟨Gout, υout, Iout, hGout, hIout, h0Iout, hIoutSub,
      hGoutInit, hGoutBase, hGoutOde, hυout, hυout0, hυoutSection,
      hGoutFirst, hυoutFirst, hRout0, hRoutFirst, hRoutSecond, hRoutIntegral⟩ :=
    exists_retained_flow_movingEvent_secondSpeedVariation_response f hf q hq
      ⟨hloOut, hOut.trans heOut.2⟩ Fout hFout I₀ hI₀ h0I₀ hFoutBase hFoutOde τout hτout hτout0
      ell hτoutSection htransverse Sout L hLv P hP hPzero hDPzero
  obtain ⟨Gin, υin, Iin, hGin, hIin, h0Iin, _,
      hGinInit, hGinBase, hGinOde, hυin, hυin0, hυinSection,
      hGinFirst, hυinFirst, hRin0, hRinFirst, hRinSecond, hRinIntegral⟩ :=
    exists_retained_flow_movingEvent_secondSpeedVariation_response f hf q hq
      ⟨heIn.1.trans hIn, hhiIn⟩ Fin hFin I₀ hI₀ h0I₀ hFinBase hFinOde τin hτin hτin0
      ell hτinSection htransverse Sin L hLv P hP hPzero hDPzero
  -- Only speed neighborhoods are intersected; neither time interval is enlarged.
  let I : Set ℝ := Iout ∩ Iin
  have hI : IsOpen I := hIout.inter hIin
  have h0I : (0 : ℝ) ∈ I := ⟨h0Iout, h0Iin⟩
  let Mold : ℝ → E := fun μ ↦ Fout (τout μ) μ - Fin (τin μ) μ
  let Rout : ℝ → E := fun μ ↦ Gout (υout μ) μ - Fout (τout μ) μ
  let Rin : ℝ → E := fun μ ↦ Gin (υin μ) μ - Fin (τin μ) μ
  let M : ℝ → E := fun μ ↦ Gout (υout μ) μ - Gin (υin μ) μ
  have hdecomp : M = fun μ ↦ Mold μ + Rout μ - Rin μ := funext fun μ ↦ by
    dsimp only [M, Mold, Rout, Rin]; abel
  have hMold0 : Mold 0 = 0 := by
    have hout : Fout e 0 = q e := hFoutBase heOut
    have hin : Fin e 0 = q e := hFinBase heIn
    simp only [Mold, hτout0, hτin0, hout, hin, sub_self]
  have hM0 : M 0 = 0 := by
    rw [hdecomp]
    simp only [hMold0, show Rout 0 = 0 from hRout0, show Rin 0 = 0 from hRin0, zero_add, sub_self]
  have hMfirst : HasDerivAt M 0 0 := by
    rw [hdecomp]
    simpa only [zero_add, sub_zero] using (hfirst.fun_add hRoutFirst).fun_sub hRinFirst
  -- The incoming response uses its own propagator and its oriented anchor-to-event integral.
  have hintegral : (∫ s in cIn..e, L (Sin.propagator e s
      (fderiv ℝ (fderiv ℝ P) (q s) (deriv (Fin s) 0) (deriv (Fin s) 0)))) = 0 :=
    (intervalIntegral.integral_congr (g := fun _ ↦ (0 : V)) fun s hs ↦ by
      simp only [hincoming s (uIcc_subset_Icc ⟨hIn, le_rfl⟩ ⟨le_rfl, hIn⟩ hs), map_zero]).trans
      intervalIntegral.integral_zero
  have hLout : L (deriv (deriv Rout) 0) = -L (deriv (deriv Mold) 0) :=
    hRoutIntegral.trans houtgoing
  have hLin : L (deriv (deriv Rin) 0) = 0 := hRinIntegral.trans hintegral
  have heventSmooth {Q : ℝ → ℝ → E} {σ : ℝ → ℝ}
      (hQ : ContDiff ℝ ∞ Q.uncurry) (hσ : ContDiffAt ℝ 2 σ 0) :
      ContDiffAt ℝ 2 (fun μ ↦ Q (σ μ) μ) 0 :=
    (hQ.of_le (by simp) : ContDiff ℝ 2 Q.uncurry).contDiffAt.comp 0 (hσ.prodMk contDiffAt_id)
  have hOldOut := heventSmooth hFout (hτout.contDiffAt (hI₀.mem_nhds h0I₀))
  have hOldIn := heventSmooth hFin (hτin.contDiffAt (hI₀.mem_nhds h0I₀))
  have hNewOut := heventSmooth hGout
    ((hυout.contDiffAt (hIout.mem_nhds h0Iout)).of_le (by simp))
  have hNewIn := heventSmooth hGin
    ((hυin.contDiffAt (hIin.mem_nhds h0Iin)).of_le (by simp))
  have hOldSmooth : ContDiffAt ℝ 2 Mold 0 := hOldOut.sub hOldIn
  have hRoutSmooth : ContDiffAt ℝ 2 Rout 0 := hNewOut.sub hOldOut
  have hRinSmooth : ContDiffAt ℝ 2 Rin 0 := hNewIn.sub hOldIn
  have hMSmooth : ContDiffAt ℝ 2 M 0 := hNewOut.sub hNewIn
  let D : E := deriv (deriv Mold) 0 + deriv (deriv Rout) 0 - deriv (deriv Rin) 0
  have hOldSecond : HasDerivAt (deriv Mold) (deriv (deriv Mold) 0) 0 :=
    (hOldSmooth.derivWithin (m := 1) (by norm_num)).differentiableAt_one.hasDerivAt
  have hderivNear : deriv M =ᶠ[𝓝 (0 : ℝ)]
      fun μ ↦ deriv Mold μ + deriv Rout μ - deriv Rin μ := by
    filter_upwards [hOldSmooth.eventually (by simp), hRoutSmooth.eventually (by simp),
      hRinSmooth.eventually (by simp)] with μ hOldμ hOutμ hInμ
    rw [hdecomp]
    exact (((hOldμ.differentiableAt (by simp)).hasDerivAt.fun_add
      (hOutμ.differentiableAt (by simp)).hasDerivAt).fun_sub
      (hInμ.differentiableAt (by simp)).hasDerivAt).deriv
  have hMsecond : HasDerivAt (deriv M) D 0 :=
    ((hOldSecond.fun_add hRoutSecond.differentiableAt.hasDerivAt).fun_sub
      hRinSecond.differentiableAt.hasDerivAt).congr_of_eventuallyEq hderivNear
  have hLD : L D = 0 := by
    simp only [D, map_sub, map_add, hLout, hLin, add_neg_cancel, sub_zero]
  -- Both corrected moving points stay in the same affine section. Differentiating
  -- that actual identity twice removes the remaining tangent component.
  have hsection : (fun μ ↦ ell (M μ)) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [hI.mem_nhds h0I] with μ hμ
    simp only [M, map_sub, (hυoutSection μ hμ.1).2,
      (hυinSection μ hμ.2).2, sub_self]
  have hsectionD : (fun μ ↦ ell (deriv M μ)) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 := by
    filter_upwards [hMSmooth.eventually (by simp), hsection.eventually_nhds] with μ hMμ hμ
    exact (ell.hasFDerivAt.comp_hasDerivAt μ
      (hMμ.differentiableAt (by simp)).hasDerivAt).unique
        ((hasDerivAt_const μ (0 : ℝ)).congr_of_eventuallyEq hμ)
  have hellD : ell D = 0 :=
    (ell.hasFDerivAt.comp_hasDerivAt 0 hMsecond).unique
      ((hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq hsectionD)
  have hDzero : D = 0 := by
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      (hker ▸ LinearMap.mem_ker.mpr hLD : D ∈ Submodule.span ℝ {f (q e)})
    rw [← ha, map_smul, smul_eq_mul] at hellD
    rw [← ha, (mul_eq_zero.mp hellD).resolve_right htransverse, zero_smul]
  exact ⟨Gout, Gin, υout, υin, I, hGout, hGin, hI, h0I, fun μ hμ ↦ hIoutSub hμ.1,
    fun μ ↦ ⟨hGoutInit μ, hGinInit μ⟩, hGoutBase, hGinBase,
    fun μ hμ ↦ ⟨hGoutOde μ hμ.1, hGinOde μ hμ.2⟩,
    hυout.mono inter_subset_left, hυin.mono inter_subset_right, hυout0, hυin0,
    fun μ hμ ↦ ⟨hυoutSection μ hμ.1, hυinSection μ hμ.2⟩,
    hGoutFirst, hGinFirst, hυoutFirst, hυinFirst, hM0, hMfirst, hMsecond.congr_deriv hDzero⟩

/-- The common-interval statement is recovered by using the same interval and
propagator twice. Its hypotheses and conclusions are unchanged. -/
theorem exists_two_branch_second_jet_cancellation
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {lo hi cOut e cIn s₀ : ℝ}
    (hlo : lo ≤ cOut) (hOut : cOut ≤ e) (hIn : e ≤ cIn) (hhi : cIn ≤ hi)
    (Fout Fin : ℝ → ℝ → E)
    (hFout : ContDiff ℝ ∞ Fout.uncurry) (hFin : ContDiff ℝ ∞ Fin.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFoutBase : EqOn (fun t ↦ Fout t 0) q (Icc lo hi))
    (hFinBase : EqOn (fun t ↦ Fin t 0) q (Icc lo hi))
    (hFoutOde : ∀ μ ∈ I₀, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t)
    (hFinOde : ∀ μ ∈ I₀, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ Fin s μ) (f (Fin t μ) - μ • Fin t μ) t)
    (τout τin : ℝ → ℝ)
    (hτout : ContDiffOn ℝ 2 τout I₀) (hτin : ContDiffOn ℝ 2 τin I₀)
    (hτout0 : τout 0 = e) (hτin0 : τin 0 = e)
    (ell : E →L[ℝ] ℝ)
    (hτoutSection : ∀ μ ∈ I₀,
      τout μ ∈ Ioo lo hi ∧ ell (Fout (τout μ) μ) = ell (q e))
    (hτinSection : ∀ μ ∈ I₀,
      τin μ ∈ Ioo lo hi ∧ ell (Fin (τin μ) μ) = ell (q e))
    (htransverse : ell (f (q e)) ≠ 0)
    (S : FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) s₀ (Icc lo hi))
    (L : E →L[ℝ] V)
    (hker : LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (q e)} : Set E))
    (hfirst : HasDerivAt (fun μ ↦ Fout (τout μ) μ - Fin (τin μ) μ) 0 0)
    (P : E → E) (hP : ContDiff ℝ ∞ P)
    (hPzero : ∀ t, P (q t) = 0) (hDPzero : ∀ t, fderiv ℝ P (q t) = 0)
    (houtgoing : (∫ s in cOut..e, L (S.propagator e s
      (fderiv ℝ (fderiv ℝ P) (q s) (deriv (Fout s) 0) (deriv (Fout s) 0)))) =
        -L (deriv (deriv (fun μ ↦ Fout (τout μ) μ - Fin (τin μ) μ)) 0))
    (hincoming : ∀ s ∈ Icc e cIn,
      fderiv ℝ (fderiv ℝ P) (q s) (deriv (Fin s) 0) (deriv (Fin s) 0) = 0) :
    ∃ (Gout Gin : ℝ → ℝ → E) (υout υin : ℝ → ℝ) (I : Set ℝ),
      let M : ℝ → E := fun μ ↦ Gout (υout μ) μ - Gin (υin μ) μ
      ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
      IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
      (∀ μ, Gout cOut μ = Fout cOut μ ∧ Gin cIn μ = Fin cIn μ) ∧
      EqOn (fun t ↦ Gout t 0) q (Icc lo hi) ∧
      EqOn (fun t ↦ Gin t 0) q (Icc lo hi) ∧
      (∀ μ ∈ I, ∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ Gout s μ)
          (f (Gout t μ) + P (Gout t μ) - μ • Gout t μ) t ∧
        HasDerivAt (fun s ↦ Gin s μ)
          (f (Gin t μ) + P (Gin t μ) - μ • Gin t μ) t) ∧
      ContDiffOn ℝ ∞ υout I ∧ ContDiffOn ℝ ∞ υin I ∧
      υout 0 = e ∧ υin 0 = e ∧
      (∀ μ ∈ I,
        (υout μ ∈ Ioo lo hi ∧ ell (Gout (υout μ) μ) = ell (q e)) ∧
        (υin μ ∈ Ioo lo hi ∧ ell (Gin (υin μ) μ) = ell (q e))) ∧
      EqOn (fun t ↦ deriv (Gout t) 0) (fun t ↦ deriv (Fout t) 0) (Icc lo hi) ∧
      EqOn (fun t ↦ deriv (Gin t) 0) (fun t ↦ deriv (Fin t) 0) (Icc lo hi) ∧
      deriv υout 0 = deriv τout 0 ∧ deriv υin 0 = deriv τin 0 ∧
      M 0 = 0 ∧ HasDerivAt M 0 0 ∧ HasDerivAt (deriv M) 0 0 := by
  obtain ⟨Gout, Gin, υout, υin, I, hGout, hGin, hI, h0I, hISub, hinit,
      hGoutBase, hGinBase, hode, hrest⟩ :=
    exists_two_branch_second_jet_cancellation_on_two_intervals f hf q hq
      hlo hOut hIn hhi Fout Fin hFout hFin I₀ hI₀ h0I₀
      hFoutBase hFinBase hFoutOde hFinOde τout τin hτout hτin hτout0 hτin0
      ell hτoutSection hτinSection htransverse S S L hker hfirst
      P hP hPzero hDPzero houtgoing hincoming
  exact ⟨Gout, Gin, υout, υin, I, hGout, hGin, hI, h0I, hISub, hinit, hGoutBase, hGinBase,
    fun μ hμ t ht ↦ ⟨(hode μ hμ).1 t ht, (hode μ hμ).2 t ht⟩, hrest⟩

end PDE.Analysis.ODE
