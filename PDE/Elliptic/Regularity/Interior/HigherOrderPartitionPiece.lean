/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Domain
import PDE.Elliptic.Regularity.Global.PrincipalHigher
import PDE.Elliptic.Regularity.Localization.HigherOrderCutoffEquation
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
public import PDE.Spaces.Sobolev.Boundary.Atlas.Cutoffs -- shake: keep
public import PDE.Elliptic.Variational.DivergenceForm

/-!
# Arbitrary-order interior partition successor

The interior partition function is compactly supported in the physical domain. Localizing the weak
equation preserves the forcing order, while the explicit weak Leibniz rows show that every first
derivative of the localized field has zero trace. The principal higher-regularity successor can
therefore be applied without a boundary argument.

This supplies the interior term of the covering argument for higher boundary regularity. Evans's
proof of §6.3.2, Theorem 5 straightens the boundary as in the proof of Theorem 4, which covers the
boundary by finitely many sets and adds the interior estimate to the boundary ones. The partition of
unity is ours.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.3.2, step 10 of the proof of Theorem 4, p. 340, and
  Theorem 5 (Higher boundary regularity) and step 5 of its proof, pp. 340-343.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (iteratedPartialDeriv)

@[expose] public section

open PDE (partialDeriv)

open scoped Sobolev

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open CompactSupportLocalization
open scoped ENNReal

variable {n : ℕ}

private def firstDerivativeRepresentative
    {m : ℕ} (hm : 2 ≤ m) {Omega : Set (ℝ^n)}
    (i : Fin n) (U : W^{m,2}(Omega)) : ℝ^n → ℝ :=
  (((derivativeWordCLM
        (n := n) (m := m) (r := 1) (p := 2) (Ω := Omega)
        [i] (by simpa using hm) U :
      W^{1,2}(Omega)) :
    WkpAmbientOn n 1 2 Omega) (baseIndex n 1) :
      DerivLp n 2 Omega)

private theorem exists_localized_with_firstDerivatives_mem_H10
    {m : ℕ} (hm : 2 ≤ m) {Omega : Set (ℝ^n)}
    (hOpen : IsOpen Omega)
    (rho : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hrhoOmega : tsupport rho.toFun ⊆ Omega)
    (U : W^{m,2}(Omega)) :
    ∃ W : W^{m,2}(Omega),
      (((((W : WkpAmbientOn n m 2 Omega) (baseIndex n m) :
          DerivLp n 2 Omega) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Omega]
        fun x ↦ rho.toFun x *
          (((U : WkpAmbientOn n m 2 Omega) (baseIndex n m) :
            DerivLp n 2 Omega) : ℝ^n → ℝ) x) ∧
      (∀ i : Fin n,
        derivativeWordCLM
            (n := n) (m := m) (r := 1) (p := 2) (Ω := Omega)
            [i] (by simp; omega) W ∈
          (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule) ∧
      ∀ i : Fin n,
        (tsupport rho.toFun).indicator
            (firstDerivativeRepresentative (by omega) i W)
          =ᵐ[domainMeasure n Omega]
            firstDerivativeRepresentative (by omega) i W := by
  classical
  have hm1 : 1 ≤ m := by omega
  let W := HigherOrderLocalizedCutoff.extendByCutoff hOpen (Subset.rfl : Omega ⊆ Omega) rho
    hrhoOmega U
  have hWrows (i : Fin n) : (((W : WkpAmbientOn n m 2 Omega) (firstDerivIndex n m hm1 i) :
      DerivLp n 2 Omega) : ℝ^n → ℝ) =ᵐ[domainMeasure n Omega]
        weakLeibnizExpansion rho.toFun (wkpWordRepresentative U) [i] := by
    simpa using HigherOrderLocalizedCutoff.extendByCutoff_coordinate_ae hOpen
      (Subset.rfl : Omega ⊆ Omega) rho hrhoOmega U (firstDerivIndex n m hm1 i)
  have hWbase := HigherOrderLocalizedCutoff.extendByCutoff_base_ae hOpen
    (Subset.rfl : Omega ⊆ Omega) rho hrhoOmega U
  refine ⟨W, hWbase, fun i ↦ ?_, fun i ↦
    HigherOrderLocalizedCutoff.indicator_eq_self_of_ae_eq_weakLeibnizExpansion U rho [i] _
      (by simpa [firstDerivativeRepresentative] using hWrows i)⟩
  let U0 : W^{1,2}(Omega) := lowerOrderCLM (n := n) (p := 2) (Ω := Omega) hm1 U
  let Ui : W^{1,2}(Omega) :=
    derivativeWordCLM (n := n) (m := m) (r := 1) (p := 2) (Ω := Omega) [i] (by simp; omega) U
  let drho : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) rho
  have hdrhoFun : drho.toFun = fun x ↦ (∂[i] rho.toFun) x := by
    funext x
    change (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ)) rho :
      𝓓((⊤ : Opens (ℝ^n)), ℝ)) x = _
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp),
      (rho.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp only [partialDeriv, TestFunction.toFun_eq_coe]
  have hdrhoOmega : tsupport drho.toFun ⊆ Omega := by
    rw [hdrhoFun]
    simpa only [partialDeriv] using (tsupport_fderiv_apply_subset ℝ (f := rho.toFun)
      (EuclideanSpace.single i (1 : ℝ))).trans hrhoOmega
  have hWi : derivativeWordCLM (n := n) (m := m) (r := 1) (p := 2) (Ω := Omega) [i]
      (by simp; omega) W = cutoffCLM (n := n) (p := 2) (Ω := Omega) rho Ui +
        cutoffCLM (n := n) (p := 2) (Ω := Omega) drho U0 := by
    apply WkpSpaceOn.ext_of_base_ae hOpen
    have hrow : baseRepresentative (derivativeWordCLM (n := n) (m := m) (r := 1) (p := 2)
        (Ω := Omega) [i] (by simp; omega) W) =ᵐ[domainMeasure n Omega]
          fun x ↦ rho.toFun x * baseRepresentative Ui x +
            (∂[i] rho.toFun) x * baseRepresentative U0 x := by
      have h := hWrows i
      rw [show weakLeibnizExpansion rho.toFun (wkpWordRepresentative U) [i] = fun x ↦
          rho.toFun x * baseRepresentative Ui x + (∂[i] rho.toFun) x * baseRepresentative U0 x by
        funext x
        simp [weakLeibnizExpansion, derivativeSplits, iteratedPartialDeriv, Ui, U0,
          derivIndexOfList_singleton, wkpWordRepresentative, hm1, baseRepresentative]] at h
      simpa [baseRepresentative] using h
    filter_upwards [hrow, cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Omega) rho Ui,
      cutoffCLM_base_apply_ae (n := n) (p := 2) (Ω := Omega) drho U0,
      baseRepresentative_add_ae (cutoffCLM (n := n) (p := 2) (Ω := Omega) rho Ui)
        (cutoffCLM (n := n) (p := 2) (Ω := Omega) drho U0)] with x hprod hfst hsnd hsum
    simp only [baseRepresentative] at hprod hsum ⊢
    rw [hprod, hsum, hfst, hsnd, hdrhoFun]
  rw [hWi]
  exact (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule.add_mem
    (cutoffCLM_mem_H10 hOpen rho hrhoOmega Ui) (cutoffCLM_mem_H10 hOpen drho hdrhoOmega U0)

private theorem exists_wkpSpaceOn_of_ae_supported_of_local
    {m : ℕ} {Omega V K : Set (ℝ^n)}
    (hVopen : IsOpen V) (hVOmega : V ⊆ Omega)
    (hKcompact : IsCompact K) (hKV : K ⊆ V)
    (f : ℝ^n → ℝ)
    (hfSupport : K.indicator f =ᵐ[domainMeasure n Omega] f)
    (U : W^{m,2}(V))
    (hU :
      ((((U : WkpAmbientOn n m 2 V) (baseIndex n m) :
          DerivLp n 2 V) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n V] f) :
    ∃ W : W^{m,2}(Omega),
      ((((W : WkpAmbientOn n m 2 Omega) (baseIndex n m) :
          DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega] f := by
  classical
  obtain ⟨chi, hchiV, hchiOne, -, -⟩ := TestFunction.exists_eq_one_on_compact hVopen hKcompact hKV
  refine ⟨HigherOrderLocalizedCutoff.extendByCutoff hVopen hVOmega chi hchiV U, ?_⟩
  have hW := HigherOrderLocalizedCutoff.extendByCutoff_base_ae hVopen hVOmega chi hchiV U
  simp only [baseRepresentative] at hW
  apply ae_of_ae_restrict_of_ae_restrict_compl V
  · have hUV : ∀ᵐ x ∂(domainMeasure n Omega).restrict V,
        (((U : WkpAmbientOn n m 2 V) (baseIndex n m) : DerivLp n 2 V) : ℝ^n → ℝ) x = f x := by
      rwa [show (domainMeasure n Omega).restrict V = domainMeasure n V by
        simpa [domainMeasure] using Measure.restrict_restrict_of_subset (μ := volume) hVOmega]
    filter_upwards [ae_restrict_of_ae hW, hUV, ae_restrict_of_ae hfSupport] with x hxW hxU hxS
    rw [hxW, hxU]
    by_cases hxK : x ∈ K
    · rw [hchiOne x hxK, one_mul]
    · rw [Set.indicator_of_notMem hxK] at hxS
      rw [← hxS, mul_zero]
  · filter_upwards [ae_restrict_of_ae hW, ae_restrict_of_ae hfSupport,
      ae_restrict_mem hVopen.measurableSet.compl] with x hxW hxS hxV
    rw [hxW, image_eq_zero_of_notMem_tsupport fun h ↦ hxV (hchiV h), zero_mul, ← hxS,
      Set.indicator_of_notMem fun h ↦ hxV (hKV h)]

/--
Arbitrary-order interior regularity after compactly supported localization.

For positive forcing order `k`, a prior `W^{k+1,2}` representative of a
general interior weak solution is multiplied by a smooth cutoff supported in
the domain. It is enough to assume the preceding-order theorem locally near
compact subsets: each differentiated localized field is supported in the
cutoff support, so its local representative can be globalized without changing
the field.
-/
theorem exists_interior_higherOrder_localized_succ_of_local_previous
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOpen : IsOpen Omega)
    (rho : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hrhoOmega : tsupport rho.toFun ⊆ Omega)
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (F : W^{k,2}(Omega))
    (u : H¹(Omega))
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
        DerivLp n 2 Omega)
      u)
    (U : W^{k + 1,2}(Omega))
    (hU :
      ((((U : WkpAmbientOn n (k + 1) 2 Omega)
        (baseIndex n (k + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega]
          ⇑((u : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega))
    (hprevious :
      ∀ (G0 : W^{k - 1,2}(Omega))
        (v : H¹₀(Omega)),
        IsWeakDivergenceSolution
          (n := n) (Ω := Omega)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := k) (m := k + 1) (p := ∞)
                (Ω := Omega) (by omega) (A i j) :
                  WkpAmbientOn n k ∞ Omega)
              (baseIndex n k) : DerivLp n ∞ Omega))
          ((G0 : WkpAmbientOn n (k - 1) 2 Omega)
            (baseIndex n (k - 1)) : DerivLp n 2 Omega)
          v →
        ∀ K : Set (ℝ^n), IsCompact K → K ⊆ Omega →
          ∃ V : Set (ℝ^n), IsOpen V ∧ K ⊆ V ∧ V ⊆ Omega ∧
            ∃ W : W^{k + 1,2}(V),
              ⇑((W : WkpAmbientOn n (k + 1) 2 V)
                  (baseIndex n (k + 1)) : DerivLp n 2 V)
                =ᵐ[domainMeasure n V]
                  ⇑((h10SubtypeL (n := n) (Ω := Omega) v :
                      WkpAmbientOn n 1 2 Omega)
                    (baseIndex n 1) : DerivLp n 2 Omega)) :
    ∃ W : W^{k + 2,2}(Omega),
      ⇑((W : WkpAmbientOn n (k + 2) 2 Omega)
          (baseIndex n (k + 2)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦
          rho.toFun x *
            ⇑((u : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) x := by
  classical
  obtain _ | r := k
  · omega
  have hU1 : lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) U = (u : H¹(Omega)) :=
    WkpSpaceOn.ext_of_base_ae hOpen _ _ (by simpa using hU)
  obtain ⟨w, hw, G, -, hGw⟩ := exists_localized_interiorWeakDivergenceSolution_higher (r + 1)
    (by omega) A F U (by rwa [hU1]) rho hrhoOmega
  obtain ⟨Uloc, hUlocBase, hUlocTrace, hUlocSupport⟩ :=
    exists_localized_with_firstDerivatives_mem_H10 (m := r + 2) (by omega) hOpen rho hrhoOmega U
  have hUloc1 : lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) Uloc = (w : H¹(Omega)) := by
    refine WkpSpaceOn.ext_of_base_ae hOpen _ _ ?_
    filter_upwards [hUlocBase, hw] with x h1 h2
    simpa [h1, baseCoordCLM_apply] using h2.symm
  have htrace0 : lowerOrderCLM (n := n) (p := 2) (Ω := Omega) (by omega) Uloc ∈
      (h10SubmoduleOn (n := n) (Ω := Omega)).toSubmodule := hUloc1 ▸ w.property
  choose D hD using fun i : Fin n ↦
    exists_coordinateDerivative_higherOrder_weakEquation_solution (r := r) hOpen A G Uloc i
      htrace0 (hUlocTrace i) (by convert hGw using 1; exact Subtype.ext hUloc1)
  have hKcompact : IsCompact (tsupport rho.toFun) := by
    simpa [HasCompactSupport] using rho.hasCompactSupport
  have hglobal (i : Fin n) : ∃ V : W^{r + 2,2}(Omega),
      ⇑((V : WkpAmbientOn n (r + 2) 2 Omega) (baseIndex n (r + 2)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega] firstDerivativeRepresentative (by omega) i Uloc := by
    obtain ⟨N, hNopen, hKN, hNOmega, localW, hlocalW⟩ :=
      hprevious (D i) _ (hD i) (tsupport rho.toFun) hKcompact hrhoOmega
    exact exists_wkpSpaceOn_of_ae_supported_of_local hNopen hNOmega hKcompact hKN _
      (hUlocSupport i) localW (by simpa [firstDerivativeRepresentative, derivativeWordCLM_apply,
        derivIndexOfList_singleton] using hlocalW)
  choose V hV using hglobal
  obtain ⟨W, hW⟩ := exists_succOrder_of_firstDerivatives (n := n) (m := r + 2) (p := 2)
    (Ω := Omega) (by simp) Uloc V fun i ↦
      Lp.ext (by simpa [firstDerivativeRepresentative] using hV i)
  refine ⟨W, hW.trans ?_⟩
  filter_upwards [hUlocBase, hU] with x hloc hglobal
  rw [hloc, hglobal]

/--
Global preceding-order regularity implies the compact-local successor.

This is the form used by the smooth-boundary
bootstrap. The local theorem above is stronger; here the regularity
neighborhood is the whole domain.
-/
theorem exists_interior_higherOrder_localized_succ_of_previous
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOpen : IsOpen Omega)
    (rho : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (hrhoOmega : tsupport rho.toFun ⊆ Omega)
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (F : W^{k,2}(Omega))
    (u : H¹(Omega))
    (hu : IsInteriorWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
        DerivLp n 2 Omega)
      u)
    (U : W^{k + 1,2}(Omega))
    (hU :
      ((((U : WkpAmbientOn n (k + 1) 2 Omega)
        (baseIndex n (k + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega]
          ⇑((u : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega))
    (hprevious :
      ∀ (G0 : W^{k - 1,2}(Omega))
        (v : H¹₀(Omega)),
        IsWeakDivergenceSolution
          (n := n) (Ω := Omega)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := k) (m := k + 1) (p := ∞)
                (Ω := Omega) (by omega) (A i j) :
                  WkpAmbientOn n k ∞ Omega)
              (baseIndex n k) : DerivLp n ∞ Omega))
          ((G0 : WkpAmbientOn n (k - 1) 2 Omega)
            (baseIndex n (k - 1)) : DerivLp n 2 Omega)
          v →
        ∃ V : W^{k + 1,2}(Omega),
          ⇑((V : WkpAmbientOn n (k + 1) 2 Omega)
              (baseIndex n (k + 1)) : DerivLp n 2 Omega)
            =ᵐ[domainMeasure n Omega]
              ⇑(((v : H¹(Omega)) :
                WkpAmbientOn n 1 2 Omega) (baseIndex n 1) :
                  DerivLp n 2 Omega)) :
    ∃ W : W^{k + 2,2}(Omega),
      ⇑((W : WkpAmbientOn n (k + 2) 2 Omega)
          (baseIndex n (k + 2)) : DerivLp n 2 Omega)
        =ᵐ[domainMeasure n Omega] fun x ↦
          rho.toFun x *
            ⇑((u : WkpAmbientOn n 1 2 Omega)
              (baseIndex n 1) : DerivLp n 2 Omega) x := by
  refine exists_interior_higherOrder_localized_succ_of_local_previous k hk hOpen rho hrhoOmega A F
    u hu U hU fun G0 v hv K _ hKOmega ↦ ?_
  obtain ⟨Vreg, hVreg⟩ := hprevious G0 v hv
  exact ⟨Omega, hOpen, hKOmega, Subset.rfl, Vreg, by simpa using hVreg⟩

variable [Fact (0 < n)]

/--
The arbitrary-order successor for the fixed interior partition piece.

This is the atlas specialization of
`exists_interior_higherOrder_localized_succ_of_previous`.
-/
theorem exists_interior_higherOrder_localized_piece
    (k : ℕ) (hk : 0 < k)
    {Omega : Set (ℝ^n)}
    (hOmega : SobolevSpace.C2BoundaryAtlas n Omega)
    (A : Fin n → Fin n → W^{k + 1,∞}(Omega))
    (F : W^{k,2}(Omega))
    (u : H¹₀(Omega))
    (hu : IsWeakDivergenceSolution
      (n := n) (Ω := Omega)
      (fun i j ↦
        ((A i j : WkpAmbientOn n (k + 1) ∞ Omega)
          (baseIndex n (k + 1)) : DerivLp n ∞ Omega))
      ((F : WkpAmbientOn n k 2 Omega) (baseIndex n k) :
        DerivLp n 2 Omega)
      u)
    (U : W^{k + 1,2}(Omega))
    (hU :
      ((((U : WkpAmbientOn n (k + 1) 2 Omega)
        (baseIndex n (k + 1)) : DerivLp n 2 Omega) : ℝ^n → ℝ))
        =ᵐ[domainMeasure n Omega]
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega))
    (hprevious :
      ∀ (G0 : W^{k - 1,2}(Omega))
        (v : H¹₀(Omega)),
        IsWeakDivergenceSolution
          (n := n) (Ω := Omega)
          (fun i j ↦
            ((lowerOrderCLM
                (n := n) (k := k) (m := k + 1) (p := ∞)
                (Ω := Omega) (by omega) (A i j) :
                  WkpAmbientOn n k ∞ Omega)
              (baseIndex n k) : DerivLp n ∞ Omega))
          ((G0 : WkpAmbientOn n (k - 1) 2 Omega)
            (baseIndex n (k - 1)) : DerivLp n 2 Omega)
          v →
        ∃ V : W^{k + 1,2}(Omega),
          ⇑((V : WkpAmbientOn n (k + 1) 2 Omega)
              (baseIndex n (k + 1)) : DerivLp n 2 Omega)
            =ᵐ[domainMeasure n Omega]
              ⇑(((v : H¹(Omega)) :
                WkpAmbientOn n 1 2 Omega) (baseIndex n 1) :
                  DerivLp n 2 Omega)) :
    ∃ W : W^{k + 2,2}(Omega),
      baseRepresentative W =ᵐ[domainMeasure n Omega]
        (fun x ↦ hOmega.toC1ExtensionAtlas.interiorCutoff.toFun x *
          ⇑(((u : H¹(Omega)) : WkpAmbientOn n 1 2 Omega)
            (baseIndex n 1) : DerivLp n 2 Omega) x) := by
  exact exists_interior_higherOrder_localized_succ_of_previous k hk
    hOmega.toC1ExtensionAtlas.isOpen _ hOmega.toC1ExtensionAtlas.interiorCutoff_support A F
    (h10SubtypeL (n := n) (Ω := Omega) u) hu.toInterior U
    (by simpa only [h10SubtypeL_apply] using hU) hprevious

end BoundaryRegularity
end GraphSpace
end SobolevSpace
