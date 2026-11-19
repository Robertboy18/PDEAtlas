/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFields
public import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness

/-!
# Whole-space Sobolev classes: Bessel realization and smooth members

A real `L²` class on `ℝⁿ` whose Fourier transform has square-integrable Bessel weight of order
`k` is the base of an element of `W^{k,2}(ℝⁿ)`, with the norm bound of the Bessel-potential
comparison. If a `C^r` function agrees almost everywhere with the base of an element of
`W^{m,p}(ℝⁿ)`, then its classical derivative words of length at most `min m r` are the weak
derivative coordinates almost everywhere, by uniqueness of weak derivatives. For a smooth member
of a `W^{m,2}` class every Fréchet derivative of order at most `m` is therefore square
integrable.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory FourierTransform TemperedDistribution BesselPotentialSpace
open scoped ENNReal Sobolev SchwartzMap BesselPotentialSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- A real `L²` class whose Fourier transform has square-integrable Bessel weight of order `k`
is the base of an element of `W^{k,2}(ℝⁿ)`, whose norm is at most `toWkpSpaceNormBound n k`
times the `L²` norm of the weighted transform. -/
theorem exists_wkpSpace_of_isRealL2_of_memLp_besselWeight {k : ℕ}
    (g : Lp ℂ 2 (volume : Measure (ℝ^n))) (hg : Fractional.IsRealL2 g)
    (h : MemLp (fun ξ ↦ Fractional.besselSymbol n k ξ * (𝓕 g : Lp ℂ 2 volume) ξ) 2 volume) :
    ∃ V : W^{k,2}(ℝ^n), Fractional.baseL2 V = g ∧
      ‖V‖ ≤ Fractional.toWkpSpaceNormBound n k *
        (eLpNorm (fun ξ ↦ Fractional.besselSymbol n k ξ * (𝓕 g : Lp ℂ 2 volume) ξ)
          2 volume).toReal := by
  have hs : MemSobolev (k : ℝ) 2 ((g : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ)) :=
    (Fractional.memSobolev_iff_memLp_besselWeight (k : ℝ) g).mpr h
  set v : H^{(k : ℝ)}(ℝ^n) := hs.toBesselPotentialSpace with hv
  have hL2 : Fractional.toL2Fun (Nat.cast_nonneg k) v = g := by
    apply (LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot)
    change ((Fractional.toL2Fun (Nat.cast_nonneg k) v : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ)) =
      ((g : Lp ℂ 2 volume) : 𝓢'(ℝ^n, ℂ))
    rw [← Fractional.toDistr_eq_toL2Fun]
    exact hs.toBesselPotentialSpace_toDistr
  have hreal : Fractional.IsRealL2 (Fractional.toL2Fun (Nat.cast_nonneg k) v) := by
    rw [hL2]; exact hg
  refine ⟨Fractional.toWkpSpace (Nat.cast_nonneg k) v hreal, ?_, ?_⟩
  · have h1 := Fractional.toL2Fun_ofWkpSpace (Fractional.toWkpSpace (Nat.cast_nonneg k) v hreal)
    rw [Fractional.ofWkpSpace_toWkpSpace] at h1
    rw [← h1, hL2]
  · refine (Fractional.norm_toWkpSpace_le v hreal).trans (le_of_eq ?_)
    congr 1
    rw [← norm_fourier_toLp_eq, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    have := Fractional.coeFn_fourier_toLp (Nat.cast_nonneg k) v
    rw [hL2] at this
    exact this

variable {p : ℝ≥0∞}

/-- The derivative words of length at most `min m r` of a `C^r` member of the class of an
element of `W^{m,p}(ℝⁿ)` are its weak derivative coordinates almost everywhere. -/
theorem iteratedPartialDeriv_ae_eq_coordinate {m r : ℕ} (V : W^{m,p}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ r f) (hfV : f =ᵐ[volume] baseRepresentative V) (α : List (Fin n))
    (hα : α.length ≤ m) (hαr : α.length ≤ r) :
    (fun x ↦ iteratedPartialDeriv α f x) =ᵐ[volume]
      ((V : WkpAmbientOn n m p Set.univ) (derivIndexOfList (n := n) (k := m) α hα) :
        ℝ^n → ℝ) := by
  have h1 := IsWkpOn.hasWeakDerivativeOn_list V.property α hα
  have h2 : HasWeakDerivativeOn (n := n) Set.univ α f (iteratedPartialDeriv α f) :=
    hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn isOpen_univ hf.contDiffOn α hαr
  have hfV' : baseRepresentative V =ᵐ[domainMeasure n Set.univ] f := by
    simpa [domainMeasure] using hfV.symm
  have h3 : HasWeakDerivativeOn (n := n) Set.univ α f
      ((V : WkpAmbientOn n m p Set.univ) (derivIndexOfList (n := n) (k := m) α hα)) :=
    h1.congr_ae hfV' Filter.EventuallyEq.rfl
  simpa [domainMeasure] using h2.unique_ae isOpen_univ h3

/-- The weak gradient of an element of `W^{1,p}(ℝⁿ)` with a `C¹` member `f` is the classical
gradient of `f` almost everywhere. -/
theorem wkpGradientCLM_ae_eq_partialDeriv [Fact (1 ≤ p)] (V : W^{1,p}(ℝ^n)) {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ 1 f) (hfV : f =ᵐ[volume] baseRepresentative V) :
    ∀ᵐ x ∂volume, ∀ i : Fin n, (wkpGradientCLM V x) i = PDE.partialDeriv i f x := by
  have hgrad := wkpGradientCLM_apply_ae (n := n) (p := p) (Ω := Set.univ) V
  simp only [domainMeasure, Measure.restrict_univ] at hgrad
  have hcoord (i : Fin n) : ((V : WkpAmbientOn n 1 p Set.univ) (singleDerivIndex n i) :
      ℝ^n → ℝ) =ᵐ[volume] fun x ↦ PDE.partialDeriv i f x := by
    have h1 := V.property (singleDerivIndex n i)
    rw [singleDerivIndex_toList] at h1
    have h2 : HasWeakDerivativeOn (n := n) Set.univ [i] f (iteratedPartialDeriv [i] f) :=
      hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn (k := 1) isOpen_univ
        hf.contDiffOn [i] le_rfl
    have hfV' : baseRepresentative V =ᵐ[domainMeasure n Set.univ] f := by
      simpa [domainMeasure] using hfV.symm
    have h3 := (h1.congr_ae hfV' Filter.EventuallyEq.rfl).unique_ae isOpen_univ h2
    simpa [domainMeasure, iteratedPartialDeriv] using h3
  filter_upwards [hgrad, ae_all_iff.2 hcoord] with x h1 h2 i
  rw [h1 i, h2 i]

/-- The derivative words of length at most `m` of a smooth member of the class of an element of
`W^{m,p}(ℝⁿ)` are in `Lᵖ`. -/
theorem memLp_iteratedPartialDeriv_of_ae_eq_baseRepresentative {m : ℕ} (V : W^{m,p}(ℝ^n))
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfV : f =ᵐ[volume] baseRepresentative V)
    (α : List (Fin n)) (hα : α.length ≤ m) :
    MemLp (fun x ↦ iteratedPartialDeriv α f x) p volume := by
  have hmem := Lp.memLp ((V : WkpAmbientOn n m p Set.univ)
    (derivIndexOfList (n := n) (k := m) α hα))
  simp only [domainMeasure, Measure.restrict_univ] at hmem
  exact hmem.ae_eq (iteratedPartialDeriv_ae_eq_coordinate (r := α.length) V
    (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)) hfV α hα le_rfl).symm

/-- A smooth member of the class of an element of `W^{m,p}(ℝⁿ)` has its Fréchet derivatives of
every order at most `m` in `Lᵖ`. -/
theorem memLp_iteratedFDeriv_of_ae_eq_baseRepresentative {m : ℕ} (V : W^{m,p}(ℝ^n))
    {f : ℝ^n → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfV : f =ᵐ[volume] baseRepresentative V)
    {k : ℕ} (hk : k ≤ m) : MemLp (iteratedFDeriv ℝ k f) p volume :=
  PDE.memLp_iteratedFDeriv_of_memLp_iteratedPartialDeriv hf k fun α hα ↦
    memLp_iteratedPartialDeriv_of_ae_eq_baseRepresentative V hf hfV α (hα.trans_le hk)

end SobolevSpace.GraphSpace
