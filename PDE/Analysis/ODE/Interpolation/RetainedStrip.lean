/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Interpolation.CubicStrip
public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.Retained

/-!
# Phase alignment of retained physical flows

The two physical branches initially solve their equations on different time
intervals. Extend them about the same complete reference trajectory, identify
them with their original branches by uniqueness, and then align their original
moving events. The moving mismatch keeps its derivatives during this extension.

The resulting cubic strip contains the prescribed gate. The enlarged families
also retain their full initial sections and their native time-slice germs, which
are needed to transport the selected first variation into the rank calculation.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Extend the actual retained branches and align their original moving events.

The field is fixed throughout. Matching derivatives refer to outgoing minus
incoming at the supplied events; the phase owner uses the opposite sign, handled
by negating that entire mismatch. The output preserves both full initial
sections, agreement on the native intervals, and their speed germs.

The cubic factor is exact on a compact interval containing the gate and the
event, for one open neighborhood of signed speeds. This construction supplies
the common-domain hypothesis of the phase theorem rather than assuming it. -/
theorem exists_retained_phase_aligned_cubic_strip
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    {H e tStar : ℝ} (he : e ∈ Ioo (0 : ℝ) H)
    (htStar : tStar ∈ Ioo (0 : ℝ) e)
    (Fout Fincoming : ℝ → ℝ → E)
    (hFout : ContDiff ℝ ∞ Fout.uncurry) (hFin : ContDiff ℝ ∞ Fincoming.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFoutBase : EqOn (fun t ↦ Fout t 0) q (Icc (0 : ℝ) H))
    (hFinBase : EqOn (fun t ↦ Fincoming t 0) q (Icc (e + e - H) (e + e)))
    (hFoutOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t)
    (hFinOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (e + e - H) (e + e),
      HasDerivAt (fun s ↦ Fincoming s μ)
        (f (Fincoming t μ) - μ • Fincoming t μ) t)
    (τout τin : ℝ → ℝ)
    (hτout : ContDiffOn ℝ ∞ τout I₀) (hτin : ContDiffOn ℝ ∞ τin I₀)
    (hτoutZero : τout 0 = e) (hτinZero : τin 0 = e)
    (hτoutNative : ∀ μ ∈ I₀, τout μ ∈ Ioo (0 : ℝ) H)
    (hτinNative : ∀ μ ∈ I₀, τin μ ∈ Ioo (e + e - H) (e + e))
    (ell : E →L[ℝ] ℝ) (htransverse : ell (f (q e)) ≠ 0)
    (hfirst : deriv (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ) 0 = 0)
    (hsecond :
      deriv (deriv (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ)) 0 = 0) :
    let lo := min 0 (e + e - H)
    let hi := max H (e + e)
    ∃ (Gout Gin U V : ℝ → ℝ → E) (C : ℝ × ℝ → E)
      (a b r : ℝ) (J : Set ℝ),
      ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
      (∀ μ, Gout 0 μ = Fout 0 μ ∧ Gin (e + e) μ = Fincoming (e + e) μ) ∧
      EqOn (fun t ↦ Gout t 0) q (Icc lo hi) ∧
      EqOn (fun t ↦ Gin t 0) q (Icc lo hi) ∧
      (∀ t ∈ Icc (0 : ℝ) H, Gout t =ᶠ[𝓝 (0 : ℝ)] Fout t) ∧
      (∀ t ∈ Icc (e + e - H) (e + e), Gin t =ᶠ[𝓝 (0 : ℝ)] Fincoming t) ∧
      e ∈ Ioo a b ∧ tStar ∈ Ioo a b ∧ Icc a b ⊆ Ioo lo hi ∧
      IsOpen J ∧ (0 : ℝ) ∈ J ∧ J ⊆ I₀ ∧
      0 < r ∧ Icc (-r) r ⊆ J ∧
      (∀ μ ∈ J,
        EqOn (fun t ↦ Gout t μ) (fun t ↦ Fout t μ) (Icc (0 : ℝ) H) ∧
        EqOn (fun t ↦ Gin t μ) (fun t ↦ Fincoming t μ)
          (Icc (e + e - H) (e + e))) ∧
      (∀ μ ∈ J,
        Gout (τout μ) μ = Fout (τout μ) μ ∧
        Gin (τin μ) μ = Fincoming (τin μ) μ) ∧
      (∀ μ ∈ J,
        (∀ t ∈ Icc lo hi,
          HasDerivAt (fun s ↦ Gout s μ) (f (Gout t μ) - μ • Gout t μ) t) ∧
        (∀ t ∈ Icc lo hi,
          HasDerivAt (fun s ↦ Gin s μ) (f (Gin t μ) - μ • Gin t μ) t)) ∧
      ContDiff ℝ ∞ U.uncurry ∧ ContDiff ℝ ∞ V.uncurry ∧ ContDiff ℝ ∞ C ∧
      (∀ μ ∈ J, ∀ t,
        U t μ = Gout (t + τout μ - e) μ ∧ V t μ = Gin (t + τin μ - e) μ) ∧
      (∀ t ∈ Icc a b, ∀ μ ∈ J,
        HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
        HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t) ∧
      EqOn (fun t ↦ U t 0) q (Icc a b) ∧
      EqOn (fun t ↦ V t 0) q (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • C (t, μ) := by
  intro lo hi
  obtain ⟨heBig, htStarBig, Gout, Gin, I, hGout, hGin,
      hI, h0I, hIsub, hinit, hbaseOut, hbaseIn, hode, hagree,
      hgermOut, hgermIn, hevents, _, _, hfirstEq, hsecondEq⟩ :=
    exists_common_interval_retained_flux_flows f hf q hq he htStar
      Fout Fincoming hFout hFin I₀ hI₀ h0I₀ hFoutBase hFinBase
      hFoutOde hFinOde τout τin hτoutNative hτinNative ell htransverse
  let M : ℝ → E := fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ
  have hflip : (fun μ ↦ Gin (τin μ) μ - Gout (τout μ) μ) = -M :=
    funext fun μ ↦ (neg_sub _ _).symm
  -- The phase convention reverses the whole mismatch, including its moving
  -- event terms. No individual chain-rule term needs to be reconstructed.
  have hphaseFirst : deriv (fun μ ↦ Gin (τin μ) μ - Gout (τout μ) μ) 0 = 0 := by
    rw [hflip, deriv.neg, hfirstEq, hfirst, neg_zero]
  have hphaseSecond :
      deriv (deriv (fun μ ↦ Gin (τin μ) μ - Gout (τout μ) μ)) 0 = 0 := by
    rw [hflip, deriv.neg']
    change deriv (-(deriv M)) 0 = 0
    rw [deriv.neg, hsecondEq, hsecond, neg_zero]
  obtain ⟨U, V, C, a, b, r, J, heStrip, htStarStrip, hstrip,
      hJ, h0J, hJI, hr, hspeed, hU, hV, hC, hphase, hstripOde,
      hUbase, hVbase, hcubic⟩ :=
    exists_phase_aligned_cubic_strip_containing_gate
      hGout hGin (hf.of_le (by simp)) hI h0I
      (hτout.mono hIsub) (hτin.mono hIsub) hτoutZero hτinZero heBig htStarBig
      (fun t ht μ hμ ↦ (hode μ hμ).1 t ht)
      (fun t ht μ hμ ↦ (hode μ hμ).2 t ht)
      hbaseOut hbaseIn hphaseFirst hphaseSecond
  refine ⟨Gout, Gin, U, V, C, a, b, r, J, hGout, hGin, hinit,
    hbaseOut, hbaseIn, hgermOut, hgermIn, heStrip, htStarStrip, hstrip,
    hJ, h0J, hJI.trans hIsub, hr, hspeed, fun μ hμ ↦ hagree μ (hJI hμ),
    fun μ hμ ↦ ⟨(hevents μ (hJI hμ)).1.2, (hevents μ (hJI hμ)).2.2⟩,
    fun μ hμ ↦ hode μ (hJI hμ), hU, hV, hC, hphase, hstripOde, hUbase, hVbase, hcubic⟩

end PDE.Analysis.ODE
