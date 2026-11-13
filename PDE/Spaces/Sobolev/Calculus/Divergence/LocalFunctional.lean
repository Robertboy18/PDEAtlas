/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.Functional
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates
import PDE.Analysis.MeasureTheory.Lp.Localization.Pairing
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Localization.Cutoff.FixedPoints

/-!
# Testing a locally L² divergence equation on compactly supported H¹ fields

Localizing the coefficients to a cutoff support makes the weak residual a
continuous functional on the zero-trace space. Smooth density then
extends the equation. A compactly supported H¹ field is fixed by a cutoff
inside the domain, so no boundary regularity or global L² bound for the flux
is required.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A locally square integrable divergence equation holds on every localized
zero-trace test. Only the coefficient norms on the cutoff support enter
the density argument. -/
theorem weakDivergence_cutoff_integral_of_testFunctions (hΩ : IsOpen Ω)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (q : Fin n → ℝ^n → ℝ) (f : ℝ^n → ℝ)
    (hq : ∀ i, MemLp ((tsupport κ.toFun).indicator (q i)) 2 (domainMeasure n Ω))
    (hf : MemLp ((tsupport κ.toFun).indicator f) 2 (domainMeasure n Ω))
    (h : ∀ φ : TestFunctionOn n Ω,
      (∑ i, ∫ x, q i x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
        ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (v : H¹₀(Ω)) :
    (∑ i, ∫ x, q i x * derivCoordCLM i (cutoffH10 hΩ κ v) x
      ∂domainMeasure n Ω) =
      ∫ x, f x * baseCoordCLM (cutoffH10 hΩ κ v) x ∂domainMeasure n Ω := by
  let Q (i : Fin n) : DerivLp n 2 Ω :=
    (hq i).toLp ((tsupport κ.toFun).indicator (q i))
  let F : DerivLp n 2 Ω := hf.toLp ((tsupport κ.toFun).indicator f)
  have hQ (w : H¹₀(Ω)) (i : Fin n) :
      ⟪Q i, derivCoordCLM i (cutoffH10 hΩ κ w)⟫ =
        ∫ x, q i x * derivCoordCLM i (cutoffH10 hΩ κ w) x ∂domainMeasure n Ω :=
    inner_toLp_indicator_eq_integral_mul (hq i) _
      (cutoffCLM_singleDeriv_tsupport_indicator_ae κ (w : H¹(Ω)) i)
  have hF (w : H¹₀(Ω)) :
      ⟪F, baseCoordCLM (cutoffH10 hΩ κ w)⟫ =
        ∫ x, f x * baseCoordCLM (cutoffH10 hΩ κ w) x ∂domainMeasure n Ω :=
    inner_toLp_indicator_eq_integral_mul hf _
      (cutoffCLM_base_tsupport_indicator_ae κ (w : H¹(Ω)))
  have hcore (φ : TestFunctionOn n Ω) :
      (∑ i, ⟪Q i, derivCoordCLM i (cutoffH10 hΩ κ (testFunctionToH10 φ))⟫) =
        ⟪F, baseCoordCLM (cutoffH10 hΩ κ (testFunctionToH10 φ))⟫ := by
    simp only [hQ, hF]
    simp only [cutoffH10_testFunction]
    let ψ : TestFunctionOn n Ω :=
      ⟨TestFunction.mul κ φ.1, tsupport_mul_subset_right.trans φ.2⟩
    have hderiv (i : Fin n) :
        (∫ x, q i x * derivCoordCLM i (testFunctionToH10 ψ) x
          ∂domainMeasure n Ω) =
        ∫ x, q i x * (∂[i] ψ.1.toFun) x ∂domainMeasure n Ω := by
      apply integral_congr_ae
      filter_upwards [derivCoordCLM_testFunction_apply_ae i ψ] with x hx
      rw [hx]
    have hbase :
        (∫ x, f x * baseCoordCLM (testFunctionToH10 ψ) x ∂domainMeasure n Ω) =
        ∫ x, f x * ψ.1.toFun x ∂domainMeasure n Ω := by
      apply integral_congr_ae
      filter_upwards [baseCoordCLM_testFunction_apply_ae ψ] with x hx
      rw [hx]
    change (∑ i, ∫ x, q i x * derivCoordCLM i (testFunctionToH10 ψ) x
      ∂domainMeasure n Ω) =
        ∫ x, f x * baseCoordCLM (testFunctionToH10 ψ) x ∂domainMeasure n Ω
    simp only [hderiv, hbase]
    exact h ψ
  simpa only [hQ, hF] using
    weakDivergence_cutoff_pairing_of_testFunctions hΩ κ Q F hcore v

/-- The divergence identity extends from smooth tests to every
H¹ field whose base representative vanishes outside a compact subset of the
open domain. Both the flux and the load need only be locally L². -/
theorem weakDivergence_integral_of_compact_base_support (hΩ : IsOpen Ω)
    (q : Fin n → ℝ^n → ℝ) (f : ℝ^n → ℝ)
    (hq : ∀ i K, IsCompact K → K ⊆ Ω → MemLp (q i) 2 (volume.restrict K))
    (hf : ∀ K, IsCompact K → K ⊆ Ω → MemLp f 2 (volume.restrict K))
    (h : ∀ φ : TestFunctionOn n Ω,
      (∑ i, ∫ x, q i x * (∂[i] φ.1.toFun) x ∂domainMeasure n Ω) =
        ∫ x, f x * φ.1.toFun x ∂domainMeasure n Ω)
    (v : H¹(Ω)) {K : Set (ℝ^n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hv : ∀ᵐ x ∂domainMeasure n Ω, x ∉ K →
      ((v : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) x = 0) :
    (∑ i, ∫ x, q i x *
      ((v : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)) x ∂domainMeasure n Ω) =
      ∫ x, f x * ((v : WkpAmbientOn n 1 2 Ω) (baseIndex n 1)) x
        ∂domainMeasure n Ω := by
  obtain ⟨κ, hκΩ, hκone, -, -⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ hK hKΩ
  have hfix : cutoffCLM (p := 2) κ v = v :=
    cutoffCLM_eq_self_of_base_support hΩ κ v hκone hv
  let w : H¹₀(Ω) :=
    ⟨cutoffCLM (p := 2) κ v, cutoffCLM_mem_H10 hΩ κ hκΩ v⟩
  have hw : (w : H¹(Ω)) = v := hfix
  have hcutw : cutoffH10 hΩ κ w = w := by
    apply Subtype.ext
    change cutoffCLM (p := 2) κ (w : H¹(Ω)) = (w : H¹(Ω))
    rw [hw, hfix]
  have hlocal {g : ℝ^n → ℝ}
      (hg : MemLp g 2 (volume.restrict (tsupport κ.toFun))) :
      MemLp ((tsupport κ.toFun).indicator g) 2 (domainMeasure n Ω) := by
    apply (memLp_indicator_iff_restrict κ.hasCompactSupport.measurableSet.nullMeasurableSet).2
    have hs : tsupport κ.toFun ∩ Ω = tsupport κ.toFun := inter_eq_left.mpr hκΩ
    rw [domainMeasure, Measure.restrict_restrict κ.hasCompactSupport.measurableSet]
    change MemLp g 2 (volume.restrict (tsupport κ.toFun ∩ Ω))
    rw [hs]
    exact hg
  have heq := weakDivergence_cutoff_integral_of_testFunctions hΩ κ q f
    (fun i ↦ hlocal (hq i _ κ.hasCompactSupport hκΩ))
    (hlocal (hf _ κ.hasCompactSupport hκΩ)) h w
  simpa only [hcutw, baseCoordCLM_apply, derivCoordCLM_apply, hw] using heq

end SobolevSpace.GraphSpace
