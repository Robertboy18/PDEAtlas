/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Calculus.DifferenceQuotient.TranslationDerivative
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Interior bounds for Sobolev difference quotients

An interior cutoff supplies a whole-space Sobolev function. Along translation segments
contained in the region where the cutoff is one, its derivative is the original weak
derivative. The Lp-valued mean value inequality therefore gives an estimate involving only
the gradient, with no lower-order error from the cutoff.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.DifferenceQuotient

open Filter MeasureTheory Set Rellich
open SobolevSpace.Extension.Lp
open SobolevSpace.CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped Distributions ENNReal Topology Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation followed by restriction depends only on the function on the translated set. -/
theorem restrict_translateLp_congr {V S : Set (ℝ^n)}
    (hV : MeasurableSet V) (hS : MeasurableSet S)
    (a : ℝ^n) (ha : MapsTo (fun x ↦ x + a) V S)
    {f g : DerivLp n p univ}
    (hfg : (f : ℝ^n → ℝ) =ᵐ[domainMeasure n S] g) :
    restrictDerivLp (subset_univ V) (translateLp p a f) =
      restrictDerivLp (subset_univ V) (translateLp p a g) := by
  have hglobal : ∀ᵐ x ∂volume, x ∈ S → f x = g x :=
    (ae_restrict_iff' hS).mp hfg
  have htrans := (measurePreserving_add_right (volume : Measure (ℝ^n)) a
    ).quasiMeasurePreserving.ae hglobal
  apply Lp.ext
  filter_upwards [restrictDerivLp_apply_ae (subset_univ V) (translateLp p a f),
    restrictDerivLp_apply_ae (subset_univ V) (translateLp p a g),
    (translateLp_apply_ae p a f).filter_mono
      (ae_mono (domainMeasure_le (subset_univ V))),
    (translateLp_apply_ae p a g).filter_mono
      (ae_mono (domainMeasure_le (subset_univ V))),
    htrans.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hV] with x hrf hrg htf htg hx hxV
  exact hrf.trans (htf.trans ((hx (ha hxV)).trans (htg.symm.trans hrg.symm)))

/-- A cutoff extension agrees with every original derivative on an open region where
the cutoff is identically one. -/
theorem extendByCutoff_coordinate_eq_on {Ω S : Set (ℝ^n)}
    (hΩ : IsOpen Ω) (hS : IsOpen S) (hSΩ : S ⊆ Ω)
    (ψ : 𝓓((⊤ : TopologicalSpace.Opens (ℝ^n)), ℝ))
    (hψ : tsupport ψ.toFun ⊆ Ω) (hone : ∀ x ∈ S, ψ.toFun x = 1)
    (U : W^{1,p}(Ω)) (q : DerivIndex n 1) :
    ((extendByCutoff hΩ (subset_univ Ω) ψ hψ U).val q : ℝ^n → ℝ)
      =ᵐ[domainMeasure n S] (U.val q : ℝ^n → ℝ) := by
  let W := extendByCutoff hΩ (subset_univ Ω) ψ hψ U
  have heq : restrictCLM hS.measurableSet (subset_univ S) W =
      restrictCLM hS.measurableSet hSΩ U := by
    apply WkpSpaceOn.ext_of_base_ae hS
    filter_upwards [restrictCLM_apply_ae hS.measurableSet (subset_univ S) W (baseIndex n 1),
      restrictCLM_apply_ae hS.measurableSet hSΩ U (baseIndex n 1),
      (extendByCutoff_base_ae hΩ (subset_univ Ω) ψ hψ U).filter_mono
        (ae_mono (domainMeasure_le (subset_univ S))),
      ae_restrict_mem hS.measurableSet] with x hx hy hz hs
    have hz' : W.val (baseIndex n 1) x = U.val (baseIndex n 1) x := by
      simpa only [baseRepresentative, hone x hs, one_mul] using hz
    exact hx.trans (hz'.trans hy.symm)
  have hr := restrictCLM_apply_ae hS.measurableSet (subset_univ S) W q
  rw [heq] at hr
  exact hr.symm.trans (restrictCLM_apply_ae hS.measurableSet hSΩ U q)

/-- A coordinate quotient is controlled by its weak derivative whenever the translation
segment stays in an open region of agreement with a whole-space Sobolev function. -/
theorem norm_restricted_differenceQuotient_le_of_agree
    (hp : p ≠ ∞) {Ω V S : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    (hV : MeasurableSet V) (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (i : Fin n) {h : ℝ} (hh : h ≠ 0)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (fun x ↦ x + coordinateStep i (t * h)) V S)
    (U : W^{1,p}(Ω)) (W : W^{1,p}(ℝ^n))
    (hag : ∀ q : DerivIndex n 1,
      (W.val q : ℝ^n → ℝ) =ᵐ[domainMeasure n S] (U.val q : ℝ^n → ℝ)) :
    ‖restrictDerivLp (subset_univ V)
      (differenceQuotientLp p i h (zeroExtendLp hΩ (wkpBaseCoordinateCLM U)))‖ ≤
        ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
  let R := restrictDerivLp (n := n) (p := p) (subset_univ V)
  have hag' (q : DerivIndex n 1) :
      (W.val q : ℝ^n → ℝ) =ᵐ[domainMeasure n S]
        (zeroExtendLp hΩ (U.val q) : ℝ^n → ℝ) :=
    (hag q).trans ((zeroExtendLp_agree_ae hΩ (U.val q)).filter_mono
      (ae_mono (domainMeasure_le hSΩ))).symm
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : DerivIndex n 1) :
      R (translateLp p (coordinateStep i (t * h)) (W.val q)) =
        R (translateLp p (coordinateStep i (t * h)) (zeroExtendLp hΩ (U.val q))) :=
    restrict_translateLp_congr hV hS _ (hseg t ht) (hag' q)
  let : AddCommGroup (DerivLp n p V) := Lp.instNormedAddCommGroup.toAddCommGroup
  let : Module ℝ (DerivLp n p V) := Lp.instNormedSpace.toModule
  let f (t : ℝ) := R (translateLp p (coordinateStep i (t * h)) (wkpBaseCoordinateCLM W))
  let f' (t : ℝ) := h • R
    (translateLp p (coordinateStep i (t * h)) (wkpCoordinateCLM (singleDerivIndex n i) W))
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    simpa only [f, f', map_smul, one_mul, Function.comp_def, id_eq] using
      R.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_translateLp_base_of_ne_top hp i W (t * h)).scomp t
        ((hasDerivAt_id t).mul_const h))
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖f' t‖ ≤ |h| * ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
    change ‖h • R (translateLp p (coordinateStep i (t * h)) (W.val _))‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, heq t (Ico_subset_Icc_self ht)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg h)
    exact (norm_restrictDerivLp_le _ _).trans_eq
      ((norm_translateLp p _ _).trans (norm_zeroExtendLp hΩ _))
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ ↦ (hd t).hasDerivWithinAt) hb
  have hquot : R (differenceQuotientLp p i h
      (zeroExtendLp hΩ (wkpBaseCoordinateCLM U))) = h⁻¹ • (f 1 - f 0) := by
    change _ = h⁻¹ • (R (translateLp p (coordinateStep i (1 * h)) (W.val _)) -
      R (translateLp p (coordinateStep i (0 * h)) (W.val _)))
    rw [heq 1 (by simp), heq 0 (by simp)]
    simp only [one_mul, zero_mul, coordinateStep, zero_smul, translateLp_zero,
      differenceQuotientLp_apply, map_smul, map_sub, wkpBaseCoordinateCLM_apply]
  rw [hquot, norm_smul, norm_inv, Real.norm_eq_abs]
  calc
    |h|⁻¹ * ‖f 1 - f 0‖ ≤
        |h|⁻¹ * (|h| * ‖wkpCoordinateCLM (singleDerivIndex n i) U‖) :=
      mul_le_mul_of_nonneg_left hmv (inv_nonneg.mpr (abs_nonneg h))
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hh), one_mul]

/-- Interior coordinate difference quotients have the sharp coordinate bound. Any positive
collar contained in the domain supplies the allowed step sizes; no extension-domain
hypothesis is needed. -/
theorem norm_restricted_differenceQuotient_le
    (hp : p ≠ ∞) {Ω V : Set (ℝ^n)} (hΩ : IsOpen Ω) (hV : MeasurableSet V)
    (hVc : IsCompact (closure V)) {ρ : ℝ} (hρ : 0 < ρ)
    (hcollar : Metric.thickening ρ V ⊆ Ω)
    (U : W^{1,p}(Ω)) (i : Fin n) {h : ℝ}
    (hh : h ≠ 0) (hhρ : |h| < ρ) :
    ‖restrictDerivLp (subset_univ V)
      (differenceQuotientLp p i h (zeroExtendLp hΩ.measurableSet (wkpBaseCoordinateCLM U)))‖ ≤
        ‖wkpCoordinateCLM (singleDerivIndex n i) U‖ := by
  let r : ℝ := (|h| + ρ) / 2
  have hhr : |h| < r := by dsimp [r]; linarith
  have hrρ : r < ρ := by dsimp [r]; linarith
  let K := Metric.cthickening r (closure V)
  let S := Metric.thickening r V
  have hK : IsCompact K := hVc.cthickening
  have hKU : K ⊆ Ω := by
    dsimp only [K]
    rw [Metric.cthickening_closure]
    exact (Metric.cthickening_subset_thickening' hρ hrρ V).trans hcollar
  have hS : IsOpen S := Metric.isOpen_thickening
  have hSK : S ⊆ K := by
    dsimp only [S, K]
    rw [Metric.cthickening_closure]
    exact Metric.thickening_subset_cthickening r V
  obtain ⟨ψ, hψ, hone, _, _⟩ := TestFunction.exists_eq_one_on_compact hΩ hK hKU
  let W := extendByCutoff hΩ (subset_univ Ω) ψ hψ U
  apply norm_restricted_differenceQuotient_le_of_agree hp hΩ.measurableSet hV
    hS.measurableSet (hSK.trans hKU) i hh (W := W)
  · intro t ht x hx
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_coordinateStep, abs_mul,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (abs_nonneg h) ht.2).trans_lt hhr
  · intro q
    exact extendByCutoff_coordinate_eq_on hΩ hS (hSK.trans hKU) ψ hψ
      (fun x hx ↦ hone x (hSK hx)) U q

/-- Compact containment in an open domain supplies a positive collar for the quotient
estimate, uniformly for every Sobolev function and every coordinate. -/
theorem exists_differenceQuotient_radius {Ω V : Set (ℝ^n)}
    (hΩ : IsOpen Ω) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.thickening ρ V ⊆ Ω := by
  obtain ⟨ρ, hρ, hsub⟩ := hVc.exists_thickening_subset_open hΩ hVΩ
  exact ⟨ρ, hρ, by simpa only [Metric.thickening_closure] using hsub⟩

end SobolevSpace.GraphSpace.DifferenceQuotient
