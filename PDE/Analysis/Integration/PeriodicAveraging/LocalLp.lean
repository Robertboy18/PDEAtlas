/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.PeriodicAveraging.Rescaling
public import PDE.Analysis.MeasureTheory.Lp.Composition.MeasureBound

/-!
# Rescaled periodic functions in local Lp spaces

The uniform pushforward bound defines rescaling on almost-everywhere classes
through Mathlib's composition operator `Lp.compMeasureLeSMul`. Its norm is uniform for
periods in `(0,1]`. Multiplication by the period consequently sends every fixed
periodic `Lᵖ` function strongly to zero on bounded domains.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.Analysis.PeriodicAveraging

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Periodic rescaling as a bounded operator into the local `Lᵖ` space. -/
def rescaleLp (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Lp E p (cellMeasure n) →L[ℝ] Lp E p (volume.restrict Ω) :=
  Lp.compMeasureLeSMul (fun x : ℝ^n ↦ toTorus n (ε⁻¹ • x))
    ((toTorus n).measurable.comp (measurable_const_smul _))
    (exists_map_toTorus_rescale_le hΩ).choose_spec.1
    ((exists_map_toTorus_rescale_le hΩ).choose_spec.2 ε hε hε1)

/-- The rescaling operator represents `u(x/ε)` on the Euclidean domain. -/
theorem rescaleLp_ae (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : Lp E p (cellMeasure n)) :
    rescaleLp hΩ ε hε hε1 u =ᵐ[volume.restrict Ω]
      fun x ↦ u (toTorus n (ε⁻¹ • x)) :=
  Lp.coeFn_compMeasureLeSMul _ _ _ _ u

/-- Rescaling commutes with scalar multiplication over any bounded scalar action. -/
theorem rescaleLp_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (c : 𝕜)
    (u : Lp E p (cellMeasure n)) :
    rescaleLp hΩ ε hε hε1 (c • u) = c • rescaleLp hΩ ε hε hε1 u := by
  apply Lp.ext
  filter_upwards [rescaleLp_ae hΩ ε hε hε1 (c • u),
    rescaleLp_ae hΩ ε hε hε1 u,
    ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
      (inv_ne_zero hε.ne')).ae_eq_comp (Lp.coeFn_smul c u)),
    Lp.coeFn_smul c (rescaleLp hΩ ε hε hε1 u)] with x hx hy hz hw
  exact hx.trans (hz.trans ((congrArg (c • ·) hy).symm.trans hw.symm))

/-- Applying a bounded linear map pointwise commutes with periodic rescaling. -/
theorem rescaleLp_compLp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : Lp E p (cellMeasure n)) :
    rescaleLp hΩ ε hε hε1 (L.compLp u) = L.compLp (rescaleLp hΩ ε hε hε1 u) := by
  apply Lp.ext
  filter_upwards [rescaleLp_ae hΩ ε hε hε1 (L.compLp u),
    rescaleLp_ae hΩ ε hε hε1 u,
    ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
      (inv_ne_zero hε.ne')).ae_eq_comp (L.coeFn_compLp u)),
    L.coeFn_compLp (rescaleLp hΩ ε hε hε1 u)] with x hx hy hz hw
  exact hx.trans (hz.trans ((congrArg L hy).symm.trans hw.symm))

/-- Periodic rescaling preserves constant functions. -/
@[simp] theorem rescaleLp_const [IsFiniteMeasure (volume.restrict Ω)]
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (c : E) :
    rescaleLp hΩ ε hε hε1 (Lp.const p (cellMeasure n) c) =
      Lp.const p (volume.restrict Ω) c := by
  apply Lp.ext
  filter_upwards [rescaleLp_ae hΩ ε hε hε1 (Lp.const p (cellMeasure n) c),
    ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
      (inv_ne_zero hε.ne')).ae_eq_comp (Lp.coeFn_const p (cellMeasure n) c)),
    Lp.coeFn_const p (volume.restrict Ω) c] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

include hΩ in
/-- A periodic `Lᵖ` function remains locally `Lᵖ` after rescaling. -/
theorem memLp_rescale (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (u : Lp E p (cellMeasure n)) :
    MemLp (fun x ↦ u (toTorus n (ε⁻¹ • x))) p (volume.restrict Ω) :=
  (Lp.memLp (rescaleLp hΩ ε hε hε1 u)).ae_eq (rescaleLp_ae hΩ ε hε hε1 u)

/-- The operator norm bound is independent of the period and of the periodic function. -/
theorem exists_norm_rescaleLp_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hε1 : ε ≤ 1,
      ∀ u : Lp E p (cellMeasure n), ‖rescaleLp hΩ ε hε hε1 u‖ ≤ C * ‖u‖ := by
  refine ⟨(exists_map_toTorus_rescale_le hΩ).choose.toReal ^ (1 / p).toReal,
    Real.rpow_nonneg ENNReal.toReal_nonneg _, ?_⟩
  intro ε hε hε1 u
  exact Lp.norm_compMeasureLeSMul_apply_le _ _ _ _ u

/-- The amplitude-scaled periodic family converges strongly in local `Lᵖ`. -/
theorem tendsto_smul_rescaleLp {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (u : Lp E p (cellMeasure n)) :
    Tendsto (fun j ↦ ε j • rescaleLp hΩ (ε j) (hε j) (hε1 j) u) l (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := exists_norm_rescaleLp_le (E := E) (p := p) hΩ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun j ↦ ?_)
    (by simpa using ht.norm.mul_const (C * ‖u‖))
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hbound (ε j) (hε j) (hε1 j) u) (norm_nonneg _)

end PDE.Analysis.PeriodicAveraging
