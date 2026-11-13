/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Weak lower semicontinuity of weighted energies on an interval

Let `Fᵢ` be square integrable on `ℝ` and converge weakly to `F`, in the sense that
`∫ w Fᵢ → ∫ w F` for every square integrable `w`. Let `ψ ≥ 0` and `h` be continuous on an open
interval `(a, b)`; `ψ` may be singular at the endpoints. If eventually the densities
`(Fᵢ - h)² ψ` are integrable on `(a, b)` with integrals at most `Mᵢ`, and `Mᵢ → m`, then
`(F - h)² ψ` is integrable on `(a, b)` with integral at most `m`.

On a compact `K ⊂ (a, b)` the function `w = 1_K (F - h) ψ` is square integrable. The pairings
give `∫ (Fᵢ - h) w → ∫_K (F - h)² ψ = X`, and the pointwise bound `G² ψ ≥ 2 G H ψ - H² ψ`
gives `Mᵢ ≥ 2 ∫ (Fᵢ - h) w - X`, hence `X ≤ m` in the limit. An exhaustion of `(a, b)` by
compact intervals finishes the proof. This is weak lower semicontinuity of the weighted norm,
proved without the Riesz representation of the dual.

## Main results

* `integral_Icc_sq_sub_mul_le_of_pairing`: the bound on one compact subinterval.
* `integral_sq_sub_mul_le_of_pairing`: the bound on the open interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace PDE.Analysis

variable {ι : Type*} {l : Filter ι}

/-- The weighted bound on one compact interval inside `(a, b)`, for square integrable
functions `Fᵢ` converging weakly to `F` in the sense of the pairings `∫ w Fᵢ → ∫ w F`. -/
theorem integral_Icc_sq_sub_mul_le_of_pairing [l.NeBot] {F : ι → ℝ → ℝ} {F' : ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hF' : MemLp F' 2 volume)
    (hpair : ∀ w : ℝ → ℝ, MemLp w 2 volume →
      Tendsto (fun i ↦ ∫ x, w x * F i x) l (𝓝 (∫ x, w x * F' x)))
    {a b c d : ℝ} (hac : a < c) (hdb : d < b) {h ψ : ℝ → ℝ}
    (hh : ContinuousOn h (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b))
    (hψnonneg : ∀ x ∈ Ioo a b, 0 ≤ ψ x) {M : ι → ℝ} {m : ℝ} (hM : Tendsto M l (𝓝 m))
    (henergy : ∀ᶠ i in l, IntegrableOn (fun x ↦ (F i x - h x) ^ 2 * ψ x) (Ioo a b) ∧
      ∫ x in Ioo a b, (F i x - h x) ^ 2 * ψ x ≤ M i) :
    IntegrableOn (fun x ↦ (F' x - h x) ^ 2 * ψ x) (Icc c d) ∧
      ∫ x in Icc c d, (F' x - h x) ^ 2 * ψ x ≤ m := by
  have hK : Icc c d ⊆ Ioo a b := Icc_subset_Ioo hac hdb
  obtain ⟨Cψ, hCψ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hψ.mono hK)
  obtain ⟨Ch, hCh⟩ := isCompact_Icc.exists_bound_of_continuousOn (hh.mono hK)
  have hhL : MemLp h 2 (volume.restrict (Icc c d)) :=
    MemLp.of_bound ((hh.mono hK).aestronglyMeasurable measurableSet_Icc) Ch
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx ↦ hCh x hx)
  have hFL (i : ι) : MemLp (fun x ↦ F i x - h x) 2 (volume.restrict (Icc c d)) :=
    ((hF i).restrict _).sub hhL
  have hGL : MemLp (fun x ↦ F' x - h x) 2 (volume.restrict (Icc c d)) :=
    (hF'.restrict _).sub hhL
  have hGψ : MemLp (fun x ↦ (F' x - h x) * ψ x) 2 (volume.restrict (Icc c d)) :=
    hGL.fun_mul (memLp_top_of_bound ((hψ.mono hK).aestronglyMeasurable measurableSet_Icc) Cψ
      ((ae_restrict_mem measurableSet_Icc).mono fun x hx ↦ hCψ x hx))
  have hwL : MemLp ((Icc c d).indicator fun x ↦ (F' x - h x) * ψ x) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Icc.nullMeasurableSet).mpr hGψ
  have hI {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Icc c d))) :
      Integrable (fun x ↦ (F' x - h x) * ψ x * g x) (volume.restrict (Icc c d)) :=
    (hg.integrable_mul hGψ).congr (ae_of_all _ fun x ↦ by simp only [Pi.mul_apply]; ring)
  have hint (i : ι) : Integrable (fun x ↦ (F i x - h x) * ((F' x - h x) * ψ x))
      (volume.restrict (Icc c d)) :=
    ((hFL i).integrable_mul hGψ).congr (ae_of_all _ fun x ↦ by simp only [Pi.mul_apply])
  have hXint : Integrable (fun x ↦ (F' x - h x) ^ 2 * ψ x) (volume.restrict (Icc c d)) :=
    (hI hGL).congr (ae_of_all _ fun x ↦ by ring)
  set X : ℝ := ∫ x in Icc c d, (F' x - h x) ^ 2 * ψ x with hX
  -- the pairing with `w = 1_{[c, d]} (F' - h) ψ`
  have hind (g : ℝ → ℝ) :
      ∫ x, (Icc c d).indicator (fun x ↦ (F' x - h x) * ψ x) x * g x =
        ∫ x in Icc c d, (F' x - h x) * ψ x * g x := by
    rw [← integral_indicator measurableSet_Icc]
    exact integral_congr_ae (ae_of_all _ fun x ↦ (indicator_mul_left _ _ _).symm)
  have hQ (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Icc c d))) :
      ∫ x in Icc c d, (g x - h x) * ((F' x - h x) * ψ x) =
        (∫ x, (Icc c d).indicator (fun x ↦ (F' x - h x) * ψ x) x * g x) -
          ∫ x in Icc c d, (F' x - h x) * ψ x * h x := by
    rw [hind g, ← integral_sub (hI hg) (hI hhL)]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  have hlim : Tendsto (fun i ↦ ∫ x in Icc c d, (F i x - h x) * ((F' x - h x) * ψ x)) l
      (𝓝 X) := by
    rw [show X = _ from (integral_congr_ae (ae_of_all _ fun x ↦ by ring)).trans
      (hQ F' (hF'.restrict _))]
    exact ((hpair _ hwL).sub_const _).congr fun i ↦ (hQ (F i) ((hF i).restrict _)).symm
  have hstep : ∀ᶠ i in l,
      2 * (∫ x in Icc c d, (F i x - h x) * ((F' x - h x) * ψ x)) - X ≤ M i := by
    filter_upwards [henergy] with i ⟨hi, hiM⟩
    have hleft : Integrable (fun x ↦ 2 * ((F i x - h x) * ((F' x - h x) * ψ x)) -
        (F' x - h x) ^ 2 * ψ x) (volume.restrict (Icc c d)) := ((hint i).const_mul 2).sub hXint
    have hmono := setIntegral_mono_on hleft (hi.mono_set hK) measurableSet_Icc fun x hx ↦ by
      nlinarith [mul_nonneg (sq_nonneg (F i x - h x - (F' x - h x))) (hψnonneg x (hK hx))]
    rw [integral_sub ((hint i).const_mul 2) hXint, integral_const_mul] at hmono
    linarith [setIntegral_mono_set hi ((ae_restrict_mem measurableSet_Ioo).mono fun x hx ↦
      mul_nonneg (sq_nonneg _) (hψnonneg x hx)) (Eventually.of_forall hK)]
  have hlimit : 2 * X - X ≤ m :=
    le_of_tendsto_of_tendsto ((hlim.const_mul 2).sub_const X) hM hstep
  exact ⟨hXint, by linarith⟩

/-- Weak lower semicontinuity of a weighted energy on an interval, for square integrable
functions `Fᵢ` converging weakly to `F`: if eventually `(Fᵢ - h)² ψ` is integrable on `(a, b)`
with `∫ₐᵇ (Fᵢ - h)² ψ ≤ Mᵢ`, and `Mᵢ → m`, then `(F - h)² ψ` is integrable on `(a, b)` with
integral at most `m`. The weight `ψ ≥ 0` and the shift `h` need only be continuous on the
open interval. -/
theorem integral_sq_sub_mul_le_of_pairing [l.NeBot] {F : ι → ℝ → ℝ} {F' : ℝ → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hF' : MemLp F' 2 volume)
    (hpair : ∀ w : ℝ → ℝ, MemLp w 2 volume →
      Tendsto (fun i ↦ ∫ x, w x * F i x) l (𝓝 (∫ x, w x * F' x)))
    {a b : ℝ} {h ψ : ℝ → ℝ}
    (hh : ContinuousOn h (Ioo a b)) (hψ : ContinuousOn ψ (Ioo a b))
    (hψnonneg : ∀ x ∈ Ioo a b, 0 ≤ ψ x) {M : ι → ℝ} {m : ℝ} (hM : Tendsto M l (𝓝 m))
    (henergy : ∀ᶠ i in l, IntegrableOn (fun x ↦ (F i x - h x) ^ 2 * ψ x) (Ioo a b) ∧
      ∫ x in Ioo a b, (F i x - h x) ^ 2 * ψ x ≤ M i) :
    IntegrableOn (fun x ↦ (F' x - h x) ^ 2 * ψ x) (Ioo a b) ∧
      ∫ x in Ioo a b, (F' x - h x) ^ 2 * ψ x ≤ m := by
  have hm : 0 ≤ m := ge_of_tendsto hM <| henergy.mono fun i hi ↦ (setIntegral_nonneg
    measurableSet_Ioo fun x hx ↦ mul_nonneg (sq_nonneg _) (hψnonneg x hx)).trans hi.2
  have hfnonneg : 0 ≤ᵐ[volume.restrict (Ioo a b)] fun x ↦ (F' x - h x) ^ 2 * ψ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg (sq_nonneg _) (hψnonneg x hx)
  rcases le_or_gt b a with hba | hab
  · rw [Ioo_eq_empty (not_lt.mpr hba), setIntegral_empty]
    exact ⟨integrableOn_empty, hm⟩
  set δ : ℕ → ℝ := fun n ↦ (b - a) / (n + 2) with hδ
  have hδpos (n : ℕ) : 0 < δ n := div_pos (sub_pos.mpr hab) (by positivity)
  have hKmono : Monotone fun n ↦ Icc (a + δ n) (b - δ n) := by
    intro n k hnk
    have hle : δ k ≤ δ n := by
      apply div_le_div_of_nonneg_left (sub_pos.mpr hab).le (by positivity)
      exact_mod_cast Nat.add_le_add_right hnk 2
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hunion : (⋃ n, Icc (a + δ n) (b - δ n)) = Ioo a b := by
    apply Subset.antisymm
    · exact iUnion_subset fun n ↦ Icc_subset_Ioo (by linarith [hδpos n]) (by linarith [hδpos n])
    · intro x hx
      have hmin : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
      obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / min (x - a) (b - x))
      have hδle : δ n ≤ min (x - a) (b - x) := by
        rw [hδ, div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hmin] at hn
        nlinarith
      exact mem_iUnion.mpr ⟨n, by
        constructor <;> linarith [min_le_left (x - a) (b - x), min_le_right (x - a) (b - x)]⟩
  have hpiece (n : ℕ) := integral_Icc_sq_sub_mul_le_of_pairing hF hF' hpair
    (c := a + δ n) (d := b - δ n) (by linarith [hδpos n]) (by linarith [hδpos n])
    hh hψ hψnonneg hM henergy
  have hlintegral : ∫⁻ x in Ioo a b, ENNReal.ofReal ((F' x - h x) ^ 2 * ψ x) ≤
      ENNReal.ofReal m := by
    rw [← hunion, setLIntegral_iUnion_of_directed _ hKmono.directed_le]
    apply iSup_le
    intro n
    have hnonneg : 0 ≤ᵐ[volume.restrict (Icc (a + δ n) (b - δ n))]
        fun x ↦ (F' x - h x) ^ 2 * ψ x := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      have hx' : x ∈ Ioo a b := hunion ▸ mem_iUnion.mpr ⟨n, hx⟩
      exact mul_nonneg (sq_nonneg _) (hψnonneg x hx')
    rw [← ofReal_integral_eq_lintegral_ofReal (hpiece n).1 hnonneg]
    exact ENNReal.ofReal_le_ofReal (hpiece n).2
  have hmeas : AEStronglyMeasurable (fun x ↦ (F' x - h x) ^ 2 * ψ x)
      (volume.restrict (Ioo a b)) :=
    ((hF'.aestronglyMeasurable.restrict.sub
      (hh.aestronglyMeasurable measurableSet_Ioo)).pow 2).mul
      (hψ.aestronglyMeasurable measurableSet_Ioo)
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hfnonneg).mpr
    (hlintegral.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hfnonneg hmeas]
  exact ENNReal.toReal_le_of_le_ofReal hm hlintegral

end PDE.Analysis
