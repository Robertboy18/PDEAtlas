/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.SineSeries.Coefficients
public import PDE.FDeriv.PartialDeriv
import PDE.Fluid.Euler.Axisymmetric.CylinderStreamExistence
public import PDE.Common.Euclidean.SpaceTime.Scalar

/-!
# Periodization in the axial variable and planar coordinates of profiles

Vorticity profiles `G(s, z)` are functions on `ℝ × ℝ`; the approximation results for functions on
the plane `ℝ^2` are stated with coordinate derivatives. We connect the two and build
periodic profiles from profiles supported in a strip `|z| ≤ a`.

* `periodizeZ hL G (s, z) = G(s, z mod L)`, with the representative of `z` in `[-L/2, L/2)`. If
  `G` vanishes for `|z| > a` with `a < L/2`, then near every point `periodizeZ hL G` is a
  translate of `G` (`periodizeZ_eventuallyEq`). So it is `C^n` with `G`, `L`-periodic, odd in `z`
  with `G`, and its derivatives `∂_s`, `∂_z` are the periodizations of those of `G`
  (`iterate_sDeriv_zDeriv_periodizeZ`).
* the derivatives `∂_s`, `∂_z` of `H ∘ pointPairEquiv.symm`, for the coordinates
  `pointPairEquiv : ℝ^2 ≃L[ℝ] ℝ × ℝ`, `x ↦ (x₀, x₁)`, are the coordinate derivatives of `H`
  (`iterate_sDeriv_zDeriv_comp_pointPairEquiv_symm`), without any
  regularity assumption.

## Main definitions

* `periodizeZ`.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open PDE.Common (pointPairEquiv)

namespace Euler.Cylinder

open Set Filter PDE.Analysis.Fourier.SineSeries
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-! ### Periodization in `z` -/

/-- The `L`-periodization in `z` of a profile: `(s, z) ↦ G(s, z mod L)`, with the representative
of `z` in `[-L/2, L/2)`. -/
def periodizeZ {L : ℝ} (hL : 0 < L) (G : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  G (q.1, toIcoMod hL (-(L / 2)) q.2)

section Periodization

variable {L : ℝ} (hL : 0 < L) {G : ℝ × ℝ → ℝ} {a : ℝ}

/-- The periodization is `L`-periodic in `z`. -/
theorem periodizeZ_add (s z : ℝ) : periodizeZ hL G (s, z + L) = periodizeZ hL G (s, z) := by
  simp [periodizeZ, toIcoMod_add_right]

/-- The periodization agrees with the profile for `|z| < L/2`. -/
theorem periodizeZ_of_abs_lt {s z : ℝ} (hz : |z| < L / 2) :
    periodizeZ hL G (s, z) = G (s, z) := by
  simp only [periodizeZ]
  rw [(toIcoMod_eq_self hL).2 ⟨by linarith [(abs_lt.1 hz).1], by linarith [(abs_lt.1 hz).2]⟩]

/-- **Near every point the periodization is a translate.** If `G` vanishes for `|z| > a` with
`a < L/2`, then near `q₀` the periodization is `q ↦ G(q - (0, d))`, `d = q₀.2 - (q₀.2 mod L)`. -/
theorem periodizeZ_eventuallyEq (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha0 : 0 ≤ a)
    (ha : a < L / 2) (q₀ : ℝ × ℝ) :
    periodizeZ hL G =ᶠ[𝓝 q₀] fun q ↦ G (q - (0, q₀.2 - toIcoMod hL (-(L / 2)) q₀.2)) := by
  set w := toIcoMod hL (-(L / 2)) q₀.2 with hwdef
  set d := q₀.2 - w with hddef
  have hsub : ∀ q : ℝ × ℝ, q - (0, d) = (q.1, q.2 - d) := fun q ↦ by ext <;> simp
  by_cases h : w = -(L / 2)
  · obtain ⟨n, hn⟩ : ∃ n : ℤ, d = n • L := ⟨_, self_sub_toIcoMod hL (-(L / 2)) q₀.2⟩
    rw [zsmul_eq_mul] at hn
    have hd : d = q₀.2 + L / 2 := by rw [hddef, h]; ring
    have hopen : Ioo (q₀.2 - (L / 2 - a)) (q₀.2 + (L / 2 - a)) ∈ 𝓝 q₀.2 :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hopen] with q hq
    simp only [Set.mem_preimage, Set.mem_Ioo] at hq
    have hR : G (q - (0, d)) = 0 := by
      rw [hsub]
      apply hG
      rw [lt_abs]
      right
      linarith [hq.2]
    rw [hR]
    simp only [periodizeZ]
    apply hG
    by_cases hqz : q₀.2 ≤ q.2
    · have : toIcoMod hL (-(L / 2)) q.2 = q.2 - d := by
        rw [toIcoMod_eq_iff]
        refine ⟨⟨by linarith, by linarith [hq.2]⟩, n, ?_⟩
        rw [zsmul_eq_mul, ← hn]
        ring
      rw [this, lt_abs]
      right
      linarith [hq.2]
    · rw [not_le] at hqz
      have : toIcoMod hL (-(L / 2)) q.2 = q.2 - d + L := by
        rw [toIcoMod_eq_iff]
        refine ⟨⟨by linarith [hq.1], by linarith⟩, n - 1, ?_⟩
        rw [zsmul_eq_mul]
        push_cast
        rw [sub_mul, ← hn]
        ring
      rw [this, lt_abs]
      left
      linarith [hq.1]
  · have hev := Euler.Cylinder.toIcoMod_eventuallyEq hL h
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hev] with q hq
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hq
    simp only [periodizeZ, hsub]
    rw [hq]

/-- The derivative of the periodization is the derivative of the profile at the representative
point. -/
theorem fderiv_periodizeZ (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha0 : 0 ≤ a)
    (ha : a < L / 2) (q₀ : ℝ × ℝ) :
    fderiv ℝ (periodizeZ hL G) q₀ = fderiv ℝ G (q₀.1, toIcoMod hL (-(L / 2)) q₀.2) := by
  rw [(periodizeZ_eventuallyEq hL hG ha0 ha q₀).fderiv_eq, fderiv_comp_sub]
  congr 1
  ext <;> simp

/-- The derivatives of a profile vanishing for `|z| > a` vanish there. -/
theorem fderiv_eq_zero_of_vanishesZ (hG : ∀ s z, a < |z| → G (s, z) = 0) {q : ℝ × ℝ}
    (hq : a < |q.2|) : fderiv ℝ G q = 0 := by
  have hopen : IsOpen {p : ℝ × ℝ | a < |p.2|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_snd)
  have hev : G =ᶠ[𝓝 q] fun _ ↦ 0 := by
    filter_upwards [hopen.mem_nhds hq] with p hp
    exact hG p.1 p.2 hp
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

/-- `∂_s` commutes with the periodization and keeps the vanishing for `|z| > a`. -/
theorem sDeriv_periodizeZ (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha0 : 0 ≤ a)
    (ha : a < L / 2) :
    sDeriv (periodizeZ hL G) = periodizeZ hL (sDeriv G) ∧
      ∀ s z, a < |z| → sDeriv G (s, z) = 0 := by
  refine ⟨funext fun q ↦ ?_, fun s z hz ↦ ?_⟩
  · simp only [sDeriv, periodizeZ, fderiv_periodizeZ hL hG ha0 ha]
  · simp only [sDeriv, fderiv_eq_zero_of_vanishesZ hG (q := (s, z)) hz,
      zero_apply]

/-- `∂_z` commutes with the periodization and keeps the vanishing for `|z| > a`. -/
theorem zDeriv_periodizeZ (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha0 : 0 ≤ a)
    (ha : a < L / 2) :
    zDeriv (periodizeZ hL G) = periodizeZ hL (zDeriv G) ∧
      ∀ s z, a < |z| → zDeriv G (s, z) = 0 := by
  refine ⟨funext fun q ↦ ?_, fun s z hz ↦ ?_⟩
  · simp only [zDeriv, periodizeZ, fderiv_periodizeZ hL hG ha0 ha]
  · simp only [zDeriv, fderiv_eq_zero_of_vanishesZ hG (q := (s, z)) hz,
      zero_apply]

/-- **Iterated derivatives of the periodization.** -/
theorem iterate_sDeriv_zDeriv_periodizeZ (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha0 : 0 ≤ a)
    (ha : a < L / 2) (l j : ℕ) :
    sDeriv^[l] (zDeriv^[j] (periodizeZ hL G)) = periodizeZ hL (sDeriv^[l] (zDeriv^[j] G)) := by
  have hz : ∀ j, zDeriv^[j] (periodizeZ hL G) = periodizeZ hL (zDeriv^[j] G) ∧
      ∀ s z, a < |z| → (zDeriv^[j] G) (s, z) = 0 := by
    intro j
    induction j with
    | zero => exact ⟨rfl, hG⟩
    | succ j ih =>
      obtain ⟨h1, h2⟩ := zDeriv_periodizeZ hL ih.2 ha0 ha
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, h1]
      · rw [Function.iterate_succ_apply']
        exact h2
  have hs : ∀ l, sDeriv^[l] (zDeriv^[j] (periodizeZ hL G)) =
      periodizeZ hL (sDeriv^[l] (zDeriv^[j] G)) ∧
      ∀ s z, a < |z| → (sDeriv^[l] (zDeriv^[j] G)) (s, z) = 0 := by
    intro l
    induction l with
    | zero => exact ⟨(hz j).1, (hz j).2⟩
    | succ l ih =>
      obtain ⟨h1, h2⟩ := sDeriv_periodizeZ hL ih.2 ha0 ha
      refine ⟨?_, ?_⟩
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.1, h1]
      · rw [Function.iterate_succ_apply']
        exact h2
  exact (hs l).1

/-- The periodization of a `C^n` profile vanishing for `|z| > a`, `a < L/2`, is `C^n`. -/
theorem contDiff_periodizeZ {n : WithTop ℕ∞} (hG : ∀ s z, a < |z| → G (s, z) = 0)
    (ha0 : 0 ≤ a) (ha : a < L / 2) (hGc : ContDiff ℝ n G) : ContDiff ℝ n (periodizeZ hL G) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  exact (hGc.comp (contDiff_id.sub contDiff_const)).contDiffAt.congr_of_eventuallyEq
    (periodizeZ_eventuallyEq hL hG ha0 ha q₀)

/-- The periodization of a profile odd in `z` and vanishing for `|z| > a`, `a < L/2`, is odd. -/
theorem periodizeZ_neg (hG : ∀ s z, a < |z| → G (s, z) = 0) (ha : a < L / 2)
    (hodd : ∀ s z, G (s, -z) = -G (s, z)) (s z : ℝ) :
    periodizeZ hL G (s, -z) = -periodizeZ hL G (s, z) := by
  simp only [periodizeZ]
  set w := toIcoMod hL (-(L / 2)) z
  have hw := toIcoMod_mem_Ico hL (-(L / 2)) z
  obtain ⟨n, hn⟩ : ∃ n : ℤ, z - w = n • L := ⟨_, self_sub_toIcoMod hL (-(L / 2)) z⟩
  rw [zsmul_eq_mul] at hn
  by_cases h : w = -(L / 2)
  · have h1 : G (s, w) = 0 := hG s w (by rw [h, abs_neg, abs_of_pos (by linarith)]; linarith)
    have h2 : toIcoMod hL (-(L / 2)) (-z) = -(L / 2) := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨le_rfl, by linarith⟩, 1 - n, ?_⟩
      rw [zsmul_eq_mul]
      push_cast
      have : z = w + n * L := by linarith
      rw [this, h]
      ring
    rw [h1, h2, neg_zero]
    exact hG s _ (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  · have hw' : -(L / 2) < w := lt_of_le_of_ne hw.1 (Ne.symm h)
    have h2 : toIcoMod hL (-(L / 2)) (-z) = -w := by
      rw [toIcoMod_eq_iff]
      refine ⟨⟨by linarith [hw.2], by linarith⟩, -n, ?_⟩
      rw [zsmul_eq_mul]
      push_cast
      linarith
    rw [h2, hodd]

end Periodization

/-! ### Planar coordinates of profiles -/

/-- `∂_s (H ∘ pointPairEquiv⁻¹) = (∂₀ H) ∘ pointPairEquiv⁻¹`. -/
theorem sDeriv_comp_pointPairEquiv_symm (H : ℝ^2 → ℝ) :
    sDeriv (H ∘ pointPairEquiv.symm) = (∂[(0 : Fin 2)] H) ∘ pointPairEquiv.symm := by
  funext q
  have h1 : pointPairEquiv.symm (1, 0) = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  simp only [sDeriv, Function.comp_apply, PDE.partialDeriv]
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    h1]

/-- `∂_z (H ∘ pointPairEquiv⁻¹) = (∂₁ H) ∘ pointPairEquiv⁻¹`. -/
theorem zDeriv_comp_pointPairEquiv_symm (H : ℝ^2 → ℝ) :
    zDeriv (H ∘ pointPairEquiv.symm) = (∂[(1 : Fin 2)] H) ∘ pointPairEquiv.symm := by
  funext q
  have h1 : pointPairEquiv.symm (0, 1) = EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  simp only [zDeriv, Function.comp_apply, PDE.partialDeriv]
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    h1]

/-- **The derivatives `∂_s^l ∂_z^j` of `H ∘ pointPairEquiv⁻¹`** are the coordinate derivatives of
`H` along the word `0^l 1^j`. -/
theorem iterate_sDeriv_zDeriv_comp_pointPairEquiv_symm (H : ℝ^2 → ℝ) (l j : ℕ) :
    sDeriv^[l] (zDeriv^[j] (H ∘ pointPairEquiv.symm)) =
      (fun x ↦ iteratedPartialDeriv (List.replicate l 0 ++ List.replicate j 1) H x) ∘
        pointPairEquiv.symm := by
  have hz : ∀ j, zDeriv^[j] (H ∘ pointPairEquiv.symm) =
      (fun x ↦ iteratedPartialDeriv (List.replicate j 1) H x) ∘ pointPairEquiv.symm := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, zDeriv_comp_pointPairEquiv_symm]
      rfl
  have hs : ∀ l (K : ℝ^2 → ℝ), sDeriv^[l] (K ∘ pointPairEquiv.symm) =
      (fun x ↦ iteratedPartialDeriv (List.replicate l 0) K x) ∘ pointPairEquiv.symm := by
    intro l K
    induction l with
    | zero => rfl
    | succ l ih =>
      rw [Function.iterate_succ_apply', ih, sDeriv_comp_pointPairEquiv_symm]
      rfl
  rw [hz, hs]
  funext q
  simp only [Function.comp_apply]
  exact (PDE.iteratedPartialDeriv_append _ _ H _).symm

end

end Euler.Cylinder
