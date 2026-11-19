/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import PDE.Analysis.MeasureTheory.Lp.Equiv

/-!
# Bochner `L²` duality for Hilbert-valued functions

Let `W` be a real Hilbert space. Applying the Riesz isomorphism `W* ≃ W` pointwise gives a
continuous linear equivalence `L²(μ; W*) ≃ L²(μ; W)`. Under it the integrated duality pairing
`∫ g(t)(u(t)) dμ` of `g ∈ L²(μ; W*)` and `u ∈ L²(μ; W)` is the `L²(μ; W)` inner product of the
Riesz transport of `g` with `u`. Hence the pairing is integrable, bounded by the product of the
`L²` norms, and continuous under strong `L²` convergence of both arguments. We also show that
every element of `W**` is evaluation at a vector of `W`.

Pointwise, the isomorphism is Mathlib's Riesz map `InnerProductSpace.toDual` (Evans,
Appendix D.3, Theorem 2). Evans uses weak limits in `L²(0, T; H⁻¹(U))` of exactly this kind
in the proof of §7.1.2, Theorem 3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.3, Theorem 2 (Riesz Representation Theorem), and
  §7.1.2, proof of Theorem 3, (27). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped InnerProductSpace Topology

namespace PDE.Analysis.Evolution

variable {α W : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- A real Hilbert space is reflexive: every continuous linear functional on `W*` is
evaluation at some vector of `W`. -/
theorem exists_eq_evaluation_of_doubleDual
    (ell : StrongDual ℝ (StrongDual ℝ W)) :
    ∃ w : W, ∀ f : StrongDual ℝ W, ell f = f w := by
  let q : StrongDual ℝ W := ell.comp
    (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv.toContinuousLinearMap
  let w : W := (InnerProductSpace.toDual ℝ W).symm q
  refine ⟨w, ?_⟩
  intro f
  let y : W := (InnerProductSpace.toDual ℝ W).symm f
  have hf : InnerProductSpace.toDual ℝ W y = f :=
    (InnerProductSpace.toDual ℝ W).apply_symm_apply f
  calc
    ell f = ell (InnerProductSpace.toDual ℝ W y) := by rw [hf]
    _ = q y := rfl
    _ = inner ℝ w y := by
      exact (InnerProductSpace.toDual_symm_apply (x := y) (y := q)).symm
    _ = inner ℝ y w := real_inner_comm _ _
    _ = f w := by
      rw [← hf]
      rfl

/-- Pointwise Riesz representation as a continuous linear equivalence
`L²(μ; W*) ≃ L²(μ; W)`. -/
def rieszLpEquiv :
    Lp (StrongDual ℝ W) 2 μ ≃L[ℝ] Lp W 2 μ :=
  (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv.symm.compLpLEquiv 2 μ

/-- Pointwise Riesz representation, lifted to a continuous map
`L²(μ; W*) → L²(μ; W)`. -/
def rieszFromDualLp :
    Lp (StrongDual ℝ W) 2 μ →L[ℝ] Lp W 2 μ :=
  rieszLpEquiv.toContinuousLinearMap

/-- The inverse pointwise Riesz map, lifted to Bochner `L²`. -/
def rieszToDualLp :
    Lp W 2 μ →L[ℝ] Lp (StrongDual ℝ W) 2 μ :=
  rieszLpEquiv.symm.toContinuousLinearMap

/-- `rieszFromDualLp` acts pointwise almost everywhere. -/
theorem rieszFromDualLp_apply_ae (g : Lp (StrongDual ℝ W) 2 μ) :
    (rieszFromDualLp g : α → W) =ᵐ[μ]
      fun t ↦ (InnerProductSpace.toDual ℝ W).symm (g t) :=
  (ContinuousLinearEquiv.toContinuousLinearMap
    (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv.symm).coeFn_compLpL g

/-- `rieszToDualLp` acts pointwise almost everywhere. -/
theorem rieszToDualLp_apply_ae (g : Lp W 2 μ) :
    (rieszToDualLp g : α → StrongDual ℝ W) =ᵐ[μ]
      fun t ↦ InnerProductSpace.toDual ℝ W (g t) :=
  (ContinuousLinearEquiv.toContinuousLinearMap
    (InnerProductSpace.toDual ℝ W).toContinuousLinearEquiv).coeFn_compLpL g

/-- The lifted Riesz maps are inverse in this direction. -/
@[simp]
theorem rieszFromDualLp_rieszToDualLp (g : Lp W 2 μ) :
    rieszFromDualLp (rieszToDualLp g) = g :=
  rieszLpEquiv.apply_symm_apply g

/-- The lifted Riesz maps are inverse in the dual-to-primal direction. -/
@[simp]
theorem rieszToDualLp_rieszFromDualLp
    (g : Lp (StrongDual ℝ W) 2 μ) :
    rieszToDualLp (rieszFromDualLp g) = g :=
  rieszLpEquiv.symm_apply_apply g

/-- `∫ g(t)(v) φ(t) dμ = ∫ ⟪R g(t), v⟫ φ(t) dμ`, where `R g = rieszFromDualLp g` is the
pointwise Riesz representative. -/
theorem integral_dual_pairing_eq_riesz
    (g : Lp (StrongDual ℝ W) 2 μ)
    (v : W) (φ : Lp ℝ 2 μ) :
    (∫ t, g t v * φ t ∂μ) =
      ∫ t, inner ℝ (rieszFromDualLp g t) v * φ t ∂μ := by
  apply integral_congr_ae
  filter_upwards [rieszFromDualLp_apply_ae g] with t ht
  rw [ht, InnerProductSpace.toDual_symm_apply]

/-- The integrated duality pairing `∫ g(t)(u(t)) dμ` is the `L²(μ; W)` inner product of the
Riesz representative of `g` with `u`. -/
theorem integral_dual_pairing_eq_L2_inner
    (g : Lp (StrongDual ℝ W) 2 μ) (u : Lp W 2 μ) :
    (∫ t, g t (u t) ∂μ) = inner ℝ (rieszFromDualLp g) u := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rieszFromDualLp_apply_ae g] with t ht
  rw [ht, InnerProductSpace.toDual_symm_apply]

/-- The pointwise duality product of two Bochner `L²` functions is
integrable. -/
theorem integrable_dual_pairing
    (g : Lp (StrongDual ℝ W) 2 μ) (u : Lp W 2 μ) :
    Integrable (fun t ↦ g t (u t)) μ := by
  have hinner := L2.integrable_inner (𝕜 := ℝ) (rieszFromDualLp g) u
  apply hinner.congr
  filter_upwards [rieszFromDualLp_apply_ae g] with t ht
  rw [ht, InnerProductSpace.toDual_symm_apply]

/-- Unbundled form of `integrable_dual_pairing`. -/
theorem integrable_dual_pairing_of_memLp
    {g : α → StrongDual ℝ W} {u : α → W}
    (hg : MemLp g 2 μ) (hu : MemLp u 2 μ) :
    Integrable (fun t ↦ g t (u t)) μ := by
  let G : Lp (StrongDual ℝ W) 2 μ := hg.toLp g
  let U : Lp W 2 μ := hu.toLp u
  have h := integrable_dual_pairing G U
  apply h.congr
  filter_upwards [hg.coeFn_toLp, hu.coeFn_toLp] with t hgt hut
  rw [show G t = g t by exact hgt, show U t = u t by exact hut]

/-- Hölder bound for the integrated duality pairing:
`‖∫ g(t)(u(t)) dμ‖ ≤ ‖R g‖_{L²} ‖u‖_{L²}`, with `R g` the Riesz representative of `g`. -/
theorem norm_integral_dual_pairing_le
    (g : Lp (StrongDual ℝ W) 2 μ) (u : Lp W 2 μ) :
    ‖∫ t, g t (u t) ∂μ‖ ≤ ‖rieszFromDualLp g‖ * ‖u‖ := by
  rw [integral_dual_pairing_eq_L2_inner]
  exact norm_inner_le_norm _ _

/-- If `(u m)` and the Riesz representatives of `(g m)` are Cauchy in `L²`, then
`∫ (g m - g n)(t)((u m - u n)(t)) dμ → 0` as `m, n → ∞`. -/
theorem cauchy_integral_dual_pairing_sub
    (g : ℕ → Lp (StrongDual ℝ W) 2 μ) (u : ℕ → Lp W 2 μ)
    (hg : CauchySeq (fun m ↦ rieszFromDualLp (g m)))
    (hu : CauchySeq u) :
    ∀ η > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      ‖∫ t, (g m - g n) t ((u m - u n) t) ∂μ‖ < η := by
  intro η hη
  have hsqrt : 0 < √η := Real.sqrt_pos.2 hη
  obtain ⟨Ng, hNg⟩ := (Metric.cauchySeq_iff.mp hg) (√η) hsqrt
  obtain ⟨Nu, hNu⟩ := (Metric.cauchySeq_iff.mp hu) (√η) hsqrt
  refine ⟨max Ng Nu, ?_⟩
  intro m hm n hn
  have hgm : Ng ≤ m := le_max_left Ng Nu |>.trans hm
  have hgn : Ng ≤ n := le_max_left Ng Nu |>.trans hn
  have hum : Nu ≤ m := le_max_right Ng Nu |>.trans hm
  have hun : Nu ≤ n := le_max_right Ng Nu |>.trans hn
  have hgdist := hNg m hgm n hgn
  have hudist := hNu m hum n hun
  have hsqrtSq : √η * √η = η := by
    rw [← pow_two, Real.sq_sqrt hη.le]
  calc
    ‖∫ t, (g m - g n) t ((u m - u n) t) ∂μ‖ ≤
        ‖rieszFromDualLp (g m - g n)‖ * ‖u m - u n‖ :=
      norm_integral_dual_pairing_le (g m - g n) (u m - u n)
    _ = dist (rieszFromDualLp (g m)) (rieszFromDualLp (g n)) *
        dist (u m) (u n) := by
      rw [map_sub]
      simp only [dist_eq_norm]
    _ < √η * √η := by
      calc
        dist (rieszFromDualLp (g m)) (rieszFromDualLp (g n)) *
            dist (u m) (u n) ≤
            √η * dist (u m) (u n) :=
          mul_le_mul_of_nonneg_right hgdist.le dist_nonneg
        _ < √η * √η :=
          mul_lt_mul_of_pos_left hudist hsqrt
    _ = η := hsqrtSq

/-- If `u i → u` in `L²(μ; W)` and the Riesz representatives of `g i` converge to that of
`g` in `L²`, then `∫ g i (t)(u i (t)) dμ → ∫ g(t)(u(t)) dμ`. -/
theorem tendsto_integral_dual_pairing_of_tendsto_L2
    {ι : Type*} {l : Filter ι}
    {u : ι → Lp W 2 μ} {uLimit : Lp W 2 μ}
    {g : ι → Lp (StrongDual ℝ W) 2 μ}
    {gLimit : Lp (StrongDual ℝ W) 2 μ}
    (hu : Tendsto u l (nhds uLimit))
    (hg : Tendsto (fun i ↦ rieszFromDualLp (g i)) l
      (nhds (rieszFromDualLp gLimit))) :
    Tendsto (fun i ↦ ∫ t, g i t (u i t) ∂μ) l
      (nhds (∫ t, gLimit t (uLimit t) ∂μ)) := by
  simpa only [integral_dual_pairing_eq_L2_inner] using hg.inner hu

end PDE.Analysis.Evolution
