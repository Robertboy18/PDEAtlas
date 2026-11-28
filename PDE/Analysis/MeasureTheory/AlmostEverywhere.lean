/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Separation.CompletelyRegular

set_option linter.style.header false

/-!
# Null sets and almost everywhere statements

The lemmas state that lines and countable unions of null sets have measure zero, and pass a property
that holds almost everywhere through a measure preserving map or a restriction. The proofs use
`measure_mono_null`, `ae_restrict_iff'` and the quasi measure preserving maps of Mathlib.

## Main results

* `PDE.Analysis.ae_add_eq_of_periodic_ae_Ioo`: Let `f : ℝ → ℝ` be periodic with period `2 * π` and
  let `s` be real. If `f (θ + s) = f θ` for almost every `θ` in `Ioo (-π) π`, then `f (θ + s) = f θ`
  for almost every real `θ`.
* `PDE.Analysis.ae_Ioi_norm_apply_le_exp_mul`: Let `T τ` be continuous linear maps on a real Hilbert
  space `E` with `‖T τ‖ ≤ Real.exp (-(τ / 4))` for all `τ ≥ 0`, and let `G : ℝ → E` satisfy
  `‖G σ‖ ≤ C` for all `σ`. Then for all real `σ` and `P`, the bound
  `‖T τ (G (σ - τ / P))‖ ≤ Real.exp (-(1 / 4) * τ) * C` holds for almost every `τ` in `Ioi 0`.
* `PDE.Analysis.ae_differentiableAt_fst_of_lipschitzOnWith`: Let `a ≤ b` and `lo ≤ hi`, and let
  `G : ℝ × ℝ → ℂ` be Lipschitz on the rectangle `Icc a b ×ˢ Icc lo hi`. Then for almost every `p` in
  this rectangle, `fun r ↦ G (r, p.2)` is differentiable at `p.1`.
* `PDE.Analysis.ae_differentiableAt_fst_of_lipschitzWith`: If `G : ℝ × ℝ → ℂ` is Lipschitz, then for
  almost every `p` in `ℝ × ℝ` the function `fun r ↦ G (r, p.2)` is differentiable at `p.1`.
* `PDE.Analysis.ae_differentiableAt_snd_of_lipschitzOnWith`: Let `lo ≤ hi` and `a ≤ b`, and let
  `G : ℝ × ℝ → ℂ` be Lipschitz on the rectangle `Icc lo hi ×ˢ Icc a b`. Then for almost every `p` in
  this rectangle, `fun z ↦ G (p.1, z)` is differentiable at `p.2`.
* `PDE.Analysis.ae_differentiableAt_snd_of_lipschitzWith`: If `G : ℝ × ℝ → ℂ` is Lipschitz, then for
  almost every `p` in `ℝ × ℝ` the function `fun z ↦ G (p.1, z)` is differentiable at `p.2`.
* `PDE.Analysis.ae_of_ae_mem_Icc_of_fract`: Let `p` be a property of real numbers such that `p σ`
  holds whenever `p (Int.fract σ)` holds. If `p σ` holds for almost every `σ` in `Icc 0 1`, then
  `p σ` holds for almost every real `σ`.
* `PDE.Analysis.ae_prod_fst_of_ae`: If a property `P` holds for almost every real `x`, then `P p.1`
  holds for almost every `p : ℝ × ℝ`, both for Lebesgue measure.

There are 25 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace PDE.Analysis

/-- Let `T τ` be continuous linear maps on a real Hilbert space `E` with
`‖T τ‖ ≤ Real.exp (-(τ / 4))` for all `τ ≥ 0`, and let `G : ℝ → E` satisfy `‖G σ‖ ≤ C` for all `σ`.
Then for all real `σ` and `P`, the bound `‖T τ (G (σ - τ / P))‖ ≤ Real.exp (-(1 / 4) * τ) * C` holds
for almost every `τ` in `Ioi 0`. -/
theorem ae_Ioi_norm_apply_le_exp_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (G : ℝ → E) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (σ : ℝ) :
    ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), ‖T τ (G (σ - τ / P))‖ ≤ Real.exp (-(1 / 4) * τ) * C := by
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ ↦ ?_
  have hτ' : (0 : ℝ) ≤ τ := le_of_lt hτ
  have he : Real.exp (-(τ / 4)) = Real.exp (-(1 / 4) * τ) := by ring_nf
  calc ‖T τ (G (σ - τ / P))‖ ≤ ‖T τ‖ * ‖G (σ - τ / P)‖ := (T τ).le_opNorm _
    _ ≤ Real.exp (-(τ / 4)) * C :=
      mul_le_mul (hnorm τ hτ') (hC _) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (-(1 / 4) * τ) * C := by rw [he]

/-- Let `f : ℝ → ℝ` be periodic with period `2 * π` and let `s` be real. If `f (θ + s) = f θ` for
almost every `θ` in `Ioo (-π) π`, then `f (θ + s) = f θ` for almost every real `θ`. The proof
translates the exceptional null set, together with the point `π`, by every integer multiple of
`2 * π` and uses periodicity. -/
theorem ae_add_eq_of_periodic_ae_Ioo {f : ℝ → ℝ} (hper : Function.Periodic f (2 * π)) (s : ℝ)
    (h : ∀ᵐ θ ∂(volume.restrict (Ioo (-π) π)), f (θ + s) = f θ) :
    ∀ᵐ θ ∂volume, f (θ + s) = f θ := by
  have h1 : ∀ᵐ θ ∂volume, θ ∈ Ioo (-π) π → f (θ + s) = f θ :=
    (ae_restrict_iff' measurableSet_Ioo).1 h
  have h2 : ∀ᵐ θ ∂volume, θ ∉ ({π} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 (measure_singleton π)
  have hQ := h1.and h2
  have h3 : ∀ n : ℤ, ∀ᵐ θ ∂volume, (θ - n • (2 * π) ∈ Ioo (-π) π →
      f (θ - n • (2 * π) + s) = f (θ - n • (2 * π))) ∧ θ - n • (2 * π) ∉ ({π} : Set ℝ) :=
    fun n ↦ (measurePreserving_sub_right volume (n • (2 * π))).quasiMeasurePreserving.ae hQ
  filter_upwards [ae_all_iff.2 h3] with θ hθ
  set n : ℤ := toIocDiv two_pi_pos (-π) θ with hn
  have hm := toIocMod_mem_Ioc two_pi_pos (-π) θ
  rw [← self_sub_toIocDiv_zsmul, ← hn] at hm
  obtain ⟨hq1, hq2⟩ := hθ n
  have hne : θ - n • (2 * π) ≠ π := fun e ↦ hq2 (by rw [e]; rfl)
  have hin : θ - n • (2 * π) ∈ Ioo (-π) π := ⟨hm.1, lt_of_le_of_ne (by linarith [hm.2]) hne⟩
  have e1 := hq1 hin
  have e2 : f (θ + s - n • (2 * π)) = f (θ + s) := hper.sub_zsmul_eq n
  have e3 : f (θ - n • (2 * π)) = f θ := hper.sub_zsmul_eq n
  rw [← e2, ← e3, ← e1]
  congr 1
  ring

/-- If `G : ℝ × ℝ → ℂ` is Lipschitz, then for almost every `p` in `ℝ × ℝ` the function
`fun r ↦ G (r, p.2)` is differentiable at `p.1`. The proof uses that the set of such `p` is
measurable and that each function `fun r ↦ G (r, z)` is Lipschitz, hence differentiable almost
everywhere. -/
theorem ae_differentiableAt_fst_of_lipschitzWith {G : ℝ × ℝ → ℂ} {C : NNReal}
    (hG : LipschitzWith C G) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun r ↦ G (r, p.2)) p.1 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun r ↦ G (r, x.2)) x.1} := by
    have h0 := measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun z r ↦ G (r, z))
      (hG.continuous.comp continuous_swap)
    exact measurable_swap h0
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas]
  refine Filter.Eventually.of_forall fun z ↦ ?_
  have hl : LipschitzWith (C * 1) (fun r ↦ G (r, z)) := hG.comp (LipschitzWith.prodMk_right z)
  exact hl.ae_differentiableAt_real

/-- If `G : ℝ × ℝ → ℂ` is Lipschitz, then for almost every `p` in `ℝ × ℝ` the function
`fun z ↦ G (p.1, z)` is differentiable at `p.2`. The proof uses that the set of such `p` is
measurable and that each function `fun z ↦ G (r, z)` is Lipschitz, hence differentiable almost
everywhere. -/
theorem ae_differentiableAt_snd_of_lipschitzWith {G : ℝ × ℝ → ℂ} {C : NNReal}
    (hG : LipschitzWith C G) :
    ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun z ↦ G (p.1, z)) p.2 := by
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun z ↦ G (x.1, z)) x.2} :=
    measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun r z ↦ G (r, z)) hG.continuous
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
  refine Filter.Eventually.of_forall fun r ↦ ?_
  have hl : LipschitzWith (C * 1) (fun z ↦ G (r, z)) := hG.comp (LipschitzWith.prodMk_left r)
  exact hl.ae_differentiableAt_real

/-- For a finite family of reals `lo : Fin k → ℝ`, almost every real `r` satisfies `r ≠ lo s` for
all `s`. -/
theorem ae_forall_fin_ne {k : ℕ} (lo : Fin k → ℝ) : ∀ᵐ r : ℝ, ∀ s, r ≠ lo s := by
  rw [ae_all_iff]
  intro s
  rw [ae_iff]
  simp

/-- Let `p` be a property of real numbers such that `p σ` holds whenever `p (Int.fract σ)` holds. If
`p σ` holds for almost every `σ` in `Icc 0 1`, then `p σ` holds for almost every real `σ`. The proof
translates the almost everywhere statement by every integer and evaluates it at `σ - ⌊σ⌋`. -/
theorem ae_of_ae_mem_Icc_of_fract {p : ℝ → Prop} (hper : ∀ σ, p (Int.fract σ) → p σ)
    (h : ∀ᵐ σ, σ ∈ Set.Icc (0 : ℝ) 1 → p σ) : ∀ᵐ σ, p σ := by
  have hn : ∀ n : ℤ, ∀ᵐ σ : ℝ, σ - (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 → p (σ - (n : ℝ)) := fun n ↦
    (measurePreserving_sub_right volume (n : ℝ)).quasiMeasurePreserving.ae h
  rw [← ae_all_iff] at hn
  filter_upwards [hn] with σ hσ
  apply hper
  have hf : σ - ((⌊σ⌋ : ℤ) : ℝ) = Int.fract σ := Int.self_sub_floor σ
  have hmem := hσ ⌊σ⌋
  rw [hf] at hmem
  exact hmem ⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩

/-- If a property `P` holds for almost every real `x`, then `P p.1` holds for almost every
`p : ℝ × ℝ`, both for Lebesgue measure. -/
theorem ae_prod_fst_of_ae {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, P x) : ∀ᵐ p : ℝ × ℝ, P p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

/-- If a property `P` holds for almost every real `x`, then `P p.2` holds for almost every
`p : ℝ × ℝ`, both for Lebesgue measure. -/
theorem ae_prod_snd_of_ae {P : ℝ → Prop} (h : ∀ᵐ x : ℝ, P x) : ∀ᵐ p : ℝ × ℝ, P p.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

/-- For real `hi`, `zlo`, `zhi`, almost every `p`, for Lebesgue measure on `ℝ × ℝ` restricted to
`Icc 0 hi ×ˢ Icc zlo zhi`, satisfies `0 < p.1`. The proof uses that the line `{0} ×ˢ univ` has
measure zero. -/
theorem ae_restrict_Icc_prod_Icc_fst_pos (hi zlo zhi : ℝ) :
    ∀ᵐ p ∂(volume.restrict (Set.Icc (0 : ℝ) hi ×ˢ Set.Icc zlo zhi)), 0 < p.1 := by
  have hnull : (volume : Measure (ℝ × ℝ)) (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
  have h0 := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc), ae_restrict_of_ae h0]
    with p hp hn
  have hne : p.1 ≠ 0 := fun h ↦ hn ⟨h, trivial⟩
  exact lt_of_le_of_ne hp.1.1 (Ne.symm hne)

/-- Let `f ι : ℝ × ℝ → ℝ`, for `ι : ℤ × ℤ`, satisfy `0 ≤ f ι p` for all `ι` at almost every `p` for
a measure `μ`, with each `p ↦ ENNReal.ofReal (f ι p)` almost everywhere measurable. If
`∑' ι, ∫⁻ p, ENNReal.ofReal (f ι p) ∂μ ≠ ⊤`, then `ι ↦ f ι p` is summable for almost every `p`. -/
theorem ae_summable_of_lintegral {μ : Measure (ℝ × ℝ)} {f : ℤ × ℤ → ℝ × ℝ → ℝ}
    (hf0 : ∀ᵐ p ∂μ, ∀ ι, 0 ≤ f ι p) (hm : ∀ ι, AEMeasurable (fun p ↦ ENNReal.ofReal (f ι p)) μ)
    (hfin : ∑' ι, ∫⁻ p, ENNReal.ofReal (f ι p) ∂μ ≠ ⊤) : ∀ᵐ p ∂μ, Summable fun ι ↦ f ι p := by
  rw [← lintegral_tsum hm] at hfin
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hm) hfin, hf0] with p hp h0
  refine (ENNReal.summable_toReal hp.ne).congr fun ι ↦ ?_
  exact ENNReal.toReal_ofReal (h0 ι)

/-- Let `n` and `J` be finite types, `s` a measurable set in `ℝ × ℝ`, and `φ : n → ℝ × ℝ → J → ℂ`.
If for all `i` and `j` there is a real `c` with `‖φ i p j‖ ≤ c` for all `p ∈ s`, then there is
`C ≥ 0` such that, for almost every `p` in `s`, `‖φ i p j‖ ≤ C` for all `i` and `j`. The constant is
the sum of the absolute values of the individual bounds. -/
theorem exists_nonneg_ae_forall_norm_le {n J : Type*} [Finite n] [Finite J] {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s)
    (φ : n → ℝ × ℝ → J → ℂ) (h : ∀ i j, ∃ c : ℝ, ∀ p ∈ s, ‖φ i p j‖ ≤ c) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ p ∂(volume.restrict s), ∀ i j, ‖φ i p j‖ ≤ C := by
  have := Fintype.ofFinite n
  have := Fintype.ofFinite J
  choose c hc using h
  refine ⟨∑ i, ∑ j, |c i j|, Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
      abs_nonneg _, ?_⟩
  refine ae_restrict_of_forall_mem hs fun p hp i j ↦ ?_
  calc ‖φ i p j‖ ≤ |c i j| := (hc i j p hp).trans (le_abs_self _)
    _ ≤ ∑ j', |c i j'| := Finset.single_le_sum (f := fun j' ↦ |c i j'|) (fun _ _ ↦ abs_nonneg _)
        (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |c i' j'| := Finset.single_le_sum (f := fun i' ↦ ∑ j', |c i' j'|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)

/-- If `p ∈ S` for almost every `p` for a measure `μ` on `ℝ × ℝ`, then for every `f : ℝ × ℝ → ℂ` the
indicator `S.indicator f` equals `f` almost everywhere for `μ`. -/
theorem indicator_ae_eq_self_of_ae_mem {μ : Measure (ℝ × ℝ)} {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hS : ∀ᵐ p ∂μ, p ∈ S) :
    S.indicator f =ᵐ[μ] f := by
  filter_upwards [hS] with p hp
  rw [Set.indicator_of_mem hp]

/-- If `¬ lo < hi`, then for every set `s` of real numbers the product `Icc lo hi ×ˢ s` has Lebesgue
measure zero in `ℝ × ℝ`. -/
theorem volume_Icc_prod_null_of_not_lt {lo hi : ℝ} (h : ¬ lo < hi) (s : Set ℝ) :
    (volume : Measure (ℝ × ℝ)) (Icc lo hi ×ˢ s) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  have h0 : (volume : Measure ℝ) (Icc lo hi) = 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
    linarith [not_lt.mp h]
  rw [h0, zero_mul]

/-- Let `E` be a set of reals with `φ + n * (2 * π) ∈ E ↔ φ ∈ E` for all integers `n` and reals `φ`.
If `E ∩ Ioo (-π) π` has Lebesgue measure zero, then `E` has Lebesgue measure zero. The proof covers
`ℝ` by the translates of `Ioc (-π) π` by integer multiples of `2 * π` and uses that Lebesgue measure
is invariant under translation. -/
theorem volume_eq_zero_of_periodic {E : Set ℝ}
    (hper : ∀ (n : ℤ) (φ : ℝ), φ + n * (2 * Real.pi) ∈ E ↔ φ ∈ E)
    (h0 : volume (E ∩ Set.Ioo (-Real.pi) Real.pi) = 0) : volume E = 0 := by
  have hp : (0 : ℝ) < 2 * Real.pi := by positivity
  have hIoc : volume (E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi)) = 0 := by
    refine le_antisymm ?_ zero_le
    have hsub : E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) ⊆
        (E ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi} := by
      rintro x ⟨hx, hx1, hx2⟩
      rcases lt_or_eq_of_le hx2 with h | h
      · exact Or.inl ⟨hx, hx1, by linarith⟩
      · exact Or.inr (by simp only [Set.mem_singleton_iff]; linarith)
    calc volume (E ∩ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))
        ≤ volume ((E ∩ Set.Ioo (-Real.pi) Real.pi) ∪ {Real.pi}) := measure_mono hsub
      _ ≤ volume (E ∩ Set.Ioo (-Real.pi) Real.pi) + volume ({Real.pi} : Set ℝ) :=
          measure_union_le _ _
      _ = 0 := by rw [h0, Real.volume_singleton, add_zero]
  have hn : ∀ n : ℤ, volume (E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi))
      (-Real.pi + (n + 1) • (2 * Real.pi))) = 0 := by
    intro n
    have e : E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi)) (-Real.pi + (n + 1) • (2 * Real.pi)) =
        (fun x ↦ x + -(n * (2 * Real.pi))) ⁻¹' (E ∩ Set.Ioc (-Real.pi)
            (-Real.pi + 2 * Real.pi)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, zsmul_eq_mul]
      have hx := hper (-n) x
      push_cast at hx
      rw [show x + -(n * (2 * Real.pi)) = x + -(n : ℝ) * (2 * Real.pi) by ring, hx]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by linarith, by push_cast at h3; linarith⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, by linarith, by push_cast; linarith⟩
    rw [e, measure_preimage_add_right, hIoc]
  have hU : E = ⋃ n : ℤ, E ∩ Set.Ioc (-Real.pi + n • (2 * Real.pi))
      (-Real.pi + (n + 1) • (2 * Real.pi)) := by
    rw [← Set.inter_iUnion, iUnion_Ioc_add_zsmul hp, Set.inter_univ]
  rw [hU]
  exact measure_iUnion_null hn

/-- If `T ⊆ ℝ` is countable, then `T ×ˢ univ` has Lebesgue measure zero in `ℝ × ℝ`. -/
theorem volume_prod_univ_eq_zero_of_countable {T : Set ℝ} (hT : T.Countable) :
    (volume : Measure (ℝ × ℝ)) (T ×ˢ univ) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hT.measure_zero, zero_mul]

/-- For every real `x`, the vertical line `{p | p.1 = x}` in `ℝ × ℝ` has Lebesgue measure zero. -/
theorem volume_setOf_fst_eq (x : ℝ) : volume {p : ℝ × ℝ | p.1 = x} = 0 := by
  have e : {p : ℝ × ℝ | p.1 = x} = {x} ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]; simp

/-- The line `{p : ℝ × ℝ | p.1 = 0}` has Lebesgue measure zero in `ℝ × ℝ`. -/
theorem volume_setOf_fst_eq_zero : volume {p : ℝ × ℝ | p.1 = 0} = 0 := volume_setOf_fst_eq 0

/-- The set of points `q` of `(ℝ × ℝ) × ℝ` with `q.2 = k * π` for some integer `k` has Lebesgue
measure zero. -/
theorem volume_setOf_snd_eq_int_mul_pi :
    (volume : Measure ((ℝ × ℝ) × ℝ)) {q | ∃ k : ℤ, q.2 = k * π} = 0 := by
  have e : {q : (ℝ × ℝ) × ℝ | ∃ k : ℤ, q.2 = k * π} =
      (univ : Set (ℝ × ℝ)) ×ˢ range (fun k : ℤ ↦ (k : ℝ) * π) := by
    ext q; simp [eq_comm]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, (countable_range _).measure_zero, mul_zero]

/-- For every real `t`, the set `{b : ℝ | b ^ 2 = t}` has Lebesgue measure zero, since it is
contained in the finite set `{√t, -√t}`. -/
theorem volume_setOf_sq_eq_eq_zero (t : ℝ) : volume {b : ℝ | b ^ 2 = t} = 0 := by
  refine measure_mono_null (t := {Real.sqrt t, -Real.sqrt t}) (fun b hb ↦ ?_)
      ((Set.toFinite _).measure_zero _)
  have hb' : b ^ 2 = t := hb
  have habs : |b| = Real.sqrt t := by rw [← hb', Real.sqrt_sq_eq_abs]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact (abs_eq (Real.sqrt_nonneg t)).1 habs

/-- For every real `v`, the line `{v} ×ˢ univ` has Lebesgue measure zero in `ℝ × ℝ`. -/
theorem volume_singleton_prod_univ (v : ℝ) : (volume : Measure (ℝ × ℝ)) ({v} ×ˢ univ) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

/-- If `T ⊆ ℝ` is countable, then `univ ×ˢ T` has Lebesgue measure zero in `ℝ × ℝ`. -/
theorem volume_univ_prod_eq_zero_of_countable {T : Set ℝ} (hT : T.Countable) :
    (volume : Measure (ℝ × ℝ)) (univ ×ˢ T) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, hT.measure_zero, mul_zero]

/-- For every real `v`, the line `univ ×ˢ {v}` has Lebesgue measure zero in `ℝ × ℝ`. -/
theorem volume_univ_prod_singleton (v : ℝ) : (volume : Measure (ℝ × ℝ)) (univ ×ˢ {v}) = 0 := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

/-- Let `a ≤ b` and `lo ≤ hi`, and let `G : ℝ × ℝ → ℂ` be Lipschitz on the rectangle
`Icc a b ×ˢ Icc lo hi`. Then for almost every `p` in this rectangle, `fun r ↦ G (r, p.2)` is
differentiable at `p.1`. The proof extends `G` to a Lipschitz function on `ℝ × ℝ` by projecting onto
the rectangle, and discards the null lines `p.1 = a` and `p.1 = b`. -/
theorem ae_differentiableAt_fst_of_lipschitzOnWith {G : ℝ × ℝ → ℂ} {C : NNReal} {a b lo hi : ℝ}
    (hab : a ≤ b) (hlh : lo ≤ hi)
    (hG : LipschitzOnWith C G (Icc a b ×ˢ Icc lo hi)) :
    ∀ᵐ p ∂(volume.restrict (Icc a b ×ˢ Icc lo hi)), DifferentiableAt ℝ (fun r ↦ G (r, p.2)) p.1 :=
        by
  let P : ℝ × ℝ → ℝ × ℝ := fun p ↦ ((projIcc a b hab p.1 : ℝ), (projIcc lo hi hlh p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc a b ×ˢ Icc lo hi := fun p ↦
      ⟨(projIcc a b hab p.1).2, (projIcc lo hi hlh p.2).2⟩
  have hPid : ∀ p ∈ Icc a b ×ˢ Icc lo hi, P p = p := fun p hp ↦
    Prod.ext (by simp [P, projIcc_of_mem hab hp.1]) (by simp [P, projIcc_of_mem hlh hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hab).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hlh).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p ↦ G (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q ↦
    (hG.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun r ↦ g (r, x.2)) x.1} := by
    have h0 := measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun z r ↦ g (r, z))
      (hg.continuous.comp continuous_swap)
    exact measurable_swap h0
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun r ↦ g (r, x.2)) x.1 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas, Measure.ae_ae_comm hmeas]
    refine Filter.Eventually.of_forall fun z ↦ ?_
    have hl : LipschitzWith (C * 1) (fun r ↦ g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
    exact hl.ae_differentiableAt_real
  have h1 := compl_mem_ae_iff.mpr (volume_singleton_prod_univ a)
  have h2 := compl_mem_ae_iff.mpr (volume_singleton_prod_univ b)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hp hmem hp1 hp2
  have hpa : p.1 ≠ a := fun e ↦ hp1 ⟨e, mem_univ _⟩
  have hpb : p.1 ≠ b := fun e ↦ hp2 ⟨e, mem_univ _⟩
  have hio : p.1 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1.1 (Ne.symm hpa), lt_of_le_of_ne hmem.1.2 hpb⟩
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hio.1 hio.2] with r hr
  simp only [hgdef, hPid (r, p.2) ⟨hr, hmem.2⟩]

/-- Let `lo ≤ hi` and `a ≤ b`, and let `G : ℝ × ℝ → ℂ` be Lipschitz on the rectangle
`Icc lo hi ×ˢ Icc a b`. Then for almost every `p` in this rectangle, `fun z ↦ G (p.1, z)` is
differentiable at `p.2`. The proof extends `G` to a Lipschitz function on `ℝ × ℝ` by projecting onto
the rectangle, and discards the null lines `p.2 = a` and `p.2 = b`. -/
theorem ae_differentiableAt_snd_of_lipschitzOnWith {G : ℝ × ℝ → ℂ} {C : NNReal} {lo hi a b : ℝ}
    (hlh : lo ≤ hi) (hab : a ≤ b)
    (hG : LipschitzOnWith C G (Icc lo hi ×ˢ Icc a b)) :
    ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc a b)), DifferentiableAt ℝ (fun z ↦ G (p.1, z)) p.2 :=
        by
  let P : ℝ × ℝ → ℝ × ℝ := fun p ↦ ((projIcc lo hi hlh p.1 : ℝ), (projIcc a b hab p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc lo hi ×ˢ Icc a b := fun p ↦
      ⟨(projIcc lo hi hlh p.1).2, (projIcc a b hab p.2).2⟩
  have hPid : ∀ p ∈ Icc lo hi ×ˢ Icc a b, P p = p := fun p hp ↦
    Prod.ext (by simp [P, projIcc_of_mem hlh hp.1]) (by simp [P, projIcc_of_mem hab hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hlh).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hab).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p ↦ G (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q ↦
    (hG.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hmeas : MeasurableSet {x : ℝ × ℝ | DifferentiableAt ℝ (fun z ↦ g (x.1, z)) x.2} :=
    measurableSet_of_differentiableAt_with_param (𝕜 := ℝ) (f := fun r z ↦ g (r, z)) hg.continuous
  have hall : ∀ᵐ x ∂(volume : Measure (ℝ × ℝ)), DifferentiableAt ℝ (fun z ↦ g (x.1, z)) x.2 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
    refine Filter.Eventually.of_forall fun r ↦ ?_
    have hl : LipschitzWith (C * 1) (fun z ↦ g (r, z)) := hg.comp (LipschitzWith.prodMk_left r)
    exact hl.ae_differentiableAt_real
  have h1 := compl_mem_ae_iff.mpr (volume_univ_prod_singleton a)
  have h2 := compl_mem_ae_iff.mpr (volume_univ_prod_singleton b)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem
      (measurableSet_Icc.prod measurableSet_Icc),
    ae_restrict_of_ae h1, ae_restrict_of_ae h2] with p hp hmem hp1 hp2
  have hpa : p.2 ≠ a := fun e ↦ hp1 ⟨mem_univ _, e⟩
  have hpb : p.2 ≠ b := fun e ↦ hp2 ⟨mem_univ _, e⟩
  have hio : p.2 ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.2.1 (Ne.symm hpa), lt_of_le_of_ne hmem.2.2 hpb⟩
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hio.1 hio.2] with z hz
  simp only [hgdef, hPid (p.1, z) ⟨hmem.1, hz⟩]

/-- A property that holds at almost every point of the circle `UnitAddCircle` holds at `t + a` for
almost every `t`, for every real `a`: a translation of the circle preserves its measure. -/
theorem ae_unitAddCircle_add_coe {p : UnitAddCircle → Prop} (a : ℝ)
    (h : ∀ᵐ t : UnitAddCircle, p t) :
    ∀ᵐ t : UnitAddCircle, p (t + (a : UnitAddCircle)) :=
  (measurePreserving_add_right (volume : Measure UnitAddCircle)
      (a : UnitAddCircle)).quasiMeasurePreserving.ae h

/-- For every real `x`, the horizontal line `{p | p.2 = x}` in `ℝ × ℝ` has Lebesgue measure zero. -/
theorem volume_setOf_snd_eq (x : ℝ) : volume {p : ℝ × ℝ | p.2 = x} = 0 := by
  have e : {p : ℝ × ℝ | p.2 = x} = (univ : Set ℝ) ×ˢ {x} := by ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]; simp

/-- The line `{q | q.2 = 0}` in `ℝ × ℝ` has Lebesgue measure zero. -/
theorem volume_setOf_snd_eq_zero : volume {q : ℝ × ℝ | q.2 = 0} = 0 := volume_setOf_snd_eq 0

/-- For every real `c`, almost every point `p` of `ℝ × ℝ` (Lebesgue measure) has `p.1 ≠ c`. The
first projection is quasi measure preserving and almost every real number differs from `c`. -/
theorem ae_fst_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ, p.1 ≠ c := by
  have h : ∀ᵐ x : ℝ, x ≠ c := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae h

/-- Almost every point `p` of `ℝ × ℝ` (Lebesgue measure) has `p.1 ≠ 0`. The exceptional set is
`{0} × ℝ`, of measure zero. -/
theorem ae_fst_ne_zero : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := ae_fst_ne 0

/-- For every real `c`, almost every point `p` of `ℝ × ℝ` (Lebesgue measure) has `p.2 ≠ c`. The
second projection is quasi measure preserving and almost every real number differs from `c`. -/
theorem ae_snd_ne (c : ℝ) : ∀ᵐ p : ℝ × ℝ, p.2 ≠ c := by
  have h : ∀ᵐ x : ℝ, x ≠ c := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).ae h

/-- Almost every point `p` of `ℝ × ℝ` (Lebesgue measure) has `p.2 ≠ 0`. The exceptional set is
`ℝ × {0}`, of measure zero. -/
theorem ae_snd_ne_zero : ∀ᵐ p : ℝ × ℝ, p.2 ≠ 0 := ae_snd_ne 0

/-- Let `s` be a measurable set of `ℝ × ℝ` with `0 ≤ p.1` for every `p` in `s`. If for almost every
`p` of `ℝ × ℝ` the property `P p` holds whenever `0 < p.1`, then `P p` holds for almost every
`p` in `s`. The points with `p.1 = 0` form a null set. -/
theorem ae_restrict_of_ae_fst_pos_imp {P : ℝ × ℝ → Prop} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (h0 : ∀ p ∈ s, 0 ≤ p.1)
    (h : ∀ᵐ p ∂volume, 0 < p.1 → P p) : ∀ᵐ p ∂(volume.restrict s), P p := by
  rw [ae_restrict_iff' hs]
  filter_upwards [h, ae_fst_ne_zero] with p hp hne hmem
  exact hp (lt_of_le_of_ne (h0 p hmem) (Ne.symm hne))

/-- The set of the points `((a, b), c)` of `(ℝ × ℝ) × ℝ` with `a = 0` has Lebesgue measure zero. -/
theorem volume_setOf_fst_fst_eq_zero : volume {x : (ℝ × ℝ) × ℝ | x.1.1 = 0} = 0 := by
  have : {x : (ℝ × ℝ) × ℝ | x.1.1 = 0} = ({0} ×ˢ univ) ×ˢ univ := by ext x; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]
  simp

end PDE.Analysis
