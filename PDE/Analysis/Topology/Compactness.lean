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

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.List.GetD
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.UniformSpace.Uniformizable
public import PDE.Analysis.Calculus.SmoothTransitionGlobalBounds
public import PDE.Analysis.LinearAlgebra.LinearMap

set_option linter.style.header false

/-!
# Compact sets, supports and bounded sets

The lemmas state that a set is compact or bounded, that a function built from compactly supported
ones has compact support, and that a continuous function is bounded on a compact set. The proofs use
`IsCompact.exists_bound_of_continuousOn`, `HasCompactSupport.mono` and the lemmas of Mathlib on
`tsupport`.

## Main results

* `PDE.Analysis.exists_subseq_tendsto_inner_of_norm_le`: Weak sequential compactness of bounded sets
  in a real Hilbert space: if `‖u n‖ ≤ C` for all `n`, then there are a strictly increasing
  `φ : ℕ → ℕ` and a vector `x` with `‖x‖ ≤ C` such that `inner ℝ (u (φ n)) y → inner ℝ x y` for
  every `y`.
* `PDE.Analysis.exists_abs_le_of_hasCompactSupport`: A continuous function `χ : ℝ → ℝ` with compact
  support is bounded: there is `C` with `|χ x| ≤ C` for all `x`.
* `PDE.Analysis.exists_eq_zero_of_notMem_Icc_neg`: If `χ : ℝ → ℝ` has compact support, then there is
  a real `Z` such that `χ z = 0` for every `z ∉ Icc (-Z) Z`.
* `PDE.Analysis.exists_le_abs_of_isCompact_ne_zero`: If `K` is a compact set of real numbers that
  does not contain `0`, then there are `δ > 0` and `R` with `δ ≤ |r|` and `|r| ≤ R` for all `r ∈ K`.
* `PDE.Analysis.exists_bound_eq_zero_of_hasCompactSupport`: A function `ψ : ℝ → ℝ` with compact
  support vanishes outside a bounded interval: there is `N` with `0 ≤ N` and `ψ z = 0` whenever
  `N < |z|`.
* `PDE.Analysis.exists_bound_of_periodic`: A continuous function `G : ℝ → E` into a normed group
  with `G (σ + 1) = G σ` for all `σ` is bounded: there is `C` with `‖G σ‖ ≤ C` for all `σ`.
* `PDE.Analysis.exists_pos_eq_zero_of_notMem_Icc`: If `χ : ℝ → ℝ` has compact support and every
  point of `tsupport χ` is positive, then there are `δ > 0` and `R` such that `χ r = 0` for every
  `r ∉ Icc δ R`.
* `PDE.Analysis.hasCompactSupport_of_eq_zero_of_lt_abs`: If `ψ : ℝ → ℝ` satisfies `ψ z = 0` for
  every `z` with `N < |z|`, for some real `N`, then `ψ` has compact support.

There are 30 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace PDE.Analysis

/-- If `p` is not in the closed support of `χ : ℝ × ℝ → ℂ`, then every point `q` close enough to `p`
is also outside `tsupport χ`. -/
theorem eventually_notMem_tsupport {χ : ℝ × ℝ → ℂ} {p : ℝ × ℝ} (hp : p ∉ tsupport χ) :
    ∀ᶠ q in 𝓝 p, q ∉ tsupport χ :=
  (isClosed_tsupport χ).isOpen_compl.mem_nhds hp

/-- A compact set `C ⊆ ℝ × ℝ` on which the first coordinate does not vanish is bounded and stays
away from the line `p.1 = 0`: there are `δ > 0` and `R` with `δ ≤ |p.1|`, `|p.1| ≤ R` and
`|p.2| ≤ R` for all `p ∈ C`. The proof takes for `δ` the minimum of `|p.1|` on `C` and for `R` the
radius of a closed ball around `0` that contains `C`. -/
theorem exists_abs_fst_bounds_of_isCompact {C : Set (ℝ × ℝ)} (hC : IsCompact C)
    (hne : ∀ p ∈ C, p.1 ≠ 0) :
    ∃ δ > 0, ∃ R : ℝ, C ⊆ {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ R} := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall 0
  by_cases h : C.Nonempty
  · obtain ⟨q, hq, hmin⟩ := hC.exists_isMinOn h (continuous_abs.comp continuous_fst).continuousOn
    refine ⟨|q.1|, abs_pos.2 (hne q hq), R, fun p hp ↦ ⟨hmin hp, ?_, ?_⟩⟩
    · have := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact (norm_fst_le p).trans this
    · have := hR hp
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact (norm_snd_le p).trans this
  · exact ⟨1, one_pos, 0, fun p hp ↦ absurd ⟨p, hp⟩ h⟩

/-- A continuous function `χ : ℝ → ℝ` with compact support is bounded: there is `C` with `|χ x| ≤ C`
for all `x`. -/
theorem exists_abs_le_of_hasCompactSupport {χ : ℝ → ℝ} (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : ∃ C, ∀ x, |χ x| ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hχ
  exact ⟨C, fun x ↦ by rw [← Real.norm_eq_abs]; exact hC x⟩

/-- A function `ψ : ℝ → ℝ` with compact support vanishes outside a bounded interval: there is `N`
with `0 ≤ N` and `ψ z = 0` whenever `N < |z|`. -/
theorem exists_bound_eq_zero_of_hasCompactSupport {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ N, 0 ≤ N ∧ ∀ z, N < |z| → ψ z = 0 := by
  obtain ⟨N, hN⟩ := (HasCompactSupport.isCompact hψc).isBounded.subset_closedBall 0
  refine ⟨max N 0, le_max_right _ _, fun z hz ↦ image_eq_zero_of_notMem_tsupport fun h ↦ ?_⟩
  have h1 := hN h
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  linarith [le_max_left N 0]

/-- A continuous function `G : ℝ → E` into a normed group with `G (σ + 1) = G σ` for all `σ` is
bounded: there is `C` with `‖G σ‖ ≤ C` for all `σ`. -/
theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] (G : ℝ → E)
    (hG : Continuous G) (hGp : ∀ σ, G (σ + 1) = G σ) : ∃ C, ∀ σ, ‖G σ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨C, fun σ ↦ ?_⟩
  obtain ⟨y, hy, hyeq⟩ := (show Function.Periodic G 1 from hGp).exists_mem_Ico₀ one_pos σ
  rw [hyeq]
  exact hC y (Ico_subset_Icc_self hy)

/-- If `ψ : ℝ → ℝ` has compact support, then there is a real `S` such that `ψ s = 0` and
`deriv ψ s = 0` whenever `S < |s|`. The topological support lies in a closed ball of radius `S`
around `0`, and `ψ` vanishes on the open set where `S < |s|`, so its derivative vanishes there too.
-/
theorem exists_deriv_eq_zero_of_hasCompactSupport {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) :
    ∃ S, ∀ s, S < |s| → ψ s = 0 ∧ deriv ψ s = 0 := by
  obtain ⟨S, hS⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  have hU : ∀ s', S < |s'| → ψ s' = 0 := fun s' hs' ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ by
    have := hS h
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    linarith)
  refine ⟨S, fun s hs ↦ ⟨hU s hs, ?_⟩⟩
  have h : ψ =ᶠ[𝓝 s] fun _ ↦ 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with s' hs'
    exact hU s' hs'
  rw [h.deriv_eq]
  exact deriv_const s 0

/-- Let `d` and `e : ℕ → ℕ → ℝ` be symmetric and satisfy `d n k ≤ 2 * d n j + 2 * d j k` and
`e n k ≤ 2 * e n j + 2 * e j k`. If for every `ε > 0` there is a finite set `S` of naturals such
that every `n` has some `k ∈ S` with `d n k < ε`, and likewise for `e`, then for every `ε > 0` there
is a finite set `S` such that every `n` has some `k ∈ S` with `d n k + e n k < ε`. The proof takes
such sets for `d` and `e` with `ε / 8` and picks, for each pair of their points that has a common
close index, one such index. -/
theorem exists_finset_add_lt_of_finset_lt (d e : ℕ → ℕ → ℝ)
    (hd : ∀ n k j, d n k ≤ 2 * d n j + 2 * d j k) (hds : ∀ n k, d n k = d k n)
    (he : ∀ n k j, e n k ≤ 2 * e n j + 2 * e j k) (hes : ∀ n k, e n k = e k n)
    (hnd : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, d n k < ε)
    (hne : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, e n k < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, d n k + e n k < ε := by
  classical
  intro ε hε
  obtain ⟨S₁, h₁⟩ := hnd (ε / 8) (by positivity)
  obtain ⟨S₂, h₂⟩ := hne (ε / 8) (by positivity)
  let P : ℕ × ℕ → Prop := fun p ↦ ∃ n, d n p.1 < ε / 8 ∧ e n p.2 < ε / 8
  let pick : ℕ × ℕ → ℕ := fun p ↦ if h : P p then h.choose else 0
  refine ⟨(S₁ ×ˢ S₂).image pick, fun n ↦ ?_⟩
  obtain ⟨a, ha, hna⟩ := h₁ n
  obtain ⟨b, hb, hnb⟩ := h₂ n
  have hP : P (a, b) := ⟨n, hna, hnb⟩
  refine ⟨pick (a, b), Finset.mem_image_of_mem _ (Finset.mem_product.mpr ⟨ha, hb⟩), ?_⟩
  have hs := hP.choose_spec
  have hpk : pick (a, b) = hP.choose := dite_eq_left hP
  rw [hpk]
  have t1 := hd n hP.choose a
  have t2 := he n hP.choose b
  rw [hds a hP.choose] at t1
  rw [hes b hP.choose] at t2
  linarith [hs.1, hs.2]

/-- If the range of a sequence `v : ℕ → X` in a pseudometric space is totally bounded, then for
every `η > 0` there is a finite set `I` of indices such that every `v n` satisfies
`dist (v n) (v i) < η` for some `i ∈ I`. The proof takes a finite `η`-net inside the range and
chooses one index for each of its points. -/
theorem exists_finset_dist_lt_of_totallyBounded {X : Type*} [PseudoMetricSpace X] (v : ℕ → X)
    (h : TotallyBounded (range v)) {η : ℝ} (hη : 0 < η) :
    ∃ I : Finset ℕ, ∀ n, ∃ i ∈ I, dist (v n) (v i) < η := by
  classical
  obtain ⟨t, hts, htf, hcov⟩ := totallyBounded_iff_subset.1 h _ (Metric.dist_mem_uniformity hη)
  let idx : X → ℕ := fun y ↦ if hy : y ∈ range v then hy.choose else 0
  refine ⟨htf.toFinset.image idx, fun n ↦ ?_⟩
  obtain ⟨y, hy, hny⟩ := mem_iUnion₂.1 (hcov (mem_range_self n))
  have hyr := hts hy
  refine ⟨idx y, Finset.mem_image_of_mem _ (htf.mem_toFinset.2 hy), ?_⟩
  have hidx : v (idx y) = y := by
    simp only [idx, dite_eq_left hyr]
    exact hyr.choose_spec
  rw [hidx]
  exact hny

/-- If `K` is a compact set of real numbers that does not contain `0`, then there are `δ > 0` and
`R` with `δ ≤ |r|` and `|r| ≤ R` for all `r ∈ K`. -/
theorem exists_le_abs_of_isCompact_ne_zero {K : Set ℝ} (hK : IsCompact K) (hKU : ∀ r ∈ K, r ≠ 0) :
    ∃ δ > 0, ∃ R : ℝ, ∀ r ∈ K, δ ≤ |r| ∧ |r| ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  by_cases h : K.Nonempty
  · obtain ⟨r0, hr0, hmin⟩ := hK.exists_isMinOn h continuous_abs.continuousOn
    refine ⟨|r0|, abs_pos.2 (hKU r0 hr0), R, fun r hr ↦ ⟨hmin hr, ?_⟩⟩
    have := hR hr
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  · exact ⟨1, one_pos, 0, fun r hr ↦ absurd ⟨r, hr⟩ h⟩

/-- If a compact set `K` of real numbers lies in `Ioo (-1) 1`, then there is `c < 1` with `t ≤ c`
for all `t ∈ K`. -/
theorem exists_lt_one_forall_le_of_isCompact {K : Set ℝ} (hK : IsCompact K) (hs : K ⊆ Ioo (-1) 1) :
    ∃ c < 1, ∀ t ∈ K, t ≤ c := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨0, by norm_num, by simp [h]⟩
  · exact ⟨sSup K, (hs (hK.sSup_mem h)).2, fun t ht ↦ le_csSup hK.bddAbove ht⟩

/-- A continuous function `f : ℝ × ℝ → ℝ` with compact support is bounded: there is `A ≥ 0` with
`|f x| ≤ A` for all `x`. -/
theorem exists_nonneg_abs_le_of_hasCompactSupport {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hcf : HasCompactSupport f) :
    ∃ A, 0 ≤ A ∧ ∀ x, |f x| ≤ A := by
  obtain ⟨A, hA⟩ := hcf.isCompact.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max A 0, le_max_right _ _, fun x ↦ ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (show |f x| ≤ A by simpa [Real.norm_eq_abs] using hA x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx, abs_zero]
    exact le_max_right _ _

/-- A continuous family `Λ : ℝ × ℝ → (E →L[ℝ] ℝ)` of continuous linear functionals on a real normed
space is bounded on the unit circle: there is `C` with `0 ≤ C` and
`‖Λ (Real.cos θ, Real.sin θ)‖ ≤ C` for all real `θ`. -/
theorem exists_norm_cos_sin_le_of_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (hΛ : Continuous Λ) :
    ∃ C, 0 ≤ C ∧ ∀ θ : ℝ, ‖Λ (Real.cos θ, Real.sin θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
      hΛ.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun θ ↦ (hC _ ?_).trans (le_max_left _ _)⟩
  rw [mem_closedBall_zero_iff, Prod.norm_def]
  exact max_le (by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one θ)
    (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)

/-- Let `E` be a finite-dimensional real normed space, `F` a real normed space, `1 ≤ d`, and
`f : E → F` continuous on `{x | x ≠ 0}` with `f (c • x) = c ^ d • f x` for all `c > 0` and all `x`.
Then there is `C ≥ 0` with `‖f x‖ ≤ C * ‖x‖ ^ d` for all `x`. Proof idea: `f` is bounded on the
compact unit sphere, every `x ≠ 0` is a positive multiple of a unit vector, and `f 0 = 0`. -/
theorem exists_norm_le_mul_pow_of_homogeneous {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {d : ℕ} (hd : 1 ≤ d) {f : E → F}
    (hf : ContinuousOn f {x | x ≠ 0}) (hh : ∀ c : ℝ, 0 < c → ∀ x, f (c • x) = c ^ d • f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖ ^ d := by
  have hsub : Metric.sphere (0 : E) 1 ⊆ {x : E | x ≠ 0} := by
    intro y hy
    change y ≠ 0
    intro h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hy
    exact zero_ne_one hy
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [apply_zero_eq_zero_of_homogeneous_pow hd hh, norm_zero]
    positivity
  have hs : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set u : E := ‖x‖⁻¹ • x with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs.ne']
  have hxu : ‖x‖ • u = x := by rw [hu, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hb : ‖f u‖ ≤ max C 0 := (hC u (by simp [hun])).trans (le_max_left _ _)
  rw [← hxu, hh _ hs, norm_smul, norm_pow, norm_norm, hxu, mul_comm]
  gcongr

/-- If `f : ℝ × ℝ → ℂ` is Lipschitz on a compact set `T`, then there is `M ≥ 0` with `‖f p‖ ≤ M` for
all `p ∈ T`. -/
theorem exists_norm_le_of_lipschitzOnWith_isCompact {f : ℝ × ℝ → ℂ} {C : NNReal} {T : Set (ℝ × ℝ)}
    (hf : LipschitzOnWith C f T)
    (hT : IsCompact T) : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ T, ‖f p‖ ≤ M := by
  obtain ⟨M, hM⟩ := hT.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨|M|, abs_nonneg M, fun p hp ↦ (hM p hp).trans (le_abs_self M)⟩

/-- If the closed support of `g : ℝ → ℝ` is contained in `Set.Ioi 0`, there is `ε > 0` such that
`g r = 0` for all `r < ε`. The proof takes a ball around `0` inside the open complement of the
closed support. -/
theorem exists_pos_eq_zero_of_tsupport_Ioi {g : ℝ → ℝ} (hg0 : tsupport g ⊆ Ioi 0) :
    ∃ ε > 0, ∀ r, r < ε → g r = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport g := fun h ↦ lt_irrefl (0 : ℝ) (hg0 h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isClosed_tsupport g).isOpen_compl 0 h0
  refine ⟨ε, hε, fun r hr ↦ ?_⟩
  by_cases hr0 : r ≤ 0
  · exact image_eq_zero_of_notMem_tsupport fun h ↦ not_lt.2 hr0 (hg0 h)
  · refine image_eq_zero_of_notMem_tsupport (hball ?_)
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (not_le.mp hr0)]
    exact hr

/-- If `ψ : ℝ × ℝ → ℝ` has compact support and every point of `tsupport ψ` has positive first
coordinate, then there are `δ > 0` and `R` with `δ ≤ p.1` and `‖p‖ ≤ R` for all `p ∈ tsupport ψ`. -/
theorem exists_pos_le_fst_of_mem_tsupport {ψ : ℝ × ℝ → ℝ} (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ δ > 0, ∃ R, ∀ p ∈ tsupport ψ, δ ≤ p.1 ∧ ‖p‖ ≤ R := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  by_cases hne : (tsupport ψ).Nonempty
  · obtain ⟨p0, hp0, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_fst.continuousOn
    exact ⟨p0.1, hpos p0 hp0, R, fun p hp ↦ ⟨hmin hp, hR p hp⟩⟩
  · exact ⟨1, one_pos, R, fun p hp ↦ absurd ⟨p, hp⟩ hne⟩

/-- Every compact set `k` of real numbers lies in a symmetric interval: there is `R > 0` with
`k ⊆ Icc (-R) R`. -/
theorem exists_pos_subset_Icc_neg_of_isCompact {k : Set ℝ} (hk : IsCompact k) :
    ∃ R : ℝ, 0 < R ∧ k ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun z hz ↦ ?_⟩
  have h1 := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := abs_le.mp (h1.trans (le_abs_self R))
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- A compact set `k ⊆ ℝ` contained in `Set.Ioi 0` is contained in an interval `Set.Icc a b` with
`0 < a`. -/
theorem exists_pos_subset_Icc_of_isCompact {k : Set ℝ} (hk : IsCompact k) (hs : k ⊆ Ioi 0) : ∃ a b :
    ℝ, 0 < a ∧ k ⊆ Icc a b := by
  rcases k.eq_empty_or_nonempty with h | h
  · exact ⟨1, 1, one_pos, h ▸ empty_subset _⟩
  obtain ⟨x, hx, hmin⟩ := hk.exists_isMinOn h continuousOn_id
  obtain ⟨b, hb⟩ := hk.bddAbove
  exact ⟨x, b, hs hx, fun y hy ↦ ⟨hmin hy, hb hy⟩⟩

/-- If `χ : ℝ → ℝ` has compact support, then there is `R > 0` with `tsupport χ ⊆ Ioo (-R) R`. -/
theorem exists_pos_tsupport_subset_Ioo_neg {χ : ℝ → ℝ} (h : HasCompactSupport χ) :
    ∃ R : ℝ, 0 < R ∧ tsupport χ ⊆ Ioo (-R) R := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun z hz ↦ ?_⟩
  have h1 := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := abs_le.mp (h1.trans (le_abs_self R))
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

/-- Let `d : ℕ → ℕ → ℝ` and let `ε` be real. If for every finite set `S` of naturals there is `n`
with `ε ≤ d n k` for all `k ∈ S`, then there is a sequence `s : ℕ → ℕ` with `ε ≤ d (s j) (s i)`
whenever `i < j`. The sequence is built by recursion, each term being chosen for the finite set of
the earlier terms. -/
theorem exists_separated_seq_of_forall_finset (d : ℕ → ℕ → ℝ) (ε : ℝ)
    (hbad : ∀ S : Finset ℕ, ∃ n, ∀ k ∈ S, ε ≤ d n k) :
    ∃ s : ℕ → ℕ, ∀ i j, i < j → ε ≤ d (s j) (s i) := by
  classical
  choose f hf using hbad
  let T : ℕ → Finset ℕ := fun j ↦ Nat.rec ∅ (fun _ t ↦ insert (f t) t) j
  have hT : ∀ j, T (j + 1) = insert (f (T j)) (T j) := fun j ↦ rfl
  have hmono : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (by rw [hT]; exact Finset.subset_insert _ _)
  refine ⟨fun j ↦ f (T j), fun i j hij ↦ hf (T j) _ ?_⟩
  have : f (T i) ∈ T (i + 1) := by rw [hT]; exact Finset.mem_insert_self _ _
  exact hmono (i + 1) j hij this

/-- Weak sequential compactness of bounded sets in a real Hilbert space: if `‖u n‖ ≤ C` for all `n`,
then there are a strictly increasing `φ : ℕ → ℕ` and a vector `x` with `‖x‖ ≤ C` such that
`inner ℝ (u (φ n)) y → inner ℝ x y` for every `y`. The proof works in the closure of the span of the
sequence, which is separable, applies sequential compactness of the closed ball of its weak dual,
and extends to all `y` by orthogonal projection onto that subspace. -/
theorem exists_subseq_tendsto_inner_of_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (x : E), StrictMono φ ∧ ‖x‖ ≤ C ∧
      ∀ y : E, Tendsto (fun n ↦ inner ℝ (u (φ n)) y) atTop (𝓝 (inner ℝ x y)) := by
  set M : Submodule ℝ E := (Submodule.span ℝ (Set.range u)).topologicalClosure with hM
  have hsep : TopologicalSpace.IsSeparable (M : Set E) := by
    rw [hM, Submodule.topologicalClosure_coe]
    exact (Set.countable_range u).isSeparable.span.closure
  have : TopologicalSpace.SeparableSpace M := hsep.separableSpace
  have : CompleteSpace M :=
    (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hmem : ∀ n, u n ∈ M := fun n ↦
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩)
  let w : ℕ → M := fun n ↦ ⟨u n, hmem n⟩
  let v : ℕ → WeakDual ℝ M := fun n ↦ StrongDual.toWeakDual (InnerProductSpace.toDual ℝ M (w n))
  have hv : ∀ n, v n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ M) C := by
    intro n
    simp only [Set.mem_preimage, Metric.mem_closedBall]
    have : WeakDual.toStrongDual (v n) = InnerProductSpace.toDual ℝ M (w n) := rfl
    rw [this, dist_zero_right (InnerProductSpace.toDual ℝ M (w n)), LinearIsometryEquiv.norm_map]
    exact hu n
  obtain ⟨f, hf, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ M 0 C hv
  refine ⟨φ, ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E), hφ, ?_, ?_⟩
  · have h1 : ‖((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E)‖
        = ‖WeakDual.toStrongDual f‖ := by
      exact (InnerProductSpace.toDual ℝ M).symm.norm_map (WeakDual.toStrongDual f)
    rw [h1]
    simpa [Metric.mem_closedBall, dist_zero_right] using hf
  · intro y
    rw [tendsto_iff_forall_eval_tendsto_topDualPairing] at hlim
    have h := hlim (M.orthogonalProjectionOnto y)
    have e1 : ∀ n, topDualPairing ℝ M (v (φ n)) (M.orthogonalProjectionOnto y)
        = inner ℝ (u (φ n)) y := by
      intro n
      change inner ℝ (w (φ n)) (M.orthogonalProjectionOnto y) = _
      exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (w (φ n)) y
    have e2 : topDualPairing ℝ M f (M.orthogonalProjectionOnto y)
        = inner ℝ ((InnerProductSpace.toDual ℝ M).symm (WeakDual.toStrongDual f) : E) y := by
      rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
          InnerProductSpace.toDual_symm_apply]
      rfl
    simp only [Function.comp_apply, e1, e2] at h
    exact h

/-- If `k` is a compact subset of `ℝ × ℝ` whose points all have positive first coordinate, then
there are `δ > 0` and `R` with `k ⊆ Icc δ R ×ˢ Icc (-R) R`. Proof idea: `δ` is the minimum of the
first coordinate on `k`, and `R` bounds the norm on `k`. -/
theorem exists_subset_Icc_prod_Icc_of_isCompact (k : Set (ℝ × ℝ)) (hk : IsCompact k)
    (hU : ∀ p ∈ k, 0 < p.1) :
    ∃ δ R : ℝ, 0 < δ ∧ k ⊆ Icc δ R ×ˢ Icc (-R) R := by
  rcases k.eq_empty_or_nonempty with h | h
  · exact ⟨1, 0, one_pos, by simp [h]⟩
  obtain ⟨x, hx, hmin⟩ := hk.exists_isMinOn h continuous_fst.continuousOn
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine ⟨x.1, R, hU x hx, fun p hp ↦ ?_⟩
  have hp' : ‖p‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hp
  have h1 : |p.1| ≤ R := by rw [← Real.norm_eq_abs]; exact (norm_fst_le p).trans hp'
  have h2 : |p.2| ≤ R := by rw [← Real.norm_eq_abs]; exact (norm_snd_le p).trans hp'
  exact ⟨⟨isMinOn_iff.1 hmin p hp, (abs_le.1 h1).2⟩, ⟨(abs_le.1 h2).1, (abs_le.1 h2).2⟩⟩

/-- If `l < r` and a compact set `K` of real numbers lies in `Ioo l r`, then there are `p` and `q`
with `l < p`, `q < r` and `K ⊆ Ioo p q`. Proof idea: for nonempty `K` take the midpoint of `l` and
`sInf K` and the midpoint of `sSup K` and `r`. -/
theorem exists_subset_Ioo_of_isCompact_subset_Ioo {K : Set ℝ} {l r : ℝ} (hlr : l < r)
    (hK : IsCompact K)
    (hKs : K ⊆ Ioo l r) : ∃ p q, l < p ∧ q < r ∧ K ⊆ Ioo p q := by
  rcases K.eq_empty_or_nonempty with h | hne
  · exact ⟨(l + r) / 2, (l + r) / 2, by linarith, by linarith, by simp [h]⟩
  · have h1 := hKs (hK.sInf_mem hne)
    have h2 := hKs (hK.sSup_mem hne)
    refine ⟨(l + sInf K) / 2, (sSup K + r) / 2, by linarith [h1.1], by linarith [h2.2], ?_⟩
    intro x hx
    have a1 := csInf_le hK.bddBelow hx
    have a2 := le_csSup hK.bddAbove hx
    constructor <;> linarith [h1.1, h2.2]

/-- If `χ : ℝ → ℝ` has compact support, then there is a real `Z` with `tsupport χ ⊆ Icc (-Z) Z`. -/
theorem exists_tsupport_subset_Icc_neg {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    ∃ Z : ℝ, tsupport χ ⊆ Icc (-Z) Z := by
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hm ↦ ?_⟩
  have := hR hm
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  exact ⟨by linarith [neg_abs_le z], by linarith [le_abs_self z]⟩

/-- Let `a : ℝ × ℝ → ℝ`. If `0 < p.1` for every `p` in the topological support of `a`, then
`0 < p.1` for every `p` with `a p ≠ 0`. -/
theorem fst_pos_of_ne_zero_of_tsupport {a : ℝ × ℝ → ℝ} (h : ∀ p ∈ tsupport a, 0 < p.1) :
    ∀ p, a p ≠ 0 → 0 < p.1 :=
  fun p hp ↦ h p (subset_tsupport _ hp)

/-- If `a : ℝ × ℝ → ℂ` has compact support, then for every real `θ` the function
`r ↦ a (r * Real.cos θ, r * Real.sin θ)` of one real variable has compact support. Proof idea: if
the support of `a` lies in the closed ball of radius `R`, a point `(r * cos θ, r * sin θ)` of the
support has `r ^ 2 = (r * cos θ) ^ 2 + (r * sin θ) ^ 2 ≤ 2 * R ^ 2`, so the function vanishes for
`|r| > 2 * |R|`. -/
theorem hasCompactSupport_comp_mul_cos_sin (a : ℝ × ℝ → ℂ) (has : HasCompactSupport a) (θ : ℝ) :
    HasCompactSupport (fun r : ℝ ↦ a (r * Real.cos θ, r * Real.sin θ)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ × ℝ)).1 has.isCompact.isBounded
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * |R|)) fun r hr ↦ ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
  have hle : ‖((r * Real.cos θ, r * Real.sin θ) : ℝ × ℝ)‖ ≤ R := by simpa using hR hmem
  have hr' : 2 * |R| < |r| := by simpa using hr
  rw [Prod.norm_def] at hle
  have h1 : |r * Real.cos θ| ≤ R := (le_max_left _ _).trans hle
  have h2 : |r * Real.sin θ| ≤ R := (le_max_right _ _).trans hle
  have hR0 : 0 ≤ R := (abs_nonneg _).trans h1
  have e1 : (r * Real.cos θ) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 : (r * Real.sin θ) ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e3 : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  have e4 : (2 * |R|) ^ 2 < |r| ^ 2 := pow_lt_pow_left₀ hr' (by positivity) two_ne_zero
  rw [sq_abs, mul_pow, sq_abs] at e4
  nlinarith

/-- If `ψ : ℝ → ℝ` satisfies `ψ z = 0` for every `z` with `N < |z|`, for some real `N`, then `ψ` has
compact support. -/
theorem hasCompactSupport_of_eq_zero_of_lt_abs {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    HasCompactSupport ψ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -N) (b := N)) fun z hz ↦ hψN z ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hz
  rcases hz with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs z)
  · exact lt_of_lt_of_le h (le_abs_self z)

/-- If `a : ℝ → ℝ` has compact support, then the supports of its integer translates `σ ↦ a (σ + n)`,
`n : ℤ`, form a locally finite family of subsets of `ℝ`. The proof puts the support of `a` in a ball
of radius `R` and shows that only the `n` with `|n| ≤ R + |x| + 1` can have support meeting the
interval `(x - 1, x + 1)`. -/
theorem locallyFinite_support_int_translates {a : ℝ → ℝ} (hs : HasCompactSupport a) :
    LocallyFinite fun n : ℤ ↦ Function.support fun σ ↦ a (σ + n) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hs.isCompact.isBounded
  intro x
  refine ⟨Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  refine (Set.finite_Icc (-⌈R + |x| + 1⌉) ⌈R + |x| + 1⌉).subset ?_
  rintro n ⟨σ, hσ1, hσ2⟩
  have hm : σ + n ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport _ hσ1)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hm
  have hb : |(n : ℝ)| ≤ R + |x| + 1 := by
    have h1 : |σ - x| < 1 := by rw [abs_lt]; constructor <;> linarith [hσ2.1, hσ2.2]
    calc |(n : ℝ)| = |(σ + n) - (σ - x) - x| := by ring_nf
      _ ≤ |σ + n| + |σ - x| + |x| := by
          have := abs_sub (σ + n - (σ - x)) x
          have := abs_sub (σ + n) (σ - x)
          linarith
      _ ≤ R + |x| + 1 := by linarith
  have hc := Int.le_ceil (R + |x| + 1)
  rw [abs_le] at hb
  constructor
  · have : (-(⌈R + |x| + 1⌉ : ℝ)) ≤ n := by linarith
    exact_mod_cast this
  · have : (n : ℝ) ≤ ⌈R + |x| + 1⌉ := by linarith
    exact_mod_cast this

/-- If `f : ℝ × ℝ → ℂ` vanishes outside a set `S`, then for every `X : ℝ × ℝ → ℂ` the functions
`fun p ↦ f p * X p` and `fun p ↦ f p * S.indicator X p` are equal. -/
theorem mul_eq_mul_indicator_of_eq_zero {f X : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)}
    (hf : ∀ p, p ∉ S → f p = 0) :
    (fun p ↦ f p * X p) = fun p ↦ f p * S.indicator X p := by
  funext p
  by_cases hp : p ∈ S
  · rw [indicator_of_mem hp]
  · rw [hf p hp, zero_mul, zero_mul]

/-- If `ψ : ℝ → ℝ` vanishes at every `z` with `N < |z|`, then its closed support is contained in
`Set.Icc (-N) N`. -/
theorem tsupport_subset_Icc {ψ : ℝ → ℝ} {N : ℝ} (hψN : ∀ z, N < |z| → ψ z = 0) :
    tsupport ψ ⊆ Icc (-N) N := by
  refine closure_minimal (fun z hz ↦ ?_) isClosed_Icc
  by_contra h
  refine hz (hψN z ?_)
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs z)
  · exact lt_of_lt_of_le h (le_abs_self z)

/-- If `χ : ℝ → ℝ` has compact support, then there is a real `Z` such that `χ z = 0` for every
`z ∉ Icc (-Z) Z`. -/
theorem exists_eq_zero_of_notMem_Icc_neg {χ : ℝ → ℝ} (hχc : HasCompactSupport χ) :
    ∃ Z : ℝ, ∀ z, z ∉ Icc (-Z) Z → χ z = 0 := by
  obtain ⟨Z, hZ⟩ := exists_tsupport_subset_Icc_neg hχc
  exact ⟨Z, fun z hz ↦ image_eq_zero_of_notMem_tsupport fun hm ↦ hz (hZ hm)⟩

/-- If `χ : ℝ → ℝ` has compact support and every point of `tsupport χ` is positive, then there are
`δ > 0` and `R` such that `χ r = 0` for every `r ∉ Icc δ R`. -/
theorem exists_pos_eq_zero_of_notMem_Icc {χ : ℝ → ℝ} (hχc : HasCompactSupport χ)
    (hχp : ∀ r ∈ tsupport χ, 0 < r) :
    ∃ δ > 0, ∃ R : ℝ, ∀ r, r ∉ Icc δ R → χ r = 0 := by
  obtain ⟨R, hR⟩ := exists_tsupport_subset_Icc_neg hχc
  by_cases h : (tsupport χ).Nonempty
  · obtain ⟨r0, hr0, hmin⟩ := hχc.isCompact.exists_isMinOn h continuousOn_id
    exact ⟨r0, hχp r0 hr0, R, fun r hr ↦ image_eq_zero_of_notMem_tsupport fun hm ↦
        hr ⟨hmin hm, (hR hm).2⟩⟩
  · exact ⟨1, one_pos, 0, fun r _ ↦ image_eq_zero_of_notMem_tsupport fun hm ↦ h ⟨r, hm⟩⟩

/-- If `ψ : ℝ × ℝ → ℝ` has compact support and `0 < p.1` for every `p` in `tsupport ψ`, then there
are reals `a b c d` with `0 < a` and `tsupport ψ ⊆ Set.Icc a b ×ˢ Set.Icc c d`. -/
theorem exists_tsupport_subset_Icc_prod_Icc {ψ : ℝ × ℝ → ℝ} (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ a b c d : ℝ, 0 < a ∧ tsupport ψ ⊆ Icc a b ×ˢ Icc c d := by
  obtain ⟨a, b, ha, hab⟩ := exists_pos_subset_Icc_of_isCompact (hc.isCompact.image continuous_fst)
    (by rintro _ ⟨p, hp, rfl⟩; exact hpos p hp)
  obtain ⟨c, hc'⟩ := (hc.isCompact.image continuous_snd).bddBelow
  obtain ⟨d, hd⟩ := (hc.isCompact.image continuous_snd).bddAbove
  exact ⟨a, b, c, d, ha, fun p hp ↦ ⟨hab ⟨p, hp, rfl⟩, hc' ⟨p, hp, rfl⟩, hd ⟨p, hp, rfl⟩⟩⟩

/-- If every point of the topological support of `α : ℝ → ℝ` is positive, then `α r = α r / r * r`
for every real `r`. At `r = 0` this holds because `0` is not in the support, so `α 0 = 0`. -/
theorem eq_div_mul_self_of_tsupport_pos {α : ℝ → ℝ} (hs : ∀ x ∈ tsupport α, 0 < x) (r : ℝ) :
    α r = α r / r * r := by
  by_cases hr : r = 0
  · subst hr
    have h0 : (0 : ℝ) ∉ tsupport α := fun h ↦ lt_irrefl (0 : ℝ) (hs 0 h)
    simp [image_eq_zero_of_notMem_tsupport h0]
  · field_simp

/-- If `x < 0` or `1 < x`, the derivative of `Real.smoothTransition` at `x` is zero. This library
has both cases with the end points included: `PDE.Analysis.deriv_smoothTransition_zero_of_nonpos`
and `PDE.Analysis.deriv_smoothTransition_zero_of_one_le`. -/
theorem deriv_smoothTransition_zero_of_lt_or_lt {x : ℝ}
    (hx : x < 0 ∨ 1 < x) : deriv Real.smoothTransition x = 0 :=
  hx.elim (fun h ↦ PDE.Analysis.deriv_smoothTransition_zero_of_nonpos h.le)
    (fun h ↦ PDE.Analysis.deriv_smoothTransition_zero_of_one_le h.le)

/-- For every real `a`, the function `s ↦ deriv Real.smoothTransition (s + a)` has compact support.
-/
theorem hasCompactSupport_deriv_smoothTransition_add (a : ℝ) : HasCompactSupport
    (fun s ↦ deriv Real.smoothTransition (s + a)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -1 - a) (b := 2 - a)) fun s hs ↦ ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hs
  refine deriv_smoothTransition_zero_of_lt_or_lt ?_
  rcases hs with hs | hs
  · left; linarith
  · right; linarith

/-- Every compact set `k` of real numbers is contained in an interval `[-Z, Z]` for some real `Z`.
This is `exists_pos_subset_Icc_neg_of_isCompact` without the sign of `Z`. -/
theorem exists_subset_Icc_neg_of_isCompact {k : Set ℝ} (hk : IsCompact k) : ∃ Z, k ⊆ Icc (-Z) Z :=
  let ⟨R, _, h⟩ := exists_pos_subset_Icc_neg_of_isCompact hk; ⟨R, h⟩

/-- For all real `a`, `b`, `c`, `d`, the rectangle `[a, b] × [c, d]` in `ℝ × ℝ` is compact. -/
theorem isCompact_Icc_prod_Icc (a b c d : ℝ) : IsCompact (Icc a b ×ˢ Icc c d) :=
  isCompact_Icc.prod isCompact_Icc

end PDE.Analysis
