/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Transport.Bootstrap
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Characteristics with an inflow set, and the bootstrap over two regions

On an outer region `D` of a transport equation `∂ₜ f + v · ∇f = -a f + B` the backward
characteristic of a point either stays in `D` down to the initial time or enters `D` through a
part `Γ` of its boundary at a later time. `SolvesAlongInflowPaths D Γ a B f t₀ T` is the
characteristic form of the equation for such a region: every point of `D` at every time is the
endpoint of a path in `D` that starts either at the initial time or on `Γ`. The sup-norm estimate
along these paths is bounded by the initial values, the values on `Γ`, and the ratio of the
forcing to the damping (`SolvesAlongInflowPaths.abs_le_max`).

`bootstrap_lt_of_inflow` combines this estimate with Lemma A.2 of Chen and Hou, Part I: an
energy that is the maximum of inner components (solutions along paths, with forcing budgets
below the damping by a margin `ε₀`) and outer components (solutions along inflow paths whose
values on the inflow sets are controlled by the inner components) stays below the threshold
`E_*` if it starts below it. A side condition `A < E_*` that is not an energy component (in
Part I, Section 6.5, the bound (6.91) of the nonlinear modes) is bootstrapped together with the
energy when it improves under the bootstrap assumption. This is the structure of the far-field
estimate of Part I, Proposition 6.15, inside the bootstrap of Section 6.5.

## Main results

* `SolvesAlongInflowPaths`, `SolvesAlongPaths.solvesAlongInflowPaths`,
  `SolvesAlongInflowPaths.const_mul`.
* `SolvesAlongInflowPaths.abs_le_max`: `|f(p, t)| ≤ max(max m₀ m_Γ, K)` when `a ≥ 0` and
  `|B| ≤ a K`.
* `SolvesAlongInflowPaths.of_hasFDerivWithinAt`: inflow paths of a region `{c ≤ g}` from
  backward characteristics and the differential form of the equation.
* `bootstrap_lt_of_inflow`: Lemma A.2 from positive times for inner and outer components, with a
  side condition.

## References

* J. Chen and T. Y. Hou, *Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis*, arXiv:2210.07191v4, Lemma A.2, Proposition 6.15 and
  Section 6.5.
  <https://arxiv.org/abs/2210.07191>
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.Transport

/-- `f` solves `∂ₜ f + v · ∇f = -a f + B` on `D` over `[t₀, T]` along inflow paths through `Γ`:
every point `p ∈ D` at every time `t ∈ [t₀, T]` is the endpoint of a path `γ` on `[t₁, t]`,
`t₁ ∈ [t₀, t]`, that stays in `D`, starts at the initial time (`t₁ = t₀`) or on `Γ`
(`γ t₁ ∈ Γ`), and along which `s ↦ f (γ s) s` is continuous on `[t₁, t]` with the right derivative
`-a (γ s) s * f (γ s) s + B (γ s) s` on `[t₁, t)`. -/
def SolvesAlongInflowPaths {X : Type*} (D Γ : Set X) (a B f : X → ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ T, ∀ p ∈ D, ∃ t₁ ∈ Icc t₀ t, ∃ γ : ℝ → X, γ t = p ∧ (t₁ = t₀ ∨ γ t₁ ∈ Γ) ∧
    (∀ s ∈ Icc t₁ t, γ s ∈ D) ∧ ContinuousOn (fun s ↦ f (γ s) s) (Icc t₁ t) ∧
    ∀ s ∈ Ico t₁ t, HasDerivWithinAt (fun s ↦ f (γ s) s)
      (-a (γ s) s * f (γ s) s + B (γ s) s) (Ici s) s

variable {X : Type*} {D Γ : Set X} {a B f : X → ℝ → ℝ} {t₀ T : ℝ}

/-- Paths that stay in `D` from the initial time are inflow paths for every inflow set. -/
theorem SolvesAlongPaths.solvesAlongInflowPaths (h : SolvesAlongPaths D a B f t₀ T) :
    SolvesAlongInflowPaths D Γ a B f t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ := h t ht p hp
  exact ⟨t₀, left_mem_Icc.mpr ht.1, γ, hγt, Or.inl rfl, hγD, hcont, hderiv⟩

namespace SolvesAlongInflowPaths

/-- A constant multiple `μ f` solves the equation with forcing `μ B`. -/
theorem const_mul (h : SolvesAlongInflowPaths D Γ a B f t₀ T) (μ : ℝ) :
    SolvesAlongInflowPaths D Γ a (fun p t ↦ μ * B p t) (fun p t ↦ μ * f p t) t₀ T := by
  intro t ht p hp
  obtain ⟨t₁, ht₁, γ, hγt, hstart, hγD, hcont, hderiv⟩ := h t ht p hp
  refine ⟨t₁, ht₁, γ, hγt, hstart, hγD, continuousOn_const.mul hcont, fun s hs ↦ ?_⟩
  convert (hderiv s hs).const_mul μ using 1
  ring

/-- **The sup-norm estimate along inflow paths.** If `f` is at most `m₀` on `D` at the initial
time and at most `m_Γ` on `Γ` at the times `[t₀, t]`, and `a ≥ 0`, `|B| ≤ a K` on `D` at the
times `[t₀, t)`, then `|f p t| ≤ max (max m₀ m_Γ) K`. -/
theorem abs_le_max (h : SolvesAlongInflowPaths D Γ a B f t₀ T) {t : ℝ} (ht : t ∈ Icc t₀ T)
    {p : X} (hp : p ∈ D) {m₀ mΓ K : ℝ} (h₀ : ∀ q ∈ D, |f q t₀| ≤ m₀)
    (hΓ : ∀ s ∈ Icc t₀ t, ∀ q ∈ Γ, |f q s| ≤ mΓ)
    (hbound : ∀ s ∈ Ico t₀ t, ∀ q ∈ D, 0 ≤ a q s ∧ |B q s| ≤ a q s * K) :
    |f p t| ≤ max (max m₀ mΓ) K := by
  obtain ⟨t₁, ht₁, γ, hγt, hstart, hγD, hcont, hderiv⟩ := h t ht p hp
  have hsub : ∀ s ∈ Ico t₁ t, s ∈ Ico t₀ t := fun s hs ↦ ⟨ht₁.1.trans hs.1, hs.2⟩
  have hcomp := abs_le_max_of_abs_forcing_le (A := fun s ↦ a (γ s) s) hcont hderiv
    (fun s hs ↦ (hbound s (hsub s hs) (γ s) (hγD s (Ico_subset_Icc_self hs))).1)
    (fun s hs ↦ by
      have := (hbound s (hsub s hs) (γ s) (hγD s (Ico_subset_Icc_self hs))).2
      simpa only [neg_mul, neg_add_cancel_comm] using this) t (right_mem_Icc.mpr ht₁.2)
  rw [hγt] at hcomp
  refine hcomp.trans (max_le_max_right K ?_)
  rcases hstart with h₁ | h₁
  · subst h₁
    exact (h₀ _ (hγD _ (left_mem_Icc.mpr ht₁.2))).trans (le_max_left _ _)
  · exact (hΓ t₁ ht₁ _ h₁).trans (le_max_right _ _)

/-- **Inflow paths from the differential form.** Let every point of `D₀` at every time
`t ∈ [t₀, T]` be the endpoint of a characteristic `γ' = v(γ)` on `[t₀, t]` that stays in `D₀`, and
let `g` be continuous. On the region `D = {x ∈ D₀ | c ≤ g x}` with the inflow set
`Γ = {x ∈ D₀ | g x = c}`, if `f` is continuous on `D × [t₀, T]`, differentiable at `(p, t)` relative
to `D × [t, ∞)` and `Df(p, t)(v(t, p), 1) = -a f + B` at the points of `D` and the times of
`[t₀, T)`, then `f` solves the equation along inflow paths of `D` through `Γ`: the characteristic
through `(p, t)` is followed backward to its last time in `{g ≤ c}`, or to `t₀` if there is
none. -/
theorem of_hasFDerivWithinAt [NormedAddCommGroup X] [NormedSpace ℝ X] {D₀ : Set X} {g : X → ℝ}
    {c : ℝ} {v : ℝ → X → X} {f' : X → ℝ → X × ℝ →L[ℝ] ℝ} (hg : Continuous g)
    (hpaths : ∀ t ∈ Icc t₀ T, ∀ p ∈ D₀, ∃ γ : ℝ → X, γ t = p ∧
      ∀ s ∈ Icc t₀ t, γ s ∈ D₀ ∧ HasDerivAt γ (v s (γ s)) s)
    (hcont : ContinuousOn (Function.uncurry f) ({x | x ∈ D₀ ∧ c ≤ g x} ×ˢ Icc t₀ T))
    (hf : ∀ t ∈ Ico t₀ T, ∀ p ∈ {x | x ∈ D₀ ∧ c ≤ g x},
      HasFDerivWithinAt (Function.uncurry f) (f' p t) ({x | x ∈ D₀ ∧ c ≤ g x} ×ˢ Ici t) (p, t))
    (heq : ∀ t ∈ Ico t₀ T, ∀ p ∈ {x | x ∈ D₀ ∧ c ≤ g x},
      f' p t (v t p, 1) = -a p t * f p t + B p t) :
    SolvesAlongInflowPaths {x | x ∈ D₀ ∧ c ≤ g x} {x | x ∈ D₀ ∧ g x = c} a B f t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγ⟩ := hpaths t ht p hp.1
  have hγc : ContinuousOn γ (Icc t₀ t) := fun s hs ↦ (hγ s hs).2.continuousAt.continuousWithinAt
  have hgγ : ContinuousOn (fun s ↦ g (γ s)) (Icc t₀ t) := hg.comp_continuousOn hγc
  -- the times in `[t₀, t]` at which the path is in `{g ≤ c}`
  set A := Icc t₀ t ∩ (fun s ↦ g (γ s)) ⁻¹' Iic c with hA
  have hAc : IsClosed A := hgγ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAb : BddAbove A := ⟨t, fun s hs ↦ hs.1.2⟩
  -- if `g ∘ γ > c` on `(r, t]`, then `c ≤ g (γ r)` by continuity
  have hlim {r : ℝ} (hr : r ∈ Icc t₀ t) (hrt : r < t) (h : ∀ s ∈ Ioc r t, c < g (γ s)) :
      c ≤ g (γ r) := by
    have : (𝓝[Ioc r t] r).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hrt.ne]
      exact left_mem_Icc.mpr hrt.le
    exact ge_of_tendsto ((hgγ r hr).mono fun s hs ↦ ⟨hr.1.trans hs.1.le, hs.2⟩)
      (eventually_nhdsWithin_of_forall fun s hs ↦ (h s hs).le)
  -- the last such time, or `t₀`
  obtain ⟨t₁, ht₁, hstart, hafter⟩ : ∃ t₁ ∈ Icc t₀ t, (t₁ = t₀ ∨ γ t₁ ∈ {x | x ∈ D₀ ∧ g x = c}) ∧
      ∀ s ∈ Ioc t₁ t, c < g (γ s) := by
    by_cases hne : A.Nonempty
    · have hmem : sSup A ∈ A := hAc.csSup_mem hne hAb
      have hlast : ∀ s ∈ Ioc (sSup A) t, c < g (γ s) := fun s hs ↦ by
        by_contra hle
        exact absurd (le_csSup hAb ⟨⟨hmem.1.1.trans hs.1.le, hs.2⟩, not_lt.mp hle⟩)
          (not_le.mpr hs.1)
      refine ⟨sSup A, hmem.1, Or.inr ⟨(hγ _ hmem.1).1, le_antisymm hmem.2 ?_⟩, hlast⟩
      rcases eq_or_lt_of_le hmem.1.2 with heq' | hlt
      · rw [heq', hγt]
        exact hp.2
      · exact hlim hmem.1 hlt hlast
    · refine ⟨t₀, left_mem_Icc.mpr ht.1, Or.inl rfl, fun s hs ↦ ?_⟩
      by_contra hle
      exact hne ⟨s, ⟨hs.1.le, hs.2⟩, not_lt.mp hle⟩
  have hsub : Icc t₁ t ⊆ Icc t₀ t := Icc_subset_Icc_left ht₁.1
  have hD : ∀ s ∈ Icc t₁ t, γ s ∈ {x | x ∈ D₀ ∧ c ≤ g x} := by
    refine fun s hs ↦ ⟨(hγ s (hsub hs)).1, ?_⟩
    rcases eq_or_lt_of_le hs.1 with rfl | h₁
    · rcases eq_or_lt_of_le ht₁.2 with h₂ | h₂
      · rw [h₂, hγt]
        exact hp.2
      · exact hlim ht₁ h₂ hafter
    · exact (hafter s ⟨h₁, hs.2⟩).le
  refine ⟨t₁, ht₁, γ, hγt, hstart, hD, ?_, fun s hs ↦ ?_⟩
  · exact hcont.comp ((hγc.mono hsub).prodMk continuousOn_id) fun s hs ↦
      ⟨hD s hs, ht₁.1.trans hs.1, hs.2.trans ht.2⟩
  · have hsI : s ∈ Icc t₁ t := Ico_subset_Icc_self hs
    have hsT : s ∈ Ico t₀ T := ⟨ht₁.1.trans hs.1, hs.2.trans_le ht.2⟩
    have hcomp := hasDerivWithinAt_comp_path (hf s hsT (γ s) (hD s hsI))
      (hγ s (hsub hsI)).2 (fun u hu ↦ hD u ⟨hsI.1.trans hu.1, hu.2⟩) le_rfl hs.2
    rwa [heq s hsT (γ s) (hD s hsI)] at hcomp

end SolvesAlongInflowPaths

/-! ### The bootstrap over an inner and an outer region -/

/-- **Part I, Lemma A.2 from positive times over two regions, with a side condition.** Let the
inner components `fᵢ` solve their equations along paths on `Dᵢ` and the outer components `gⱼ`
along inflow paths on `D'ⱼ` with inflow sets `Γⱼ`, on `[ε, T]` for every `ε ∈ (0, T]`, and let
`E(t) = max(supᵢ μᵢ ‖fᵢ(t)‖, supⱼ μ'ⱼ ‖gⱼ(t)‖)` be continuous with `E(0) < E_*`. Let `A` be a
continuous side quantity (a bootstrap condition that is not an energy component). Assume that
whenever the running maximum of `E` is below `E_*` and `A < E_*` on `[0, t]`, the inner forcings
have budgets `μᵢ |Fᵢ| ≤ Hᵢ ≤ M`, `Hᵢ ≤ aᵢ E_* - ε₀` with `ε₀ > 0` (the hypotheses of Lemma A.2),
and the outer dampings are nonnegative with `μ'ⱼ |Gⱼ| ≤ bⱼ K` for a fixed `K < E_*`; that the side
quantity improves, `A(t) ≤ K_A < E_*`, whenever the running maximum of `E` is below `E_*` and
`A < E_*` on `[0, t)`; and that the values of the outer components on the inflow sets are at most
the inner part of the energy. Then `E < E_*` and `A < E_*` on `[0, T]`. -/
theorem bootstrap_lt_of_inflow {ι κ : Type*} {X : ι → Type*} {Y : κ → Type*} {D : ∀ i, Set (X i)}
    {D' Γ : ∀ j, Set (Y j)} {f a F H : ∀ i, X i → ℝ → ℝ} {g b G : ∀ j, Y j → ℝ → ℝ} {μ : ι → ℝ}
    {μ' : κ → ℝ} {E A : ℝ → ℝ≥0∞} {T Estar ε₀ M K KA : ℝ} (hμ : ∀ i, 0 < μ i) (hμ' : ∀ j, 0 < μ' j)
    (hsol : ∀ ε, 0 < ε → ε ≤ T → ∀ i, SolvesAlongPaths (D i) (a i) (F i) (f i) ε T)
    (hsol' : ∀ ε, 0 < ε → ε ≤ T → ∀ j, SolvesAlongInflowPaths (D' j) (Γ j) (b j) (G j) (g j) ε T)
    (hE_eq : ∀ t ∈ Icc 0 T, E t = max (⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p t|))
      (⨆ j, ⨆ q ∈ D' j, ENNReal.ofReal (μ' j * |g j q t|)))
    (hE : ContinuousOn E (Icc 0 T)) (hA : ContinuousOn A (Icc 0 T))
    (hbudget : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar →
      (∀ s ∈ Icc 0 t, A s < ENNReal.ofReal Estar) → ∀ i, ∀ p ∈ D i, μ i * |F i p t| ≤ H i p t ∧
      H i p t ≤ M ∧ H i p t ≤ a i p t * Estar - ε₀)
    (houter : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar →
      (∀ s ∈ Icc 0 t, A s < ENNReal.ofReal Estar) → ∀ j, ∀ q ∈ D' j, 0 ≤ b j q t ∧
      μ' j * |G j q t| ≤ b j q t * K)
    (hside : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar →
      (∀ s ∈ Ico 0 t, A s < ENNReal.ofReal Estar) → A t ≤ ENNReal.ofReal KA)
    (hinflow : ∀ t ∈ Icc 0 T, ∀ j, ∀ q ∈ Γ j, ENNReal.ofReal (μ' j * |g j q t|) ≤ ⨆ i, ⨆ p ∈ D i,
      ENNReal.ofReal (μ i * |f i p t|))
    (hε₀ : 0 < ε₀) (hM : 0 ≤ M) (hK : K < Estar) (hKA : KA < Estar)
    (h0 : E 0 < ENNReal.ofReal Estar) :
    ∀ t ∈ Icc 0 T, E t < ENNReal.ofReal Estar ∧ A t < ENNReal.ofReal Estar := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hEstar : 0 < Estar := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h0)
  have hKA' : ENNReal.ofReal KA < ENNReal.ofReal Estar :=
    (ENNReal.ofReal_lt_ofReal_iff hEstar).mpr hKA
  -- the side condition at `t = 0`
  have h0I : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hrun0 : runningMax E 0 < ENNReal.ofReal Estar :=
    runningMax_lt le_rfl (hE.mono (Icc_subset_Icc_right hT)) fun s hs ↦ by
      obtain rfl : s = 0 := le_antisymm hs.2 hs.1
      exact h0
  have hA0 : A 0 < ENNReal.ofReal Estar :=
    (hside 0 h0I hrun0 fun s hs ↦ absurd hs.2 (not_lt.mpr hs.1)).trans_lt hKA'
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · obtain rfl : t = 0 := le_antisymm (hT0 ▸ ht.2) ht.1
    exact ⟨h0, hA0⟩
  -- `E < E_*` and `A < E_*` on `[0, ε]`
  have hnear : ∀ᶠ s in 𝓝[≥] (0 : ℝ), E s < ENNReal.ofReal Estar ∧ A s < ENNReal.ofReal Estar := by
    rw [← nhdsWithin_Icc_eq_nhdsGE hTpos]
    exact ((hE 0 h0I).eventually (eventually_lt_nhds h0)).and
      ((hA 0 h0I).eventually (eventually_lt_nhds hA0))
  obtain ⟨δ₀, hδ₀, hδE⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hnear
  set ε := min (δ₀ / 2) T with hε_def
  have hε : 0 < ε := lt_min (half_pos hδ₀) hTpos
  have hεT : ε ≤ T := min_le_right _ _
  have hsmall : ∀ s ∈ Icc 0 ε, E s < ENNReal.ofReal Estar ∧ A s < ENNReal.ofReal Estar :=
    fun s hs ↦ hδE ⟨hs.1, hs.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ₀))⟩
  rcases lt_or_ge t ε with htε | htε
  · exact hsmall t ⟨ht.1, htε.le⟩
  -- the level of the improvement
  have hEε : E ε < ENNReal.ofReal Estar := (hsmall ε ⟨hε.le, le_rfl⟩).1
  have hEεtop : E ε ≠ ⊤ := (hEε.trans ENNReal.ofReal_lt_top).ne
  set Eε := (E ε).toReal with hEεdef
  have hEε_lt : Eε < Estar := ENNReal.toReal_lt_of_lt_ofReal hEε
  set d := ε₀ / (M + ε₀) with hd_def
  have hd : 0 < d := div_pos hε₀ (by linarith)
  set mI := max Eε ((1 - d) * Estar) with hmI_def
  set m := max (max mI K) KA with hm_def
  have hmI_lt : mI < Estar := max_lt hEε_lt (by nlinarith)
  have hm_lt : m < Estar := max_lt (max_lt hmI_lt hK) hKA
  have hEε_mem : ε ∈ Icc 0 T := ⟨hε.le, hεT⟩
  -- the values at time `ε` are at most `E(ε)`
  have hinit : ∀ i, ∀ q ∈ D i, |μ i * f i q ε| ≤ Eε := fun i q hq ↦ by
    rw [abs_mul, abs_of_pos (hμ i), ← ENNReal.ofReal_le_iff_le_toReal hEεtop, hE_eq ε hEε_mem]
    exact le_max_of_le_left (le_iSup_of_le i (le_iSup₂_of_le q hq le_rfl))
  have hinit' : ∀ j, ∀ q ∈ D' j, |μ' j * g j q ε| ≤ Eε := fun j q hq ↦ by
    rw [abs_mul, abs_of_pos (hμ' j), ← ENNReal.ofReal_le_iff_le_toReal hEεtop, hE_eq ε hEε_mem]
    exact le_max_of_le_right (le_iSup_of_le j (le_iSup₂_of_le q hq le_rfl))
  -- the continuity argument on `[ε, T]` for `max E A`
  have hEA : ContinuousOn (fun s ↦ max (E s) (A s)) (Icc ε T) :=
    (hE.mono (Icc_subset_Icc hε.le le_rfl)).sup (hA.mono (Icc_subset_Icc hε.le le_rfl))
  have hboot : ∀ s ∈ Icc ε T, max (E s) (A s) ≤ ENNReal.ofReal m := by
    refine le_of_bootstrap (c := ENNReal.ofReal Estar) hEA (max_lt hEε (hsmall ε ⟨hε.le, le_rfl⟩).2)
      ((ENNReal.ofReal_lt_ofReal_iff hEstar).mpr hm_lt) fun t' ht' hlt ↦ ?_
    have ht'I : t' ∈ Icc 0 T := ⟨hε.le.trans ht'.1, ht'.2⟩
    have hall : ∀ s ∈ Icc 0 t', E s < ENNReal.ofReal Estar ∧ A s < ENNReal.ofReal Estar :=
      fun s hs ↦ (le_total s ε).elim (fun hsε ↦ hsmall s ⟨hs.1, hsε⟩)
        fun hsε ↦ max_lt_iff.mp (hlt s ⟨hsε, hs.2⟩)
    have hrun : ∀ s ∈ Icc 0 t', runningMax E s < ENNReal.ofReal Estar := fun s hs ↦
      runningMax_lt hs.1 (hE.mono (Icc_subset_Icc_right (hs.2.trans ht'I.2)))
        fun u hu ↦ (hall u ⟨hu.1, hu.2.trans hs.2⟩).1
    have hAs : ∀ s ∈ Icc 0 t', ∀ u ∈ Icc 0 s, A u < ENNReal.ofReal Estar := fun s hs u hu ↦
      (hall u ⟨hu.1, hu.2.trans hs.2⟩).2
    -- the inner components at every time of `[ε, t']`
    have hinner : ∀ s ∈ Icc ε t', ∀ i, ∀ p ∈ D i, |μ i * f i p s| ≤ mI := by
      intro s hs i p hp
      refine ((hsol ε hε hεT i).const_mul (μ i)).abs_le_max ⟨hs.1, hs.2.trans ht'.2⟩ hp
        (hinit i) fun u hu q hq ↦ ?_
      have huI : u ∈ Icc 0 T := ⟨hε.le.trans hu.1, hu.2.le.trans (hs.2.trans ht'.2)⟩
      have hut' : u ∈ Icc 0 t' := ⟨huI.1, hu.2.le.trans hs.2⟩
      obtain ⟨hHF, hHM, hHa⟩ := hbudget u huI (hrun u hut') (hAs u hut') i q hq
      have hH₀ : 0 ≤ H i q u := (mul_nonneg (hμ i).le (abs_nonneg _)).trans hHF
      refine ⟨nonneg_of_mul_nonneg_left (by linarith) hEstar, ?_⟩
      rw [abs_mul, abs_of_pos (hμ i)]
      linarith [le_one_sub_div_mul hε₀ hM hHM hHa]
    -- the inner energy at every time of `[ε, t']`
    have hinnerE : ∀ s ∈ Icc ε t',
        (⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p s|)) ≤ ENNReal.ofReal mI := by
      refine fun s hs ↦ iSup_le fun i ↦ iSup₂_le fun p hp ↦ ENNReal.ofReal_le_ofReal ?_
      simpa only [abs_mul, abs_of_pos (hμ i)] using hinner s hs i p hp
    have hmI0 : 0 ≤ mI := ENNReal.toReal_nonneg.trans (le_max_left _ _)
    -- the outer components at `t'`
    have houterE : (⨆ j, ⨆ q ∈ D' j, ENNReal.ofReal (μ' j * |g j q t'|)) ≤
        ENNReal.ofReal m := by
      refine iSup_le fun j ↦ iSup₂_le fun q hq ↦ ENNReal.ofReal_le_ofReal ?_
      have h := ((hsol' ε hε hεT j).const_mul (μ' j)).abs_le_max (mΓ := mI) (K := K)
        ⟨ht'.1, ht'.2⟩ hq (hinit' j)
        (fun s hs q' hq' ↦ by
          have hsI : s ∈ Icc 0 T := ⟨hε.le.trans hs.1, hs.2.trans ht'.2⟩
          have h1 := (hinflow s hsI j q' hq').trans (hinnerE s hs)
          rw [abs_mul, abs_of_pos (hμ' j)]
          exact (ENNReal.ofReal_le_ofReal_iff hmI0).mp h1)
        fun u hu q' hq' ↦ by
          have huI : u ∈ Icc 0 T := ⟨hε.le.trans hu.1, hu.2.le.trans ht'.2⟩
          have hut' : u ∈ Icc 0 t' := ⟨huI.1, hu.2.le⟩
          rw [abs_mul, abs_of_pos (hμ' j)]
          exact houter u huI (hrun u hut') (hAs u hut') j q' hq'
      rw [abs_mul, abs_of_pos (hμ' j)] at h
      exact h.trans ((max_le_max (max_le (le_max_left _ _) le_rfl) le_rfl).trans (le_max_left _ _))
    -- the side condition at `t'`
    have hAt' : A t' ≤ ENNReal.ofReal m :=
      (hside t' ht'I (hrun t' ⟨ht'I.1, le_rfl⟩) fun s hs ↦ (hall s ⟨hs.1, hs.2.le⟩).2).trans
        (ENNReal.ofReal_le_ofReal (le_max_right _ _))
    refine max_le ?_ hAt'
    rw [hE_eq t' ht'I]
    exact max_le ((hinnerE t' ⟨ht'.1, le_rfl⟩).trans
      (ENNReal.ofReal_le_ofReal ((le_max_left _ _).trans (le_max_left _ _)))) houterE
  exact max_lt_iff.mp
    ((hboot t ⟨htε, ht.2⟩).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hEstar).mpr hm_lt))

end PDE.Hyperbolic.Transport
