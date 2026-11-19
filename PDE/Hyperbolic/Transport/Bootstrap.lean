/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Transport.QuadrantFlow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sup-norm estimates along characteristics and the bootstrap

Chen and Hou, Part I, Appendix A, estimate a system of transport equations
`∂ₜ fᵢ + vᵢ · ∇fᵢ = -aᵢᵢ fᵢ + Bᵢ` in the energy `E(t) = maxᵢ μᵢ ‖fᵢ(t)‖_∞` by following
characteristics. We prove both of their lemmas from the characteristic form of the
equations, `SolvesAlongPaths`: every point of the domain at every time is the endpoint of a path
along which `f` satisfies the scalar equation `F' = -a F + B`. The one-point components
(`fᵢ(x)`), the two-point components (`fᵢ(x, z)`, Hölder quotients) and the scalar components
(`fᵢ = aᵢ(t)`, constant paths) all have this form, with different domains.

The energy is `ℝ≥0∞`-valued, the supremum of the weighted values. Its continuity in time is a
hypothesis.

## Main results

* `le_of_bootstrap`: the continuity argument in any linear order with the order topology.
* `le_of_forcing_le`, `abs_le_max_of_abs_forcing_le`: the scalar comparison for
  `F' + A F = B` with `A ≥ 0` and `|B| ≤ A K`: `|F(t)| ≤ max(|F(a)|, K)`. No integrating factor is
  needed, so `A` and `B` need not be integrable.
* `SolvesAlongPaths`, `SolvesAlongPaths.abs_le_max`, and the bridge from the transport equation
  in differential form, `SolvesAlongPaths.of_hasFDerivWithinAt` and
  `IsTangentLipschitzField.solvesAlongPaths` (characteristics of a field tangent to an orthant);
  `SolvesAlongPaths.of_hasDerivWithinAt` for scalar unknowns.
* `le_exp_mul_of_damping_dominates`: **Part I, Lemma A.1**,
  `E(t) ≤ e^{-λ (t - t₀)} E(t₀)` under (A.2) and (A.3).
* `le_one_sub_div_mul`: the convex combination `C ≤ (1 - δ) A` behind Lemma A.2.
* `bootstrap_le_max`: **Part I, Lemma A.2** in bootstrap form,
  `E(t) ≤ max(E(0), (1 - δ) E_*)`, `δ = ε₀ / (M + ε₀)`, with (A.10) required only while
  `E_max(t) < E_*`; `bootstrap_le_max_of_budget` is the same with one aggregate budget per
  component, and `le_max_of_forcing_le_mul` the core with `|Bᵢ| ≤ aᵢ K`.
* `bootstrap_lt_of_budget_of_pos`: Lemma A.2 with the equations required only on `[ε, T]` for
  every `ε > 0`, so that nothing about the time derivatives at `t = 0` is used
  (`SolvesAlongPaths.comp_add_const` and `SolvesAlongPaths.of_comp_add_const` shift the time).

## Implementation notes

* The proof of Lemma A.2 uses `C_i ≤ (1 - δ) A_i E_*` (`le_one_sub_div_mul`).
* The hypotheses (A.11) are non-strict inequalities with `M ≥ 0`; the proof uses `δ > 0`.
* The forcing bound (A.10) is a bound on `μᵢ |Bᵢ + Nᵢ + ε̄ᵢ|`; a bound on
  `μᵢ (|Bᵢ| + |Nᵢ| + |ε̄ᵢ|)` implies it.
* Lemma A.1 holds for every real `λ`; it is a decay estimate when `λ > 0`.
* The transport equations in differential form use only right time derivatives: the
  finite-rank part of the perturbation has time corners at the stopping times of its modes.
* (A.10) is stated with `E_max(t) = runningMax E t`, as in Part I, so that it covers the Duhamel
  memory terms of the finite-rank part.
* The proof of Lemma A.1 bootstraps the weighted energy `e^{λ' (t - t₀)} E(t)` with `λ' < λ`
  below a level `K > E(t₀)`, with the improvement `max(E(t₀), K M / (M + λ - λ')) < K`.

## References

* J. Chen and T. Y. Hou, *Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis*, arXiv:2210.07191, Appendix A, Lemmas A.1 and A.2.
  <https://arxiv.org/abs/2210.07191>
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped ENNReal NNReal

namespace PDE.Hyperbolic.Transport

/-! ### The continuity argument and the scalar comparison -/

/-- **The continuity argument.** If `E` is continuous on `[a, b]`, starts below `c`, and the
bootstrap assumption `E < c` on `[a, t]` always improves to `E t ≤ m` for a fixed `m < c`, then
`E ≤ m` on `[a, b]`. -/
theorem le_of_bootstrap {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {E : ℝ → α} {a b : ℝ} {c m : α} (hE : ContinuousOn E (Icc a b)) (ha : E a < c)
    (hm : m < c) (himprove : ∀ t ∈ Icc a b, (∀ s ∈ Icc a t, E s < c) → E t ≤ m) :
    ∀ t ∈ Icc a b, E t ≤ m := by
  have hlt : ∀ t ∈ Icc a b, E t < c := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁, hct₁⟩ := hcon
    have hclosed : IsClosed (Icc a b ∩ E ⁻¹' Ici c) :=
      hE.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    obtain ⟨τ, hτB, hτleast⟩ :=
      (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isLeast ⟨t₁, ht₁, hct₁⟩
    have hτ : τ ∈ Icc a b := hτB.1
    have hcτ : c ≤ E τ := hτB.2
    have haτ : a < τ := by
      rcases hτ.1.lt_or_eq with h | h
      · exact h
      · exact absurd (h ▸ hcτ) (not_le.mpr ha)
    have hbefore : ∀ s ∈ Ico a τ, E s ≤ m := by
      intro s hs
      have hsI : s ∈ Icc a b := ⟨hs.1, hs.2.le.trans hτ.2⟩
      refine himprove s hsI fun u hu ↦ ?_
      by_contra hu'
      have hτu := hτleast ⟨⟨hu.1, hu.2.trans hsI.2⟩, le_of_not_gt hu'⟩
      exact absurd (hτu.trans hu.2) (not_le.mpr hs.2)
    have hτm : E τ ≤ m := by
      have hcont : ContinuousWithinAt E (Ico a τ) τ :=
        (hE τ hτ).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc_right hτ.2))
      have : (𝓝[Ico a τ] τ).NeBot := right_nhdsWithin_Ico_neBot haτ
      exact le_of_tendsto hcont (eventually_nhdsWithin_of_forall hbefore)
    exact absurd (hcτ.trans hτm) (not_le.mpr hm)
  exact fun t ht ↦ himprove t ht fun s hs ↦ hlt s ⟨hs.1, hs.2.trans ht.2⟩

/-- **Scalar comparison, one-sided.** If `F' + A F ≤ A K` with `A ≥ 0` on `[a, b)`, then `F` stays
below any `m ≥ max(F(a), K)` on `[a, b]`. Only right derivatives are used. -/
theorem le_of_forcing_le {F F' A : ℝ → ℝ} {a b K m : ℝ} (hF : ContinuousOn F (Icc a b))
    (hF' : ∀ s ∈ Ico a b, HasDerivWithinAt F (F' s) (Ici s) s) (hA : ∀ s ∈ Ico a b, 0 ≤ A s)
    (hforcing : ∀ s ∈ Ico a b, F' s + A s * F s ≤ A s * K) (ha : F a ≤ m) (hK : K ≤ m) :
    ∀ t ∈ Icc a b, F t ≤ m := by
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hlen : 0 < 1 + (t - a) := by linarith [ht.1]
  set δ := ε / (1 + (t - a)) with hδdef
  have hδ : 0 < δ := div_pos hε hlen
  have hbarrier := image_le_of_deriv_right_lt_deriv_boundary hF hF'
    (B := fun s ↦ m + δ * (1 + (s - a))) (B' := fun _ ↦ δ) (by simp; linarith)
    (fun s ↦ by
      simpa using (((hasDerivAt_id s).sub_const a).const_add 1).const_mul δ |>.const_add m)
    (fun s hs hFs ↦ by
      have h1 := hforcing s hs
      have h2 := hA s hs
      have hs1 : 0 ≤ s - a := sub_nonneg.mpr hs.1
      have hKF : K ≤ F s := by rw [hFs]; nlinarith
      nlinarith [mul_nonneg h2 (sub_nonneg.mpr hKF)]) ht
  have hε' : δ * (1 + (t - a)) = ε := by rw [hδdef]; field_simp
  linarith

/-- **Scalar comparison.** If `|F' + A F| ≤ A K` with `A ≥ 0` on `[a, b)`, then
`|F(t)| ≤ max(|F(a)|, K)` on `[a, b]`. This is the sup-norm estimate of Part I, Lemmas A.1 and
A.2, along one characteristic. -/
theorem abs_le_max_of_abs_forcing_le {F F' A : ℝ → ℝ} {a b K : ℝ} (hF : ContinuousOn F (Icc a b))
    (hF' : ∀ s ∈ Ico a b, HasDerivWithinAt F (F' s) (Ici s) s) (hA : ∀ s ∈ Ico a b, 0 ≤ A s)
    (hforcing : ∀ s ∈ Ico a b, |F' s + A s * F s| ≤ A s * K) :
    ∀ t ∈ Icc a b, |F t| ≤ max |F a| K := by
  intro t ht
  rw [abs_le]
  constructor
  · have h := le_of_forcing_le (F := fun s ↦ -F s) (F' := fun s ↦ -F' s) hF.neg
      (fun s hs ↦ (hF' s hs).neg) hA
      (fun s hs ↦ by have := (abs_le.mp (hforcing s hs)).1; linarith)
      ((neg_le_abs (F a)).trans (le_max_left _ _)) (le_max_right _ _) t ht
    linarith
  · exact le_of_forcing_le hF hF' hA (fun s hs ↦ (abs_le.mp (hforcing s hs)).2)
      ((le_abs_self (F a)).trans (le_max_left _ _)) (le_max_right _ _) t ht

/-! ### Transport equations in characteristic form -/

/-- **The chain rule along a characteristic.** If `f` is differentiable relative to
`D × [t₀, ∞)` at `(γ s, s)` and the path `γ` has velocity `w` at `s` and stays in `D` on
`[s, t]` with `t₀ ≤ s < t`, then `s ↦ f (γ s) s` has the right derivative `Df(γ s, s)(w, 1)`. -/
theorem hasDerivWithinAt_comp_path {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {D : Set X} {f : X → ℝ → ℝ} {L : X × ℝ →L[ℝ] ℝ} {γ : ℝ → X} {w : X} {t₀ s t : ℝ}
    (hf : HasFDerivWithinAt (Function.uncurry f) L (D ×ˢ Ici t₀) (γ s, s))
    (hγ : HasDerivAt γ w s) (hD : ∀ u ∈ Icc s t, γ u ∈ D) (hs : t₀ ≤ s) (hst : s < t) :
    HasDerivWithinAt (fun s ↦ f (γ s) s) (L (w, 1)) (Ici s) s := by
  have hcurve : HasDerivWithinAt (fun s ↦ (γ s, s)) (w, 1) (Icc s t) s :=
    (HasDerivAt.prodMk hγ (hasDerivAt_id' s)).hasDerivWithinAt
  have hmaps : MapsTo (fun s ↦ (γ s, s)) (Icc s t) (D ×ˢ Ici t₀) := fun u hu ↦
    ⟨hD u hu, hs.trans hu.1⟩
  exact (hf.comp_hasDerivWithinAt (f := fun u ↦ (γ u, u)) s hcurve hmaps).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE hst)


/-- `f` solves `∂ₜ f + v · ∇f = -a f + B` on `D` over `[t₀, T]` in characteristic form: every
point `p ∈ D` at every time `t ∈ [t₀, T]` is the endpoint of a path `γ` that stays in `D` on
`[t₀, t]`, along which `s ↦ f (γ s) s` is continuous on `[t₀, t]` and has the right derivative
`-a (γ s) s * f (γ s) s + B (γ s) s` on `[t₀, t)`. No velocity field appears: the paths are the
backward characteristics, and only their existence and the scalar equation along them are used.
Scalar unknowns are the case of a one-point domain and constant paths. -/
def SolvesAlongPaths {X : Type*} (D : Set X) (a B f : X → ℝ → ℝ) (t₀ T : ℝ) : Prop :=
  ∀ t ∈ Icc t₀ T, ∀ p ∈ D, ∃ γ : ℝ → X, γ t = p ∧ (∀ s ∈ Icc t₀ t, γ s ∈ D) ∧
    ContinuousOn (fun s ↦ f (γ s) s) (Icc t₀ t) ∧
    ∀ s ∈ Ico t₀ t, HasDerivWithinAt (fun s ↦ f (γ s) s)
      (-a (γ s) s * f (γ s) s + B (γ s) s) (Ici s) s

namespace SolvesAlongPaths

variable {X : Type*} {D : Set X} {a B f : X → ℝ → ℝ} {t₀ T : ℝ}

/-- **Scalar unknowns.** If `t ↦ f p t` itself satisfies `f' = -a f + B` from the right for every
`p ∈ D`, then `f` solves the equation along the constant paths. This is the form of the scalar
components of an energy, which have no transport term. -/
theorem of_hasDerivWithinAt (hcont : ∀ p ∈ D, ContinuousOn (f p) (Icc t₀ T))
    (hderiv : ∀ p ∈ D, ∀ s ∈ Ico t₀ T,
      HasDerivWithinAt (f p) (-a p s * f p s + B p s) (Ici s) s) :
    SolvesAlongPaths D a B f t₀ T := fun _ ht p hp ↦
  ⟨fun _ ↦ p, rfl, fun _ _ ↦ hp, (hcont p hp).mono (Icc_subset_Icc_right ht.2),
    fun s hs ↦ hderiv p hp s ⟨hs.1, hs.2.trans_le ht.2⟩⟩

/-- A constant multiple `μ f` solves the equation with forcing `μ B`. -/
theorem const_mul (h : SolvesAlongPaths D a B f t₀ T) (μ : ℝ) :
    SolvesAlongPaths D a (fun p t ↦ μ * B p t) (fun p t ↦ μ * f p t) t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ := h t ht p hp
  refine ⟨γ, hγt, hγD, continuousOn_const.mul hcont, fun s hs ↦ ?_⟩
  convert (hderiv s hs).const_mul μ using 1
  ring

/-- The split of the right-hand side into damping and forcing can be changed pointwise: only the
value `-a f + B` along the paths matters. -/
theorem congr (h : SolvesAlongPaths D a B f t₀ T) {a' B' : X → ℝ → ℝ}
    (heq : ∀ t ∈ Icc t₀ T, ∀ p ∈ D, -a' p t * f p t + B' p t = -a p t * f p t + B p t) :
    SolvesAlongPaths D a' B' f t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ := h t ht p hp
  refine ⟨γ, hγt, hγD, hcont, fun s hs ↦ ?_⟩
  rw [heq s ⟨hs.1, hs.2.le.trans ht.2⟩ (γ s) (hγD s (Ico_subset_Icc_self hs))]
  exact hderiv s hs

/-- The weighted function `e^{λ (t - t₀)} f` solves the equation with damping `a - λ` and forcing
`e^{λ (t - t₀)} B`. -/
theorem exp_mul (h : SolvesAlongPaths D a B f t₀ T) (lam : ℝ) :
    SolvesAlongPaths D (fun p t ↦ a p t - lam) (fun p t ↦ Real.exp (lam * (t - t₀)) * B p t)
      (fun p t ↦ Real.exp (lam * (t - t₀)) * f p t) t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ := h t ht p hp
  have hexp (s : ℝ) : HasDerivAt (fun s ↦ Real.exp (lam * (s - t₀)))
      (Real.exp (lam * (s - t₀)) * lam) s := by
    simpa using (((hasDerivAt_id s).sub_const t₀).const_mul lam).exp
  refine ⟨γ, hγt, hγD,
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
      ).continuousOn.mul hcont, fun s hs ↦ ?_⟩
  convert (hexp s).hasDerivWithinAt.mul (hderiv s hs) using 1
  ring

/-- **Shifting time**: if `f` solves the equation on `[t₀ + s, T + s]`, then `f(·, · + s)` solves
the shifted equation on `[t₀, T]`, along the shifted paths. -/
theorem comp_add_const {s : ℝ} (h : SolvesAlongPaths D a B f (t₀ + s) (T + s)) :
    SolvesAlongPaths D (fun p t ↦ a p (t + s)) (fun p t ↦ B p (t + s))
      (fun p t ↦ f p (t + s)) t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ :=
    h (t + s) ⟨by linarith [ht.1], by linarith [ht.2]⟩ p hp
  have hmaps : MapsTo (fun u ↦ u + s) (Icc t₀ t) (Icc (t₀ + s) (t + s)) :=
    fun u hu ↦ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  refine ⟨fun u ↦ γ (u + s), hγt, fun u hu ↦ hγD (u + s) (hmaps hu),
    hcont.comp (continuous_id.add continuous_const).continuousOn hmaps, fun u hu ↦ ?_⟩
  have hshift : HasDerivWithinAt (fun u ↦ u + s) 1 (Ici u) u :=
    ((hasDerivAt_id' u).add_const s).hasDerivWithinAt
  have h' := (hderiv (u + s) ⟨by linarith [hu.1], by linarith [hu.2]⟩).scomp u hshift
    fun v hv ↦ by simp only [mem_Ici] at hv ⊢; linarith
  simpa [Function.comp_def] using h'

/-- **Shifting time back**: if `f(·, · + s)` solves the shifted equation on `[t₀ - s, T - s]`,
then `f` solves the equation on `[t₀, T]`. -/
theorem of_comp_add_const {s : ℝ}
    (h : SolvesAlongPaths D (fun p t ↦ a p (t + s)) (fun p t ↦ B p (t + s))
      (fun p t ↦ f p (t + s)) (t₀ - s) (T - s)) :
    SolvesAlongPaths D a B f t₀ T := by
  rw [sub_eq_add_neg, sub_eq_add_neg] at h
  simpa only [neg_add_cancel_right] using h.comp_add_const

/-- **The sup-norm estimate along characteristics.** If `f` starts below `m₀` on `D`, and
`a ≥ 0`, `|B| ≤ a K` on `D` at the times `[t₀, t)`, then `|f p t| ≤ max(m₀, K)`. -/
theorem abs_le_max (h : SolvesAlongPaths D a B f t₀ T) {t : ℝ} (ht : t ∈ Icc t₀ T) {p : X}
    (hp : p ∈ D) {m₀ K : ℝ} (h₀ : ∀ q ∈ D, |f q t₀| ≤ m₀)
    (hbound : ∀ s ∈ Ico t₀ t, ∀ q ∈ D, 0 ≤ a q s ∧ |B q s| ≤ a q s * K) :
    |f p t| ≤ max m₀ K := by
  obtain ⟨γ, hγt, hγD, hcont, hderiv⟩ := h t ht p hp
  have hcomp := abs_le_max_of_abs_forcing_le (A := fun s ↦ a (γ s) s) hcont hderiv
    (fun s hs ↦ (hbound s hs (γ s) (hγD s (Ico_subset_Icc_self hs))).1)
    (fun s hs ↦ by
      have := (hbound s hs (γ s) (hγD s (Ico_subset_Icc_self hs))).2
      simpa only [neg_mul, neg_add_cancel_comm] using this) t (right_mem_Icc.mpr ht.1)
  rw [hγt] at hcomp
  exact hcomp.trans (max_le_max_right K (h₀ _ (hγD t₀ (left_mem_Icc.mpr ht.1))))

/-- **From the differential form.** If every point of `D` at every time is the endpoint of a
characteristic `γ' = v(γ)` that stays in `D`, and `f` is differentiable at `(p, t)` relative to
`D × [t, ∞)` (a right derivative in time) with `Df(p, t)(v(t, p), 1) = -a f + B`, then `f`
solves the equation along these paths. -/
theorem of_hasFDerivWithinAt [NormedAddCommGroup X] [NormedSpace ℝ X] {v : ℝ → X → X}
    {f' : X → ℝ → X × ℝ →L[ℝ] ℝ}
    (hpaths : ∀ t ∈ Icc t₀ T, ∀ p ∈ D, ∃ γ : ℝ → X, γ t = p ∧
      ∀ s ∈ Icc t₀ t, γ s ∈ D ∧ HasDerivAt γ (v s (γ s)) s)
    (hcont : ContinuousOn (Function.uncurry f) (D ×ˢ Icc t₀ T))
    (hf : ∀ t ∈ Ico t₀ T, ∀ p ∈ D,
      HasFDerivWithinAt (Function.uncurry f) (f' p t) (D ×ˢ Ici t) (p, t))
    (heq : ∀ t ∈ Ico t₀ T, ∀ p ∈ D, f' p t (v t p, 1) = -a p t * f p t + B p t) :
    SolvesAlongPaths D a B f t₀ T := by
  intro t ht p hp
  obtain ⟨γ, hγt, hγ⟩ := hpaths t ht p hp
  have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
  have hγcont : ContinuousOn γ (Icc t₀ t) := fun s hs ↦ (hγ s hs).2.continuousAt.continuousWithinAt
  refine ⟨γ, hγt, fun s hs ↦ (hγ s hs).1, ?_, fun s hs ↦ ?_⟩
  · exact hcont.comp (hγcont.prodMk continuousOn_id) fun s hs ↦ ⟨(hγ s hs).1, hsub hs⟩
  · have hsI : s ∈ Icc t₀ t := Ico_subset_Icc_self hs
    have hcomp := hasDerivWithinAt_comp_path (hf s ⟨hs.1, hs.2.trans_le ht.2⟩ (γ s) (hγ s hsI).1)
      (hγ s hsI).2 (fun u hu ↦ (hγ u ⟨hsI.1.trans hu.1, hu.2⟩).1) le_rfl hs.2
    rwa [heq s ⟨hs.1, hs.2.trans_le ht.2⟩ (γ s) (hγ s hsI).1] at hcomp

end SolvesAlongPaths

/-- A transport equation `∂ₜ f + v · ∇f = -a f + B` in differential form on the open (closed)
orthant, with a velocity tangent to its faces, holds along the characteristics. -/
theorem IsTangentLipschitzField.solvesAlongPaths {ι : Type*} [Fintype ι] {S : Set ι}
    {v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {t₀ T : ℝ} {K : ℝ≥0}
    (hv : IsTangentLipschitzField S v t₀ T K) {D : Set (EuclideanSpace ℝ ι)}
    (hD : D = openOrthant S ∨ D = closedOrthant S) {a B f : EuclideanSpace ℝ ι → ℝ → ℝ}
    {f' : EuclideanSpace ℝ ι → ℝ → EuclideanSpace ℝ ι × ℝ →L[ℝ] ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (D ×ˢ Icc t₀ T))
    (hf : ∀ t ∈ Ico t₀ T, ∀ p ∈ D,
      HasFDerivWithinAt (Function.uncurry f) (f' p t) (D ×ˢ Ici t) (p, t))
    (heq : ∀ t ∈ Ico t₀ T, ∀ p ∈ D, f' p t (v t p, 1) = -a p t * f p t + B p t) :
    SolvesAlongPaths D a B f t₀ T := by
  refine SolvesAlongPaths.of_hasFDerivWithinAt (v := v) (fun t ht p hp ↦ ?_) hcont hf heq
  rcases hD with rfl | rfl
  · obtain ⟨γ, hγt, hγ, hγo⟩ :=
      hv.exists_backward_characteristic ht (openOrthant_subset_closedOrthant hp)
    exact ⟨γ, hγt, fun s hs ↦ ⟨hγo hp s hs, (hγ s hs).2⟩⟩
  · obtain ⟨γ, hγt, hγ, -⟩ := hv.exists_backward_characteristic ht hp
    exact ⟨γ, hγt, hγ⟩

/-! ### Part I, Lemma A.1 -/

/-- **Part I, Lemma A.1.** Let `fᵢ` (`i` in a finite set) solve `∂ₜ fᵢ + vᵢ · ∇fᵢ = -aᵢᵢ fᵢ + Bᵢ`
along characteristics on `Dᵢ` over `[t₀, T]`, and let `E(t) = maxᵢ μᵢ ‖fᵢ(t)‖_∞` with `μᵢ > 0`
be continuous. If (A.2) `|Bᵢ| ≤ ∑_{j ≠ i} |aᵢⱼ| ‖fⱼ‖_∞` and (A.3)
`aᵢᵢ - ∑_{j ≠ i} μᵢ μⱼ⁻¹ |aᵢⱼ| ≥ λ`, `∑_{j ≠ i} μᵢ μⱼ⁻¹ |aᵢⱼ| ≤ M` hold, then
`E(t) ≤ e^{-λ (t - t₀)} E(t₀)` on `[t₀, T]`. The sup norms are extended reals. -/
theorem le_exp_mul_of_damping_dominates {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    {D : ∀ i, Set (X i)} {f a B : ∀ i, X i → ℝ → ℝ} {a₁ : ∀ i, ι → X i → ℝ → ℝ} {μ : ι → ℝ}
    {E : ℝ → ℝ≥0∞} {t₀ T lam M : ℝ} (hμ : ∀ i, 0 < μ i)
    (hsol : ∀ i, SolvesAlongPaths (D i) (a i) (B i) (f i) t₀ T)
    (hE_eq : ∀ t ∈ Icc t₀ T, E t = ⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p t|))
    (hE : ContinuousOn E (Icc t₀ T))
    (hB : ∀ t ∈ Icc t₀ T, ∀ i, ∀ p ∈ D i, ENNReal.ofReal |B i p t| ≤ ∑ j ∈ Finset.univ.erase i,
      ENNReal.ofReal |a₁ i j p t| * ⨆ q ∈ D j, ENNReal.ofReal |f j q t|)
    (hdiag : ∀ t ∈ Icc t₀ T, ∀ i, ∀ p ∈ D i, lam ≤ a i p t - ∑ j ∈ Finset.univ.erase i,
      μ i / μ j * |a₁ i j p t|)
    (hM : ∀ t ∈ Icc t₀ T, ∀ i, ∀ p ∈ D i, ∑ j ∈ Finset.univ.erase i, μ i / μ j * |a₁ i j p t| ≤ M)
    (hM₀ : 0 ≤ M) :
    ∀ t ∈ Icc t₀ T, E t ≤ ENNReal.ofReal (Real.exp (-lam * (t - t₀))) * E t₀ := by
  intro t ht
  have ht₀ : t₀ ∈ Icc t₀ T := ⟨le_rfl, ht.1.trans ht.2⟩
  by_cases htop : E t₀ = ⊤
  · rw [htop, ENNReal.mul_top (by simpa using Real.exp_pos _)]
    exact le_top
  set E₀ := (E t₀).toReal with hE₀def
  have hE₀ : 0 ≤ E₀ := ENNReal.toReal_nonneg
  -- the components at time `t₀` are bounded by `E₀`
  have hcomp (s : ℝ) (hs : s ∈ Icc t₀ T) (hfin : E s ≠ ⊤) (i : ι) (q : X i) (hq : q ∈ D i) :
      μ i * |f i q s| ≤ (E s).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hfin, hE_eq s hs]
    exact le_iSup_of_le i (le_iSup₂_of_le q hq le_rfl)
  have hmain : ∀ η : ℝ, 0 < η →
      E t ≤ ENNReal.ofReal (Real.exp (-(lam - η) * (t - t₀)) * (E₀ + η)) := by
    intro η hη
    set lam' := lam - η
    set K := E₀ + η with hKdef
    have hK : 0 < K := by positivity
    set w : ℝ → ℝ := fun s ↦ Real.exp (lam' * (s - t₀)) with hwdef
    have hw (s : ℝ) : 0 < w s := Real.exp_pos _
    set K₁ := K * M / (M + η) with hK₁def
    have hMη : 0 < M + η := by linarith
    have hK₁ : K₁ < K := by
      rw [hK₁def, div_lt_iff₀ hMη]
      linarith [mul_pos hK hη]
    have hK₁₀ : 0 ≤ K₁ := by positivity
    have hcont : ContinuousOn (fun s ↦ ENNReal.ofReal (w s) * E s) (Icc t₀ T) :=
      (ENNReal.continuous_ofReal.comp (by fun_prop : Continuous fun s ↦
        Real.exp (lam' * (s - t₀)))).continuousOn.ennreal_mul hE
        (fun s _ ↦ Or.inl (by simpa using hw s)) (fun s _ ↦ Or.inr ENNReal.ofReal_ne_top)
    have hstart : ENNReal.ofReal (w t₀) * E t₀ < ENNReal.ofReal K := by
      change ENNReal.ofReal (Real.exp (lam' * (t₀ - t₀))) * E t₀ < ENNReal.ofReal K
      rw [sub_self, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
        ← ENNReal.ofReal_toReal htop, ENNReal.ofReal_lt_ofReal_iff hK]
      linarith
    have hlevel : ENNReal.ofReal (max E₀ K₁) < ENNReal.ofReal K :=
      (ENNReal.ofReal_lt_ofReal_iff hK).mpr (max_lt (by linarith) hK₁)
    have hboot := le_of_bootstrap hcont hstart hlevel (fun t' ht' hb ↦ by
      -- the weighted components solve the equation with damping `a - λ'`
      have hbound : ∀ i, ∀ p ∈ D i, w t' * (μ i * |f i p t'|) ≤ max E₀ K₁ := by
        intro i p hp
        have hsolw := ((hsol i).const_mul (μ i)).exp_mul lam'
        have h := hsolw.abs_le_max ht' hp (m₀ := E₀) (K := K₁)
          (fun q hq ↦ by
            simp only [sub_self, mul_zero, Real.exp_zero, one_mul, abs_mul, abs_of_pos (hμ i)]
            exact hcomp t₀ ht₀ htop i q hq)
          (fun s hs q hq ↦ by
            have hsI : s ∈ Icc t₀ T := ⟨hs.1, hs.2.le.trans ht'.2⟩
            have hbs := hb s ⟨hs.1, hs.2.le⟩
            have hfin : E s ≠ ⊤ := by
              intro hinf
              rw [hinf, ENNReal.mul_top (by simpa using hw s)] at hbs
              exact absurd hbs (not_lt.mpr le_top)
            set Es := (E s).toReal
            -- the sup norms of the other components
            have hsup (j : ι) : (⨆ q' ∈ D j, ENNReal.ofReal |f j q' s|) ≤
                ENNReal.ofReal (Es / μ j) :=
              iSup₂_le fun q' hq' ↦ ENNReal.ofReal_le_ofReal (by
                rw [le_div_iff₀ (hμ j), mul_comm]
                exact hcomp s hsI hfin j q' hq')
            have hBle : |B i q s| ≤
                ∑ j ∈ Finset.univ.erase i, |a₁ i j q s| * (Es / μ j) := by
              have h1 := (hB s hsI i q hq).trans (Finset.sum_le_sum fun j _ ↦
                mul_le_mul_of_nonneg_left (hsup j) zero_le)
              have h2 : ∑ j ∈ Finset.univ.erase i,
                  ENNReal.ofReal |a₁ i j q s| * ENNReal.ofReal (Es / μ j) =
                  ENNReal.ofReal (∑ j ∈ Finset.univ.erase i, |a₁ i j q s| * (Es / μ j)) := by
                rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ by have := hμ j; positivity)]
                exact Finset.sum_congr rfl fun j _ ↦ (ENNReal.ofReal_mul (abs_nonneg _)).symm
              exact (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun j _ ↦ by
                have := hμ j; positivity)).mp (h1.trans_eq h2)
            set C := ∑ j ∈ Finset.univ.erase i, μ i / μ j * |a₁ i j q s|
            have hC₀ : 0 ≤ C := Finset.sum_nonneg fun j _ ↦ by
              have := hμ i; have := hμ j; positivity
            have hμB : μ i * |B i q s| ≤ C * Es := by
              refine (mul_le_mul_of_nonneg_left hBle (hμ i).le).trans_eq ?_
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              have := (hμ j).ne'
              field_simp
            have hwEs : w s * Es < K := by
              rwa [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (hw s).le,
                ENNReal.ofReal_lt_ofReal_iff hK] at hbs
            have hCM := hM s hsI i q hq
            have hCa := hdiag s hsI i q hq
            refine ⟨by simp only [lam']; linarith, ?_⟩
            simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (hμ i)]
            calc w s * (μ i * |B i q s|) ≤ w s * (C * Es) := mul_le_mul_of_nonneg_left hμB (hw s).le
              _ = C * (w s * Es) := by ring
              _ ≤ C * K := mul_le_mul_of_nonneg_left hwEs.le hC₀
              _ ≤ (a i q s - lam') * K₁ := by
                  rw [hK₁def, mul_div_assoc', le_div_iff₀ hMη]
                  have h2 : C + η ≤ a i q s - lam' := by simp only [lam']; linarith
                  nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg hK.le hM₀),
                    mul_le_mul_of_nonneg_left hCM (mul_nonneg hK.le hη.le)])
        simpa only [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (hμ i)] using h
      have hEt' : E t' ≤ ENNReal.ofReal (max E₀ K₁ / w t') := by
        rw [hE_eq t' ht']
        exact iSup_le fun i ↦ iSup₂_le fun p hp ↦ ENNReal.ofReal_le_ofReal (by
          rw [le_div_iff₀ (hw t'), mul_comm]
          exact hbound i p hp)
      calc ENNReal.ofReal (w t') * E t' ≤ ENNReal.ofReal (w t') *
            ENNReal.ofReal (max E₀ K₁ / w t') := by gcongr
        _ = ENNReal.ofReal (max E₀ K₁) := by
            rw [← ENNReal.ofReal_mul (hw t').le, mul_div_cancel₀ _ (hw t').ne'])
      t ht
    have hwt : ENNReal.ofReal (w t) * E t ≤ ENNReal.ofReal K := hboot.trans hlevel.le
    have hne : ENNReal.ofReal (w t) ≠ 0 := by simpa using hw t
    have hsplit : ENNReal.ofReal (Real.exp (-lam' * (t - t₀)) * K) =
        ENNReal.ofReal K / ENNReal.ofReal (w t) := by
      rw [← ENNReal.ofReal_div_of_pos (hw t), hwdef, neg_mul, Real.exp_neg, mul_comm,
        div_eq_mul_inv]
    rw [hsplit, ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hwt
  have hlim : Tendsto (fun η ↦ ENNReal.ofReal (Real.exp (-(lam - η) * (t - t₀)) * (E₀ + η)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (Real.exp (-lam * (t - t₀)) * E₀))) := by
    have hc : Continuous fun η : ℝ ↦ ENNReal.ofReal (Real.exp (-(lam - η) * (t - t₀)) * (E₀ + η)) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hle := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη ↦ hmain η hη)
  rwa [ENNReal.ofReal_mul (Real.exp_pos _).le, hE₀def, ENNReal.ofReal_toReal htop] at hle

/-! ### Part I, Lemma A.2 -/

/-- The running maximum `E_max(t) = sup_{0 ≤ s ≤ t} E(s)` of Part I, Lemma A.2. -/
def runningMax (E : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ⨆ s ∈ Icc 0 t, E s

/-- A continuous energy that stays below `c` on `[0, t]` has its running maximum below `c`: the
maximum over the compact interval is attained. -/
theorem runningMax_lt {E : ℝ → ℝ≥0∞} {t : ℝ} {c : ℝ≥0∞} (ht : 0 ≤ t)
    (hE : ContinuousOn E (Icc 0 t)) (h : ∀ s ∈ Icc 0 t, E s < c) : runningMax E t < c := by
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ht) hE
  exact (iSup₂_le fun s hs ↦ hmax hs).trans_lt (h s₀ hs₀)

/-- The convex combination behind Part I, Lemma A.2: if `C ≤ M` and `C ≤ A - ε₀` with `ε₀ > 0`
and `M ≥ 0`, then `C ≤ (1 - δ) A` with `δ = ε₀ / (M + ε₀)`. -/
theorem le_one_sub_div_mul {C A M ε₀ : ℝ} (hε₀ : 0 < ε₀) (hM : 0 ≤ M) (hCM : C ≤ M)
    (hCA : C ≤ A - ε₀) : C ≤ (1 - ε₀ / (M + ε₀)) * A := by
  have hpos : 0 < M + ε₀ := by linarith
  have h1 : 1 - ε₀ / (M + ε₀) = M / (M + ε₀) := by field_simp; ring
  rw [h1, div_mul_eq_mul_div, le_div_iff₀ hpos]
  nlinarith [mul_le_mul_of_nonneg_left hCA hM, mul_le_mul_of_nonneg_right hCM hε₀.le]

/-- **The bootstrap with an abstract forcing budget.** Let `fᵢ` solve
`∂ₜ fᵢ + vᵢ · ∇fᵢ = -aᵢ fᵢ + Bᵢ` along characteristics on `Dᵢ` over `[0, T]`, and let
`E(t) = supᵢ ‖fᵢ(t)‖_∞` be continuous with `E(0) < c`. If, whenever `E < c` on `[0, t]`, the
damping is nonnegative and `|Bᵢ| ≤ aᵢ K` at time `t` for a fixed `K < c`, then
`E(t) ≤ max(E(0), K)` on `[0, T]`. -/
theorem le_max_of_forcing_le_mul {ι : Type*} {X : ι → Type*} {D : ∀ i, Set (X i)}
    {a B f : ∀ i, X i → ℝ → ℝ} {E : ℝ → ℝ≥0∞} {T c K : ℝ}
    (hsol : ∀ i, SolvesAlongPaths (D i) (a i) (B i) (f i) 0 T)
    (hE_eq : ∀ t ∈ Icc 0 T, E t = ⨆ i, ⨆ p ∈ D i, ENNReal.ofReal |f i p t|)
    (hE : ContinuousOn E (Icc 0 T)) (h0 : E 0 < ENNReal.ofReal c) (hK : K < c)
    (hforcing : ∀ t ∈ Icc 0 T, (∀ s ∈ Icc 0 t, E s < ENNReal.ofReal c) →
      ∀ i, ∀ p ∈ D i, 0 ≤ a i p t ∧ |B i p t| ≤ a i p t * K) :
    ∀ t ∈ Icc 0 T, E t ≤ max (E 0) (ENNReal.ofReal K) := by
  intro t ht
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hc : 0 < c := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h0)
  have hE0 : E 0 ≠ ⊤ := (h0.trans ENNReal.ofReal_lt_top).ne
  have hinit : ∀ i, ∀ q ∈ D i, |f i q 0| ≤ (E 0).toReal := fun i q hq ↦ by
    rw [← ENNReal.ofReal_le_iff_le_toReal hE0, hE_eq 0 hT]
    exact le_iSup_of_le i (le_iSup₂_of_le q hq le_rfl)
  refine le_of_bootstrap (c := ENNReal.ofReal c) hE h0
    (max_lt h0 ((ENNReal.ofReal_lt_ofReal_iff hc).mpr hK)) (fun t' ht' hboot ↦ ?_) t ht
  have hbound : ∀ i, ∀ p ∈ D i, |f i p t'| ≤ max (E 0).toReal K := fun i p hp ↦
    (hsol i).abs_le_max ht' hp (hinit i) fun s hs q hq ↦
      hforcing s ⟨hs.1, hs.2.le.trans ht'.2⟩ (fun u hu ↦ hboot u ⟨hu.1, hu.2.trans hs.2.le⟩) i q hq
  rw [hE_eq t' ht']
  calc (⨆ i, ⨆ p ∈ D i, ENNReal.ofReal |f i p t'|) ≤ ENNReal.ofReal (max (E 0).toReal K) :=
        iSup_le fun i ↦ iSup₂_le fun p hp ↦ ENNReal.ofReal_le_ofReal (hbound i p hp)
    _ = max (E 0) (ENNReal.ofReal K) := by rw [ENNReal.ofReal_max, ENNReal.ofReal_toReal hE0]

/-- **Part I, Lemma A.2, with an aggregate forcing budget.** Let `fᵢ` (`i` in any index set)
solve `∂ₜ fᵢ + vᵢ · ∇fᵢ = -aᵢᵢ fᵢ + forcingᵢ` along characteristics on `Dᵢ` over `[0, T]`, and
let `E(t) = supᵢ μᵢ ‖fᵢ(t)‖_∞`, `μᵢ > 0`, be continuous with `E(0) < E_*`. If at every time where
`E_max(t) = sup_{s ≤ t} E(s) < E_*` there are budgets `Hᵢ` with `μᵢ |forcingᵢ| ≤ Hᵢ ≤ M` and
`Hᵢ ≤ aᵢᵢ E_* - ε₀`, where `ε₀ > 0` and `M ≥ 0`, then `E(t) ≤ max(E(0), (1 - δ) E_*)` on `[0, T]`
with `δ = ε₀ / (M + ε₀)`. With `Hᵢ = ∑_{j ≠ i} (|aᵢⱼ| E_* + |aᵢⱼ,₂| E_*² + |aᵢⱼ,₃|)` this is
`bootstrap_le_max`; a budget evaluated at `E_*` matches tables certified at the threshold. -/
theorem bootstrap_le_max_of_budget {ι : Type*} {X : ι → Type*} {D : ∀ i, Set (X i)}
    {f a forcing H : ∀ i, X i → ℝ → ℝ} {μ : ι → ℝ} {E : ℝ → ℝ≥0∞} {T Estar ε₀ M : ℝ}
    (hμ : ∀ i, 0 < μ i) (hsol : ∀ i, SolvesAlongPaths (D i) (a i) (forcing i) (f i) 0 T)
    (hE_eq : ∀ t ∈ Icc 0 T, E t = ⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p t|))
    (hE : ContinuousOn E (Icc 0 T))
    (hbudget : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar → ∀ i, ∀ p ∈ D i,
      μ i * |forcing i p t| ≤ H i p t ∧ H i p t ≤ M ∧ H i p t ≤ a i p t * Estar - ε₀)
    (hε₀ : 0 < ε₀) (hM₀ : 0 ≤ M) (h0 : E 0 < ENNReal.ofReal Estar) :
    ∀ t ∈ Icc 0 T, E t ≤ max (E 0) (ENNReal.ofReal ((1 - ε₀ / (M + ε₀)) * Estar)) := by
  have hEstar : 0 < Estar := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h0)
  have hδ : 0 < ε₀ / (M + ε₀) := div_pos hε₀ (by linarith)
  refine le_max_of_forcing_le_mul (a := a) (B := fun i p t ↦ μ i * forcing i p t)
    (f := fun i p t ↦ μ i * f i p t) (c := Estar) (fun i ↦ (hsol i).const_mul (μ i))
    (fun t ht ↦ by simp only [abs_mul, abs_of_pos (hμ _)]; exact hE_eq t ht) hE h0
    (by linarith [mul_pos hδ hEstar]) ?_
  intro t ht hboot i p hp
  obtain ⟨hHf, hHM, hHa⟩ := hbudget t ht
    (runningMax_lt ht.1 (hE.mono (Icc_subset_Icc_right ht.2)) hboot) i p hp
  have hH₀ : 0 ≤ H i p t := (mul_nonneg (hμ i).le (abs_nonneg _)).trans hHf
  refine ⟨nonneg_of_mul_nonneg_left (by linarith) hEstar, ?_⟩
  rw [abs_mul, abs_of_pos (hμ i)]
  linarith [le_one_sub_div_mul hε₀ hM₀ hHM hHa]

/-- **Part I, Lemma A.2, in bootstrap form.** Let `fᵢ` (`i` in a finite set) solve
`∂ₜ fᵢ + vᵢ · ∇fᵢ = -aᵢᵢ fᵢ + Bᵢ + Nᵢ + ε̄ᵢ` along characteristics on `Dᵢ` over `[0, T]`, with
`forcingᵢ = Bᵢ + Nᵢ + ε̄ᵢ`, and let `E(t) = maxᵢ μᵢ ‖fᵢ(t)‖_∞`, `μᵢ > 0`, be continuous with
`E(0) < E_*`. Assume

* (A.10), only at the times where `E_max(t) = sup_{s ≤ t} E(s) < E_*`:
  `μᵢ |forcingᵢ| ≤ ∑_{j ≠ i} (|aᵢⱼ| E_max + |aᵢⱼ,₂| E_max² + |aᵢⱼ,₃|)`;
* (A.11), non-strict: `aᵢᵢ E_* - ∑_{j ≠ i} (|aᵢⱼ| E_* + |aᵢⱼ,₂| E_*² + |aᵢⱼ,₃|) ≥ ε₀` and
  `∑_{j ≠ i} (|aᵢⱼ| E_* + |aᵢⱼ,₂| E_*² + |aᵢⱼ,₃|) ≤ M`, with `ε₀ > 0` and `M ≥ 0`.

Then `E(t) ≤ max(E(0), (1 - δ) E_*)` on `[0, T]` with `δ = ε₀ / (M + ε₀)`, so `E < E_*`
throughout. The forcing bound is the `E_max` form of Part I. -/
theorem bootstrap_le_max {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    {D : ∀ i, Set (X i)} {f a forcing : ∀ i, X i → ℝ → ℝ} {a₁ a₂ a₃ : ∀ i, ι → X i → ℝ → ℝ}
    {μ : ι → ℝ} {E : ℝ → ℝ≥0∞} {T Estar ε₀ M : ℝ} (hμ : ∀ i, 0 < μ i)
    (hsol : ∀ i, SolvesAlongPaths (D i) (a i) (forcing i) (f i) 0 T)
    (hE_eq : ∀ t ∈ Icc 0 T, E t = ⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p t|))
    (hE : ContinuousOn E (Icc 0 T))
    (hforcing : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar → ∀ i, ∀ p ∈ D i,
      μ i * |forcing i p t| ≤ ∑ j ∈ Finset.univ.erase i, (|a₁ i j p t| * (runningMax E t).toReal +
      |a₂ i j p t| * (runningMax E t).toReal ^ 2 + |a₃ i j p t|))
    (hdiag : ∀ t ∈ Icc 0 T, ∀ i, ∀ p ∈ D i, ε₀ ≤ a i p t * Estar - ∑ j ∈ Finset.univ.erase i,
      (|a₁ i j p t| * Estar + |a₂ i j p t| * Estar ^ 2 + |a₃ i j p t|))
    (hM : ∀ t ∈ Icc 0 T, ∀ i, ∀ p ∈ D i, ∑ j ∈ Finset.univ.erase i,
      (|a₁ i j p t| * Estar + |a₂ i j p t| * Estar ^ 2 + |a₃ i j p t|) ≤ M)
    (hε₀ : 0 < ε₀) (hM₀ : 0 ≤ M) (h0 : E 0 < ENNReal.ofReal Estar) :
    ∀ t ∈ Icc 0 T, E t ≤ max (E 0) (ENNReal.ofReal ((1 - ε₀ / (M + ε₀)) * Estar)) := by
  refine bootstrap_le_max_of_budget (H := fun i p t ↦ ∑ j ∈ Finset.univ.erase i,
      (|a₁ i j p t| * Estar + |a₂ i j p t| * Estar ^ 2 + |a₃ i j p t|)) hμ hsol hE_eq hE
    (fun t ht hmax i p hp ↦ ⟨?_, hM t ht i p hp, by linarith [hdiag t ht i p hp]⟩) hε₀ hM₀ h0
  have hmax_le : (runningMax E t).toReal ≤ Estar := (ENNReal.toReal_lt_of_lt_ofReal hmax).le
  have hmax₀ : 0 ≤ (runningMax E t).toReal := ENNReal.toReal_nonneg
  exact (hforcing t ht hmax i p hp).trans (Finset.sum_le_sum fun j _ ↦ by gcongr)

/-- **Part I, Lemma A.2 from positive times.** In the situation of `bootstrap_le_max_of_budget`,
with the equations required only on `[ε, T]` for every `ε ∈ (0, T]` instead of on `[0, T]`,
`E < E_*` on `[0, T]`: by continuity `E < E_*` near `t = 0`, and the bootstrap runs from a small
positive time. No time derivative at `t = 0` is used. -/
theorem bootstrap_lt_of_budget_of_pos {ι : Type*} {X : ι → Type*} {D : ∀ i, Set (X i)}
    {f a forcing H : ∀ i, X i → ℝ → ℝ} {μ : ι → ℝ} {E : ℝ → ℝ≥0∞} {T Estar ε₀ M : ℝ}
    (hμ : ∀ i, 0 < μ i)
    (hsol : ∀ ε, 0 < ε → ε ≤ T → ∀ i, SolvesAlongPaths (D i) (a i) (forcing i) (f i) ε T)
    (hE_eq : ∀ t ∈ Icc 0 T, E t = ⨆ i, ⨆ p ∈ D i, ENNReal.ofReal (μ i * |f i p t|))
    (hE : ContinuousOn E (Icc 0 T))
    (hbudget : ∀ t ∈ Icc 0 T, runningMax E t < ENNReal.ofReal Estar → ∀ i, ∀ p ∈ D i,
      μ i * |forcing i p t| ≤ H i p t ∧ H i p t ≤ M ∧ H i p t ≤ a i p t * Estar - ε₀)
    (hε₀ : 0 < ε₀) (hM₀ : 0 ≤ M) (h0 : E 0 < ENNReal.ofReal Estar) :
    ∀ t ∈ Icc 0 T, E t < ENNReal.ofReal Estar := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · obtain rfl : t = 0 := le_antisymm (hT0 ▸ ht.2) ht.1
    exact h0
  have hEstar : 0 < Estar := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le h0)
  -- `E < E_*` on a right neighborhood of `0`
  have hnear : ∀ᶠ s in 𝓝[≥] (0 : ℝ), E s < ENNReal.ofReal Estar := by
    rw [← nhdsWithin_Icc_eq_nhdsGE hTpos]
    exact (hE 0 ⟨le_rfl, hT⟩).eventually (eventually_lt_nhds h0)
  obtain ⟨δ, hδ, hδE⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hnear
  set ε := min (δ / 2) T with hε_def
  have hε : 0 < ε := lt_min (half_pos hδ) hTpos
  have hεT : ε ≤ T := min_le_right _ _
  have hsmall : ∀ s ∈ Icc 0 ε, E s < ENNReal.ofReal Estar := fun s hs ↦
    hδE ⟨hs.1, hs.2.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))⟩
  rcases lt_or_ge t ε with htε | htε
  · exact hsmall t ⟨ht.1, htε.le⟩
  have hmax₀ : runningMax E ε < ENNReal.ofReal Estar :=
    runningMax_lt hε.le (hE.mono (Icc_subset_Icc_right hεT)) hsmall
  have hmaps : ∀ u ∈ Icc 0 (T - ε), u + ε ∈ Icc 0 T := fun u hu ↦
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  -- the bootstrap for the shifted components on `[0, T - ε]`
  have hshift := bootstrap_le_max_of_budget (D := D) (μ := μ) (Estar := Estar) (ε₀ := ε₀)
    (M := M) (T := T - ε) (E := fun u ↦ E (u + ε)) (f := fun i p u ↦ f i p (u + ε))
    (a := fun i p u ↦ a i p (u + ε)) (forcing := fun i p u ↦ forcing i p (u + ε))
    (H := fun i p u ↦ H i p (u + ε)) hμ
    (fun i ↦ by
      have h := hsol ε hε hεT i
      rw [show ε = 0 + ε by ring, show T = T - ε + ε by ring] at h
      exact h.comp_add_const) (fun u hu ↦ hE_eq (u + ε) (hmaps u hu))
    (hE.comp (continuous_id.add continuous_const).continuousOn hmaps)
    (fun u hu hmax i p hp ↦ by
      refine hbudget (u + ε) (hmaps u hu) ?_ i p hp
      refine lt_of_le_of_lt (iSup₂_le fun s hs ↦ ?_) (max_lt hmax₀ hmax)
      rcases le_total s ε with hsε | hsε
      · exact (le_iSup₂ (f := fun s (_ : s ∈ Icc 0 ε) ↦ E s) s ⟨hs.1, hsε⟩).trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        have hmem : s - ε ∈ Icc 0 u := ⟨by linarith, by linarith [hs.2]⟩
        have := le_iSup₂ (f := fun v (_ : v ∈ Icc 0 u) ↦ E (v + ε)) (s - ε) hmem
        simp only [sub_add_cancel] at this
        exact this)
    hε₀ hM₀ (by simpa using hsmall ε ⟨hε.le, le_rfl⟩)
  have hδ' : 0 < ε₀ / (M + ε₀) := div_pos hε₀ (by linarith)
  have h := hshift (t - ε) ⟨by linarith, by linarith [ht.2]⟩
  simp only [sub_add_cancel, zero_add] at h
  refine h.trans_lt (max_lt (hsmall ε ⟨hε.le, le_rfl⟩) ?_)
  rw [ENNReal.ofReal_lt_ofReal_iff hEstar]
  linarith [mul_pos hδ' hEstar]

end PDE.Hyperbolic.Transport
