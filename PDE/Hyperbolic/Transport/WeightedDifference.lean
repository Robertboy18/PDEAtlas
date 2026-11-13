/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Transport.Bootstrap
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The two-point transport identity

For a transported quantity `∂ₜ f + b · ∇f = c f + R`, a spatial weight `φ` and a gap weight `g`,
the weighted difference

`F(x, z, t) = (f(x) φ(x) - f(z) φ(z)) g(x - z)`

solves the two-point transport equation

`∂ₜ F + (b(x) · ∇ₓ + b(z) · ∇_z) F = (d(x) + (b(x) - b(z)) · ∇g(x - z) / g(x - z)) F`
`  + (d(x) - d(z)) g(x - z) (f φ)(z) + (R φ(x) - R φ(z)) g(x - z)`,

`d = c + b · ∇φ / φ`. This is Chen and Hou, Part I, Lemma 2.4; it turns a weighted Hölder estimate
into a weighted sup estimate on pairs of points. The first term is the damping, the second is
controlled by a sup estimate, the third is the forcing.

The weights `g_i` of (C.1b) contain `|h₁|` and `|h₂|`, so they are not differentiable on the
gap axes `h₁ = 0` and `h₂ = 0`.
Along a pair of characteristics only the right derivative of `s ↦ g(x(s) - z(s))` enters, so the
identity is proved in that form (`hasDerivWithinAt_weightedDifference`), as a statement about the
transport along the two-point characteristics
(`IsTangentLipschitzField.solvesAlongPaths_weightedDifference`), and in differential form for a
differentiable `g` (`hasFDerivAt_weightedDifference`).

## Main results

* `HasDerivAt.hasDerivWithinAt_abs_Ici`: the right derivative of `|y|`, also where `y = 0`.
* `hasDerivWithinAt_weightedDifference`: the identity along a pair of paths, with one-sided
  derivatives and a rate `r` for the gap weight, `(g ∘ h)' = r g`.
* `hasFDerivAt_weightedDifference`: Part I, Lemma 2.4 in differential form.
* `IsTangentLipschitzField.solvesAlongPaths_weightedDifference`: the weighted difference of a
  transported quantity solves the two-point transport equation along the characteristics of the
  field `(b(x), b(z))` on the off-diagonal pairs of the open orthant.

## References

* J. Chen and T. Y. Hou, *Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis*, arXiv:2210.07191, Lemma 2.4 and Appendix A.1.
  <https://arxiv.org/abs/2210.07191>
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace PDE.Hyperbolic.Transport

/-- The right derivative of `|y|` for a differentiable `y`: `sign(y) y'` where `y ≠ 0`, and `|y'|`
where `y = 0`. The gap weights of Chen and Hou depend on `|h₁|` and `|h₂|`, and this is how they
are differentiated along characteristics. -/
theorem HasDerivAt.hasDerivWithinAt_abs_Ici {y : ℝ → ℝ} {y' s : ℝ} (hy : HasDerivAt y y' s) :
    HasDerivWithinAt (fun u ↦ |y u|) (if y s = 0 then |y'| else if 0 < y s then y' else -y')
      (Ici s) s := by
  by_cases h0 : y s = 0
  · simp only [h0, ↓reduceIte]
    have h1 := hy.hasDerivWithinAt (s := Ici s)
    rw [hasDerivWithinAt_iff_isLittleO] at h1 ⊢
    refine (Asymptotics.IsBigO.of_bound 1 (eventually_nhdsWithin_of_forall fun u hu ↦ ?_)
      ).trans_isLittleO h1
    have hu' : 0 ≤ u - s := sub_nonneg.mpr hu
    simp only [h0, abs_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs, one_mul]
    rw [show (u - s) * |y'| = |(u - s) * y'| by rw [abs_mul, abs_of_nonneg hu']]
    exact abs_abs_sub_abs_le_abs_sub _ _
  · rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have h := ((hasDerivAt_abs_neg hneg).comp s hy).hasDerivWithinAt (s := Ici s)
      simp only [h0, not_lt.mpr hneg.le, ↓reduceIte]
      exact h.congr_deriv (by ring)
    · have h := ((hasDerivAt_abs_pos hpos).comp s hy).hasDerivWithinAt (s := Ici s)
      simp only [h0, hpos, ↓reduceIte]
      exact h.congr_deriv (by ring)

/-- **Part I, Lemma 2.4, along a pair of paths.** If, at time `s` and relative to a set `S`,
`u' = cₓ u + Rₓ` and `w' = c_z w + R_z` (the transported quantity at the two points), `φₓ`, `φ_z`
have derivatives `φₓ'`, `φ_z'` (the spatial weight at the two points, `φₓ ≠ 0 ≠ φ_z`), and
`G' = r G` (the gap weight), then `F = (u φₓ - w φ_z) G` satisfies
`F' = (dₓ + r) F + (dₓ - d_z) G w φ_z + (Rₓ φₓ - R_z φ_z) G` with `dₓ = cₓ + φₓ' / φₓ` and
`d_z = c_z + φ_z' / φ_z`. -/
theorem hasDerivWithinAt_weightedDifference {u w φx φz G : ℝ → ℝ} {S : Set ℝ}
    {s cx cz Rx Rz φx' φz' r : ℝ} (hu : HasDerivWithinAt u (cx * u s + Rx) S s)
    (hw : HasDerivWithinAt w (cz * w s + Rz) S s) (hφx : HasDerivWithinAt φx φx' S s)
    (hφz : HasDerivWithinAt φz φz' S s) (hG : HasDerivWithinAt G (r * G s) S s)
    (hφx0 : φx s ≠ 0) (hφz0 : φz s ≠ 0) :
    HasDerivWithinAt (fun s ↦ (u s * φx s - w s * φz s) * G s)
      ((cx + φx' / φx s + r) * ((u s * φx s - w s * φz s) * G s) +
        (cx + φx' / φx s - (cz + φz' / φz s)) * G s * (w s * φz s) +
        (Rx * φx s - Rz * φz s) * G s) S s := by
  convert ((hu.mul hφx).sub (hw.mul hφz)).mul hG using 1
  simp only [Pi.sub_apply, Pi.mul_apply]
  field_simp
  ring

/-- **Part I, Lemma 2.4.** Let `f` satisfy `∂ₜ f + b · ∇f = c f + R` at `x` and at `z` at time `t`
(through the derivatives `Lₓ`, `L_z` of `(y, t) ↦ f y t`), let `φ` be differentiable at `x` and
`z` with `φ x ≠ 0 ≠ φ z`, and let `g` be differentiable at `x - z` with `g(x - z) ≠ 0`. Then
`F(x, z, t) = (f(x) φ(x) - f(z) φ(z)) g(x - z)` is differentiable at `((x, z), t)` and its
derivative along `((b(x), b(z)), 1)` is
`(d(x) + (b(x) - b(z)) · ∇g(x - z) / g(x - z)) F + (d(x) - d(z)) g(x - z) (f φ)(z)`
`+ (R φ(x) - R φ(z)) g(x - z)`, with `d(y) = c(y) + b(y) · ∇φ(y) / φ(y)`. -/
theorem hasFDerivAt_weightedDifference {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : X → ℝ → ℝ} {φ g : X → ℝ} {b : ℝ → X → X} {c R : X → ℝ → ℝ} {x z : X} {t : ℝ}
    {Lx Lz : X × ℝ →L[ℝ] ℝ} {φx' φz' g' : X →L[ℝ] ℝ}
    (hfx : HasFDerivAt (Function.uncurry f) Lx (x, t))
    (hfz : HasFDerivAt (Function.uncurry f) Lz (z, t))
    (hx : Lx (b t x, 1) = c x t * f x t + R x t) (hz : Lz (b t z, 1) = c z t * f z t + R z t)
    (hφx : HasFDerivAt φ φx' x) (hφz : HasFDerivAt φ φz' z) (hg : HasFDerivAt g g' (x - z))
    (hφx0 : φ x ≠ 0) (hφz0 : φ z ≠ 0) (hg0 : g (x - z) ≠ 0) :
    ∃ L : (X × X) × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun q : (X × X) × ℝ ↦
        (f q.1.1 q.2 * φ q.1.1 - f q.1.2 q.2 * φ q.1.2) * g (q.1.1 - q.1.2)) L ((x, z), t) ∧
      L ((b t x, b t z), 1) =
        (c x t + φx' (b t x) / φ x + g' (b t x - b t z) / g (x - z)) *
            ((f x t * φ x - f z t * φ z) * g (x - z)) +
          (c x t + φx' (b t x) / φ x - (c z t + φz' (b t z) / φ z)) * g (x - z) *
            (f z t * φ z) +
          (R x t * φ x - R z t * φ z) * g (x - z) := by
  set q₀ : (X × X) × ℝ := ((x, z), t)
  have h1 : HasFDerivAt (𝕜 := ℝ) (fun q : (X × X) × ℝ ↦ q.1) _ q₀ := hasFDerivAt_fst
  have h2 : HasFDerivAt (𝕜 := ℝ) (fun q : (X × X) × ℝ ↦ q.2) _ q₀ := hasFDerivAt_snd
  have hpx : HasFDerivAt (𝕜 := ℝ) (fun q : (X × X) × ℝ ↦ (q.1.1, q.2)) _ q₀ := h1.fst.prodMk h2
  have hpz : HasFDerivAt (𝕜 := ℝ) (fun q : (X × X) × ℝ ↦ (q.1.2, q.2)) _ q₀ := h1.snd.prodMk h2
  have hd : HasFDerivAt (𝕜 := ℝ) (fun q : (X × X) × ℝ ↦ q.1.1 - q.1.2) _ q₀ := h1.fst.sub h1.snd
  have hFx := (hfx.comp q₀ hpx).mul (hφx.comp q₀ h1.fst)
  have hFz := (hfz.comp q₀ hpz).mul (hφz.comp q₀ h1.snd)
  have hF := (hFx.sub hFz).mul (hg.comp q₀ hd)
  refine ⟨_, hF, ?_⟩
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul, Function.comp_apply, Pi.mul_apply, Pi.sub_apply, q₀, Function.uncurry_apply_pair]
  rw [hx, hz]
  field_simp
  ring

/-- **Part I, Lemma 2.4, along the two-point characteristics.** Let `b` be tangent to the
orthant, let `f` solve `∂ₜ f + b · ∇f = c f + R` in differential form on the open orthant (with
right time derivatives), let
`φ` be differentiable and nonzero there, and let the gap weight `g` be continuous away from `0`,
with right derivative `r(h(s), h'(s)) g(h(s))` along every differentiable curve `h` with
`h(s) ≠ 0`. Then the weighted difference `F((x, z), t) = (f(x) φ(x) - f(z) φ(z)) g(x - z)` solves
the two-point transport equation along the characteristics of `(b(x), b(z))` on the pairs of
distinct points of the open orthant, with damping `-(d(x) + r(x - z, b(x) - b(z)))` and forcing
`(d(x) - d(z)) g(x - z) (f φ)(z) + (R φ(x) - R φ(z)) g(x - z)`, `d = c + b · ∇φ / φ`.
`SolvesAlongPaths.congr` moves the base point of `d` from `x` to `z`. -/
theorem IsTangentLipschitzField.solvesAlongPaths_weightedDifference {ι : Type*} [Fintype ι]
    {S : Set ι} {b : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {t₀ T : ℝ} {K : ℝ≥0}
    (hb : IsTangentLipschitzField S b t₀ T K) {f c R : EuclideanSpace ℝ ι → ℝ → ℝ}
    {f' : EuclideanSpace ℝ ι → ℝ → EuclideanSpace ℝ ι × ℝ →L[ℝ] ℝ}
    {φ g : EuclideanSpace ℝ ι → ℝ} {φ' : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] ℝ}
    {r : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → ℝ}
    (hfcont : ContinuousOn (Function.uncurry f) (openOrthant S ×ˢ Icc t₀ T))
    (hf : ∀ t ∈ Ico t₀ T, ∀ p ∈ openOrthant S,
      HasFDerivWithinAt (Function.uncurry f) (f' p t) (openOrthant S ×ˢ Ici t) (p, t))
    (heq : ∀ t ∈ Ico t₀ T, ∀ p ∈ openOrthant S, f' p t (b t p, 1) = c p t * f p t + R p t)
    (hφ : ∀ p ∈ openOrthant S, HasFDerivAt φ (φ' p) p) (hφ0 : ∀ p ∈ openOrthant S, φ p ≠ 0)
    (hgcont : ContinuousOn g {h | h ≠ 0})
    (hg : ∀ (h : ℝ → EuclideanSpace ℝ ι) (δ : EuclideanSpace ℝ ι) (s : ℝ), HasDerivAt h δ s →
      h s ≠ 0 → HasDerivWithinAt (fun s ↦ g (h s)) (r (h s) δ * g (h s)) (Ici s) s) :
    SolvesAlongPaths
      {q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι | q.1 ∈ openOrthant S ∧ q.2 ∈ openOrthant S ∧
        q.1 ≠ q.2}
      (fun q t ↦ -(c q.1 t + φ' q.1 (b t q.1) / φ q.1 + r (q.1 - q.2) (b t q.1 - b t q.2)))
      (fun q t ↦ (c q.1 t + φ' q.1 (b t q.1) / φ q.1 - (c q.2 t + φ' q.2 (b t q.2) / φ q.2)) *
          g (q.1 - q.2) * (f q.2 t * φ q.2) + (R q.1 t * φ q.1 - R q.2 t * φ q.2) * g (q.1 - q.2))
      (fun q t ↦ (f q.1 t * φ q.1 - f q.2 t * φ q.2) * g (q.1 - q.2)) t₀ T := by
  intro t ht q hq
  obtain ⟨hx, hz, hxz⟩ := hq
  obtain ⟨γ, hγt, hγ, hγx, hγz, hγne⟩ := hb.exists_backward_pair_characteristic ht
    (openOrthant_subset_closedOrthant hx) (openOrthant_subset_closedOrthant hz)
  have hX (s : ℝ) (hs : s ∈ Icc t₀ t) : (γ s).1 ∈ openOrthant S := hγx hx s hs
  have hZ (s : ℝ) (hs : s ∈ Icc t₀ t) : (γ s).2 ∈ openOrthant S := hγz hz s hs
  have hne (s : ℝ) (hs : s ∈ Icc t₀ t) : (γ s).1 - (γ s).2 ≠ 0 := sub_ne_zero.mpr (hγne hxz s hs)
  have hsub : Icc t₀ t ⊆ Icc t₀ T := Icc_subset_Icc_right ht.2
  have hXd (s : ℝ) (hs : s ∈ Icc t₀ t) : HasDerivAt (fun s ↦ (γ s).1) (b s (γ s).1) s :=
    (hγ s hs).2.2.fst
  have hZd (s : ℝ) (hs : s ∈ Icc t₀ t) : HasDerivAt (fun s ↦ (γ s).2) (b s (γ s).2) s :=
    (hγ s hs).2.2.snd
  refine ⟨γ, hγt.symm ▸ rfl, fun s hs ↦ ⟨hX s hs, hZ s hs, sub_ne_zero.mp (hne s hs)⟩, ?_, ?_⟩
  · have hγc : ContinuousOn γ (Icc t₀ t) := fun s hs ↦ (hγ s hs).2.2.continuousAt.continuousWithinAt
    have hfX : ContinuousOn (fun s ↦ f (γ s).1 s) (Icc t₀ t) :=
      hfcont.comp (hγc.fst.prodMk continuousOn_id) fun s hs ↦ ⟨hX s hs, hsub hs⟩
    have hfZ : ContinuousOn (fun s ↦ f (γ s).2 s) (Icc t₀ t) :=
      hfcont.comp (hγc.snd.prodMk continuousOn_id) fun s hs ↦ ⟨hZ s hs, hsub hs⟩
    have hφX : ContinuousOn (fun s ↦ φ (γ s).1) (Icc t₀ t) := fun s hs ↦
      ((hφ _ (hX s hs)).continuousAt.comp (f := fun s ↦ (γ s).1)
        (hXd s hs).continuousAt).continuousWithinAt
    have hφZ : ContinuousOn (fun s ↦ φ (γ s).2) (Icc t₀ t) := fun s hs ↦
      ((hφ _ (hZ s hs)).continuousAt.comp (f := fun s ↦ (γ s).2)
        (hZd s hs).continuousAt).continuousWithinAt
    have hgc : ContinuousOn (fun s ↦ g ((γ s).1 - (γ s).2)) (Icc t₀ t) :=
      hgcont.comp (hγc.fst.sub hγc.snd) fun s hs ↦ hne s hs
    exact ((hfX.mul hφX).sub (hfZ.mul hφZ)).mul hgc
  · intro s hs
    have hsI : s ∈ Icc t₀ t := Ico_subset_Icc_self hs
    have hsT : s ∈ Ico t₀ T := ⟨hs.1, hs.2.trans_le ht.2⟩
    have hu := hasDerivWithinAt_comp_path (hf s hsT _ (hX s hsI)) (hXd s hsI)
      (fun u hu ↦ hX u ⟨hsI.1.trans hu.1, hu.2⟩) le_rfl hs.2
    have hw := hasDerivWithinAt_comp_path (hf s hsT _ (hZ s hsI)) (hZd s hsI)
      (fun u hu ↦ hZ u ⟨hsI.1.trans hu.1, hu.2⟩) le_rfl hs.2
    rw [heq s hsT _ (hX s hsI)] at hu
    rw [heq s hsT _ (hZ s hsI)] at hw
    have hφx : HasDerivWithinAt (fun s ↦ φ (γ s).1) (φ' (γ s).1 (b s (γ s).1)) (Ici s) s :=
      (HasFDerivAt.comp_hasDerivAt s (hφ _ (hX s hsI)) (hXd s hsI)).hasDerivWithinAt
    have hφz : HasDerivWithinAt (fun s ↦ φ (γ s).2) (φ' (γ s).2 (b s (γ s).2)) (Ici s) s :=
      (HasFDerivAt.comp_hasDerivAt s (hφ _ (hZ s hsI)) (hZd s hsI)).hasDerivWithinAt
    have hG := hg (fun s ↦ (γ s).1 - (γ s).2) _ s ((hXd s hsI).sub (hZd s hsI)) (hne s hsI)
    have h := hasDerivWithinAt_weightedDifference hu hw hφx hφz hG (hφ0 _ (hX s hsI))
      (hφ0 _ (hZ s hsI))
    convert h using 1
    ring

end PDE.Hyperbolic.Transport
