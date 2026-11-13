/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Curves defined by a moving direction

For a `C¹` vector field `r` near `x₀`, the equation
`x - x₀ = s • r x` defines a local `C¹` curve through `x₀`. At `s = 0`,
the derivative in `x` of the residual is the identity, regardless of `Dr x₀`.
The implicit-function theorem therefore applies without an invertibility
assumption on the vector field.

The tangent is `r x₀`. This is an implicit curve, not an integral curve:
its displacement is parallel to the vector field at its endpoint.

The parameterized version constructs this curve jointly in strength and base
point, with its full derivative along zero strength. A scalar parameter with
nonzero derivative also has a joint local inverse, retaining the other
parameters. Both constructions use Mathlib's implicit-function theorem.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter
open scoped ContDiff Topology

/-- Construct the local solution of `x - x₀ = s • r x` in a real Banach space.
The tangent and local uniqueness follow from the implicit equation.
No nonvanishing or normalization assumption on `r` is needed here. -/
theorem exists_implicit_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : E → E} {x₀ : E} (hr : ContDiffAt ℝ 1 r x₀) :
    ∃ S : ℝ → E,
      S 0 = x₀ ∧ ContDiffAt ℝ 1 S 0 ∧ HasDerivAt S (r x₀) 0 ∧
      (∀ᶠ s in 𝓝 0, S s - x₀ = s • r (S s)) ∧
      (∀ᶠ z : ℝ × E in 𝓝 (0, x₀),
        z.2 - x₀ = z.1 • r z.2 ↔ S z.1 = z.2) := by
  let G : ℝ × E → E := fun z ↦ z.2 - x₀ - z.1 • r z.2
  have hG : ContDiffAt ℝ 1 G (0, x₀) :=
    (contDiffAt_snd.sub contDiffAt_const).sub
      (contDiffAt_fst.smul (hr.comp (0, x₀) contDiffAt_snd))
  have hbase : G (0, x₀) = 0 := by simp [G]
  have hpartial :
      (fderiv ℝ G (0, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
        ContinuousLinearMap.id ℝ E := by
    have hd : HasFDerivAt (fun x ↦ G (0, x)) (ContinuousLinearMap.id ℝ E) x₀ := by
      simpa only [G, id, zero_smul, sub_zero] using (hasFDerivAt_id x₀).sub_const x₀
    exact ((hG.differentiableAt one_ne_zero).hasFDerivAt.comp x₀
      (hasFDerivAt_prodMk_right (0 : ℝ) x₀)).unique hd
  have hinv : ((fderiv ℝ G (0, x₀)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.id ℝ E) (by ext x; rfl) (by ext x; rfl)
  let S : ℝ → E := hG.implicitFunction one_ne_zero hinv
  have hS0 : S 0 = x₀ := hG.implicitFunction_apply_self one_ne_zero hinv
  have hS : ContDiffAt ℝ 1 S 0 := hG.contDiffAt_implicitFunction one_ne_zero hinv
  have heq : ∀ᶠ s in 𝓝 0, S s - x₀ = s • r (S s) := by
    filter_upwards [hG.eventually_apply_implicitFunction one_ne_zero hinv] with s hs
    change G (s, S s) = G (0, x₀) at hs
    rw [hbase] at hs
    simpa only [G, sub_eq_zero] using hs
  have hrS : DifferentiableAt ℝ (fun s ↦ r (S s)) 0 := by
    have hr' : DifferentiableAt ℝ r (S 0) := by
      simpa only [hS0] using hr.differentiableAt one_ne_zero
    exact hr'.comp 0 (hS.differentiableAt one_ne_zero)
  have htangent : HasDerivAt (fun s ↦ x₀ + s • r (S s)) (r x₀) 0 := by
    simpa only [Pi.add_def, Pi.smul_def', id, zero_smul, one_smul, zero_add, hS0] using
      (hasDerivAt_const 0 x₀).add ((hasDerivAt_id 0).smul hrS.hasDerivAt)
  refine ⟨S, hS0, hS, htangent.congr_of_eventuallyEq ?_, heq, ?_⟩
  · filter_upwards [heq] with s hs
    exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  · filter_upwards [hG.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv] with z hz
    change G z = G (0, x₀) ↔ S z.1 = z.2 at hz
    rw [hbase] at hz
    simpa only [G, sub_eq_zero] using hz

/-- Solve the implicit ray equation jointly in strength and base point.
Along zero strength, the full derivative sends `(a, h)` to `h + a • r (x, x)`.
The identity and this derivative hold on one neighborhood of the base point. -/
theorem exists_implicit_ray_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r : E × E → E} {x₀ : E} (hr : ContDiffAt ℝ 1 r (x₀, x₀)) :
    ∃ S : ℝ × E → E,
      S (0, x₀) = x₀ ∧ ContDiffAt ℝ 1 S (0, x₀) ∧
      (∀ᶠ x in 𝓝 x₀, S (0, x) = x ∧
        HasFDerivAt S
          (ContinuousLinearMap.snd ℝ ℝ E +
            (ContinuousLinearMap.fst ℝ ℝ E).smulRight (r (x, x))) (0, x)) ∧
      (∀ᶠ p in 𝓝 (0, x₀), S p - p.2 = p.1 • r (p.2, S p)) ∧
      (∀ᶠ z : (ℝ × E) × E in 𝓝 ((0, x₀), x₀),
        z.2 - z.1.2 = z.1.1 • r (z.1.2, z.2) ↔ S z.1 = z.2) := by
  let G : (ℝ × E) × E → E := fun z ↦ z.2 - z.1.2 - z.1.1 • r (z.1.2, z.2)
  have hG : ContDiffAt ℝ 1 G ((0, x₀), x₀) :=
    (contDiffAt_snd.sub contDiffAt_fst.snd).sub
      (contDiffAt_fst.fst.smul
        (hr.comp ((0, x₀), x₀) (contDiffAt_fst.snd.prodMk contDiffAt_snd)))
  have hbase : G ((0, x₀), x₀) = 0 := by simp [G]
  have hpartial :
      (fderiv ℝ G ((0, x₀), x₀)).comp (ContinuousLinearMap.inr ℝ (ℝ × E) E) =
        ContinuousLinearMap.id ℝ E := by
    have hd : HasFDerivAt (fun x ↦ G ((0, x₀), x))
        (ContinuousLinearMap.id ℝ E) x₀ := by
      simpa only [G, id, zero_smul, sub_zero] using (hasFDerivAt_id x₀).sub_const x₀
    exact ((hG.differentiableAt one_ne_zero).hasFDerivAt.comp x₀
      (hasFDerivAt_prodMk_right (0, x₀) x₀)).unique hd
  have hinv : ((fderiv ℝ G ((0, x₀), x₀)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) E)).IsInvertible := by
    rw [hpartial]
    exact ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.id ℝ E) (by ext x; rfl) (by ext x; rfl)
  let S : ℝ × E → E := hG.implicitFunction one_ne_zero hinv
  have hS0 : S (0, x₀) = x₀ := hG.implicitFunction_apply_self one_ne_zero hinv
  have hS : ContDiffAt ℝ 1 S (0, x₀) :=
    hG.contDiffAt_implicitFunction one_ne_zero hinv
  have heq : ∀ᶠ p in 𝓝 (0, x₀), S p - p.2 = p.1 • r (p.2, S p) := by
    filter_upwards [hG.eventually_apply_implicitFunction one_ne_zero hinv] with p hp
    change G (p, S p) = G ((0, x₀), x₀) at hp
    rw [hbase] at hp
    simpa only [G, sub_eq_zero] using hp
  have hiff : ∀ᶠ z : (ℝ × E) × E in 𝓝 ((0, x₀), x₀),
      z.2 - z.1.2 = z.1.1 • r (z.1.2, z.2) ↔ S z.1 = z.2 := by
    filter_upwards [hG.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv] with z hz
    change G z = G ((0, x₀), x₀) ↔ S z.1 = z.2 at hz
    rw [hbase] at hz
    simpa only [G, sub_eq_zero] using hz
  have hzero : ∀ᶠ x in 𝓝 x₀, S (0, x) = x := by
    have ht : Tendsto (fun x : E ↦ (((0 : ℝ), x), x)) (𝓝 x₀) (𝓝 ((0, x₀), x₀)) :=
      (continuousAt_const.prodMk continuousAt_id).prodMk continuousAt_id
    filter_upwards [ht.eventually hiff] with x hx
    exact hx.mp (by simp)
  have hparam : Tendsto (fun x : E ↦ ((0 : ℝ), x)) (𝓝 x₀) (𝓝 (0, x₀)) :=
    continuousAt_const.prodMk continuousAt_id
  have hdiag : Tendsto (fun x : E ↦ (x, x)) (𝓝 x₀) (𝓝 (x₀, x₀)) :=
    continuousAt_id.prodMk continuousAt_id
  refine ⟨S, hS0, hS, ?_, heq, hiff⟩
  filter_upwards [hzero, hparam.eventually (hS.eventually (by simp)),
    hdiag.eventually (hr.eventually (by simp)), hparam.eventually heq.eventually_nhds]
    with x hx hSx hrx heqx
  have hrS : DifferentiableAt ℝ (fun p : ℝ × E ↦ r (p.2, S p)) (0, x) := by
    have hr' : DifferentiableAt ℝ r (x, S (0, x)) := by
      simpa only [hx] using hrx.differentiableAt one_ne_zero
    exact hr'.comp (0, x)
      (differentiableAt_snd.prodMk (hSx.differentiableAt one_ne_zero))
  have hd :
      HasFDerivAt (fun p : ℝ × E ↦ p.2 + p.1 • r (p.2, S p))
        (ContinuousLinearMap.snd ℝ ℝ E +
          (ContinuousLinearMap.fst ℝ ℝ E).smulRight (r (x, x))) (0, x) := by
    simpa only [Pi.add_def, Pi.smul_def', zero_smul, zero_add, hx] using
      hasFDerivAt_snd.add (hasFDerivAt_fst.smul hrS.hasFDerivAt)
  refine ⟨hx, hd.congr_of_eventuallyEq ?_⟩
  filter_upwards [heqx] with p hp
  exact (sub_eq_iff_eq_add.mp hp).trans (add_comm _ _)

/-- Invert the real variable of a jointly `C¹` scalar function while retaining
its Banach-space parameter. Both inverse identities hold on full product
neighborhoods. These are actual local identities, not properties of an
unrestricted choice of preimages. -/
theorem exists_implicit_inverse_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : ℝ × E → ℝ} {q₀ : E} {a : ℝ}
    (hf : ContDiffAt ℝ 1 f (0, q₀))
    (hd : HasDerivAt (fun s ↦ f (s, q₀)) a 0) (ha : a ≠ 0) :
    ∃ inverse : ℝ × E → ℝ,
      inverse (f (0, q₀), q₀) = 0 ∧
      ContDiffAt ℝ 1 inverse (f (0, q₀), q₀) ∧
      (∀ᶠ p in 𝓝 (f (0, q₀), q₀), f (inverse p, p.2) = p.1) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), q₀), inverse (f p, p.2) = p.1) := by
  let G : (ℝ × E) × ℝ → ℝ := fun z ↦ f (z.2, z.1.2) - z.1.1
  have hG : ContDiffAt ℝ 1 G ((f (0, q₀), q₀), 0) :=
    (hf.comp ((f (0, q₀), q₀), 0)
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)).sub contDiffAt_fst.fst
  have hbase : G ((f (0, q₀), q₀), 0) = 0 := sub_self _
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a ha)
  have hpartial :
      (fderiv ℝ G ((f (0, q₀), q₀), 0)).comp
        (ContinuousLinearMap.inr ℝ (ℝ × E) ℝ) = (e : ℝ →L[ℝ] ℝ) := by
    have hds : HasFDerivAt (fun s ↦ G ((f (0, q₀), q₀), s))
        (e : ℝ →L[ℝ] ℝ) 0 :=
      (hd.sub_const (f (0, q₀))).hasFDerivAt_equiv ha
    exact (hG.differentiableAt_one.hasFDerivAt.comp 0
      (hasFDerivAt_prodMk_right (f (0, q₀), q₀) (0 : ℝ))).unique hds
  have hinv : ((fderiv ℝ G ((f (0, q₀), q₀), 0)).comp
      (ContinuousLinearMap.inr ℝ (ℝ × E) ℝ)).IsInvertible := ⟨e, hpartial.symm⟩
  let inverse : ℝ × E → ℝ := hG.implicitFunction one_ne_zero hinv
  have hi : ContDiffAt ℝ 1 inverse (f (0, q₀), q₀) :=
    hG.contDiffAt_implicitFunction one_ne_zero hinv
  refine ⟨inverse, hG.implicitFunction_apply_self one_ne_zero hinv, hi, ?_, ?_⟩
  · filter_upwards [hG.eventually_apply_implicitFunction one_ne_zero hinv] with p hp
    change G (p, inverse p) = G ((f (0, q₀), q₀), 0) at hp
    rw [hbase] at hp
    exact sub_eq_zero.mp hp
  · have ht : Tendsto (fun p : ℝ × E ↦ ((f p, p.2), p.1))
        (𝓝 (0, q₀)) (𝓝 ((f (0, q₀), q₀), 0)) :=
      (hf.continuousAt.prodMk continuousAt_snd).prodMk continuousAt_fst
    filter_upwards [ht.eventually
      (hG.eventually_apply_eq_iff_implicitFunction one_ne_zero hinv)] with p hp
    change G ((f p, p.2), p.1) = G ((f (0, q₀), q₀), 0) ↔
      inverse (f p, p.2) = p.1 at hp
    exact hp.mp (by simp only [G, sub_self])

end PDE.Analysis
