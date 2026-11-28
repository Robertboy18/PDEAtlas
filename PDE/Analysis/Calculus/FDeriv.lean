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

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import PDE.FDeriv.Calculus.Symmetric

set_option linter.style.header false

/-!
# Fréchet derivatives and partial derivatives

The lemmas compute `fderiv` of products, compositions and coordinate functions, evaluate a
derivative in a direction, and state differentiability of such expressions. The proofs combine the
rules of Mathlib (`HasFDerivAt.comp`, `fderiv_fun_mul`) and evaluate the result with `simp`.

## Main results

* `PDE.Analysis.differentiable_of_smooth`: A `C^∞` map `f : E → F` between real normed spaces is
  differentiable.
* `PDE.Analysis.continuous_fderiv_comp_prodMk_right`: If `f : ℝ × E → F` is `C^1`, where `E` and `F`
  are real normed spaces, then the derivative in the second variable,
  `z ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2`, is continuous on `ℝ × E`.
* `PDE.Analysis.differentiableAt_comp_fst`: If `g : ℝ → E`, with `E` a real normed space, is
  differentiable at `t`, then `z ↦ g z.1` on `ℝ × ℝ` is differentiable at `(t, x)` for every real
  `x`.
* `PDE.Analysis.differentiableAt_comp_snd`: If `g : ℝ → E`, with `E` a real normed space, is
  differentiable at `x`, then `z ↦ g z.2` on `ℝ × ℝ` is differentiable at `(t, x)` for every real
  `t`.
* `PDE.Analysis.differentiableAt_partial_deriv_of_contDiffAt`: If `F : ℝ → ℝ → ℂ` is `C^2` at
  `(t, x)` as a function on `ℝ × ℝ`, then both partial derivatives,
  `z ↦ deriv (fun t' => F t' z.2) z.1` and `z ↦ deriv (fun x' ↦ F z.1 x') z.2`, are differentiable
  at `(t, x)` as functions on `ℝ × ℝ`. Near `(t, x)` they are the values of the Fréchet derivative
  on the basis vectors `(1, 0)` and `(0, 1)`, and the Fréchet derivative is differentiable at
  `(t, x)`.
* `PDE.Analysis.exists_lipschitzOnWith_fderiv_closedBall`: If `g : ℝ × ℝ → F`, with `F` a real
  normed space, is `C^2`, then `g` is `C^1` and there is `L : ℝ≥0` such that `fderiv ℝ g` is
  `L`-Lipschitz on the closed unit ball `Metric.closedBall 0 1`.
* `PDE.Analysis.fderiv_apply_eq_zero_of_notMem_tsupport`: If `p` is outside the topological support
  of `ψ : ℝ × ℝ → ℝ`, then `fderiv ℝ ψ p u = 0` for every `u : ℝ × ℝ`.
* `PDE.Analysis.fderiv_fst_mul_apply`: If `ψ : ℝ × ℝ → ℝ` is smooth, then for all `p u : ℝ × ℝ`,
  `fderiv ℝ (fun p ↦ p.1 * ψ p) p u = u.1 * ψ p + p.1 * fderiv ℝ ψ p u`.

There are 19 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace PDE.Analysis

/-- If `g : ℝ → E`, with `E` a real normed space, is differentiable at `t`, then `z ↦ g z.1` on
`ℝ × ℝ` is differentiable at `(t, x)` for every real `x`. -/
theorem differentiableAt_comp_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    {t x : ℝ}
    (hg : DifferentiableAt ℝ g t) : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ g z.1) (t, x) :=
  hg.comp (t, x) differentiableAt_fst

/-- If `g : ℝ → E`, with `E` a real normed space, is differentiable at `x`, then `z ↦ g z.2` on
`ℝ × ℝ` is differentiable at `(t, x)` for every real `t`. -/
theorem differentiableAt_comp_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : ℝ → E}
    {t x : ℝ}
    (hg : DifferentiableAt ℝ g x) : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ g z.2) (t, x) :=
  hg.comp (t, x) differentiableAt_snd

/-- If `F : ℝ → ℝ → ℂ` is `C^2` at `(t, x)` as a function on `ℝ × ℝ`, then both partial derivatives,
`z ↦ deriv (fun t' ↦ F t' z.2) z.1` and `z ↦ deriv (fun x' ↦ F z.1 x') z.2`, are differentiable at
`(t, x)` as functions on `ℝ × ℝ`. Near `(t, x)` they are the values of the Fréchet derivative on the
basis vectors `(1, 0)` and `(0, 1)`, and the Fréchet derivative is differentiable at `(t, x)`. -/
theorem differentiableAt_partial_deriv_of_contDiffAt {F : ℝ → ℝ → ℂ} {t x : ℝ}
    (hF : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (t, x)) :
    DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ deriv (fun t' ↦ F t' z.2) z.1) (t, x) ∧
      DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ deriv (fun x' ↦ F z.1 x') z.2) (t, x) := by
  set G : ℝ × ℝ → ℂ := fun z ↦ F z.1 z.2 with hGdef
  have hev : ∀ᶠ w in nhds ((t, x) : ℝ × ℝ), DifferentiableAt ℝ G w :=
    (hF.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by norm_num)
  have hDD : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have pX : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun x' ↦ F w.1 x') w.2 = fderiv ℝ G w ((0 : ℝ), (1 : ℝ)) := fun w hw ↦ by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.2 ((hasDerivAt_const w.2 w.1).prodMk
        (hasDerivAt_id w.2))).deriv
    exact h
  have pT : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun t' ↦ F t' w.2) w.1 = fderiv ℝ G w ((1 : ℝ), (0 : ℝ)) := fun w hw ↦ by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.1 ((hasDerivAt_id w.1).prodMk
        (hasDerivAt_const w.1 w.2))).deriv
    exact h
  refine ⟨?_, ?_⟩
  · have hd : DifferentiableAt ℝ (fun w ↦ fderiv ℝ G w ((1 : ℝ), (0 : ℝ))) (t, x) :=
      hDD.clm_apply (differentiableAt_const _)
    exact hd.congr_of_eventuallyEq (hev.mono fun w hw ↦ pT w hw)
  · have hd : DifferentiableAt ℝ (fun w ↦ fderiv ℝ G w ((0 : ℝ), (1 : ℝ))) (t, x) :=
      hDD.clm_apply (differentiableAt_const _)
    exact hd.congr_of_eventuallyEq (hev.mono fun w hw ↦ pX w hw)

/-- A `C^∞` map `f : E → F` between real normed spaces is differentiable. -/
theorem differentiable_of_smooth {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (h : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  (contDiff_infty.1 h 1).differentiable (by norm_num)

/-- If `g : ℝ × ℝ → F`, with `F` a real normed space, is `C^2`, then `g` is `C^1` and there is
`L : ℝ≥0` such that `fderiv ℝ g` is `L`-Lipschitz on the closed unit ball `Metric.closedBall 0 1`.
-/
theorem exists_lipschitzOnWith_fderiv_closedBall {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : ℝ × ℝ → F} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 1 g ∧ ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ g) (Metric.closedBall 0 1) :=
  ⟨hg.of_le (by
    norm_num), ((hg.fderiv_right (m := 1) (by
      norm_num)).locallyLipschitz.locallyLipschitzOn).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 1)⟩

/-- If `p` is outside the topological support of `ψ : ℝ × ℝ → ℝ`, then `fderiv ℝ ψ p u = 0` for
every `u : ℝ × ℝ`. -/
theorem fderiv_apply_eq_zero_of_notMem_tsupport {ψ : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hp : p ∉ tsupport ψ)
    (u : ℝ × ℝ) : fderiv ℝ ψ p u = 0 := by
  rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hp (tsupport_fderiv_subset ℝ h))]
  rfl

/-- If `f : ℝ × ℝ → ℝ` is differentiable at `x` and `t ↦ f (t, x.2)` has derivative `d` at `x.1`,
then `fderiv ℝ f x (1, 0) = d`. -/
theorem fderiv_apply_one_zero_eq_of_hasDerivAt {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) {d : ℝ}
    (hd : HasDerivAt (fun t ↦ f (t, x.2)) d x.1) : fderiv ℝ f x (1, 0) = d := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (t, x.2)) ((1 : ℝ), (0 : ℝ)) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ (t, x.2)) x.1 h1).unique hd

/-- If `f : ℝ × ℝ → ℝ` is differentiable at `x` and `t ↦ f (x.1, t)` has derivative `d` at `x.2`,
then `fderiv ℝ f x (0, 1) = d`. -/
theorem fderiv_apply_zero_one_eq_of_hasDerivAt {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ}
    (hf : DifferentiableAt ℝ f x) {d : ℝ}
    (hd : HasDerivAt (fun t ↦ f (x.1, t)) d x.2) : fderiv ℝ f x (0, 1) = d := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (x.1, t)) ((0 : ℝ), (1 : ℝ)) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ (x.1, t)) x.2 h1).unique hd

/-- If `ψ : ℝ × ℝ → ℝ` is smooth, then for all `p u : ℝ × ℝ`,
`fderiv ℝ (fun p ↦ p.1 * ψ p) p u = u.1 * ψ p + p.1 * fderiv ℝ ψ p u`. -/
theorem fderiv_fst_mul_apply {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ ↦ p.1 * ψ p) p u = u.1 * ψ p + p.1 * fderiv ℝ ψ p u := by
  have hd : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)).differentiableAt
  rw [fderiv_fun_mul differentiableAt_fst hd]
  simp [fderiv_fst]
  ring

/-- Let `F : ℝ → ℂ` be differentiable at `p.1` and `c : ℝ → ℝ` be differentiable at `p.2`, and put
`G q = F q.1 * (c q.2 : ℂ)` on `ℝ × ℝ`. Then `fderiv ℝ G p (1, 0) = deriv F p.1 * (c p.2 : ℂ)` and
`fderiv ℝ G p (0, 1) = F p.1 * (deriv c p.2 : ℂ)`. This is the product rule for `q ↦ F q.1` and
`q ↦ (c q.2 : ℂ)`, evaluated at the two basis vectors. -/
theorem fderiv_fst_mul_ofReal_snd_apply {F : ℝ → ℂ} {c : ℝ → ℝ} {p : ℝ × ℝ}
    (hF : DifferentiableAt ℝ F p.1)
    (hc : DifferentiableAt ℝ c p.2) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ F q.1 * (c q.2 : ℂ)) p (1, 0) = deriv F p.1 * (c p.2 : ℂ) ∧
    fderiv ℝ (fun q : ℝ × ℝ ↦ F q.1 * (c q.2 : ℂ)) p (0, 1) = F p.1 * ((deriv c p.2 : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ ↦ F q.1) ((fderiv ℝ F p.1).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    hF.hasFDerivAt.comp p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : ℝ × ℝ ↦ (c q.2 : ℂ))
      (Complex.ofRealCLM.comp ((fderiv ℝ c p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ))) p :=
    Complex.ofRealCLM.hasFDerivAt.comp p (hc.hasFDerivAt.comp p hasFDerivAt_snd)
  have h3 := HasFDerivAt.fderiv (f := fun q : ℝ × ℝ ↦ F q.1 * (c q.2 : ℂ)) (h1.mul h2)
  constructor
  · rw [h3]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero,
          zero_add]
    rw [mul_comm]
    rfl
  · rw [h3]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero,
          add_zero]
    rfl

/-- If `α β : ℝ → ℝ` are differentiable, then for every `p : ℝ × ℝ`,
`fderiv ℝ (fun q ↦ α q.1 * β q.2) p (0, 1) = α p.1 * deriv β p.2`. The function is restricted to
the line `t ↦ (p.1, t)`, where its derivative is that of `t ↦ α p.1 * β t`. -/
theorem fderiv_fst_mul_snd_apply_zero_one {α β : ℝ → ℝ} (hα : Differentiable ℝ α)
    (hβ : Differentiable ℝ β) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) p (0, 1) = α p.1 * deriv β p.2 := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) (p.1, p.2) :=
    ((hα _).comp _ differentiableAt_fst).mul ((hβ _).comp _ differentiableAt_snd)
  have hc : HasDerivAt (fun t : ℝ ↦ (p.1, t)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasDerivAt ((fun q : ℝ × ℝ ↦ α q.1 * β q.2) ∘ fun t : ℝ ↦ (p.1, t))
      (fderiv ℝ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) (p.1, p.2) (0, 1)) p.2 :=
    hd.hasFDerivAt.comp_hasDerivAt p.2 hc
  exact h2.unique ((hβ p.2).hasDerivAt.const_mul (α p.1))

/-- If `g : ℝ × ℝ → ℝ` is differentiable, then for every `x : ℝ × ℝ` the function `t ↦ g (t, x.2)`
has derivative `fderiv ℝ g x (1, 0)` at `x.1`. -/
theorem hasDerivAt_comp_prodMk_left_fderiv {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    HasDerivAt (fun t ↦ g (t, x.2)) (fderiv ℝ g x (1, 0)) x.1 :=
  (hg x).hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ (t, x.2)) x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))

/-- If `F : ℝ × ℝ → ℂ` has Fréchet derivative `F'` at `(t, x)`, then `t' ↦ F (t', x)` has derivative
`F' (1, 0)` at `t`. -/
theorem hasDerivAt_comp_prodMk_left_of_hasFDerivAt {F : ℝ × ℝ → ℂ} {F' : ℝ × ℝ →L[ℝ] ℂ} {t x : ℝ}
    (h : HasFDerivAt F F' (t, x)) :
    HasDerivAt (fun t' ↦ F (t', x)) (F' (1, 0)) t := by
  have hl : HasDerivAt (fun t' : ℝ ↦ (t', x)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact h.comp_hasDerivAt t hl

/-- If `g : ℝ × ℝ → ℝ` is differentiable, then for every `x : ℝ × ℝ` the function `t ↦ g (x.1, t)`
has derivative `fderiv ℝ g x (0, 1)` at `x.2`. -/
theorem hasDerivAt_comp_prodMk_right_fderiv {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    HasDerivAt (fun t ↦ g (x.1, t)) (fderiv ℝ g x (0, 1)) x.2 :=
  (hg x).hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ (x.1, t)) x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))

/-- If `F : ℝ × ℝ → ℂ` has Fréchet derivative `F'` at `(t, x)`, then `x' ↦ F (t, x')` has derivative
`F' (0, 1)` at `x`. -/
theorem hasDerivAt_comp_prodMk_right_of_hasFDerivAt {F : ℝ × ℝ → ℂ} {F' : ℝ × ℝ →L[ℝ] ℂ} {t x : ℝ}
    (h : HasFDerivAt F F' (t, x)) :
    HasDerivAt (fun x' ↦ F (t, x')) (F' (0, 1)) x := by
  have hl : HasDerivAt (fun x' : ℝ ↦ (t, x')) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  exact h.comp_hasDerivAt x hl

/-- Symmetry of mixed partial derivatives: if `Φ : ℝ → ℝ → ℂ` is `C^2` at `(t, x)` as a function on
`ℝ × ℝ`, then `x' ↦ deriv (fun t' ↦ Φ t' x') t` has derivative
`deriv (fun t' ↦ deriv (fun x' ↦ Φ t' x') x) t` at `x`, and `x' ↦ Φ t x'` is differentiable at
`x`. Both partial derivatives are written as values of the Fréchet derivative on the basis vectors,
and the symmetry of the second derivative is used. -/
theorem hasDerivAt_deriv_comm_of_contDiffAt {Φ : ℝ → ℝ → ℂ} {t x : ℝ}
    (hΦ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Φ z.1 z.2) (t, x)) :
    HasDerivAt (fun x' ↦ deriv (fun t' ↦ Φ t' x') t) (deriv
        (fun t' ↦ deriv (fun x' ↦ Φ t' x') x) t) x ∧
      DifferentiableAt ℝ (fun x' ↦ Φ t x') x := by
  set G : ℝ × ℝ → ℂ := fun z ↦ Φ z.1 z.2 with hGdef
  have hev : ∀ᶠ w in nhds ((t, x) : ℝ × ℝ), DifferentiableAt ℝ G w :=
    (hΦ.eventually (by simp)).mono fun w hw ↦ hw.differentiableAt (by norm_num)
  have hDD : DifferentiableAt ℝ (fderiv ℝ G) (t, x) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsym := hΦ.isSymmSndFDerivAt (by simp)
  have lineX : ∀ a b : ℝ, HasDerivAt (fun x' : ℝ ↦ ((a, x') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) b :=
      fun a b ↦
    (hasDerivAt_const b a).prodMk (hasDerivAt_id b)
  have lineT : ∀ a b : ℝ, HasDerivAt (fun t' : ℝ ↦ ((t', a) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) b :=
      fun a b ↦
    (hasDerivAt_id b).prodMk (hasDerivAt_const b a)
  have pX : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun x' ↦ Φ w.1 x') w.2 = fderiv ℝ G w ((0 : ℝ), (1 : ℝ)) := fun w hw ↦ by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.2 (lineX w.1 w.2)).deriv
    exact h
  have pT : ∀ w : ℝ × ℝ, DifferentiableAt ℝ G w →
      deriv (fun t' ↦ Φ t' w.2) w.1 = fderiv ℝ G w ((1 : ℝ), (0 : ℝ)) := fun w hw ↦ by
    have h := (hw.hasFDerivAt.comp_hasDerivAt w.1 (lineT w.2 w.1)).deriv
    exact h
  have e1 : (fun t' ↦ deriv (fun x' ↦ Φ t' x') x) =ᶠ[nhds t]
      fun t' ↦ fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)) :=
    ((lineT x t).continuousAt.tendsto.eventually hev).mono fun t' h ↦ pX (t', x) h
  have e2 : (fun x' ↦ deriv (fun t' ↦ Φ t' x') t) =ᶠ[nhds x]
      fun x' ↦ fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)) :=
    ((lineX t x).continuousAt.tendsto.eventually hev).mono fun x' h ↦ pT (t, x') h
  have d1 : HasDerivAt (fun t' ↦ fderiv ℝ G (t', x) ((0 : ℝ), (1 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) t := by
    have := (hDD.hasFDerivAt.comp_hasDerivAt t (lineT x t))
    exact this.clm_apply (hasDerivAt_const t ((0 : ℝ), (1 : ℝ))) |>.congr_deriv (by simp)
  have d2 : HasDerivAt (fun x' ↦ fderiv ℝ G (t, x') ((1 : ℝ), (0 : ℝ)))
      (fderiv ℝ (fderiv ℝ G) (t, x) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))) x := by
    have := (hDD.hasFDerivAt.comp_hasDerivAt x (lineX t x))
    exact this.clm_apply (hasDerivAt_const x ((1 : ℝ), (0 : ℝ))) |>.congr_deriv (by simp)
  refine ⟨?_, ?_⟩
  · rw [(d1.congr_of_eventuallyEq e1).deriv, hsym]
    exact d2.congr_of_eventuallyEq e2
  · exact (hev.self_of_nhds).comp x (lineX t x).differentiableAt

/-- If `f : ℝ × E → F` is `C^1`, where `E` and `F` are real normed spaces, then for every `σ : ℝ`
and `y : E` the slice `x ↦ f (σ, x)` has Fréchet derivative
`(fderiv ℝ f (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)` at `y`. -/
theorem hasFDerivAt_comp_prodMk_right_of_contDiff {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} (hf : ContDiff ℝ 1 f) (σ : ℝ) (y : E) :
    HasFDerivAt (fun x ↦ f (σ, x)) ((fderiv ℝ f (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
  ((hf.differentiable one_ne_zero) (σ, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)

/-- Let `A B : ℝ × ℝ → ℂ` have Fréchet derivatives `A' p` and `B' p` at every `p`, with `A'` and
`B'` continuous, let `π : ℝ × ℝ → ℝ` be continuous, and suppose `A p = B p` and `A' p = B' p`
whenever `π p = c`. Then the glued function `q ↦ if c ≤ π q then B q else A q` has Fréchet
derivative `if c ≤ π p then B' p else A' p` at every `p`, and this derivative is continuous in `p`.
Away from the level set `π p = c` the glued function agrees locally with `A` or `B`, and on it the
difference `A - B` vanishes with zero derivative. -/
theorem hasFDerivAt_ite_and_continuous_of_eq {A B : ℝ × ℝ → ℂ} {A' B' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)}
    (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (c : ℝ) (hA : ∀ p, HasFDerivAt A (A' p) p)
        (hB : ∀ p, HasFDerivAt B (B' p) p)
    (hA' : Continuous A') (hB' : Continuous B')
    (hv : ∀ p, π p = c → A p = B p) (hd : ∀ p, π p = c → A' p = B' p) :
    (∀ p, HasFDerivAt (fun q ↦ if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p) ∧
      Continuous (fun p ↦ if c ≤ π p then B' p else A' p) := by
  refine ⟨fun p ↦ ?_, Continuous.if_le hB' hA' continuous_const hπ fun p hp ↦ (hd p hp.symm).symm⟩
  rcases lt_trichotomy (π p) c with h | h | h
  · rw [ite_eq_right (not_le.2 h)]
    refine (hA p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_lt_nhds h)] with q hq
    rw [ite_eq_right (not_le.2 hq)]
  · rw [ite_eq_left h.ge]
    have hz : HasFDerivAt (fun q ↦ A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      have hs := (hA p).sub (hB p)
      rw [hd p h, sub_self] at hs
      exact hs
    have hk : HasFDerivAt (fun q ↦ if c ≤ π q then (0 : ℂ) else A q - B q)
        (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      rw [hasFDerivAt_iff_isLittleO] at hz ⊢
      refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1
        (Filter.Eventually.of_forall fun q ↦ ?_)) hz
      simp only [ite_eq_left h.ge, zero_apply, sub_zero, hv p h, sub_self, one_mul]
      split_ifs <;> simp
    refine ((hB p).add hk).congr_fderiv (add_zero _) |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun q ↦ ?_)
    simp only [Pi.add_apply]
    split_ifs <;> ring
  · rw [ite_eq_left h.le]
    refine (hB p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_gt_nhds h)] with q hq
    rw [ite_eq_left hq.le]

/-- Let `A B : ℝ × ℝ → ℂ` have Fréchet derivatives `A' p` and `B' p` at every `p`, let
`π : ℝ × ℝ → ℝ` be continuous, and suppose `B p = A p` and `B' p = A' p` whenever `c = π p`. Then
the glued function `q ↦ if c ≤ π q then B q else A q` has Fréchet derivative
`if c ≤ π p then B' p else A' p` at every `p`. Away from the level set `π p = c` the glued function
agrees locally with `A` or `B`, and on it the difference `A - B` vanishes with zero derivative. -/
theorem hasFDerivAt_ite_of_eq_of_fderiv_eq {A B : ℝ × ℝ → ℂ} {A' B' : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℂ)}
    (π : ℝ × ℝ → ℝ)
    (hπ : Continuous π) (c : ℝ)
    (hA : ∀ p, HasFDerivAt A (A' p) p) (hB : ∀ p, HasFDerivAt B (B' p) p)
    (h0 : ∀ p, c = π p → B p = A p) (h1 : ∀ p, c = π p → B' p = A' p) (p : ℝ × ℝ) :
    HasFDerivAt (fun q ↦ if c ≤ π q then B q else A q) (if c ≤ π p then B' p else A' p) p := by
  rcases lt_trichotomy (π p) c with h | h | h
  · rw [ite_eq_right (not_le.2 h)]
    refine (hA p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_lt_nhds h)] with q hq
    rw [ite_eq_right (not_le.2 hq)]
  · rw [ite_eq_left h.ge]
    have hd : HasFDerivAt (fun q ↦ A q - B q) (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      have := (hA p).sub (hB p)
      rwa [h1 p h.symm, sub_self] at this
    have hK : HasFDerivAt (fun q ↦ if c ≤ π q then (0 : ℂ) else A q - B q)
        (0 : ℝ × ℝ →L[ℝ] ℂ) p := by
      rw [hasFDerivAt_iff_isLittleO] at hd ⊢
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hd
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun q ↦ ?_)
      have hp0 : A p - B p = 0 := by rw [h0 p h.symm, sub_self]
      simp only [ite_eq_left h.ge, zero_apply, sub_zero, one_mul, hp0]
      split_ifs <;> simp
    have := (hB p).add hK
    rw [add_zero] at this
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ ?_)
    simp only [Pi.add_apply]
    split_ifs <;> ring
  · rw [ite_eq_left h.le]
    refine (hB p).congr_of_eventuallyEq ?_
    filter_upwards [(hπ.tendsto p).eventually (eventually_gt_nhds h)] with q hq
    rw [ite_eq_left hq.le]

/-- If `φ : ℝ × ℝ → ℂ` is `K`-Lipschitz, then `‖fderiv ℝ φ p u‖ ≤ K` for every point `p` and every
vector `u` with `‖u‖ ≤ 1`. -/
theorem norm_fderiv_apply_le_of_lipschitzWith {φ : ℝ × ℝ → ℂ} {K : NNReal} (hφ : LipschitzWith K φ)
    (p u : ℝ × ℝ) (hu : ‖u‖ ≤ 1) :
    ‖fderiv ℝ φ p u‖ ≤ K :=
  ((fderiv ℝ φ p).le_opNorm u).trans (by
    calc ‖fderiv ℝ φ p‖ * ‖u‖ ≤ K * 1 := mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hφ) hu
             (norm_nonneg _) K.2
      _ = K := mul_one _)

/-- If `f : ℝ × E → F` is `C^1`, where `E` and `F` are real normed spaces, then the derivative in
the second variable, `z ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2`, is continuous on `ℝ × E`. -/
theorem continuous_fderiv_comp_prodMk_right {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : ℝ × E ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2) := by
  have h : (fun z : ℝ × E ↦ fderiv ℝ (fun x ↦ f (z.1, x)) z.2) =
      fun z ↦ (fderiv ℝ f z).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    funext z
    exact (hasFDerivAt_comp_prodMk_right_of_contDiff hf z.1 z.2).fderiv
  rw [h]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

/-- Let `Φ : ℝ → ℝ → ℂ` be `C^2` at `(t, x)` as a function on `ℝ × ℝ`, let `c : ℝ → ℂ`, and write
`L Ψ = t * (1 - t) * ∂ₜΨ + c t * Ψ + 2 * Ψ`. Then `L` commutes with `Ψ ↦ -∂ₓΨ` at `(t, x)`: the
value of `L (-∂ₓΦ)` minus the `x`-derivative of `-(L Φ)` is `0`. The proof uses the symmetry of the
mixed partial derivatives of `Φ`. -/
theorem mul_deriv_add_mul_comm_neg_deriv {Φ : ℝ → ℝ → ℂ} (c : ℝ → ℂ) {t x : ℝ}
    (hΦ : ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Φ z.1 z.2) (t, x)) :
    ((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' ↦ -deriv (fun x' ↦ Φ t' x') x) t +
        c t * -deriv (fun x' ↦ Φ t x') x + 2 * -deriv (fun x' ↦ Φ t x') x -
      deriv (fun x' ↦ -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' ↦ Φ t' x') t + c t * Φ t x' + 2 *
          Φ t x')) x
      = 0 := by
  obtain ⟨hm, hd⟩ := hasDerivAt_deriv_comm_of_contDiffAt hΦ
  have hsum : HasDerivAt (fun x' ↦ -(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' ↦ Φ t' x') t + c t *
      Φ t x' +
      2 * Φ t x')) (-(((t * (1 - t) : ℝ) : ℂ) * deriv (fun t' ↦ deriv (fun x' ↦ Φ t' x') x) t +
        c t * deriv (fun x' ↦ Φ t x') x + 2 * deriv (fun x' ↦ Φ t x') x)) x :=
    (((hm.const_mul _).add (hd.hasDerivAt.const_mul _)).add (hd.hasDerivAt.const_mul _)).neg
  have hn : deriv (fun t' ↦ -deriv (fun x' ↦ Φ t' x') x) t =
      -deriv (fun t' ↦ deriv (fun x' ↦ Φ t' x') x) t :=
    deriv.neg
  rw [hsum.deriv, hn]
  ring

/-- Let `f : E → F` between real normed spaces have the derivative `f' z` at every `z` of the ball
`Metric.ball y r`, `0 < r`, with `‖f' z - f' w‖ ≤ K * ‖z - w‖` on the ball and `0 ≤ K`. Then
there is `M ≥ 0` with `‖f' z‖ ≤ M`, `‖f z - f w‖ ≤ M * ‖z - w‖` and `‖f z‖ ≤ ‖f y‖ + M * r` on
the ball. One may take `M = ‖f' y‖ + K * r`, by the mean value inequality on the convex ball. -/
theorem exists_bound_of_lipschitz_fderiv_ball {E : Type*} {F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {y : E} {r : ℝ} {f' : E → (E →L[ℝ] F)}
        {K : ℝ} (hr : 0 < r)
    (hK0 : 0 ≤ K) (hd : ∀ z ∈ Metric.ball y r, HasFDerivAt f (f' z) z)
    (hK : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f' z - f' w‖ ≤ K * ‖z - w‖) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ M) ∧
      (∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r, ‖f z - f w‖ ≤ M * ‖z - w‖) ∧
      (∀ z ∈ Metric.ball y r, ‖f z‖ ≤ ‖f y‖ + M * r) := by
  have hy : y ∈ Metric.ball y r := Metric.mem_ball_self hr
  have hb : ∀ z ∈ Metric.ball y r, ‖f' z‖ ≤ ‖f' y‖ + K * r := by
    intro z hz
    have h1 := hK z hz y hy
    have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
    have h3 : ‖f' z‖ ≤ ‖f' y‖ + ‖f' z - f' y‖ := by
      have := norm_add_le (f' y) (f' z - f' y)
      simpa using this
    nlinarith [norm_nonneg (z - y)]
  have hM0 : 0 ≤ ‖f' y‖ + K * r := by positivity
  have hl : ∀ z ∈ Metric.ball y r, ∀ w ∈ Metric.ball y r,
      ‖f z - f w‖ ≤ (‖f' y‖ + K * r) * ‖z - w‖ := by
    intro z hz w hw
    exact (convex_ball y r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun x hx ↦ (hd x hx).hasFDerivWithinAt) hb hw hz
  refine ⟨‖f' y‖ + K * r, hM0, hb, hl, fun z hz ↦ ?_⟩
  have h1 := hl z hz y hy
  have h2 : ‖z - y‖ < r := by rw [Metric.mem_ball, dist_eq_norm] at hz; exact hz
  have h3 : ‖f z‖ ≤ ‖f y‖ + ‖f z - f y‖ := by
    have := norm_add_le (f y) (f z - f y)
    simpa using this
  nlinarith [norm_nonneg (z - y)]

/-- For differentiable `α, β : ℝ → ℝ` and a point `p` of `ℝ × ℝ`, the derivative of
`q ↦ α q.1 * β q.2` at `p` in the direction `(1, 0)` is `deriv α p.1 * β p.2`. The function is
restricted to the line `r ↦ (r, p.2)`, where it is `r ↦ α r * β p.2`. -/
theorem fderiv_fst_mul_snd_apply_one_zero {α β : ℝ → ℝ} (hα : Differentiable ℝ α)
    (hβ : Differentiable ℝ β) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) p (1, 0) = deriv α p.1 * β p.2 := by
  have hΦ : DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ α q.1 * β q.2) (p.1, p.2) :=
    ((hα _).comp _ differentiableAt_fst).mul ((hβ _).comp _ differentiableAt_snd)
  have h1 : HasDerivAt (fun r : ℝ ↦ (r, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 := hΦ.hasFDerivAt.comp_hasDerivAt p.1 h1
  have h3 : HasDerivAt (fun r ↦ α r * β p.2) (deriv α p.1 * β p.2) p.1 :=
    (hα p.1).hasDerivAt.mul_const _
  exact h2.unique h3

/-- For smooth `g, η : ℝ → ℝ` and a point `p` of `ℝ × ℝ`, the derivative of `q ↦ g q.1 * η q.2` at
`p` in the direction `(0, 1)` is `g p.1 * deriv η p.2`. A case of
`fderiv_fst_mul_snd_apply_zero_one`, which asks for differentiable functions only. -/
theorem fderiv_fst_mul_snd_apply_zero_one_of_contDiff {g η : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hη : ContDiff ℝ ∞ η) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ ↦ g q.1 * η q.2) p (0, 1) = g p.1 * deriv η p.2 :=
  fderiv_fst_mul_snd_apply_zero_one (hg.differentiable (by simp)) (hη.differentiable (by simp)) p

/-- For a smooth `ψ : ℝ × ℝ → ℝ`, a point `p` and directions `u`, `w`, the derivative at `p` in the
direction `w` of `q ↦ fderiv ℝ ψ q u` equals the derivative at `p` in the direction `u` of
`q ↦ fderiv ℝ ψ q w`. A case of `PDE.fderiv_fderiv_apply_comm`, which asks for `ContDiffAt ℝ 2` at
the point, on any normed spaces. -/
theorem fderiv_fderiv_apply_comm_of_contDiff {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u w : ℝ × ℝ) :
    fderiv ℝ (fun q ↦ fderiv ℝ ψ q u) p w = fderiv ℝ (fun q ↦ fderiv ℝ ψ q w) p u :=
  PDE.fderiv_fderiv_apply_comm ψ p u w (hψ.of_le (by simp)).contDiffAt

/-- For a continuous linear map `ℓ` between real normed spaces and a function `g` differentiable at
`y`, the derivative of `z ↦ ℓ (g z)` at `y` in a direction `a` is `ℓ (fderiv ℝ g y a)`. By the
chain rule. -/
theorem fderiv_clm_comp_apply {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ℓ : E →L[ℝ] G) {g : H → E} {y : H} (hg : DifferentiableAt ℝ g y) (a : H) :
    fderiv ℝ (fun z ↦ ℓ (g z)) y a = ℓ (fderiv ℝ g y a) := by
  have h : HasFDerivAt (fun z ↦ ℓ (g z)) (ℓ.comp (fderiv ℝ g y)) y :=
    ℓ.hasFDerivAt.comp y hg.hasFDerivAt
  rw [h.fderiv]
  rfl

end PDE.Analysis
