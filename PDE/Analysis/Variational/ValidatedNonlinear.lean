/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Schauder
public import PDE.Analysis.Operator.FiniteRankCorrection
public import PDE.Analysis.TrilinearForm
import PDE.Analysis.Evolution.Galerkin.Restriction

/-!
# Validated nonlinear weak solutions

For an approximate solution, the correction equation has the form
`A u + N u = ell`, where `ell` is the negative residual. A reconstruction `R` may
turn the linear part into a coercive form `B = A ∘ R`. Lax–Milgram defines the
iteration `x ↦ B⁻¹ (ell - N (R x))`.

We prove existence on an energy ball using a compact injective embedding into a weaker
normed space. A bound on `N` makes the ball invariant, and a Lipschitz estimate in the
weaker norm gives continuity. Its constant need not be small. The energy radius, residual
budget, reconstruction bound, and coercivity modulus are all supplied by the application.

The nonlinear bound is stated on the whole ball, not just at numerical sample points.
For a quadratic nonlinearity one can supply `ε = C * (g * r)²` and check
`‖ell‖ + ε ≤ c * r`. Other nonlinearities use the same theorem with their own bound.

For transport nonlinearities, energy cancellation lets the iteration keep the
unknown output in the differentiated slot. The advecting-field space may differ
from the solution space. A closed, convex, bounded invariant set can impose
separate value and gradient radii. The split-energy theorem retains both
coercivity margins and a nonlinear bound in the value norm, as needed for
finite-rank profile corrections. It also holds in a closed subspace, with every
hypothesis required only there and the equation tested only by its vectors, for
example in a symmetry sector.

## Main statements

* `exists_solution_of_compact_embedding`: the abstract theorem, with the budget
  `‖ell‖ + ε ≤ c * r`.
* `exists_solution_near_quadratic`: for a quadratic load from a bilinear map with bound `k`,
  an embedding bound `s ≥ ‖e‖`, a reconstruction bound `g ≥ ‖R‖` and a residual bound `β` of
  the candidate `p`, the scalar check `β + k * s² * (g * r)² ≤ c * r` with `c > 0`, `r ≥ 0`
  gives an exact solution with `‖u - p‖ ≤ g * r`.
* `exists_solution_of_split_energy_transport`: with coercivity margins `a, b > 0` in the value
  and gradient norms, a residual bound `ε` and a nonlinear bound `M` in the value norm, radii
  with `ε + M * r₀² ≤ a * r₀` and `a * r₀² ≤ 4 * b * r₁²` give a solution of value norm at
  most `r₀` and gradient norm at most `r₁`;
  `exists_solution_of_split_energy_transport_on_submodule` is the same statement in a closed
  subspace.

## How it works

We follow the proof of Theorem 3 of Hou, Wang and Yang (Section 3.2.3) in an abstract Hilbert
space. Lax–Milgram (`solveCLM`) defines the iteration, the bound on `N` and the budget
`‖ell‖ + ε ≤ c * r` make the energy ball invariant, and the Lipschitz estimate in the weaker
norm gives continuity there. Schauder's theorem, in the form
`PDE.FixedPoint.exists_isFixedPt_of_compact_embedding`, gives the fixed point; the compact
injective embedding `e` plays the role of the compact embedding `H1 → B` of their Assumption 2.
The transport theorems follow their proof of Proposition 1 in Section 4.3: the unknown output
sits in the differentiated slot as in (4.24), the transport term cancels as in (4.25), and the
radii come from the a priori estimate (4.27).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 3.2.3, Theorem 3 and
  its proof, pp. 21-22, and Section 4.3, (4.24)-(4.27) and the choice of radii after
  Assumption 6, pp. 28-30. <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A quadratic weak load obtained from a bounded bilinear map in the weaker space. -/
def quadraticLoad (e : V →L[ℝ] W) (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V)
    (u : V) : StrongDual ℝ V :=
  P (e u) (e u)

/-- Both terms of the linearization of a quadratic weak load. Symmetry of `P` is not needed. -/
def quadraticLinearization (e : V →L[ℝ] W) (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V)
    (p : V) : V →L[ℝ] StrongDual ℝ V :=
  (P (e p)).comp e + (P.flip (e p)).comp e

omit [CompleteSpace V] in
/-- The quadratic correction has an exact linearization and quadratic remainder. -/
theorem quadraticLoad_add (e : V →L[ℝ] W) (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V)
    (p u : V) :
    quadraticLoad e P (p + u) =
      quadraticLoad e P p + quadraticLinearization e P p u + quadraticLoad e P u := by
  ext v
  simp [quadraticLoad, quadraticLinearization, map_add]
  ring

omit [CompleteSpace V] in
/-- Energy-norm growth of the quadratic weak load, using a supplied bilinear bound. -/
theorem quadraticLoad_norm_le (e : V →L[ℝ] W)
    (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V) {k : NNReal}
    (hP : PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy P k) (u : V) :
    ‖quadraticLoad e P u‖ ≤ k * ‖e‖ ^ 2 * ‖u‖ ^ 2 := by
  have hload : ‖quadraticLoad e P u‖ ≤ k * ‖e u‖ * ‖e u‖ := by
    apply (P (e u) (e u)).opNorm_le_bound (by positivity)
    intro v
    exact hP (e u) (e u) v
  calc
    ‖quadraticLoad e P u‖ ≤ k * ‖e u‖ * ‖e u‖ := hload
    _ ≤ k * (‖e‖ * ‖u‖) * (‖e‖ * ‖u‖) := by
      gcongr <;> exact e.le_opNorm u
    _ = k * ‖e‖ ^ 2 * ‖u‖ ^ 2 := by ring

omit [CompleteSpace V] in
/-- The difference estimate uses the weaker norm for the difference of the inputs. -/
theorem quadraticLoad_sub_norm_le (e : V →L[ℝ] W)
    (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V) {k : NNReal}
    (hP : PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy P k) (u v : V) :
    ‖quadraticLoad e P u - quadraticLoad e P v‖ ≤
      k * (‖e u‖ + ‖e v‖) * ‖e (u - v)‖ := by
  simpa only [quadraticLoad, map_sub] using
    hP.norm_quadratic_dual_sub_le k.property (e u) (e v)

/-- A verified linear reconstruction and nonlinear ball budget give an exact weak solution.
Compactness is required only for the embedding into `W`; the energy ball in `V` need not
be compact, and the iteration need not be a contraction. -/
theorem exists_solution_of_compact_embedding
    (A B : V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] V)
    (hfactor : B = A.comp R) (e : V →L[ℝ] W)
    (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {c r ε : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    {g γ C : NNReal} (hR : ‖R‖ ≤ g)
    (hRweak : ∀ u, ‖e (R u)‖ ≤ γ * ‖e u‖)
    (hN : ∀ u, ‖u‖ ≤ g * r → ‖N u‖ ≤ ε)
    (hNcontinuous : ∀ u, ‖u‖ ≤ g * r → ∀ v, ‖v‖ ≤ g * r →
      ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ‖ell‖ + ε ≤ c * r) :
    ∃ u, ‖u‖ ≤ g * r ∧ ∀ v, A u v + N u v = ell v := by
  have hB : IsCoercive B := ⟨c, hc, hcoercive⟩
  let Q := solveCLM B hB
  let T : V → V := fun u ↦ Q (ell - N (R u))
  have hRball (u : V) (hu : ‖u‖ ≤ r) : ‖R u‖ ≤ g * r := by
    calc
      ‖R u‖ ≤ ‖R‖ * ‖u‖ := R.le_opNorm u
      _ ≤ g * ‖u‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg u)
      _ ≤ g * r := mul_le_mul_of_nonneg_left hu g.property
  have hmap (u : V) (hu : ‖u‖ ≤ r) : ‖T u‖ ≤ r := by
    have hload : ‖ell - N (R u)‖ ≤ ‖ell‖ + ε :=
      (norm_sub_le ell (N (R u))).trans (add_le_add (le_refl ‖ell‖) (hN _ (hRball u hu)))
    calc
      ‖T u‖ ≤ ‖ell - N (R u)‖ / c :=
        solve.norm_le_div B hB c hc hcoercive (ell - N (R u))
      _ ≤ (‖ell‖ + ε) / c := div_le_div_of_nonneg_right hload hc.le
      _ ≤ r := (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hbudget)
  have hcontinuous (u : V) (hu : ‖u‖ ≤ r) (v : V) (hv : ‖v‖ ≤ r) :
      ‖e (T u - T v)‖ ≤ (‖e‖₊ * ‖Q‖₊ * C * γ : NNReal) * ‖e (u - v)‖ := by
    have hdiff : T u - T v = -Q (N (R u) - N (R v)) := by
      change Q (ell - N (R u)) - Q (ell - N (R v)) = -Q (N (R u) - N (R v))
      rw [← map_sub]
      have hload : (ell - N (R u)) - (ell - N (R v)) = -(N (R u) - N (R v)) := by
        abel
      rw [hload, map_neg]
    have hweak := hRweak (u - v)
    rw [map_sub] at hweak
    have hNdiff : ‖N (R u) - N (R v)‖ ≤ C * γ * ‖e (u - v)‖ := by
      calc
        ‖N (R u) - N (R v)‖ ≤ C * ‖e (R u - R v)‖ :=
          hNcontinuous _ (hRball u hu) _ (hRball v hv)
        _ ≤ C * (γ * ‖e (u - v)‖) := mul_le_mul_of_nonneg_left hweak C.property
        _ = C * γ * ‖e (u - v)‖ := by ring
    calc
      ‖e (T u - T v)‖ ≤ ‖e‖ * ‖T u - T v‖ := e.le_opNorm _
      _ = ‖e‖ * ‖Q (N (R u) - N (R v))‖ := by rw [hdiff, norm_neg]
      _ ≤ ‖e‖ * (‖Q‖ * ‖N (R u) - N (R v)‖) :=
        mul_le_mul_of_nonneg_left (Q.le_opNorm _) (norm_nonneg e)
      _ ≤ ‖e‖ * (‖Q‖ * (C * γ * ‖e (u - v)‖)) := by gcongr
      _ = (‖e‖₊ * ‖Q‖₊ * C * γ : NNReal) * ‖e (u - v)‖ := by
        simp only [NNReal.coe_mul, coe_nnnorm]
        ring
  obtain ⟨x, hx, hfix⟩ :=
    PDE.FixedPoint.exists_isFixedPt_of_compact_embedding e he hcompact T hr hmap hcontinuous
  refine ⟨R x, hRball x hx, ?_⟩
  intro v
  have h := solveCLM.isWeakSolution B hB (ell - N (R x)) v
  change B (T x) v = ell v - N (R x) v at h
  rw [hfix, hfactor] at h
  change A (R x) v = ell v - N (R x) v at h
  linarith

/-- Specialization to residual-corrected finite-rank data. Tightening either the tail
budget or the basis-solve budget changes the scalar margin without changing this proof. -/
theorem exists_solution_of_finite_rank_correction
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L₀ K : V →L[ℝ] StrongDual ℝ V) (S : V →L[ℝ] F) (Ψ Φ : F →L[ℝ] V)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {c δ η r ε : ℝ} (hr : 0 ≤ r)
    (hbase : ∀ u, c * ‖u‖ * ‖u‖ ≤ L₀ u u)
    (htail : ‖K.comp (ContinuousLinearMap.id ℝ V - Ψ.comp S)‖ ≤ δ)
    (hres : ‖PDE.Analysis.Operator.FiniteRankCorrection.residual (L₀ + K) K S Ψ Φ‖ ≤ η)
    (hmargin : δ + η < c) {g γ C : NNReal}
    (hR : ‖ContinuousLinearMap.id ℝ V + Φ.comp S‖ ≤ g)
    (hRweak : ∀ u, ‖e (u + Φ (S u))‖ ≤ γ * ‖e u‖)
    (hN : ∀ u, ‖u‖ ≤ g * r → ‖N u‖ ≤ ε)
    (hNcontinuous : ∀ u, ‖u‖ ≤ g * r → ∀ v, ‖v‖ ≤ g * r →
      ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ‖ell‖ + ε ≤ (c - (δ + η)) * r) :
    ∃ u, ‖u‖ ≤ g * r ∧ ∀ v, (L₀ + K) u v + N u v = ell v := by
  exact exists_solution_of_compact_embedding (L₀ + K)
    (PDE.Analysis.Operator.FiniteRankCorrection.corrected L₀ K S Ψ Φ)
    (ContinuousLinearMap.id ℝ V + Φ.comp S)
    (PDE.Analysis.Operator.FiniteRankCorrection.corrected_eq_comp L₀ K S Ψ Φ)
    e he hcompact N ell (sub_pos.mpr hmargin) hr
    (PDE.Analysis.Operator.FiniteRankCorrection.corrected_pairing_ge L₀ K S Ψ Φ
      hbase htail hres) hR hRweak hN hNcontinuous hbudget

/-- An approximate solution of a quadratic weak equation has a nearby exact solution
when its residual, verified linear reconstruction, and quadratic radius budget close. -/
theorem exists_solution_near_quadratic
    (A₀ : V →L[ℝ] StrongDual ℝ V) (e : V →L[ℝ] W)
    (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (P : W →L[ℝ] W →L[ℝ] StrongDual ℝ V) {k s : NNReal}
    (hP : PDE.Analysis.ContinuousTrilinearForm.IsBoundedBy P k)
    (hembedding : ‖e‖ ≤ s) (p : V) (ell : StrongDual ℝ V)
    (B : V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] V)
    (hfactor : B = (A₀ + quadraticLinearization e P p).comp R)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    {g γ : NNReal} (hR : ‖R‖ ≤ g) (hRweak : ∀ u, ‖e (R u)‖ ≤ γ * ‖e u‖)
    {β : ℝ} (hresidual : ‖ell - A₀ p - quadraticLoad e P p‖ ≤ β)
    (hbudget : β + k * s ^ 2 * (g * r) ^ 2 ≤ c * r) :
    ∃ u, ‖u - p‖ ≤ g * r ∧ ∀ v, A₀ u v + quadraticLoad e P u v = ell v := by
  have hN (u : V) (hu : ‖u‖ ≤ g * r) :
      ‖quadraticLoad e P u‖ ≤ k * s ^ 2 * (g * r) ^ 2 := by
    apply (quadraticLoad_norm_le e P hP u).trans
    gcongr
  have hcontinuous (u : V) (hu : ‖u‖ ≤ g * r) (v : V) (hv : ‖v‖ ≤ g * r) :
      ‖quadraticLoad e P u - quadraticLoad e P v‖ ≤
        (2 * k * s * g * r.toNNReal : NNReal) * ‖e (u - v)‖ := by
    have hsum : ‖e u‖ + ‖e v‖ ≤ 2 * s * (g * r) := by
      have hu' := (e.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg e))
      have hv' := (e.le_opNorm v).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg e))
      have hs : ‖e‖ * (g * r) ≤ s * (g * r) := by gcongr
      linarith
    calc
      ‖quadraticLoad e P u - quadraticLoad e P v‖ ≤
          k * (‖e u‖ + ‖e v‖) * ‖e (u - v)‖ := quadraticLoad_sub_norm_le e P hP u v
      _ ≤ k * (2 * s * (g * r)) * ‖e (u - v)‖ := by gcongr
      _ = (2 * k * s * g * r.toNNReal : NNReal) * ‖e (u - v)‖ := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat, Real.coe_toNNReal r hr]
        ring
  obtain ⟨w, hw, heq⟩ := exists_solution_of_compact_embedding
    (A₀ + quadraticLinearization e P p) B R hfactor e he hcompact
    (quadraticLoad e P) (ell - A₀ p - quadraticLoad e P p) hc hr hcoercive
    hR hRweak hN hcontinuous
    ((add_le_add hresidual (le_refl _)).trans hbudget)
  refine ⟨p + w, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using hw
  · intro v
    have h := heq v
    have hquad := DFunLike.congr_fun (quadraticLoad_add e P p w) v
    simp only [add_apply, sub_apply] at h hquad
    rw [map_add, add_apply]
    linarith

/-- Transport validation on a closed, convex, bounded energy set. The invariant-set
condition is an a priori estimate for the tested equation; transport cancels there.
This allows separate value and gradient budgets in the modified profile iteration. -/
theorem exists_solution_of_transport_cancellation_on
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ a u, transport a u u = 0)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {s : Set V} (hne : s.Nonempty) (hclosed : IsClosed s) (hconvex : Convex ℝ s)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hbound : ∀ u ∈ s, ‖u‖ ≤ r)
    (hcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    {k C : NNReal} (htransport : ∀ a u, ‖transport (R a) u‖ ≤ k * ‖e a‖ * ‖u‖)
    (hNcontinuous : ∀ u ∈ s, ∀ v ∈ s,
      ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hinvariant : ∀ a ∈ s, ∀ u, B u u ≤ (ell - N a) u → u ∈ s) :
    ∃ u ∈ s, ∀ v, B u v + transport (R u) u v + N u v = ell v := by
  let D : V → V →L[ℝ] StrongDual ℝ V := fun a ↦ B + transport (R a)
  have hD (a : V) : IsCoercive (D a) := by
    refine ⟨c, hc, fun u ↦ ?_⟩
    simpa only [D, add_apply, hcancel, add_zero] using hcoercive u
  let T : V → V := fun a ↦ solve (D a) (hD a) (ell - N a)
  have hequation (a v : V) : D a (T a) v = ell v - N a v :=
    solve.isWeakSolution (D a) (hD a) (ell - N a) v
  have hmap : Set.MapsTo T s s := by
    intro a ha
    apply hinvariant a ha
    have h := hequation a (T a)
    simpa only [D, add_apply, hcancel, add_zero, sub_apply] using h.le
  let q : NNReal := ⟨‖e‖ * (C + k * r) / c, by positivity⟩
  have hcontinuous (a : V) (ha : a ∈ s) (b : V) (hb : b ∈ s) :
      ‖e (T a - T b)‖ ≤ q * ‖e (a - b)‖ := by
    let load := -(N a - N b) - transport (R (a - b)) (T b)
    have hdiff : D a (T a - T b) = load := by
      ext v
      have hleft := hequation a v
      have hright := hequation b v
      simp only [D, load, map_sub, add_apply, sub_apply, neg_apply] at hleft hright ⊢
      linarith only [hleft, hright]
    have hnorm : ‖T a - T b‖ ≤ ‖load‖ / c := by
      apply norm_le_dual_norm_div_of_pairing load c hc
      rw [← hdiff]
      simpa only [D, add_apply, hcancel, add_zero] using hcoercive (T a - T b)
    have hload : ‖load‖ ≤ (C + k * r) * ‖e (a - b)‖ := by
      calc
        ‖load‖ ≤ ‖N a - N b‖ + ‖transport (R (a - b)) (T b)‖ := by
          simpa only [load, norm_neg] using
            norm_sub_le (-(N a - N b)) (transport (R (a - b)) (T b))
        _ ≤ C * ‖e (a - b)‖ + k * ‖e (a - b)‖ * ‖T b‖ :=
          add_le_add (hNcontinuous a ha b hb) (htransport (a - b) (T b))
        _ ≤ C * ‖e (a - b)‖ + k * ‖e (a - b)‖ * r := by
          gcongr
          exact hbound (T b) (hmap hb)
        _ = _ := by ring
    calc
      ‖e (T a - T b)‖ ≤ ‖e‖ * ‖T a - T b‖ := e.le_opNorm _
      _ ≤ ‖e‖ * (‖load‖ / c) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg e)
      _ ≤ ‖e‖ * (((C + k * r) * ‖e (a - b)‖) / c) := by gcongr
      _ = q * ‖e (a - b)‖ := by
        change ‖e‖ * (((C + k * r) * ‖e (a - b)‖) / c) =
          (‖e‖ * (C + k * r) / c) * ‖e (a - b)‖
        ring
  obtain ⟨u, hu, hfix⟩ :=
    PDE.FixedPoint.exists_isFixedPt_of_compact_embedding_on e he hcompact hne hclosed hconvex
      ((Metric.isBounded_closedBall (x := (0 : V)) (r := r)).subset fun u hu ↦ by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hbound u hu) T hmap hcontinuous
  refine ⟨u, hu, fun v ↦ ?_⟩
  have h := hequation u v
  rw [hfix] at h
  change B u v + transport (R u) u v = ell v - N u v at h
  linarith only [h]

/-- A transport iteration can use its unknown output in the differentiated slot.
Skew transport preserves coercivity, so only the remaining nonlinear load enters
the ball budget. The weaker embedding supplies compactness and continuity. -/
theorem exists_solution_of_transport_cancellation
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ a u, transport a u u = 0)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {c r ε : ℝ} (hc : 0 < c) (hr : 0 ≤ r)
    (hcoercive : ∀ u, c * ‖u‖ * ‖u‖ ≤ B u u)
    {k C : NNReal} (htransport : ∀ a u, ‖transport (R a) u‖ ≤ k * ‖e a‖ * ‖u‖)
    (hN : ∀ u, ‖u‖ ≤ r → ‖N u‖ ≤ ε)
    (hNcontinuous : ∀ u, ‖u‖ ≤ r → ∀ v, ‖v‖ ≤ r →
      ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ‖ell‖ + ε ≤ c * r) :
    ∃ u, ‖u‖ ≤ r ∧ ∀ v, B u v + transport (R u) u v + N u v = ell v := by
  have hinvariant (a : V) (ha : ‖a‖ ≤ r) (u : V)
      (hu : B u u ≤ (ell - N a) u) : ‖u‖ ≤ r := by
    have hnorm := norm_le_dual_norm_div_of_pairing (ell - N a) c hc u
      ((hcoercive u).trans hu)
    have hload : ‖ell - N a‖ ≤ ‖ell‖ + ε :=
      (norm_sub_le ell (N a)).trans (add_le_add (le_refl ‖ell‖) (hN a ha))
    exact hnorm.trans <| (div_le_div_of_nonneg_right hload hc.le).trans <|
      (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hbudget)
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    exists_solution_of_transport_cancellation_on B transport R hcancel e he hcompact N ell
      (s := Metric.closedBall (0 : V) r) ⟨0, by simpa using hr⟩
      Metric.isClosed_closedBall (convex_closedBall (0 : V) r) hc hr
      (fun u hu ↦ by simpa only [Metric.mem_closedBall, dist_zero_right] using hu)
      hcoercive htransport
      (fun u hu v hv ↦ hNcontinuous u
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu) v
        (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv))
      (fun a ha u hu ↦ by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hinvariant a (by simpa only [Metric.mem_closedBall, dist_zero_right] using ha) u hu)

/-- Transport validation with separate value and gradient radii. The residual and
remaining nonlinear load are tested in the value norm. Completing the square in
the energy estimate controls the gradient radius without losing the mass margin.

These are the two conditions on the radii that Hou, Wang and Yang derive from their (4.27)
in Section 4.3, where `x₀` and `x₁` are chosen so that both hold with equality. The nonlinear
bound `M` is an input, so an application can use its finite-rank estimate instead of a
generic product of Sobolev inclusion norms. -/
theorem exists_solution_of_split_energy_transport
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ a u, transport a u u = 0)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {a b r₀ r₁ ε M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hM : 0 ≤ M)
    (hcoercive : ∀ u, a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ B u u)
    (hell : ∀ v, |ell v| ≤ ε * ‖mass v‖)
    (hN : ∀ u, ‖mass u‖ ≤ r₀ → ‖gradient u‖ ≤ r₁ →
      ∀ v, |N u v| ≤ M * ‖mass u‖ ^ 2 * ‖mass v‖)
    {k C : NNReal} (htransport : ∀ u v, ‖transport (R u) v‖ ≤ k * ‖e u‖ * ‖v‖)
    (hNcontinuous : ∀ u, ‖mass u‖ ≤ r₀ → ‖gradient u‖ ≤ r₁ →
      ∀ v, ‖mass v‖ ≤ r₀ → ‖gradient v‖ ≤ r₁ → ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ε + M * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u, ‖mass u‖ ≤ r₀ ∧ ‖gradient u‖ ≤ r₁ ∧
      ∀ v, B u v + transport (R u) u v + N u v = ell v := by
  let s := mass ⁻¹' Metric.closedBall 0 r₀ ∩ gradient ⁻¹' Metric.closedBall 0 r₁
  have hmem (u : V) : u ∈ s ↔ ‖mass u‖ ≤ r₀ ∧ ‖gradient u‖ ≤ r₁ := by
    simp only [s, Set.mem_inter_iff, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
  have hbound (u : V) (hu : u ∈ s) : ‖u‖ ≤ r₀ + r₁ := by
    obtain ⟨h₀, h₁⟩ := (hmem u).mp hu
    have h₀sq := (sq_le_sq₀ (norm_nonneg _) hr₀).mpr h₀
    have h₁sq := (sq_le_sq₀ (norm_nonneg _) hr₁).mpr h₁
    nlinarith only [hnorm u, h₀sq, h₁sq, norm_nonneg u, hr₀, hr₁, mul_nonneg hr₀ hr₁]
  have hcoercive' (u : V) : min a b * ‖u‖ * ‖u‖ ≤ B u u := by
    calc
      min a b * ‖u‖ * ‖u‖ = min a b * (‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2) := by
        rw [← hnorm u]
        ring
      _ ≤ a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 := by
        rw [mul_add]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg _))
      _ ≤ B u u := hcoercive u
  have hinvariant (w : V) (hw : w ∈ s) (u : V)
      (hu : B u u ≤ (ell - N w) u) : u ∈ s := by
    obtain ⟨hw₀, hw₁⟩ := (hmem w).mp hw
    have hwsq := (sq_le_sq₀ (norm_nonneg _) hr₀).mpr hw₀
    have henergy : a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ a * r₀ * ‖mass u‖ := by
      calc
        _ ≤ (ell - N w) u := (hcoercive u).trans hu
        _ ≤ |ell u| + |N w u| := by
          change ell u - N w u ≤ _
          linarith only [le_abs_self (ell u), neg_abs_le (N w u)]
        _ ≤ ε * ‖mass u‖ + M * ‖mass w‖ ^ 2 * ‖mass u‖ :=
          add_le_add (hell u) (hN w hw₀ hw₁ u)
        _ ≤ (ε + M * r₀ ^ 2) * ‖mass u‖ := by
          rw [add_mul]
          gcongr
        _ ≤ a * r₀ * ‖mass u‖ := mul_le_mul_of_nonneg_right hbudget (norm_nonneg _)
    have hmass : ‖mass u‖ ≤ r₀ := by
      have hsq : ‖mass u‖ ^ 2 ≤ r₀ * ‖mass u‖ := by
        apply (mul_le_mul_iff_of_pos_left ha).mp
        nlinarith only [henergy, mul_nonneg hb.le (sq_nonneg ‖gradient u‖)]
      by_cases hzero : ‖mass u‖ = 0
      · simpa only [hzero] using hr₀
      · have hpos : 0 < ‖mass u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
        rw [pow_two] at hsq
        exact (mul_le_mul_iff_of_pos_right hpos).mp hsq
    have hgrad : ‖gradient u‖ ≤ r₁ := by
      apply (sq_le_sq₀ (norm_nonneg _) hr₁).mp
      apply (mul_le_mul_iff_of_pos_left hb).mp
      nlinarith only [henergy, hgradient,
        mul_nonneg ha.le (sq_nonneg (‖mass u‖ - r₀ / 2))]
    exact (hmem u).mpr ⟨hmass, hgrad⟩
  obtain ⟨u, hu, heq⟩ := exists_solution_of_transport_cancellation_on
    B transport R hcancel e he hcompact N ell
    ⟨0, (hmem 0).mpr (by simpa only [map_zero, norm_zero] using And.intro hr₀ hr₁)⟩
    ((Metric.isClosed_closedBall.preimage mass.continuous).inter
      (Metric.isClosed_closedBall.preimage gradient.continuous))
    (((convex_closedBall (0 : H) r₀).linear_preimage mass.toLinearMap).inter
      ((convex_closedBall (0 : Z) r₁).linear_preimage gradient.toLinearMap))
    (lt_min ha hb) (add_nonneg hr₀ hr₁) hbound hcoercive' htransport
    (fun u hu v hv ↦ hNcontinuous u ((hmem u).mp hu).1 ((hmem u).mp hu).2 v
      ((hmem v).mp hv).1 ((hmem v).mp hv).2) hinvariant
  exact ⟨u, ((hmem u).mp hu).1, ((hmem u).mp hu).2, heq⟩

/-- Split-energy transport validation in a closed subspace `S`. The norm splitting,
coercivity, cancellation, residual and nonlinear bounds are required only on `S`. The
solution lies in `S` and satisfies the equation against the test vectors of `S`.
Lax–Milgram and the fixed-point argument run in the Hilbert space `S` itself, so the
iteration on the ambient space need not preserve `S`. -/
theorem exists_solution_of_split_energy_transport_on_submodule
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (S : Submodule ℝ V) (hS : IsClosed (S : Set V))
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u ∈ S, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ u ∈ S, ∀ v ∈ S, transport (R u) v v = 0)
    (e : V →L[ℝ] W) (he : Set.InjOn e S) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {a b r₀ r₁ ε M : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr₀ : 0 ≤ r₀) (hr₁ : 0 ≤ r₁) (hM : 0 ≤ M)
    (hcoercive : ∀ u ∈ S, a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ B u u)
    (hell : ∀ v ∈ S, |ell v| ≤ ε * ‖mass v‖)
    (hN : ∀ u ∈ S, ‖mass u‖ ≤ r₀ → ‖gradient u‖ ≤ r₁ →
      ∀ v ∈ S, |N u v| ≤ M * ‖mass u‖ ^ 2 * ‖mass v‖)
    {k C : NNReal}
    (htransport : ∀ u ∈ S, ∀ v ∈ S, ‖transport (R u) v‖ ≤ k * ‖e u‖ * ‖v‖)
    (hNcontinuous : ∀ u ∈ S, ‖mass u‖ ≤ r₀ → ‖gradient u‖ ≤ r₁ →
      ∀ v ∈ S, ‖mass v‖ ≤ r₀ → ‖gradient v‖ ≤ r₁ → ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ε + M * r₀ ^ 2 ≤ a * r₀)
    (hgradient : a * r₀ ^ 2 ≤ 4 * b * r₁ ^ 2) :
    ∃ u ∈ S, ‖mass u‖ ≤ r₀ ∧ ‖gradient u‖ ≤ r₁ ∧
      ∀ v ∈ S, B u v + transport (R u) u v + N u v = ell v := by
  have : CompleteSpace S := hS.completeSpace_coe
  obtain ⟨u, hu₀, hu₁, heq⟩ := exists_solution_of_split_energy_transport
    (mass.comp S.subtypeL) (gradient.comp S.subtypeL) (fun u ↦ hnorm u u.2)
    (PDE.Analysis.Evolution.restrictForm S B)
    (ContinuousTrilinearForm.restrict transport (R.comp S.subtypeL) S.subtypeL S.subtypeL)
    (ContinuousLinearMap.id ℝ S) (fun u v ↦ hcancel u u.2 v v.2) (e.comp S.subtypeL)
    (fun u v huv ↦ Subtype.ext (he u.2 v.2 huv)) (hcompact.comp_clm S.subtypeL)
    (fun u ↦ PDE.Analysis.Evolution.restrictFunctional S (N u))
    (PDE.Analysis.Evolution.restrictFunctional S ell) ha hb hr₀ hr₁ hM
    (fun u ↦ by
      rw [PDE.Analysis.Evolution.restrictForm_apply]
      exact hcoercive u u.2)
    (fun v ↦ hell v v.2) (fun u hu₀ hu₁ v ↦ hN u u.2 hu₀ hu₁ v v.2)
    (fun u v ↦ (PDE.Analysis.Evolution.norm_restrictFunctional_le S _).trans
      (htransport u u.2 v v.2))
    (fun u hu₀ hu₁ v hv₀ hv₁ ↦
      (PDE.Analysis.Evolution.norm_restrictFunctional_le S (N u - N v)).trans
        (hNcontinuous u u.2 hu₀ hu₁ v v.2 hv₀ hv₁))
    hbudget hgradient
  exact ⟨u, u.2, hu₀, hu₁, fun v hv ↦ heq ⟨v, hv⟩⟩

end PDE.Analysis.Variational
