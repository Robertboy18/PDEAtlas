/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.FactoredOperator
public import PDE.Analysis.Calculus.LocalExtrema
import CAS.ExactTactic

/-!
# Factored parabolic maximum principle

This is Evans's §7.1.4(a), Theorem 8 (Weak maximum principle), for an operator without zeroth-order
term whose principal part is given by finitely many vector fields `σₖ(x, t)`:
`Lu = -∑ₖ D²u(x, t)[σₖ(x, t), σₖ(x, t)] + Du(x, t)[b(x, t)]`. In Euclidean coordinates this is
`-∑ᵢⱼ aᵢⱼ u_{xᵢxⱼ}` with `aᵢⱼ = ∑ₖ (σₖ)ᵢ (σₖ)ⱼ`, that is `A = σσᵀ`, and every symmetric positive
semidefinite real matrix has such a factorization. In a general normed space the family `σ` is part
of the coefficient data. The weak principle uses only the semidefiniteness this form exposes at a
maximum, so the coefficients need neither continuity nor uniform parabolicity.

The main theorem, `subsolution_le_of_boundary_le`, is stated for functions `u : E → ℝ → ℝ`. It
assumes:

* `Ω` is open, nonempty, and has compact closure;
* `T > 0`;
* `u` is continuous on `closure Ω × [0, T]`;
* the spatial slices are `C²` and the time slices are differentiable in `Ω × (0, T]`;
* `uₜ + Lu ≤ 0` there; and
* `u ≤ M` on the parabolic boundary.

The conclusion is `u ≤ M` on the whole closed cylinder.

## Main definitions

* `closedCylinder`, `parabolicBoundary`: the closed cylinder `Ū_T` and the parabolic boundary
  `Γ_T = Ū_T - U_T` of Evans's §2.3.2.
* `factoredEllipticOperator`, `factoredParabolicOperator`: the operators `L` and `uₜ + Lu`.

## Main results

* `subsolution_le_of_boundary_le`: Evans's Theorem 8(i).
* `boundary_le_supersolution`: Evans's Theorem 8(ii).
* `strict_maximum_core`, `subsolution_le_of_strict_perturbation`: the two steps of the proof, for an
  abstract operator.

## How it works

Evans first treats a strict subsolution (65). At a maximum `(x₀, t₀)` with `0 < t₀ < T` he has
`uₜ = 0` (66) and `Lu ≥ 0`, which he obtains in the proof of §6.4.1, Theorem 1 by diagonalizing `A`
with an orthogonal matrix, (9)-(10); at `t₀ = T` he still has `uₜ ≥ 0`. The general case applies
this to `u - εt` and lets `ε → 0`. In `strict_maximum_core` a maximizer on the compact cylinder that
lies above the boundary bound is an interior point at a positive time, for any operator.
`strict_subsolution_le_of_boundary_le` supplies the two signs: `uₜ ≥ 0` from the maximum on
`[0, T]`, using only past-directed increments at `t = T`, and `Lu ≥ 0` from
`factoredEllipticOperator_nonneg_at_localMax`, where each `D²u[σₖ, σₖ]` is a second directional
derivative at a maximum and no diagonalization is needed. `subsolution_le_of_strict_perturbation`
chooses `ε` depending on a hypothetical point above `M` instead of passing to the limit, as Evans
does in step 2 of the proof of Theorem 9.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, the definitions of the parabolic cylinder and the
  parabolic boundary, p. 52; §6.4.1, the proof of Theorem 1, (7)-(10), p. 345; §7.1.4(a), (61) and
  Theorem 8 (Weak maximum principle) and its proof, (62)-(66), pp. 389-390, and step 2 of the proof
  of Theorem 9, p. 391.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace ParabolicMaximum

open Filter Function Set PDE.Analysis
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed spacetime cylinder `closure Ω × [0,T]`. -/
def closedCylinder (Ω : Set E) (T : ℝ) : Set (E × ℝ) :=
  closure Ω ×ˢ Icc 0 T

/-- Evans's parabolic boundary: the lateral boundary together with the initial-time face.
For `T > 0`, the terminal-time section consists of `frontier Ω × {T}`; spatial interior
points at time `T` are excluded. -/
def parabolicBoundary (Ω : Set E) (T : ℝ) : Set (E × ℝ) :=
  (frontier Ω ×ˢ Icc 0 T) ∪ (closure Ω ×ˢ ({0} : Set ℝ))

/-- A nondivergence-form elliptic operator with factored principal
coefficient and no zeroth-order term:

`Lu = -∑ₖ D²u[σₖ,σₖ] + Du[b]`.

Dropping the zeroth-order term gives the `c = 0` case of Evans's §7.1.4(a),
Theorem 8. -/
def factoredEllipticOperator {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) : ℝ :=
  -(∑ k, secondDirectionalDerivative (fun y ↦ u y t) x (σ x t k)) +
    fderiv ℝ (fun y ↦ u y t) x (b x t)

/-- The corresponding parabolic operator `uₜ + Lu`. -/
def factoredParabolicOperator {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) : ℝ :=
  deriv (u x) t + factoredEllipticOperator σ b u x t

/-- The spatial operator is nonnegative at a spatial local maximum.  The
drift term vanishes by Fermat's theorem, while every principal directional
second derivative is nonpositive. -/
theorem factoredEllipticOperator_nonneg_at_localMax {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    {u : E → ℝ → ℝ} {x : E} {t : ℝ}
    (hmax : IsLocalMax (fun y ↦ u y t) x)
    (hu : ContDiffAt ℝ 2 (fun y ↦ u y t) x) :
    0 ≤ factoredEllipticOperator σ b u x t := by
  simpa only [EllipticMaximum.factoredOperator, factoredEllipticOperator,
    zero_mul, add_zero] using
    EllipticMaximum.factoredOperator_nonneg_at_localMax
      (fun y ↦ σ y t) (fun y ↦ b y t) (fun _ ↦ 0) hmax hu (by simp)

omit [NormedSpace ℝ E] in
/-- The compact-cylinder core of the weak parabolic maximum principle.

The operator `P` is abstract. It only has to be nonnegative at points above
the boundary bound `M` where the spatial slice has a local maximum and the
time slice has a maximum on `[0,T]`. The extremum argument is thus separate
from the differential calculation, and Theorems 8 and 9 share this proof. -/
theorem strict_maximum_core
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (P : (E → ℝ → ℝ) → E → ℝ → ℝ)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (hoperator : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      IsLocalMax (fun y ↦ u y t) x →
      IsMaxOn (u x) (Icc 0 T) t →
      M < u x t → 0 ≤ P u x t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, P u x t < 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  classical
  let K : Set (E × ℝ) := closedCylinder Ω T
  have hKcompact : IsCompact K := hΩcompact.prod isCompact_Icc
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hΩne
    exact ⟨(x, 0), subset_closure hx, ⟨le_rfl, hT.le⟩⟩
  obtain ⟨p, hpK, hpmax⟩ :=
    hKcompact.exists_isMaxOn hKne (by simpa [K] using hucont)
  intro q hqK
  have hqp : u q.1 q.2 ≤ u p.1 p.2 := hpmax (by simpa [K] using hqK)
  by_contra hqM
  have hpM : M < u p.1 p.2 := lt_of_not_ge hqM |>.trans_le hqp
  have hp_not_boundary : p ∉ parabolicBoundary Ω T := by
    intro hpbd
    exact (not_lt_of_ge (hboundary p hpbd)) hpM
  have hpx_closure : p.1 ∈ closure Ω := hpK.1
  have hpt_Icc : p.2 ∈ Icc 0 T := hpK.2
  have hpx_not_frontier : p.1 ∉ frontier Ω := by
    intro hxfrontier
    apply hp_not_boundary
    exact Or.inl ⟨hxfrontier, hpt_Icc⟩
  have hpx : p.1 ∈ Ω := by
    have hx : p.1 ∈ closure Ω \ frontier Ω :=
      ⟨hpx_closure, hpx_not_frontier⟩
    rw [closure_sdiff_frontier, hΩopen.interior_eq] at hx
    exact hx
  have hpt_ne : p.2 ≠ 0 := by
    intro htzero
    apply hp_not_boundary
    exact Or.inr ⟨hpx_closure, by simp [htzero]⟩
  have hpt_pos : 0 < p.2 := lt_of_le_of_ne hpt_Icc.1 (Ne.symm hpt_ne)
  have hpt : p.2 ∈ Ioc 0 T := ⟨hpt_pos, hpt_Icc.2⟩
  have hspatialMax : IsLocalMax (fun y ↦ u y p.2) p.1 := by
    filter_upwards [hΩopen.mem_nhds hpx] with y hy
    exact @hpmax (y, p.2) ⟨subset_closure hy, hpt_Icc⟩
  have htimeMax : IsMaxOn (u p.1) (Icc 0 T) p.2 := by
    intro t ht
    exact @hpmax (p.1, t) ⟨hpx_closure, ht⟩
  exact (not_lt_of_ge
    (hoperator p.1 hpx p.2 hpt hspatialMax htimeMax hpM))
    (hsub p.1 hpx p.2 hpt)

/-- Strict-subsolution form of the weak parabolic maximum principle.

This is the compact-cylinder extremum argument in Evans's §7.1.4(a), Theorem 8.
The strict inequality rules out a maximizer away from the parabolic boundary,
including a maximizer on the terminal-time face. -/
theorem strict_subsolution_le_of_boundary_le {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      factoredParabolicOperator σ b u x t < 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  apply strict_maximum_core hΩopen hΩne hΩcompact hT
    (factoredParabolicOperator σ b) u hucont
  · intro x hx t ht hspatialMax htimeMax _hgap
    have hut_nonneg : 0 ≤ deriv (u x) t :=
      htimeMax.deriv_nonneg_of_left_lt ht.1 ht.2 (hutime x hx t ht)
    have hLu_nonneg : 0 ≤ factoredEllipticOperator σ b u x t :=
      factoredEllipticOperator_nonneg_at_localMax σ b hspatialMax
        (huspace x hx t ht)
    simpa [factoredParabolicOperator] using add_nonneg hut_nonneg hLu_nonneg
  · exact hsub
  · exact hboundary

/-- Subtracting `εt` leaves the spatial operator unchanged. -/
theorem factoredEllipticOperator_sub_time {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (ε : ℝ) (x : E) (t : ℝ) :
    factoredEllipticOperator σ b (fun y s ↦ u y s - ε * s) x t =
      factoredEllipticOperator σ b u x t := by
  simpa only [EllipticMaximum.factoredOperator, factoredEllipticOperator,
    zero_mul, add_zero, sub_zero] using
    EllipticMaximum.factoredOperator_sub_const
      (fun y ↦ σ y t) (fun y ↦ b y t) (fun _ ↦ 0) (fun y ↦ u y t) x (ε * t)

/-- Under time differentiability, the perturbation `uε = u - εt` lowers
the parabolic residual by exactly `ε`. -/
theorem factoredParabolicOperator_sub_time {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (ε : ℝ) (x : E) (t : ℝ)
    (hut : DifferentiableAt ℝ (u x) t) :
    factoredParabolicOperator σ b (fun y s ↦ u y s - ε * s) x t =
      factoredParabolicOperator σ b u x t - ε := by
  rw [factoredParabolicOperator, factoredParabolicOperator,
    factoredEllipticOperator_sub_time σ b u ε x t]
  have hlin : HasDerivAt (fun s : ℝ ↦ ε * s) ε t := by
    cas
  have hderiv :
      deriv (fun s ↦ u x s - ε * s) t = deriv (u x) t - ε :=
    (hut.hasDerivAt.sub hlin).deriv
  rw [hderiv]
  ring

/-- The factored spatial operator is linear under negation. -/
theorem factoredEllipticOperator_neg {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) :
    factoredEllipticOperator σ b (fun y s ↦ -u y s) x t =
      -factoredEllipticOperator σ b u x t := by
  simpa only [EllipticMaximum.factoredOperator, factoredEllipticOperator,
    zero_mul, add_zero] using
    EllipticMaximum.factoredOperator_neg
      (fun y ↦ σ y t) (fun y ↦ b y t) (fun _ ↦ 0) (fun y ↦ u y t) x

/-- The full parabolic operator is linear under negation. -/
theorem factoredParabolicOperator_neg {m : ℕ}
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ) (x : E) (t : ℝ) :
    factoredParabolicOperator σ b (fun y s ↦ -u y s) x t =
      -factoredParabolicOperator σ b u x t := by
  rw [factoredParabolicOperator, factoredParabolicOperator,
    factoredEllipticOperator_neg]
  have hderiv : deriv (fun s ↦ -u x s) t = -deriv (u x) t := by
    exact deriv.neg
  rw [hderiv]
  ring

/-- Pass from a strict maximum principle to a weak one by subtracting `εt`.

The operator may be nonlinear: it is enough that this perturbation lowers its
value by at least `ε`. The regularity assumptions are preserved by the affine
perturbation, and the nonnegative time coordinate preserves the boundary bound. -/
theorem subsolution_le_of_strict_perturbation
    {Ω : Set E} {T M : ℝ} (hT : 0 < T)
    (P : (E → ℝ → ℝ) → E → ℝ → ℝ)
    (hstrict : ∀ v : E → ℝ → ℝ,
      ContinuousOn (fun p : E × ℝ ↦ v p.1 p.2) (closedCylinder Ω T) →
      (∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ v y t) x) →
      (∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (v x) t) →
      (∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, P v x t < 0) →
      (∀ p ∈ parabolicBoundary Ω T, v p.1 p.2 ≤ M) →
      ∀ p ∈ closedCylinder Ω T, v p.1 p.2 ≤ M)
    (u : E → ℝ → ℝ)
    (hucont : ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, DifferentiableAt ℝ (u x) t)
    (hperturb : ∀ ε > 0, ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      P (fun y s ↦ u y s - ε * s) x t ≤ P u x t - ε)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T, P u x t ≤ 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  intro q hq
  by_contra hqM
  let d : ℝ := u q.1 q.2 - M
  have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hqM)
  let ε : ℝ := d / (2 * (T + 1))
  have hε : 0 < ε := div_pos hd (by positivity)
  let uε : E → ℝ → ℝ := fun x t ↦ u x t - ε * t
  have huεboundary : ∀ p ∈ parabolicBoundary Ω T, uε p.1 p.2 ≤ M := by
    intro p hp
    have hpt : 0 ≤ p.2 := by
      rcases hp with hp | hp
      · exact hp.2.1
      · rw [hp.2]
    exact (sub_le_self _ (mul_nonneg hε.le hpt)).trans (hboundary p hp)
  have hglobal := hstrict uε (hucont.sub (continuous_const.mul continuous_snd).continuousOn)
    (fun x hx t ht ↦ (huspace x hx t ht).sub contDiffAt_const)
    (fun x hx t ht ↦ (hutime x hx t ht).sub (by cas))
    (fun x hx t ht ↦ (hperturb ε hε x hx t ht).trans_lt (by linarith [hsub x hx t ht]))
    huεboundary q hq
  have hεT : ε * (2 * (T + 1)) = d := by
    dsimp only [ε]
    field_simp
  dsimp only [uε, d] at hglobal hεT
  linarith [mul_le_mul_of_nonneg_left hq.2.2 hε.le, mul_pos hε hT]

/-- Evans's §7.1.4(a), Theorem 8(i): weak parabolic maximum principle.

For a subsolution of `uₜ + Lu ≤ 0` with zero zeroth-order coefficient, the
upper bound on the parabolic boundary controls the entire closed cylinder.
In finite-dimensional Euclidean space, the coefficient factorization
represents an arbitrary symmetric positive-semidefinite principal matrix. -/
theorem subsolution_le_of_boundary_le {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsub : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      factoredParabolicOperator σ b u x t ≤ 0)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, u p.1 p.2 ≤ M) :
    ∀ p ∈ closedCylinder Ω T, u p.1 p.2 ≤ M := by
  apply subsolution_le_of_strict_perturbation hT (factoredParabolicOperator σ b)
    (strict_subsolution_le_of_boundary_le hΩopen hΩne hΩcompact hT σ b)
    u hucont huspace hutime ?_ hsub hboundary
  intro ε _hε x hx t ht
  exact (factoredParabolicOperator_sub_time σ b u ε x t (hutime x hx t ht)).le

/-- Evans's §7.1.4(a), Theorem 8(ii), obtained by applying the maximum principle
to `-u`. -/
theorem boundary_le_supersolution {m : ℕ}
    {Ω : Set E} {T M : ℝ}
    (hΩopen : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩcompact : IsCompact (closure Ω)) (hT : 0 < T)
    (σ : E → ℝ → Fin m → E) (b : E → ℝ → E)
    (u : E → ℝ → ℝ)
    (hucont :
      ContinuousOn (fun p : E × ℝ ↦ u p.1 p.2) (closedCylinder Ω T))
    (huspace : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      ContDiffAt ℝ 2 (fun y ↦ u y t) x)
    (hutime : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      DifferentiableAt ℝ (u x) t)
    (hsuper : ∀ x ∈ Ω, ∀ t ∈ Ioc 0 T,
      0 ≤ factoredParabolicOperator σ b u x t)
    (hboundary : ∀ p ∈ parabolicBoundary Ω T, M ≤ u p.1 p.2) :
    ∀ p ∈ closedCylinder Ω T, M ≤ u p.1 p.2 := by
  have hneg := subsolution_le_of_boundary_le hΩopen hΩne hΩcompact hT
    σ b (fun x t ↦ -u x t) hucont.neg
    (fun x hx t ht ↦ (huspace x hx t ht).neg)
    (fun x hx t ht ↦ (hutime x hx t ht).neg)
    (fun x hx t ht ↦ by
      rw [factoredParabolicOperator_neg]
      exact neg_nonpos.mpr (hsuper x hx t ht))
    (fun p hp ↦ neg_le_neg (hboundary p hp))
  exact fun p hp ↦ neg_le_neg_iff.mp (hneg p hp)

end ParabolicMaximum
