/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.MinMax
public import Mathlib.Tactic.Positivity

/-!
# Energy convergence of weak eigenfunction expansions

Completeness of the pivot-space eigenbasis does not by itself give convergence
in the energy space. Coercivity supplies the additional argument: the weighted
squared coefficients are summable, so finite tails have small energy and hence
small energy-space norm. Completeness constructs their sum in `V`; injectivity
of the inclusion identifies it with the original displacement.

The index set may be arbitrary, and `V` need not be a Hilbert space. For a
countable basis, the resulting `HasSum` theorem also gives convergence of
the usual initial spectral truncations.

For the Dirichlet eigenfunctions of Evans, §6.5.1, `hasSum_weakEigenfunction_expansion` is the
conclusion of step 3 of his proof of Theorem 2, that the series (8) converges also in
`H¹₀(U)`, and `hasSum_eigenvalue_mul_inner_sq` is the identity `B[u, u] = ∑ d_k² λ_k` of his
step 4. Evans shows that the `w_k / λ_k^{1/2}` form an orthonormal basis of `H¹₀(U)` for the
inner product `B[ , ]`. We bound instead the partial sums of `λ_k d_k²` by `B[u, u]`, use
coercivity and the completeness of `V`, and identify the sum through the injectivity of `j`.

## Main results

* `summable_weakEigenfunction_series`: if `∑ λ i (a i)²` is summable, then `∑ a i • u i`
  converges in `V`.
* `hasSum_weakEigenfunction_expansion`: for injective `j`, `v = ∑ ⟪b i, j v⟫ • u i` in `V`.
* `hasSum_eigenvalue_mul_inner_sq`: for injective `j`, `B v v = ∑ λ i ⟪b i, j v⟫²`.
* `eq_of_apply_weakEigenfunctions_eq`: if every vector has such an expansion, continuous
  linear functionals that agree on the eigenfunctions are equal.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, steps 3 and 4 of the proof of Theorem 2
  (Variational principle for the principal eigenvalue), pp. 357-358.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Variational

open Filter
open scoped Topology BigOperators InnerProductSpace

variable {ι V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Summability of the eigenvalue-weighted squared coefficients gives convergence
of the weak eigenfunction series in the energy space. This is square summability,
not an assumption of absolute summability in `V`. -/
theorem summable_weakEigenfunction_series
    (B : V →L[ℝ] StrongDual ℝ V) {c : ℝ} (hc : 0 < c)
    (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (j : V →L[ℝ] H) (b : ι → H) (hb : Orthonormal ℝ b)
    (lambda : ι → ℝ) (u : ι → V) (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ)
    (a : ι → ℝ) (ha : Summable fun i ↦ lambda i * (a i) ^ 2) :
    Summable (fun i ↦ a i • u i) := by
  classical
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp ha (c * ε ^ 2) (by positivity)
  refine ⟨s, fun t ht ↦ ?_⟩
  have htail : c * ‖∑ i ∈ t, a i • u i‖ ^ 2 < c * ε ^ 2 := by
    calc
      c * ‖∑ i ∈ t, a i • u i‖ ^ 2 ≤
          B (∑ i ∈ t, a i • u i) (∑ i ∈ t, a i • u i) := hcoercive _
      _ = ∑ i ∈ t, lambda i * (a i) ^ 2 :=
        energy_sum_weakEigenfunctions B j b hb lambda u hju hweak t a
      _ ≤ ‖∑ i ∈ t, lambda i * (a i) ^ 2‖ := le_abs_self _
      _ < c * ε ^ 2 := hs t ht
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
    ((mul_lt_mul_iff_right₀ hc).mp htail)

/-- The pivot coefficients of a complete weak eigenfunction family reconstruct
every displacement in the energy norm. Injectivity of `j` is essential for
identifying the energy-space sum from its pivot image. -/
theorem hasSum_weakEigenfunction_expansion
    (B : V →L[ℝ] StrongDual ℝ V) (hsymm : ∀ v w, B v w = B w v)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (j : V →L[ℝ] H) (hj : Function.Injective j)
    (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (u : ι → V) (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ) (v : V) :
    HasSum (fun i ↦ ⟪b i, j v⟫_ℝ • u i) v := by
  have hnonneg (w : V) : 0 ≤ B w w :=
    (mul_nonneg hc.le (sq_nonneg _)).trans (hcoercive w)
  have hweighted : Summable (fun i ↦ lambda i * ⟪b i, j v⟫_ℝ ^ 2) :=
    summable_of_sum_le (fun i ↦ mul_nonneg (hlambda i) (sq_nonneg _))
      (fun s ↦ sum_eigenvalue_mul_inner_sq_le
        B hnonneg hsymm j b b.orthonormal lambda u hju hweak s v)
  obtain ⟨v', hv'⟩ := summable_weakEigenfunction_series
    B hc hcoercive j b b.orthonormal lambda u hju hweak
      (fun i ↦ ⟪b i, j v⟫_ℝ) hweighted
  have hJ : HasSum (fun i ↦ ⟪b i, j v⟫_ℝ • b i) (j v') := by
    simpa only [map_smul, hju] using hv'.mapL j
  have hJv : HasSum (fun i ↦ ⟪b i, j v⟫_ℝ • b i) (j v) := by
    simpa only [b.repr_apply_apply] using b.hasSum_repr (j v)
  have hv : v' = v := hj (hJ.unique hJv)
  simpa only [hv] using hv'

/-- Parseval's identity for the spatial energy follows from convergence in `V`.
The finite-mode inequality becomes an equality after all modes are included. -/
theorem hasSum_eigenvalue_mul_inner_sq
    (B : V →L[ℝ] StrongDual ℝ V) (hsymm : ∀ v w, B v w = B w v)
    {c : ℝ} (hc : 0 < c) (hcoercive : ∀ v, c * ‖v‖ ^ 2 ≤ B v v)
    (j : V →L[ℝ] H) (hj : Function.Injective j)
    (b : HilbertBasis ι ℝ H) (lambda : ι → ℝ) (hlambda : ∀ i, 0 ≤ lambda i)
    (u : ι → V) (hju : ∀ i, j (u i) = b i)
    (hweak : ∀ i v, B (u i) v = lambda i * ⟪b i, j v⟫_ℝ) (v : V) :
    HasSum (fun i ↦ lambda i * ⟪b i, j v⟫_ℝ ^ 2) (B v v) := by
  classical
  have hexpansion := hasSum_weakEigenfunction_expansion
    B hsymm hc hcoercive j hj b lambda hlambda u hju hweak v
  have hcont : Continuous (fun w : V ↦ B w w) := by fun_prop
  have hlimit := hcont.continuousAt.tendsto.comp hexpansion
  change Tendsto (fun s : Finset ι ↦ ∑ i ∈ s, lambda i * ⟪b i, j v⟫_ℝ ^ 2)
    atTop (𝓝 (B v v))
  simpa only [Function.comp_def, SummationFilter.unconditional,
    energy_sum_weakEigenfunctions B j b b.orthonormal lambda u hju hweak] using hlimit

end PDE.Analysis.Variational

open scoped InnerProductSpace

namespace PDE.Analysis.Variational

variable {ι V H : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Energy-norm convergence of an eigenfunction expansion lets its coefficients
determine every continuous linear functional on the energy space. Pivot-space
completeness alone would not justify this conclusion. -/
theorem eq_of_apply_weakEigenfunctions_eq
    (J : V →L[ℝ] H) (basis : ι → H) (e : ι → V)
    (hexpansion : ∀ v : V, HasSum (fun i ↦ ⟪basis i, J v⟫_ℝ • e i) v)
    (l₁ l₂ : StrongDual ℝ V) (heq : ∀ i, l₁ (e i) = l₂ (e i)) :
    l₁ = l₂ := by
  ext v
  have h₁ := (hexpansion v).mapL l₁
  have h₂ := (hexpansion v).mapL l₂
  change HasSum (fun i ↦ l₁ (⟪basis i, J v⟫_ℝ • e i)) (l₁ v) at h₁
  change HasSum (fun i ↦ l₂ (⟪basis i, J v⟫_ℝ • e i)) (l₂ v) at h₂
  have hterms :
      (fun i ↦ l₁ (⟪basis i, J v⟫_ℝ • e i)) =
        (fun i ↦ l₂ (⟪basis i, J v⟫_ℝ • e i)) := by
    funext i
    rw [map_smul, map_smul, heq]
  rw [hterms] at h₁
  exact h₁.unique h₂

end PDE.Analysis.Variational
