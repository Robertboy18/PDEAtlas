/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Galerkin.TrialProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Spectrum
import PDE.Analysis.Spectral.CompactOperator

/-!
# Spectral Galerkin trial spaces

Galerkin schemes need a family of finite-dimensional trial spaces `S_m ⊆ V`
whose union is dense and whose projections are uniformly stable.  For a
Gelfand triple `V ↪ H ↪ V*` of Hilbert spaces with compact inclusion `J : V → H`, we
build such a family without choosing a basis.  The Gram operator `R = J†J`
on `V` is compact, symmetric and injective, so by the spectral theorem for
compact symmetric operators its eigenspaces span a dense subspace of `V`.
Thresholding (`S_m` is the sum of the eigenspaces with `|μ| ≥ 1/(m+1)`)
gives an increasing family of finite-dimensional, `R`-invariant subspaces
with dense union.  Because `⟪R u, v⟫_V = ⟪J u, J v⟫_H`, invariance under `R`
makes the `V`-orthogonal projection onto `S_m` also `H`-orthogonal after
inclusion, so it is a `StableTrialProjection` with stability constant one.
This is the abstract form of the eigenfunction bases (for instance of the
Dirichlet Laplacian) used for Galerkin approximations in the textbooks.

## Main results

* `gramOperator`: `J†J`, with `isCompactOperator_gramOperator`,
  `gramOperator_isSymmetric` and `gramOperator_injective`.
* `thresholdSpace`: the `m`th spectral threshold space, with
  `finiteDimensional_thresholdSpace`, `monotone_thresholdSpace`,
  `dense_iSup_thresholdSpace` and `thresholdProjection_tendsto`.
* `threshold_residual_pivot_orthogonal`: the energy-projection residual is
  pivot-orthogonal to the threshold space.
* `stableTrialProjectionOfCompatibility`, `stableTrialProjectionThreshold`:
  norm-one stable trial projections.
* `gramSpectralGalerkinSystem`: the resulting `StableTrialSystem`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, the remark after equation (13) (eigenfunctions
  of `-Δ` as a Galerkin basis), and Appendix D.6, Theorem 7 (eigenvectors of a compact,
  symmetric operator). <https://doi.org/10.1090/gsm/019>
* R. Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing,
  2001, Chapter III (the evolution Navier-Stokes equation). <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

noncomputable section

open Set Function Filter
open scoped Topology InnerProductSpace

namespace PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-! ## The compact Gram operator -/

/-- The positive symmetric Gram operator associated to `J : V → H`. -/
def gramOperator (J : V →L[ℝ] H) : V →L[ℝ] V :=
  J.adjoint.comp J

/-- The Gram operator pulls the pivot-space inner product back along `J`. -/
@[simp]
theorem inner_gramOperator_apply (J : V →L[ℝ] H) (u v : V) :
    inner ℝ (gramOperator J u) v = inner ℝ (J u) (J v) := by
  exact J.adjoint_inner_left v (J u)

/-- Compactness of `J` implies compactness of its Gram operator. -/
theorem isCompactOperator_gramOperator
    (J : V →L[ℝ] H) (hJ : IsCompactOperator J) :
    IsCompactOperator (gramOperator J) :=
  hJ.clm_comp J.adjoint

/-- The Gram operator is symmetric in the energy-space inner product. -/
theorem gramOperator_isSymmetric (J : V →L[ℝ] H) :
    (gramOperator J : Module.End ℝ V).IsSymmetric := by
  intro u v
  change inner ℝ (J.adjoint (J u)) v =
    inner ℝ u (J.adjoint (J v))
  rw [J.adjoint_inner_left, J.adjoint_inner_right]

/-- An injective inclusion has an injective Gram operator. -/
theorem gramOperator_injective
    (J : V →L[ℝ] H) (hJ : Function.Injective J) :
    Function.Injective (gramOperator J) := by
  rw [gramOperator]
  exact (J.adjoint_comp_self_injective_iff).2 hJ

/-! ## Finite spectral threshold spaces -/

/-- Eigenvalues whose absolute value is at least `1 / (m + 1)`. -/
def thresholdEigenvalues (R : V →L[ℝ] V) (m : ℕ) : Set ℝ :=
  {μ | Module.End.HasEigenvalue (R : Module.End ℝ V) μ ∧
    1 / (m + 1 : ℝ) ≤ |μ|}

/-- The sum of all eigenspaces whose eigenvalues pass the `m`th threshold. -/
def thresholdSpace
    (R : V →L[ℝ] V) (m : ℕ) : Submodule ℝ V :=
  ⨆ μ : thresholdEigenvalues R m,
    Module.End.eigenspace (R : Module.End ℝ V) μ.1

omit [CompleteSpace V] in
/-- Only finitely many eigenvalues of a compact operator pass a positive
threshold. -/
theorem thresholdEigenvalues_finite
    (R : V →L[ℝ] V) (hR : IsCompactOperator R) (m : ℕ) :
    (thresholdEigenvalues R m).Finite := by
  simpa only [thresholdEigenvalues, Real.norm_eq_abs] using
    PDE.Analysis.finite_eigenvalues_norm_ge R hR (by positivity : 0 < 1 / (m + 1 : ℝ))

/-- A compact operator's spectral threshold space is finite-dimensional. -/
theorem finiteDimensional_thresholdSpace
    (R : V →L[ℝ] V) (hR : IsCompactOperator R) (m : ℕ) :
    FiniteDimensional ℝ (thresholdSpace R m) := by
  classical
  let : Finite (thresholdEigenvalues R m) :=
    Set.finite_coe_iff.mpr (thresholdEigenvalues_finite R hR m)
  let (μ : thresholdEigenvalues R m) :
      FiniteDimensional ℝ
        (Module.End.eigenspace (R : Module.End ℝ V) μ.1) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hR μ.1 (by
      intro hzero
      have hpos : 0 < 1 / (m + 1 : ℝ) := by positivity
      simpa [hzero] using lt_of_lt_of_le hpos μ.2.2)
  exact Submodule.finiteDimensional_iSup _

omit [CompleteSpace V] in
/-- Lowering the threshold enlarges the trial space. -/
theorem monotone_thresholdSpace (R : V →L[ℝ] V) :
    Monotone (thresholdSpace R) := by
  intro m k hmk
  apply iSup_le
  intro μ
  have hden : (m + 1 : ℝ) ≤ (k + 1 : ℝ) := by
    exact_mod_cast Nat.add_le_add_right hmk 1
  let ν : thresholdEigenvalues R k :=
    ⟨μ.1, μ.2.1,
      (one_div_le_one_div_of_le (by positivity) hden).trans μ.2.2⟩
  exact le_iSup_of_le ν le_rfl

/-! ## Spectral exhaustion and approximation -/

omit [CompleteSpace V] in
/-- For an injective operator, the threshold spaces exhaust the sum of all
eigenspaces.  Injectivity removes the otherwise omitted zero eigenspace. -/
theorem iSup_thresholdSpace_eq_iSup_eigenspaces
    (R : V →L[ℝ] V) (hRinj : Function.Injective R) :
    ⨆ m, thresholdSpace R m =
      ⨆ μ : ℝ, Module.End.eigenspace (R : Module.End ℝ V) μ := by
  apply le_antisymm
  · exact iSup_le fun _ ↦
      iSup_le fun μ ↦
        le_iSup
          (fun ν : ℝ ↦
            Module.End.eigenspace (R : Module.End ℝ V) ν)
          μ.1
  · apply iSup_le
    intro μ
    by_cases hμzero : μ = 0
    · subst μ
      rw [Module.End.eigenspace_zero, LinearMap.ker_eq_bot.mpr hRinj]
      exact bot_le
    by_cases hμeig :
        Module.End.HasEigenvalue (R : Module.End ℝ V) μ
    · obtain ⟨m, hm⟩ :=
        exists_nat_one_div_lt (abs_pos.mpr hμzero)
      let μm : thresholdEigenvalues R m :=
        ⟨μ, hμeig, hm.le⟩
      exact le_iSup_of_le m (le_iSup_of_le μm le_rfl)
    · have hbot :
          Module.End.eigenspace (R : Module.End ℝ V) μ = ⊥ := by
        simpa only [Module.End.hasEigenvalue_iff, not_ne_iff] using hμeig
      rw [hbot]
      exact bot_le

/-- The increasing threshold spaces of a compact injective symmetric
operator have dense union. -/
theorem dense_iSup_thresholdSpace
    (R : V →L[ℝ] V) (hRc : IsCompactOperator R)
    (hRs : (R : Module.End ℝ V).IsSymmetric)
    (hRi : Function.Injective R) :
    (⨆ m, thresholdSpace R m).topologicalClosure = ⊤ := by
  rw [iSup_thresholdSpace_eq_iSup_eigenspaces R hRi]
  exact (Submodule.topologicalClosure_eq_top_iff).2
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
      hRc hRs)

/-- The energy-orthogonal projection onto a compact operator's `m`th
threshold space.  Compactness supplies finite-dimensionality, hence the
orthogonal projection. -/
def thresholdOrthogonalProjection
    (R : V →L[ℝ] V) (hRc : IsCompactOperator R) (m : ℕ) :
    V →L[ℝ] thresholdSpace R m := by
  letI : FiniteDimensional ℝ (thresholdSpace R m) :=
    finiteDimensional_thresholdSpace R hRc m
  letI : CompleteSpace (thresholdSpace R m) :=
    FiniteDimensional.complete ℝ _
  exact (thresholdSpace R m).orthogonalProjectionOnto

/-- Energy-orthogonal projections onto the threshold spaces converge strongly
to the identity. -/
theorem thresholdProjection_tendsto
    (R : V →L[ℝ] V) (hRc : IsCompactOperator R)
    (hRs : (R : Module.End ℝ V).IsSymmetric)
    (hRi : Function.Injective R) (v : V) :
    Tendsto
      (fun m ↦ ((thresholdOrthogonalProjection R hRc m v :
        thresholdSpace R m) : V))
      atTop (nhds v) := by
  let (m : ℕ) : FiniteDimensional ℝ (thresholdSpace R m) :=
    finiteDimensional_thresholdSpace R hRc m
  let (m : ℕ) : CompleteSpace (thresholdSpace R m) :=
    FiniteDimensional.complete ℝ _
  simpa only [thresholdOrthogonalProjection,
    Submodule.coe_orthogonalProjectionOnto_apply] using
      Submodule.starProjection_tendsto_self
        (thresholdSpace R) (monotone_thresholdSpace R) v (by
          rw [dense_iSup_thresholdSpace R hRc hRs hRi])

/-- Eventual approximation in the energy norm by threshold-space vectors. -/
theorem eventually_approximable_thresholdSpace
    (R : V →L[ℝ] V) (hRc : IsCompactOperator R)
    (hRs : (R : Module.End ℝ V).IsSymmetric)
    (hRi : Function.Injective R) :
    ∀ v : V, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in atTop,
        ∃ w : thresholdSpace R m, ‖v - (w : V)‖ < ε := by
  intro v ε hε
  let (m : ℕ) : FiniteDimensional ℝ (thresholdSpace R m) :=
    finiteDimensional_thresholdSpace R hRc m
  let (m : ℕ) : CompleteSpace (thresholdSpace R m) :=
    FiniteDimensional.complete ℝ _
  obtain ⟨N, hN⟩ :=
    Metric.tendsto_atTop.mp
      (thresholdProjection_tendsto R hRc hRs hRi v) ε hε
  refine Filter.eventually_atTop.2 ⟨N, fun m hm ↦ ?_⟩
  refine ⟨thresholdOrthogonalProjection R hRc m v, ?_⟩
  simpa [dist_eq_norm, norm_sub_rev] using hN m hm

/-! ## Compatibility of spectral and pivot projections -/

omit [CompleteSpace V] in
/-- Every threshold space is invariant under its defining operator. -/
theorem thresholdSpace_invariant
    (R : V →L[ℝ] V) (m : ℕ) {w : V}
    (hw : w ∈ thresholdSpace R m) :
    R w ∈ thresholdSpace R m := by
  refine Submodule.iSup_induction _
    (motive := fun x ↦ R x ∈ thresholdSpace R m) hw ?_ ?_ ?_
  · intro μ x hx
    have hxEq := Module.End.mem_eigenspace_iff.mp hx
    change R x = μ.1 • x at hxEq
    rw [hxEq]
    exact (thresholdSpace R m).smul_mem μ.1
      (Submodule.mem_iSup_of_mem μ hx)
  · simp
  · intro x y hx hy
    simpa using (thresholdSpace R m).add_mem hx hy

/-- The energy projection residual is pivot-orthogonal to a Gram spectral
threshold space. -/
theorem threshold_residual_pivot_orthogonal
    (J : V →L[ℝ] H) (m : ℕ)
    [CompleteSpace (thresholdSpace (gramOperator J) m)]
    (v : V) (w : thresholdSpace (gramOperator J) m) :
    inner ℝ
      (J (v - (thresholdSpace (gramOperator J) m).starProjection v))
      (J (w : V)) = 0 := by
  let S := thresholdSpace (gramOperator J) m
  have hRw : gramOperator J (w : V) ∈ S :=
    thresholdSpace_invariant (gramOperator J) m w.2
  calc
    inner ℝ (J (v - S.starProjection v)) (J (w : V)) =
        inner ℝ (gramOperator J (v - S.starProjection v)) (w : V) := by
      rw [inner_gramOperator_apply]
    _ = inner ℝ (v - S.starProjection v)
          (gramOperator J (w : V)) := by
      exact gramOperator_isSymmetric J _ _
    _ = 0 := S.starProjection_inner_eq_zero v _ hRw

/-! ## Stable pivot projections -/

/-- The inclusion restricted to an energy trial space. -/
def includedTrial
    (J : V →L[ℝ] H) (S : Submodule ℝ V) : S →L[ℝ] H :=
  J.domRestrict S

/-- The image of an energy trial space in the pivot space. -/
def pivotTrialSpace
    (J : V →L[ℝ] H) (S : Submodule ℝ V) : Submodule ℝ H :=
  (includedTrial J S).toLinearMap.range

/-- Construct a norm-one stable trial projection when the energy-orthogonal
residual is also pivot-orthogonal to the trial space. -/
def stableTrialProjectionOfCompatibility
    (T : GelfandTriple (V := V) (H := H))
    (S : Submodule ℝ V) [FiniteDimensional ℝ S]
    (hcompat : ∀ (v : V) (w : S),
      inner ℝ
        (T.inclusion (v - S.starProjection v))
        (T.inclusion (w : V)) = 0) :
    StableTrialProjection T S 1 := by
  letI : CompleteSpace S := FiniteDimensional.complete ℝ S
  let J := T.inclusion
  let jS := includedTrial J S
  let W : Submodule ℝ H := pivotTrialSpace J S
  have hjS : Function.Injective jS :=
    T.injective.comp Subtype.val_injective
  have hWfd : FiniteDimensional ℝ W := by
    dsimp [W, pivotTrialSpace]
    exact LinearMap.finiteDimensional_range jS.toLinearMap
  letI : FiniteDimensional ℝ W := hWfd
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  let e : S ≃L[ℝ] W :=
    jS.equivRange hjS W.closed_of_finiteDimensional
  let P : H →L[ℝ] S :=
    e.symm.toContinuousLinearMap.comp W.orthogonalProjectionOnto
  have hPcoe (h : H) :
      J ((P h : S) : V) = W.starProjection h := by
    change ((e (P h) : W) : H) = W.starProjection h
    rw [show P h = e.symm (W.orthogonalProjectionOnto h) by rfl]
    rw [e.apply_symm_apply]
    rfl
  have hfix (w : S) : P (J (w : V)) = w := by
    apply Subtype.ext
    apply T.injective
    rw [hPcoe]
    exact W.starProjection_eq_self_iff.mpr ⟨w, rfl⟩
  have hpivot (w : S) (h : H) :
      inner ℝ (J (w : V)) (h - J (P h : V)) = 0 := by
    rw [hPcoe, real_inner_comm]
    exact W.starProjection_inner_eq_zero h _ ⟨w, rfl⟩
  have henergy (v : V) :
      P (J v) = S.orthogonalProjectionOnto v := by
    apply Subtype.ext
    apply T.injective
    rw [hPcoe]
    apply W.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨S.orthogonalProjectionOnto v, rfl⟩
    · intro y hy
      obtain ⟨w, rfl⟩ := hy
      simpa [J, includedTrial, map_sub] using hcompat v w
  exact
    { projection := P
      fixes := hfix
      pivotOrthogonal := hpivot
      norm_le := fun v ↦ by
        rw [henergy]
        simpa using S.norm_orthogonalProjectionOnto_apply_le v }

/-- Compact Gram spectral spaces carry pivot-orthogonal trial projections
with energy stability constant one. -/
def stableTrialProjectionThreshold
    (T : GelfandTriple (V := V) (H := H))
    (hcompact : IsCompactOperator T.inclusion) (m : ℕ) :
    StableTrialProjection T
      (thresholdSpace (gramOperator T.inclusion) m) 1 := by
  let hGramCompact :=
    isCompactOperator_gramOperator T.inclusion hcompact
  letI : FiniteDimensional ℝ
      (thresholdSpace (gramOperator T.inclusion) m) :=
    finiteDimensional_thresholdSpace
      (gramOperator T.inclusion) hGramCompact m
  letI : CompleteSpace
      (thresholdSpace (gramOperator T.inclusion) m) :=
    FiniteDimensional.complete ℝ _
  exact stableTrialProjectionOfCompatibility T
    (thresholdSpace (gramOperator T.inclusion) m)
    (threshold_residual_pivot_orthogonal T.inclusion m)

/-- The canonical stable spectral Galerkin system associated to a compact
Gelfand inclusion. Its trial spaces are the threshold spaces of the compact
Gram operator `J†J`. -/
def gramSpectralGalerkinSystem
    (T : GelfandTriple (V := V) (H := H))
    (hcompact : IsCompactOperator T.inclusion) :
    StableTrialSystem T := by
  let R := gramOperator T.inclusion
  have hRcompact : IsCompactOperator R := by
    simpa [R] using isCompactOperator_gramOperator T.inclusion hcompact
  have hRsymmetric : (R : Module.End ℝ V).IsSymmetric := by
    simpa [R] using gramOperator_isSymmetric T.inclusion
  have hRinjective : Function.Injective R := by
    simpa [R] using gramOperator_injective T.inclusion T.injective
  exact
    { space := thresholdSpace R
      finiteDimensional := fun m ↦
        finiteDimensional_thresholdSpace R hRcompact m
      stabilityConstant := 1
      projection := fun m ↦ by
        simpa [R] using stableTrialProjectionThreshold T hcompact m
      denseEnergy :=
        eventually_approximable_thresholdSpace
          R hRcompact hRsymmetric hRinjective }

end PDE.Analysis.Evolution
