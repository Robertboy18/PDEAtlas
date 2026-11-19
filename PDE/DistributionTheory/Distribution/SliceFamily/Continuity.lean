/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.SliceFamily.Basic

/-!
# Continuity estimates for distribution-valued fiber slices

`PDE.DistributionTheory.Distribution.SliceFamily.Basic` shows that for a distribution `T` on `F`
and a test function `Φ` on `E × F`, the slice family `x ↦ ⟨T, Φ(x, ·)⟩` is a test function on
`E`. We prove that the map `Φ ↦ (x ↦ ⟨T, Φ(x, ·)⟩)` is continuous on each fixed
compact-support stage, which is the estimate needed to make it a continuous linear map of LF
spaces (assembled in `PDE.DistributionTheory.Distribution.SliceFamily`).

Fix a compact `K ⊆ E × F` with projections `K₁ ⊆ E` and
`K₂ ⊆ F`. By `Distribution.exists_norm_restrictToSupportedIn_le_supSeminorm`, the restriction
of `T` to `𝓓_{K₂}(F)` has finite order: `‖⟨T, ψ⟩‖ ≤ C · max_{j ≤ k} ‖D^j ψ‖_∞`. Since the
`n`-th derivative of the slice family in directions `m₁, …, mₙ` is `⟨T, (∂_{(m,0)}^n Φ)(x, ·)⟩`,
one gets, for `Φ ∈ 𝓓_K(E × F)`,

`‖D^n ⟨T, Φ(x, ·)⟩‖ ≤ C · max_{j ≤ n + k} ‖D^j Φ‖_∞`,

so the slice map is continuous from `𝓓_K(E × F)` to `𝓓_{K₁}(E, G)` and loses `k` derivatives.
This is the standard argument in the construction of tensor products of distributions; see
Hörmander, Chapter V.

## Main results

* `applyDistributionToSliceRightSupportedCLM`: for each compact `K`, the slice map
  `𝓓_K(E × F, ℝ) →L[ℝ] 𝓓_{K₁}(E, G)` with the bound above.

## Implementation notes

The remaining declarations are private: the identification of iterated directional
derivatives of test functions with `iteratedFDeriv`, bundled versions of directional derivatives
and of slicing on fixed-support stages, and the seminorm comparison
`supSeminorm_sliceRight_iteratedLineDerivSupported_le` that bounds the `k`-th order seminorm of a
sliced derivative by the `(n + k)`-th order seminorm of `Φ` times `∏ ‖mⱼ‖`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter V, "Distributions in Product Spaces".
  <https://doi.org/10.1007/978-3-642-61497-2_6>
-/

@[expose] public section

open Function Set TopologicalSpace
open scoped CompactConvergenceCLM Distributions

noncomputable section

namespace TestFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

section Continuity

open LineDeriv

private theorem lineDerivOp_apply_testFunction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (v : E) (f : 𝓓((⊤ : Opens E), H)) (x : E) :
    ∂_{v} f x = lineDeriv ℝ f x v := by
  change (lineDerivCLM ℝ v f : 𝓓((⊤ : Opens E), H)) x =
    lineDeriv ℝ f x v
  exact lineDerivCLM_apply_of_le (by simp)

private theorem iteratedLineDerivOp_eq_iteratedFDeriv_testFunction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : ℕ} (m : Fin n → E) (f : 𝓓((⊤ : Opens E), H)) (x : E) :
    ∂^{m} f x = iteratedFDeriv ℝ n (fun z : E ↦ f z) x m := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedFDeriv_succ_apply_left,
      ← fderiv_continuousMultilinear_apply_const_apply]
    · simp only [lineDerivOp_apply_testFunction, ← ih]
      exact
        ((∂^{Fin.tail m} f : 𝓓((⊤ : Opens E), H)).contDiff.differentiable
          (by simp)).differentiableAt.lineDeriv_eq_fderiv
    · exact
        (f.contDiff.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x

private theorem iteratedLineDerivOp_applyDistributionToSliceRight
    [FiniteDimensional ℝ E]
    {n : ℕ} (m : Fin n → E)
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    ∂^{m} (applyDistributionToSliceRight T Φ) =
      applyDistributionToSliceRight T
        (∂^{fun i ↦ (m i, (0 : F))} Φ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, ih]
    change
      lineDerivCLM ℝ (m 0)
          (applyDistributionToSliceRight T
            (∂^{fun i ↦ (Fin.tail m i, (0 : F))} Φ)) =
        applyDistributionToSliceRight T
          (∂^{fun i ↦ (m i, (0 : F))} Φ)
    rw [lineDerivCLM_applyDistributionToSliceRight]
    rw [iteratedLineDerivOp_succ_left]
    rfl

private theorem iteratedFDeriv_applyDistributionToSliceRight_apply
    [FiniteDimensional ℝ E]
    (n : ℕ) (m : Fin n → E)
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) (x : E) :
    iteratedFDeriv ℝ n
        (fun z : E ↦ applyDistributionToSliceRight T Φ z) x m =
      T (sliceRight x (∂^{fun i ↦ (m i, (0 : F))} Φ)) := by
  rw [← iteratedLineDerivOp_eq_iteratedFDeriv_testFunction]
  rw [iteratedLineDerivOp_applyDistributionToSliceRight]
  exact applyDistributionToSliceRight_apply T _ x

private def lineDerivSupportedCLM
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) (v : X) :
    𝓓_{K}(X, H) →L[ℝ] 𝓓_{K}(X, H) :=
  ContDiffMapSupportedIn.postcompCLM
      ((ContinuousLinearMap.apply ℝ H) v) ∘L
    ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤

@[simp]
private theorem lineDerivSupportedCLM_apply
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) (v : X) (f : 𝓓_{K}(X, H)) (x : X) :
    lineDerivSupportedCLM K v f x = fderiv ℝ (fun z : X ↦ f z) x v := by
  change ((ContinuousLinearMap.apply ℝ H) v)
    (fderiv ℝ (fun z : X ↦ f z) x) = _
  rfl

private theorem norm_applyCLM_le
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (v : X) :
    ‖((ContinuousLinearMap.apply ℝ H) v : (X →L[ℝ] H) →L[ℝ] H)‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    ((ContinuousLinearMap.apply ℝ H) v) (norm_nonneg v)
  intro A
  simpa [mul_comm] using A.le_opNorm v

private theorem seminorm_lineDerivSupportedCLM_le
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) (v : X) (i : ℕ) (f : 𝓓_{K}(X, H)) :
    ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K i
        (lineDerivSupportedCLM K v f) ≤
      ‖v‖ * ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K (i + 1) f := by
  calc
    ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K i
        (lineDerivSupportedCLM K v f) ≤
        ‖((ContinuousLinearMap.apply ℝ H) v : (X →L[ℝ] H) →L[ℝ] H)‖ *
          ContDiffMapSupportedIn.seminorm ℝ X (X →L[ℝ] H) ⊤ K i
            (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f) :=
      ContDiffMapSupportedIn.seminorm_postcompLM_le ℝ
        ((ContinuousLinearMap.apply ℝ H) v)
        (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f)
    _ ≤ ‖v‖ *
          ContDiffMapSupportedIn.seminorm ℝ X (X →L[ℝ] H) ⊤ K i
            (ContDiffMapSupportedIn.fderivCLM ℝ ⊤ ⊤ f) := by
      gcongr
      exact norm_applyCLM_le v
    _ = ‖v‖ *
          ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K (i + 1) f := by
      change ‖v‖ *
          ContDiffMapSupportedIn.seminorm ℝ X (X →L[ℝ] H) ⊤ K i
            (ContDiffMapSupportedIn.fderivLM ℝ ⊤ ⊤ f) =
        ‖v‖ *
          ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K (i + 1) f
      rw [ContDiffMapSupportedIn.seminorm_fderivLM_top]

private def iteratedLineDerivSupportedCLM
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) :
    ∀ {n : ℕ}, (Fin n → X) → 𝓓_{K}(X, H) →L[ℝ] 𝓓_{K}(X, H)
  | 0, _ => ContinuousLinearMap.id ℝ _
  | _n + 1, m =>
      lineDerivSupportedCLM K (m 0) ∘L
        iteratedLineDerivSupportedCLM K (Fin.tail m)

@[simp]
private theorem iteratedLineDerivSupportedCLM_zero
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) (m : Fin 0 → X) :
    iteratedLineDerivSupportedCLM (H := H) K m =
      ContinuousLinearMap.id ℝ _ :=
  rfl

private theorem iteratedLineDerivSupportedCLM_succ
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {n : ℕ} (K : Compacts X) (m : Fin (n + 1) → X) :
    iteratedLineDerivSupportedCLM (H := H) K m =
      lineDerivSupportedCLM K (m 0) ∘L
        iteratedLineDerivSupportedCLM K (Fin.tail m) :=
  rfl

private theorem iteratedLineDerivSupportedCLM_apply_eq_iteratedFDeriv
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) :
    ∀ {n : ℕ} (m : Fin n → X) (f : 𝓓_{K}(X, H)) (x : X),
      iteratedLineDerivSupportedCLM K m f x =
        iteratedFDeriv ℝ n (fun z : X ↦ f z) x m := by
  intro n
  induction n with
  | zero =>
      intro m f x
      simp
  | succ n ih =>
      intro m f x
      rw [iteratedLineDerivSupportedCLM_succ,
        iteratedFDeriv_succ_apply_left,
        ← fderiv_continuousMultilinear_apply_const_apply]
      · change fderiv ℝ
          (fun z : X ↦ iteratedLineDerivSupportedCLM K (Fin.tail m) f z)
          x (m 0) = _
        rw [show
          (fun z : X ↦ iteratedLineDerivSupportedCLM K (Fin.tail m) f z) =
            fun z : X ↦
              iteratedFDeriv ℝ n (fun w : X ↦ f w) z (Fin.tail m) by
          funext z
          exact ih (Fin.tail m) f z]
      · exact
          (f.contDiff.differentiable_iteratedFDeriv
            (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n)) x

private theorem seminorm_iteratedLineDerivSupportedCLM_le
    {X H : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (K : Compacts X) :
    ∀ {n : ℕ} (m : Fin n → X) (i : ℕ) (f : 𝓓_{K}(X, H)),
      ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K i
          (iteratedLineDerivSupportedCLM K m f) ≤
        (∏ j, ‖m j‖) *
          ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K (i + n) f := by
  intro n
  induction n with
  | zero =>
      intro m i f
      simp
  | succ n ih =>
      intro m i f
      rw [iteratedLineDerivSupportedCLM_succ]
      calc
        ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K i
            ((lineDerivSupportedCLM K (m 0) ∘L
              iteratedLineDerivSupportedCLM K (Fin.tail m)) f) ≤
            ‖m 0‖ *
              ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K (i + 1)
                (iteratedLineDerivSupportedCLM K (Fin.tail m) f) :=
          seminorm_lineDerivSupportedCLM_le K (m 0) i _
        _ ≤ ‖m 0‖ *
              ((∏ j, ‖Fin.tail m j‖) *
                ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K
                  ((i + 1) + n) f) := by
          gcongr
          exact ih (Fin.tail m) (i + 1) f
        _ = (∏ j, ‖m j‖) *
              ContDiffMapSupportedIn.seminorm ℝ X H ⊤ K
                (i + (n + 1)) f := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.tail]
          ring_nf

/-- The first-coordinate projection of a compact subset of the product. -/
def leftProjectionCompact
    (K : Compacts (E × F)) : Compacts E :=
  ⟨Prod.fst '' (K : Set (E × F)), K.2.image continuous_fst⟩

private def rightProjectionCompact
    (K : Compacts (E × F)) : Compacts F :=
  ⟨Prod.snd '' (K : Set (E × F)), K.2.image continuous_snd⟩

private def sliceRightSupportedInProjection
    (K : Compacts (E × F)) (x : E)
    (φ : 𝓓_{K}(E × F, ℝ)) :
    𝓓_{rightProjectionCompact K}(F, ℝ) where
  toFun := fun y ↦ φ (x, y)
  contDiff' := φ.contDiff.comp (contDiff_const.prodMk contDiff_id)
  zero_on_compl' := by
    intro y hy
    apply φ.zero_on_compl
    simp only [Set.mem_compl_iff]
    intro hxy
    exact hy ⟨(x, y), hxy, rfl⟩

@[simp]
private theorem sliceRightSupportedInProjection_apply
    (K : Compacts (E × F)) (x : E)
    (φ : 𝓓_{K}(E × F, ℝ)) (y : F) :
    sliceRightSupportedInProjection K x φ y = φ (x, y) :=
  rfl

private theorem seminorm_sliceRightSupportedInProjection_le
    (K : Compacts (E × F)) (x : E) (i : ℕ)
    (φ : 𝓓_{K}(E × F, ℝ)) :
    ContDiffMapSupportedIn.seminorm ℝ F ℝ ⊤
        (rightProjectionCompact K) i
        (sliceRightSupportedInProjection K x φ) ≤
      ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K i φ := by
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℝ
    (apply_nonneg _ _) i (sliceRightSupportedInProjection K x φ)).2
  intro y _hy
  change ‖iteratedFDeriv ℝ i
      (fun z : F ↦
        TestFunction.ofSupportedIn
          (Ω := (⊤ : Opens (E × F))) (subset_univ _) φ (x, z)) y‖ ≤ _
  rw [iteratedFDeriv_sliceRight]
  change ‖(iteratedFDeriv ℝ i
      (fun p : E × F ↦
        TestFunction.ofSupportedIn
          (Ω := (⊤ : Opens (E × F))) (subset_univ _) φ p)
        (x, y)).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inr ℝ E F)‖ ≤ _
  apply
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  calc
    ‖iteratedFDeriv ℝ i
        (fun p : E × F ↦
          TestFunction.ofSupportedIn
            (Ω := (⊤ : Opens (E × F))) (subset_univ _) φ p)
          (x, y)‖ *
          ∏ _ : Fin i, ‖ContinuousLinearMap.inr ℝ E F‖ ≤
        ‖iteratedFDeriv ℝ i
          (fun p : E × F ↦
            TestFunction.ofSupportedIn
              (Ω := (⊤ : Opens (E × F))) (subset_univ _) φ p)
            (x, y)‖ * 1 := by
      gcongr
      exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
        (fun _ _ ↦ by
          exact ContinuousLinearMap.norm_inr_le_one ℝ E F)
    _ = ‖iteratedFDeriv ℝ i (fun p : E × F ↦ φ p) (x, y)‖ := by
      rw [mul_one]
      rfl
    _ ≤ ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K i φ :=
      ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ

/-- Applying a distribution to the right slices of a test function supported in `K`, viewed as
a smooth function supported in the projection of `K`. -/
def applyDistributionToSliceRightSupported
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (K : Compacts (E × F))
    (φ : 𝓓_{K}(E × F, ℝ)) :
    𝓓_{leftProjectionCompact K}(E, G) where
  toFun :=
    applyDistributionToSliceRight T
      (TestFunction.ofSupportedIn (subset_univ _) φ)
  contDiff' :=
    (applyDistributionToSliceRight T
      (TestFunction.ofSupportedIn (subset_univ _) φ)).contDiff
  zero_on_compl' := by
    intro x hx
    rw [applyDistributionToSliceRight_apply]
    have hslice :
        sliceRight x (TestFunction.ofSupportedIn (subset_univ _) φ) = 0 := by
      ext y
      change φ (x, y) = 0
      apply φ.zero_on_compl
      simp only [Set.mem_compl_iff]
      intro hxy
      exact hx ⟨(x, y), hxy, rfl⟩
    simp [hslice]

@[simp]
private theorem applyDistributionToSliceRightSupported_apply
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (K : Compacts (E × F))
    (φ : 𝓓_{K}(E × F, ℝ)) (x : E) :
    applyDistributionToSliceRightSupported T K φ x =
      T (sliceRight x (TestFunction.ofSupportedIn (subset_univ _) φ)) :=
  applyDistributionToSliceRight_apply T _ x

private theorem iteratedFDeriv_applyDistributionToSliceRightSupported_apply
    [FiniteDimensional ℝ E]
    (n : ℕ) (m : Fin n → E)
    (T : 𝓓'((⊤ : Opens F), G))
    (K : Compacts (E × F))
    (φ : 𝓓_{K}(E × F, ℝ)) (x : E) :
    iteratedFDeriv ℝ n
        (fun z : E ↦ applyDistributionToSliceRightSupported T K φ z) x m =
      Distribution.restrictToSupportedInCLM T (rightProjectionCompact K)
        (sliceRightSupportedInProjection K x
          (iteratedLineDerivSupportedCLM K
            (fun i ↦ (m i, (0 : F))) φ)) := by
  change
    iteratedFDeriv ℝ n
        (fun z : E ↦
          applyDistributionToSliceRight T
            (TestFunction.ofSupportedIn (subset_univ _) φ) z) x m = _
  rw [iteratedFDeriv_applyDistributionToSliceRight_apply]
  rw [Distribution.restrictToSupportedInCLM_apply]
  congr 1
  ext y
  change
    (∂^{fun i ↦ (m i, (0 : F))}
      (TestFunction.ofSupportedIn (subset_univ _) φ)) (x, y) =
      iteratedLineDerivSupportedCLM K (fun i ↦ (m i, (0 : F))) φ (x, y)
  rw [iteratedLineDerivOp_eq_iteratedFDeriv_testFunction,
    iteratedLineDerivSupportedCLM_apply_eq_iteratedFDeriv]
  rfl

private theorem supSeminorm_sliceRight_iteratedLineDerivSupported_le
    (K : Compacts (E × F)) (x : E)
    {n : ℕ} (m : Fin n → E) (k : ℕ)
    (φ : 𝓓_{K}(E × F, ℝ)) :
    ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤
        (rightProjectionCompact K) k
        (sliceRightSupportedInProjection K x
          (iteratedLineDerivSupportedCLM K
            (fun i ↦ (m i, (0 : F))) φ)) ≤
      (∏ j, ‖m j‖) *
        ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
          (n + k) φ := by
  have hnonneg :
      0 ≤ (∏ j, ‖m j‖) *
        ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
          (n + k) φ :=
    mul_nonneg (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
      (apply_nonneg _ _)
  apply Seminorm.finset_sup_apply_le hnonneg
  intro i hi
  calc
    ContDiffMapSupportedIn.seminorm ℝ F ℝ ⊤
        (rightProjectionCompact K) i
        (sliceRightSupportedInProjection K x
          (iteratedLineDerivSupportedCLM K
            (fun j ↦ (m j, (0 : F))) φ)) ≤
      ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K i
        (iteratedLineDerivSupportedCLM K
          (fun j ↦ (m j, (0 : F))) φ) :=
      seminorm_sliceRightSupportedInProjection_le K x i _
    _ ≤ (∏ j, ‖(m j, (0 : F))‖) *
        ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K
          (i + n) φ :=
      seminorm_iteratedLineDerivSupportedCLM_le K
        (fun j ↦ (m j, (0 : F))) i φ
    _ = (∏ j, ‖m j‖) *
        ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K
          (i + n) φ := by
      simp
    _ ≤ (∏ j, ‖m j‖) *
        ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
          (n + k) φ := by
      apply mul_le_mul_of_nonneg_left _ <|
        Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
      exact Seminorm.le_finset_sup_apply
        (Finset.mem_Iic.2 <| by
          have hik : i ≤ k := Finset.mem_Iic.1 hi
          omega)

/-- Applying a distribution to right slices on one fixed compact-support stage, as a
continuous linear map. -/
def applyDistributionToSliceRightSupportedCLM
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (K : Compacts (E × F)) :
    𝓓_{K}(E × F, ℝ) →L[ℝ]
      𝓓_{leftProjectionCompact K}(E, G) :=
  let Φ : 𝓓_{K}(E × F, ℝ) →ₗ[ℝ]
      𝓓_{leftProjectionCompact K}(E, G) :=
    { toFun := applyDistributionToSliceRightSupported T K
      map_add' := fun φ ψ ↦ ContDiffMapSupportedIn.ext fun x ↦ by
        change
          T (sliceRight x
            (TestFunction.ofSupportedIn (subset_univ _) (φ + ψ))) =
          T (sliceRight x
            (TestFunction.ofSupportedIn (subset_univ _) φ)) +
            T (sliceRight x
              (TestFunction.ofSupportedIn (subset_univ _) ψ))
        rw [← map_add]
        congr 1
      map_smul' := fun c φ ↦ ContDiffMapSupportedIn.ext fun x ↦ by
        change
          T (sliceRight x
            (TestFunction.ofSupportedIn (subset_univ _) (c • φ))) =
          c • T (sliceRight x
            (TestFunction.ofSupportedIn (subset_univ _) φ))
        rw [← map_smul]
        congr 1 }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine WithSeminorms.continuous_of_isBounded
        (ContDiffMapSupportedIn.withSeminorms ℝ (E × F) ℝ ⊤ K)
        (ContDiffMapSupportedIn.withSeminorms ℝ E G ⊤
          (leftProjectionCompact K)) _
        (.of_real fun n ↦ ?_)
      obtain ⟨k, C, _hC, hT⟩ :=
        Distribution.exists_norm_restrictToSupportedIn_le_supSeminorm
          T (rightProjectionCompact K)
      refine ⟨Finset.Iic (n + k), (C : ℝ), fun φ ↦ ?_⟩
      apply ((Φ φ).seminorm_top_le_iff ℝ
        (mul_nonneg C.coe_nonneg (apply_nonneg _ _)) n).2
      intro x _hx
      apply ContinuousMultilinearMap.opNorm_le_bound
        (mul_nonneg C.coe_nonneg (apply_nonneg _ _))
      intro m
      change
        ‖iteratedFDeriv ℝ n
          (fun z : E ↦ applyDistributionToSliceRightSupported T K φ z)
          x m‖ ≤ _
      rw [iteratedFDeriv_applyDistributionToSliceRightSupported_apply]
      calc
        ‖Distribution.restrictToSupportedInCLM T
            (rightProjectionCompact K)
            (sliceRightSupportedInProjection K x
              (iteratedLineDerivSupportedCLM K
                (fun i ↦ (m i, (0 : F))) φ))‖ ≤
            (C : ℝ) *
              ContDiffMapSupportedIn.supSeminorm ℝ F ℝ ⊤
                (rightProjectionCompact K) k
                (sliceRightSupportedInProjection K x
                  (iteratedLineDerivSupportedCLM K
                    (fun i ↦ (m i, (0 : F))) φ)) :=
          hT _
        _ ≤ (C : ℝ) *
            ((∏ j, ‖m j‖) *
              ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
                (n + k) φ) := by
          apply mul_le_mul_of_nonneg_left
            (supSeminorm_sliceRight_iteratedLineDerivSupported_le
              K x m k φ) C.coe_nonneg
        _ = ((C : ℝ) *
              ((Finset.Iic (n + k)).sup
                (ContDiffMapSupportedIn.seminorm ℝ (E × F) ℝ ⊤ K)) φ) *
              ∏ j, ‖m j‖ := by
          change (C : ℝ) * ((∏ j, ‖m j‖) *
              ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
                (n + k) φ) =
            ((C : ℝ) *
              ContDiffMapSupportedIn.supSeminorm ℝ (E × F) ℝ ⊤ K
                (n + k) φ) * ∏ j, ‖m j‖
          ring }

end Continuity

end TestFunction
