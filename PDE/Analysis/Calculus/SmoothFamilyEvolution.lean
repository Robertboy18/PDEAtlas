/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothFamilyIntegral
public import PDE.FDeriv.PartialDeriv

/-!
# Time derivatives of the spatial jets of a smooth family

Let `F s` and `G s` be smooth families of order `m` on an open set of times `J`
(`PDE.Analysis.IsSmoothFamilyOn`): every map is `C^m` and the spatial derivatives of order at
most `m` are jointly continuous in time and space; nothing is assumed about derivatives in time.
If `∂ₛ F(s, y) = G(s, y)` at every point `y` of an open set `U`, then the spatial derivatives
commute with the time derivative on `U`, and the commuted identity extends to the closure of `U`:
for every coordinate word `l` of length at most `m` and every `x ∈ closure U`,
`∂ₛ (∂^l F(s))(x) = (∂^l G(s))(x)` (`IsSmoothFamilyOn.hasDerivAt_iteratedPartialDeriv`).

The proof writes `F(s) = F(r) + ∫ᵣˢ G` on `U`, differentiates under the integral sign on the open
set `U`, and passes to the closure through the continuity of both sides of the integrated
identity. The typical use is an evolution equation `∂ₜf = R` that holds only in an open domain,
where `R` is the restriction of a smooth family defined on the whole space: the time derivatives of
the jets of `f` at boundary points are the jets of the extended right side.

## Main results

* `isSmoothFamilyOn_of_continuousOn`, `IsSmoothFamilyOn.smul_continuousOn`,
  `IsSmoothFamilyOn.comp_time`, `IsSmoothFamilyOn.of_local`,
  `isSmoothFamilyOn_of_continuousOn_iteratedFDeriv`: constructions of smooth families.
* `IsSmoothFamilyOn.eq_add_integral`: the integrated form `F(s) = F(r) + ∫ᵣˢ G` on `U`.
* `IsSmoothFamilyOn.hasDerivAt_fderiv`: one spatial derivative commutes with `∂ₛ` on `U`.
* `IsSmoothFamilyOn.hasDerivAt_of_mem_closure`: the time derivative at points of `closure U`.
* `IsSmoothFamilyOn.iteratedPartialDeriv`,
  `IsSmoothFamilyOn.continuousOn_iteratedPartialDeriv_apply`: coordinate derivatives of a smooth
  family.
* `IsSmoothFamilyOn.hasDerivAt_iteratedPartialDeriv`: the time derivative of a jet.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology Interval

namespace PDE.Analysis

section Constructions

variable {P Q : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] {m : ℕ} {I J : Set ℝ}

/-- A family of constant maps whose value is continuous in time is smooth of every order. -/
theorem isSmoothFamilyOn_of_continuousOn {c : ℝ → Q} (hc : ContinuousOn c I) :
    IsSmoothFamilyOn m (fun r (_ : P) ↦ c r) I := by
  induction m generalizing Q with
  | zero =>
    rw [isSmoothFamilyOn_zero_iff]
    exact hc.comp continuousOn_fst fun q hq ↦ hq.1
  | succ m ih =>
    rw [isSmoothFamilyOn_succ_iff]
    refine ⟨fun r _ ↦ differentiable_const _, hc.comp continuousOn_fst fun q hq ↦ hq.1, ?_⟩
    exact (isSmoothFamilyOn_const (Q := P →L[ℝ] Q) (f := fun (_ : P) ↦ 0) contDiff_const).congr
      fun r _ ↦ by funext p; simp

/-- Scalar multiples of a smooth family by a function continuous in time are smooth. -/
theorem IsSmoothFamilyOn.smul_continuousOn {c : ℝ → ℝ} {F : ℝ → P → Q} (hc : ContinuousOn c I)
    (hF : IsSmoothFamilyOn m F I) : IsSmoothFamilyOn m (fun r p ↦ c r • F r p) I :=
  ((isSmoothFamilyOn_of_continuousOn hc).bilinear (ContinuousLinearMap.lsmul ℝ ℝ) hF).congr
    fun _ _ ↦ rfl

/-- A smooth family composed in time with a continuous map is smooth. -/
theorem IsSmoothFamilyOn.comp_time {F : ℝ → P → Q} {g : ℝ → ℝ} (hF : IsSmoothFamilyOn m F J)
    (hg : ContinuousOn g I) (hgI : MapsTo g I J) :
    IsSmoothFamilyOn m (fun r ↦ F (g r)) I :=
  ⟨fun _ hr ↦ hF.contDiff (hgI hr), fun _ hj ↦ (hF.continuousOn_iteratedFDeriv hj).comp
    ((hg.comp continuousOn_fst fun _ hq ↦ hq.1).prodMk continuousOn_snd)
    fun _ hq ↦ ⟨hgI hq.1, mem_univ _⟩⟩

/-- **Locality in time.** A family that is smooth on a neighbourhood within `I` of every time of
`I` is smooth on `I`. -/
theorem IsSmoothFamilyOn.of_local {F : ℝ → P → Q}
    (h : ∀ r ∈ I, ∃ V : Set ℝ, IsOpen V ∧ r ∈ V ∧ IsSmoothFamilyOn m F (V ∩ I)) :
    IsSmoothFamilyOn m F I := by
  refine ⟨fun r hr ↦ ?_, fun j hj ↦ ?_⟩
  · obtain ⟨V, -, hrV, hV⟩ := h r hr
    exact hV.contDiff ⟨hrV, hr⟩
  · refine continuousOn_of_locally_continuousOn fun q hq ↦ ?_
    obtain ⟨V, hVo, hrV, hV⟩ := h q.1 hq.1
    refine ⟨V ×ˢ univ, hVo.prod isOpen_univ, ⟨hrV, mem_univ _⟩, ?_⟩
    refine (hV.continuousOn_iteratedFDeriv hj).mono fun p hp ↦ ?_
    exact ⟨⟨hp.2.1, hp.1.1⟩, mem_univ _⟩

/-- A field whose slices are `C^m` and whose spatial derivatives of order at most `m` are
continuous on `P × I` is a smooth family of order `m` in its time variable. -/
theorem isSmoothFamilyOn_of_continuousOn_iteratedFDeriv {f : P → ℝ → Q}
    (hf : ∀ r ∈ I, ContDiff ℝ m (fun x ↦ f x r))
    (hj : ∀ j ≤ m, ContinuousOn
      (fun p : P × ℝ ↦ iteratedFDeriv ℝ j (fun y ↦ f y p.2) p.1) (univ ×ˢ I)) :
    IsSmoothFamilyOn m (fun r x ↦ f x r) I :=
  ⟨hf, fun j hjm ↦ (hj j hjm).comp (continuous_snd.prodMk continuous_fst).continuousOn
    fun _ hq ↦ ⟨mem_univ _, hq.1⟩⟩

end Constructions

end PDE.Analysis

namespace PDE.Analysis.IsSmoothFamilyOn

variable {E Q : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Q]
  [NormedSpace ℝ Q] [CompleteSpace Q] {F G : ℝ → E → Q} {J : Set ℝ} {U : Set E} {a b : ℝ}

/-- Every point of an open set of reals is interior to a closed interval inside the set. -/
theorem exists_Icc_subset (hJ : IsOpen J) {r : ℝ} (hr : r ∈ J) :
    ∃ a b : ℝ, r ∈ Ioo a b ∧ Icc a b ⊆ J := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hJ r hr
  refine ⟨r - δ / 2, r + δ / 2, ⟨by linarith, by linarith⟩, fun s hs ↦ hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hs.1, hs.2]

/-- **The integrated form.** If `∂ₛ F(s, y) = G(s, y)` on `U` at the times of `[a, b]` and `G` is
jointly continuous there, then `F(s) = F(r) + ∫ᵣˢ G` on `U` for `r, s ∈ [a, b]`. -/
theorem eq_add_integral (hG : IsSmoothFamilyOn 0 G (Icc a b))
    (hFG : ∀ s ∈ Icc a b, ∀ y ∈ U, HasDerivAt (fun ρ ↦ F ρ y) (G s y) s)
    {r s : ℝ} (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) {y : E} (hy : y ∈ U) :
    F s y = F r y + ∫ ρ in r..s, G ρ y := by
  have hsub : uIcc r s ⊆ Icc a b := uIcc_subset_Icc hr hs
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun ρ ↦ F ρ y)
    (fun ρ hρ ↦ hFG ρ (hsub hρ) y hy)
    ((ODE.continuousOn_slice hG y).mono hsub).intervalIntegrable
  rw [h]
  abel

/-- The interval integral from `r` of a function continuous near `r` has the value of the function
as derivative at `r`. -/
private theorem hasDerivAt_integral_self {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [CompleteSpace R] {φ : ℝ → R} (hφ : ContinuousOn φ (Icc a b)) {r : ℝ} (hr : r ∈ Ioo a b) :
    HasDerivAt (fun s ↦ ∫ ρ in r..s, φ ρ) (φ r) r :=
  intervalIntegral.integral_hasDerivAt_right
    ((hφ.mono (by simp [Ioo_subset_Icc_self hr])).intervalIntegrable)
    ((hφ.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr)
    (hφ.continuousAt (Icc_mem_nhds hr.1 hr.2))

variable [FiniteDimensional ℝ E]

/-- **One spatial derivative commutes with the time derivative.** Let `G` be a smooth family of
order one on an open set of times `J`, let the maps `F s` be differentiable, and let
`∂ₛ F(s, y) = G(s, y)` on the open set `U`. Then `∂ₛ DF(s)(y) = DG(s)(y)` on `U`. -/
theorem hasDerivAt_fderiv (hJ : IsOpen J) (hU : IsOpen U)
    (hF : ∀ s ∈ J, Differentiable ℝ (F s)) (hG : IsSmoothFamilyOn 1 G J)
    (hFG : ∀ s ∈ J, ∀ y ∈ U, HasDerivAt (fun ρ ↦ F ρ y) (G s y) s) {r : ℝ} (hr : r ∈ J)
    {y : E} (hy : y ∈ U) :
    HasDerivAt (fun s ↦ fderiv ℝ (F s) y) (fderiv ℝ (G r) y) r := by
  obtain ⟨a, b, hrab, hab⟩ := exists_Icc_subset hJ hr
  have hG' := hG.mono_set hab
  have hrI : r ∈ Icc a b := Ioo_subset_Icc_self hrab
  have hD : IsSmoothFamilyOn 0 (fun ρ z ↦ fderiv ℝ (G ρ) z) (Icc a b) :=
    (isSmoothFamilyOn_succ_iff.mp hG').2.2
  have key : ∀ s ∈ Icc a b,
      fderiv ℝ (F s) y = fderiv ℝ (F r) y + ∫ ρ in r..s, fderiv ℝ (G ρ) y := by
    intro s hs
    have heq : F s =ᶠ[𝓝 y] fun z ↦ F r z + ∫ ρ in r..s, G ρ z := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact eq_add_integral (hG'.mono (Nat.zero_le 1))
        (fun s' hs' z' hz' ↦ hFG s' (hab hs') z' hz') hrI hs hz
    rw [heq.fderiv_eq]
    exact ((hF r (hab hrI) y).hasFDerivAt.add
      (ODE.hasFDerivAt_integral_of_isSmoothFamilyOn hG' hrI hs y)).fderiv
  have hderiv := (hasDerivAt_integral_self (ODE.continuousOn_slice hD y) hrab).const_add
    (fderiv ℝ (F r) y)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hrab.1 hrab.2] with s hs
  exact key s hs

omit [FiniteDimensional ℝ E] in
/-- `hasDerivAt_of_mem_closure` for a complete target. -/
private theorem hasDerivAt_of_mem_closure_of_complete (hJ : IsOpen J)
    (hF : ∀ s ∈ J, Continuous (F s))
    (hG : IsSmoothFamilyOn 0 G J)
    (hFG : ∀ s ∈ J, ∀ y ∈ U, HasDerivAt (fun ρ ↦ F ρ y) (G s y) s) {r : ℝ} (hr : r ∈ J)
    {x : E} (hx : x ∈ closure U) :
    HasDerivAt (fun s ↦ F s x) (G r x) r := by
  obtain ⟨a, b, hrab, hab⟩ := exists_Icc_subset hJ hr
  have hG' := hG.mono_set hab
  have hrI : r ∈ Icc a b := Ioo_subset_Icc_self hrab
  have key : ∀ s ∈ Icc a b, F s x = F r x + ∫ ρ in r..s, G ρ x := by
    intro s hs
    have hEq : EqOn (F s) (fun z ↦ F r z + ∫ ρ in r..s, G ρ z) U := fun z hz ↦
      eq_add_integral hG' (fun s' hs' z' hz' ↦ hFG s' (hab hs') z' hz') hrI hs hz
    exact hEq.closure (hF s (hab hs)) ((hF r (hab hrI)).add (hG'.continuous_integral hrI hs)) hx
  have hderiv := (hasDerivAt_integral_self (ODE.continuousOn_slice hG' x) hrab).const_add (F r x)
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hrab.1 hrab.2] with s hs
  exact key s hs

omit [FiniteDimensional ℝ E] [CompleteSpace Q] in
/-- **Time derivatives at points of the closure.** Let `G` be jointly continuous on an open set of
times `J`, let the maps `F s` be continuous, and let `∂ₛ F(s, y) = G(s, y)` on `U`. Then
`∂ₛ F(s, x) = G(s, x)` at every point `x` of the closure of `U`. The target need not be
complete: the statement for the completion pulls back along the isometric embedding. -/
theorem hasDerivAt_of_mem_closure (hJ : IsOpen J) (hF : ∀ s ∈ J, Continuous (F s))
    (hG : IsSmoothFamilyOn 0 G J)
    (hFG : ∀ s ∈ J, ∀ y ∈ U, HasDerivAt (fun ρ ↦ F ρ y) (G s y) s) {r : ℝ} (hr : r ∈ J)
    {x : E} (hx : x ∈ closure U) :
    HasDerivAt (fun s ↦ F s x) (G r x) r := by
  let ι : Q →ₗᵢ[ℝ] UniformSpace.Completion Q := UniformSpace.Completion.toComplₗᵢ
  have h := hasDerivAt_of_mem_closure_of_complete (F := fun s y ↦ ι (F s y))
    (G := fun s y ↦ ι (G s y)) hJ (fun s hs ↦ ι.continuous.comp (hF s hs))
    (hG.clm_comp ι.toContinuousLinearMap)
    (fun s hs y hy ↦ ι.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hFG s hs y hy)) hr hx
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  have heq (s : ℝ) : ‖ι (F s x) - ι (F r x) - (s - r) • ι (G r x)‖ =
      ‖F s x - F r x - (s - r) • G r x‖ := by
    rw [← map_smul, ← map_sub, ← map_sub, LinearIsometry.norm_map]
  exact Asymptotics.isLittleO_norm_left.mp
    (by simpa only [heq] using Asymptotics.isLittleO_norm_left.mpr h)

omit [CompleteSpace Q] in
/-- The coordinate derivatives along a word of length `l` of a smooth family of order `m + l` are
a smooth family of order `m`. -/
theorem iteratedPartialDeriv {n m : ℕ} {F : ℝ → ℝ^n → Q} (l : List (Fin n))
    (hF : IsSmoothFamilyOn (m + l.length) F J) :
    IsSmoothFamilyOn m (fun r ↦ PDE.iteratedPartialDeriv l (F r)) J := by
  induction l generalizing m with
  | nil => exact hF.congr fun r _ ↦ rfl
  | cons i rest ih =>
    have h1 := ih (m := m + 1) (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hF)
    have h2 := (isSmoothFamilyOn_succ_iff.mp h1).2.2
    exact (h2.clm_comp (ContinuousLinearMap.apply ℝ Q (EuclideanSpace.single i (1 : ℝ)))).congr
      fun r _ ↦ rfl

omit [CompleteSpace Q] in
/-- A coordinate derivative of a smooth family at a fixed point is continuous in time. -/
theorem continuousOn_iteratedPartialDeriv_apply {n : ℕ} {F : ℝ → ℝ^n → Q} (l : List (Fin n))
    (hF : IsSmoothFamilyOn l.length F J) (x : ℝ^n) :
    ContinuousOn (fun r ↦ PDE.iteratedPartialDeriv l (F r) x) J := by
  rw [← zero_add l.length] at hF
  exact (hF.iteratedPartialDeriv l).continuousOn.comp
    (continuous_id.prodMk continuous_const).continuousOn fun _ hr ↦ ⟨hr, mem_univ _⟩

/-- **The time derivative of a jet.** Let `F` and `G` be smooth families of order `l.length` on an
open set of times `J`, and let `∂ₛ F(s, y) = G(s, y)` on the open set `U`. At every point `x` of
the closure of `U`, the coordinate derivative `∂^l F(s)(x)` along the word `l` has the time
derivative `∂^l G(s)(x)`. -/
theorem hasDerivAt_iteratedPartialDeriv {n : ℕ} {F G : ℝ → ℝ^n → Q} {U : Set (ℝ^n)}
    (l : List (Fin n)) (hJ : IsOpen J) (hU : IsOpen U)
    (hF : IsSmoothFamilyOn l.length F J) (hG : IsSmoothFamilyOn l.length G J)
    (hFG : ∀ s ∈ J, ∀ y ∈ U, HasDerivAt (fun ρ ↦ F ρ y) (G s y) s) {r : ℝ} (hr : r ∈ J)
    {x : ℝ^n} (hx : x ∈ closure U) :
    HasDerivAt (fun s ↦ PDE.iteratedPartialDeriv l (F s) x)
      (PDE.iteratedPartialDeriv l (G r) x) r := by
  have hopen : ∀ (l : List (Fin n)) (m : ℕ), IsSmoothFamilyOn (m + l.length) F J →
      IsSmoothFamilyOn (m + l.length) G J → ∀ s ∈ J, ∀ y ∈ U,
        HasDerivAt (fun ρ ↦ PDE.iteratedPartialDeriv l (F ρ) y)
          (PDE.iteratedPartialDeriv l (G s) y) s := by
    intro l
    induction l with
    | nil => exact fun _ _ _ ↦ hFG
    | cons i rest ih =>
      intro m hFm hGm s hs y hy
      have hlen : m + (i :: rest).length = (m + 1) + rest.length := by
        simp only [List.length_cons]
        omega
      rw [hlen] at hFm hGm
      have hF1 := hFm.iteratedPartialDeriv (m := m + 1) rest
      have hG1 := hGm.iteratedPartialDeriv (m := m + 1) rest
      have hstep := hasDerivAt_fderiv hJ hU
        (fun ρ hρ ↦ (hF1.contDiff hρ).differentiable (by simp)) (hG1.mono (by omega))
        (ih (m + 1) hFm hGm) hs hy
      exact (ContinuousLinearMap.apply ℝ Q (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt
        |>.comp_hasDerivAt s hstep
  rw [← zero_add l.length] at hF hG
  exact hasDerivAt_of_mem_closure hJ
    (fun s hs ↦ ((hF.iteratedPartialDeriv l).contDiff hs).continuous) (hG.iteratedPartialDeriv l)
    (hopen l 0 hF hG) hr hx

end PDE.Analysis.IsSmoothFamilyOn
