/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Compactness.AubinLions.TemporalCompactness
public import PDE.Analysis.Operator.CompactConvergence
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Trajectory compactness from fixed tests

A uniformly bounded family in a real Hilbert space becomes equicontinuous after a
compact linear observation if its scalar pairings with every vector in a dense test
family are equicontinuous. On a compact time domain this gives precompactness in the
uniform norm of the observed trajectories.

For a sequence of Galerkin trajectories, each fixed test needs a common time modulus
only after some index. The finitely many earlier curves are handled by their individual
continuity. The modulus and the first admissible index may both depend on the test.
Thus the scalar estimates can come from eventual inclusion of a regular test in nested
trials, without a uniform norm bound for the drift in the Hilbert space or its dual.

The proof combines Hilbert weak compactness with the compact-operator upgrade from weak
to strong convergence, then applies Mathlib's Arzelà–Ascoli theorem. Compact containment
in the observed space is derived from the energy bound and the compact operator;
compact containment in the original Hilbert space is not needed.

For a separable Hilbert pivot, `exists_subsequence_tendstoUniformly_pairings` constructs
one weakly continuous trajectory limit with the same energy bound. Every fixed scalar
pairing converges uniformly along this subsequence. The proof first extracts limits for
a countable dense set of pairings, then identifies their pointwise weak state.
`tendstoUniformly_compactOperator_of_dense_pairings` upgrades this same subsequence under
any compact observation, so different spatial cutoffs do not require different limits.

`exists_subsequence_tendstoUniformly_pairings_family` makes the same extraction on
countably many compact domains at once. This lets an exhaustion by compact time
intervals share one subsequence, with an energy bound and test moduli for each interval.

`StableTrialSystem.exists_uniform_subsequence_of_pairing_integrals` specializes the
result to a Galerkin trial system. Trial density supplies the dense tests;
scalar integral identities and per-test L² bounds supply their time moduli. The bounds
need not combine into a norm bound on a dual-valued derivative.

The compact spatial observation and the scalar time estimates are hypotheses.
-/

@[expose] public section

noncomputable section


open Filter Set
open scoped Topology BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem tendsto_compactOperator_of_dense_pairings
    (J : H →L[ℝ] E) (hJ : IsCompactOperator J)
    (test : R → H) (htest : DenseRange test)
    {ι : Type*} {l : Filter ι} {u : ι → H} {uLimit : H}
    (hbounded : Bornology.IsBounded (range u))
    (hpair : ∀ r, Tendsto (fun i ↦ inner ℝ (test r) (u i)) l
      (𝓝 (inner ℝ (test r) uLimit))) :
    Tendsto (fun i ↦ J (u i)) l (𝓝 (J uLimit)) := by
  have hcompact := hJ.isCompact_closure_image_of_bounded
    (f := J.toLinearMap) hbounded
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun i ↦ subset_closure ⟨u i, mem_range_self i, rfl⟩)
  intro y _ hy
  obtain ⟨U, hU, hyU⟩ := mapClusterPt_iff_ultrafilter.mp hy
  obtain ⟨w, V, hV, hw⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
      (U : Filter ι) u hbounded
  have hp : ∀ r, inner ℝ (test r) w = inner ℝ (test r) uLimit := by
    intro r
    have hwr : Tendsto (fun i ↦ inner ℝ (test r) (u i)) V
        (𝓝 (inner ℝ (test r) w)) := by
      simpa only [LinearEquiv.symm_apply_apply, innerSL_apply_apply] using
        WeakCompactness.tendsto_evaluation hw (innerSL ℝ (test r))
    exact tendsto_nhds_unique hwr ((hpair r).mono_left (hV.trans hU))
  have hwu : w = uLimit := by
    apply ext_inner_left ℝ
    have heq := htest.equalizer
      (g := fun v ↦ inner ℝ v w) (h := fun v ↦ inner ℝ v uLimit)
      (by fun_prop) (by fun_prop) (funext hp)
    exact congrFun heq
  have hstrong := tendsto_compactOperator_of_tendsto_weak_of_bounded J hJ hbounded hw
  rw [hwu] at hstrong
  exact tendsto_nhds_unique (hyU.mono_left hV) hstrong

/-- Uniform dense scalar convergence of bounded trajectories upgrades to uniform convergence
under a compact linear observation. The limit need not be norm-continuous. -/
theorem tendstoUniformly_compactOperator_of_dense_pairings
    {ι X : Type*} {l : Filter ι}
    (J : H →L[ℝ] E) (hJ : IsCompactOperator J)
    (test : R → H) (htest : DenseRange test)
    (u : ι → X → H) (uLimit : X → H) (M : ℝ)
    (hbound : ∀ i x, ‖u i x‖ ≤ M) (hlimitBound : ∀ x, ‖uLimit x‖ ≤ M)
    (hpair : ∀ r, TendstoUniformly (fun i x ↦ inner ℝ (test r) (u i x))
      (fun x ↦ inner ℝ (test r) (uLimit x)) l) :
    TendstoUniformly (fun i x ↦ J (u i x)) (fun x ↦ J (uLimit x)) l := by
  let v : ι × X → H := fun p ↦ u p.1 p.2 - uLimit p.2
  have hv : Bornology.IsBounded (range v) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨2 * M, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hbound p.1 p.2, hlimitBound p.2])
  have hvpair : ∀ r, Tendsto (fun p ↦ inner ℝ (test r) (v p))
      (l ×ˢ (⊤ : Filter X)) (𝓝 (inner ℝ (test r) (0 : H))) := by
    intro r
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply Filter.mem_prod_top.mpr
    filter_upwards [(Metric.tendstoUniformly_iff.mp (hpair r)) ε hε] with i hi
    intro x
    simpa only [v, inner_sub_right, inner_zero_right, dist_zero_right, Real.norm_eq_abs,
      Real.dist_eq, abs_sub_comm] using hi x
  have hvstrong := tendsto_compactOperator_of_dense_pairings J hJ test htest hv hvpair
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hεv := Filter.mem_prod_top.mp ((Metric.tendsto_nhds.mp hvstrong) ε hε)
  filter_upwards [hεv] with i hi
  intro x
  rw [dist_comm, dist_eq_norm]
  simpa only [v, map_sub, map_zero, dist_zero_right] using hi x

/-- A compact observation of a uniformly bounded Hilbert-space family is equicontinuous
when all pairings with a dense family of fixed test vectors are equicontinuous.
The unobserved curves need not be strongly continuous. -/
theorem equicontinuous_compactOperator_of_dense_pairings
    {ι X : Type*} [TopologicalSpace X]
    (J : H →L[ℝ] E) (hJ : IsCompactOperator J)
    (test : R → H) (htest : DenseRange test)
    (u : ι → X → H) (M : ℝ) (hbound : ∀ i x, ‖u i x‖ ≤ M)
    (hpair : ∀ r, Equicontinuous (fun i x ↦ inner ℝ (test r) (u i x))) :
    Equicontinuous (fun i x ↦ J (u i x)) := by
  intro x
  let v : X × ι → H := fun p ↦ u p.2 p.1 - u p.2 x
  have hv : Bornology.IsBounded (range v) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨2 * M, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (norm_sub_le _ _).trans (by linarith [hbound p.2 p.1, hbound p.2 x])
  have hvpair : ∀ r, Tendsto (fun p ↦ inner ℝ (test r) (v p))
      (𝓝 x ×ˢ (⊤ : Filter ι)) (𝓝 (inner ℝ (test r) (0 : H))) := by
    intro r
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply Filter.mem_prod_top.mpr
    filter_upwards [(Metric.equicontinuousAt_iff_right.mp (hpair r x)) ε hε] with y hy
    intro i
    simpa only [v, inner_sub_right, inner_zero_right, dist_zero_right, Real.norm_eq_abs,
      Real.dist_eq, abs_sub_comm] using hy i
  have hvstrong := tendsto_compactOperator_of_dense_pairings J hJ test htest hv hvpair
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hεv := (Metric.tendsto_nhds.mp hvstrong) ε hε
  have hεv' := Filter.mem_prod_top.mp hεv
  filter_upwards [hεv'] with y hy
  intro i
  rw [dist_comm, dist_eq_norm]
  simpa only [v, map_sub, map_zero, dist_zero_right] using hy i

private theorem equicontinuous_of_equicontinuous_tail
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    (f : ℕ → X → Y) (hf : ∀ n, Continuous (f n)) (N : ℕ)
    (htail : Equicontinuous (fun n : Ici N ↦ f n.val)) :
    Equicontinuous f := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hearly : ∀ᶠ y in 𝓝 x, ∀ n ∈ Finset.range N, dist (f n x) (f n y) < ε := by
    apply (Finset.range N).eventually_all.mpr
    intro n _
    filter_upwards [(Metric.tendsto_nhds.mp (hf n).continuousAt) ε hε] with y hy
    simpa only [dist_comm] using hy
  filter_upwards [hearly, (Metric.equicontinuousAt_iff_right.mp (htail x)) ε hε] with y hy ht
  intro n
  by_cases hn : n < N
  · exact hy n (Finset.mem_range.mpr hn)
  · exact ht ⟨n, Nat.le_of_not_gt hn⟩

/-- A uniformly energy-bounded sequence is precompact in the uniform norm after a compact
linear observation if each fixed dense test sees an equicontinuous tail of the sequence.
The tail index and time modulus may depend on the test. No common dual bound on these
scalar estimates is required, and the observed space need not be complete. -/
theorem isCompact_closure_range_compactOperator_of_eventually_equicontinuous_pairings
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (J : H →L[ℝ] E) (hJ : IsCompactOperator J)
    (test : R → H) (htest : DenseRange test)
    (u : ℕ → X →ᵇ H) (M : ℝ) (hbound : ∀ n x, ‖u n x‖ ≤ M)
    (hpair : ∀ r, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun x ↦ inner ℝ (test r) (u n.val x))) :
    IsCompact (closure (range (fun n ↦ (u n).comp J J.lipschitzWith))) := by
  let K := closure (J '' Metric.closedBall (0 : H) M)
  have hK : IsCompact K := hJ.isCompact_closure_image_closedBall M
  have hequi := equicontinuous_compactOperator_of_dense_pairings
    J hJ test htest (fun n x ↦ u n x) M hbound (fun r ↦ by
      obtain ⟨N, hN⟩ := hpair r
      exact equicontinuous_of_equicontinuous_tail
        (fun n x ↦ inner ℝ (test r) (u n x)) (fun n ↦ by fun_prop) N hN)
  apply BoundedContinuousFunction.arzela_ascoli K hK
  · rintro f x ⟨n, rfl⟩
    exact subset_closure ⟨u n x, by simpa using hbound n x, rfl⟩
  · let chooseIndex : range (fun n ↦ (u n).comp J J.lipschitzWith) → ℕ :=
      fun f ↦ Classical.choose f.property
    have hindex : ∀ f : range (fun n ↦ (u n).comp J J.lipschitzWith),
        (u (chooseIndex f)).comp J J.lipschitzWith = f.val :=
      fun f ↦ Classical.choose_spec f.property
    convert hequi.comp chooseIndex using 1
    ext f x
    exact congrArg (fun g : X →ᵇ E ↦ g x) (hindex f).symm

/-- Fixed-test equicontinuity on countably many compact domains yields one
subsequence with uniformly convergent Hilbert pairings on every domain. Each
limit is weakly continuous and retains that domain's energy bound. The scalar
time estimates need only hold eventually, with the first index and modulus
allowed to depend on both the domain and the test. -/
theorem exists_subsequence_tendstoUniformly_pairings_family
    [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (X : I → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (test : R → H) (htest : DenseRange test)
    (u : ℕ → ∀ i, X i →ᵇ H) (M : I → ℝ)
    (hbound : ∀ n i x, ‖u n i x‖ ≤ M i)
    (hpair : ∀ i r, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun x ↦ inner ℝ (test r) (u n.val i x))) :
    ∃ uLimit : ∀ i, X i → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i x, ‖uLimit i x‖ ≤ M i) ∧
      (∀ i, Continuous (fun x ↦ toWeakSpace ℝ H (uLimit i x))) ∧
      ∀ i (v : H), TendstoUniformly (fun n x ↦ inner ℝ v (u (φ n) i x))
        (fun x ↦ inner ℝ v (uLimit i x)) atTop := by
  let d : ℕ → H := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  let obs (n : ℕ) (ik : I × ℕ) : X ik.1 →ᵇ ℝ :=
    (u n ik.1).comp (innerSL ℝ (d ik.2)) (innerSL ℝ (d ik.2)).lipschitzWith
  let K (ik : I × ℕ) : Set (X ik.1 →ᵇ ℝ) := closure (range (fun n ↦ obs n ik))
  have hK (ik : I × ℕ) : IsCompact (K ik) :=
    isCompact_closure_range_compactOperator_of_eventually_equicontinuous_pairings
      (innerSL ℝ (d ik.2)) (isCompactOperator_of_locallyCompactSpace_dom _)
      test htest (fun n ↦ u n ik.1) (M ik.1)
      (fun n x ↦ hbound n ik.1 x) (hpair ik.1)
  obtain ⟨p, _, φ, hφ, hp⟩ := (isCompact_univ_pi hK).tendsto_subseq
    (x := obs) (fun n ik _ ↦ subset_closure (mem_range_self n))
  have hpU (i : I) (k : ℕ) : TendstoUniformly
      (fun n x ↦ inner ℝ (d k) (u (φ n) i x)) (p (i, k)) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (tendsto_pi_nhds.mp hp (i, k))
  have hstate (i : I) (x : X i) :
      ∃ w : H, ‖w‖ ≤ M i ∧ ∀ k, inner ℝ (d k) w = p (i, k) x := by
    have hb : Bornology.IsBounded (range (fun n ↦ u (φ n) i x)) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨M i, ?_⟩
      rintro _ ⟨n, rfl⟩
      exact hbound (φ n) i x
    obtain ⟨w, V, hV, hw⟩ :=
      WeakCompactness.exists_ultrafilter_tendsto_weak_of_isBounded_range_filter
        atTop (fun n ↦ u (φ n) i x) hb
    refine ⟨w, ?_, ?_⟩
    · simpa only [LinearEquiv.symm_apply_apply] using
        WeakCompactness.norm_le_of_tendsto_of_norm_le hw
          (Eventually.of_forall fun n ↦ hbound (φ n) i x)
    · intro k
      have hweak : Tendsto (fun n ↦ inner ℝ (d k) (u (φ n) i x)) V
          (𝓝 (inner ℝ (d k) w)) := by
        simpa only [LinearEquiv.symm_apply_apply, innerSL_apply_apply] using
          WeakCompactness.tendsto_evaluation hw (innerSL ℝ (d k))
      exact tendsto_nhds_unique hweak (((hpU i k).tendsto_at x).mono_left hV)
  choose uLimit hlimitBound hlimitPair using hstate
  have hdU (i : I) (k : ℕ) : TendstoUniformly
      (fun n x ↦ inner ℝ (d k) (u (φ n) i x))
      (fun x ↦ inner ℝ (d k) (uLimit i x)) atTop := by
    simpa only [hlimitPair] using hpU i k
  have heval (i : I) (ell : H →L[ℝ] ℝ) : TendstoUniformly
      (fun n x ↦ ell (u (φ n) i x)) (fun x ↦ ell (uLimit i x)) atTop :=
    tendstoUniformly_compactOperator_of_dense_pairings
      ell (isCompactOperator_of_locallyCompactSpace_dom _) d hd
      (fun n x ↦ u (φ n) i x) (uLimit i) (M i)
      (fun n x ↦ hbound (φ n) i x) (hlimitBound i) (hdU i)
  refine ⟨uLimit, φ, hφ, hlimitBound, ?_, fun i v ↦ heval i (innerSL ℝ v)⟩
  intro i
  apply WeakBilin.continuous_of_continuous_eval
  intro ell
  change Continuous (fun x ↦ ell (uLimit i x))
  exact (heval i ell).continuous
    (Eventually.of_forall fun n ↦ ell.continuous.comp (u (φ n) i).continuous).frequently

/-- A bounded sequence with eventual fixed-test time moduli in a separable Hilbert space
has one weakly continuous, energy-bounded trajectory limit. The same subsequence converges
uniformly after pairing with every fixed vector. -/
theorem exists_subsequence_tendstoUniformly_pairings
    [TopologicalSpace.SeparableSpace H]
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (test : R → H) (htest : DenseRange test)
    (u : ℕ → X →ᵇ H) (M : ℝ) (hbound : ∀ n x, ‖u n x‖ ≤ M)
    (hpair : ∀ r, ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun x ↦ inner ℝ (test r) (u n.val x))) :
    ∃ uLimit : X → H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ x, ‖uLimit x‖ ≤ M) ∧
      Continuous (fun x ↦ toWeakSpace ℝ H (uLimit x)) ∧
      ∀ v : H, TendstoUniformly (fun n x ↦ inner ℝ v (u (φ n) x))
        (fun x ↦ inner ℝ v (uLimit x)) atTop := by
  obtain ⟨v, φ, hφ, hM, hc, hv⟩ :=
    exists_subsequence_tendstoUniformly_pairings_family (fun _ : Unit ↦ X)
      test htest (fun n _ ↦ u n) (fun _ ↦ M)
      (fun n _ x ↦ hbound n x) (fun _ ↦ hpair)
  exact ⟨v (), φ, hφ, hM (), hc (), hv ()⟩

open MeasureTheory

/-- The pivot images of all finite trial spaces of a stable trial system are dense. -/
theorem StableTrialSystem.denseRange_inclusion_sigma
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : GelfandTriple (V := V) (H := H)} (trials : StableTrialSystem T) :
    DenseRange (fun v : Σ k, trials.space k ↦ T.inclusion (v.2 : V)) := by
  rw [Metric.denseRange_iff]
  intro x ε hε
  obtain ⟨k, v, hv⟩ := (trials.densePivot x ε hε).exists
  exact ⟨⟨k, v⟩, by simpa only [dist_eq_norm] using hv⟩

/-- A scalar integral identity with an eventually uniform L² right-hand side makes the
pairings of a trajectory sequence with a fixed trial test eventually equicontinuous:
the square root of the time increment is a common modulus of continuity. -/
theorem StableTrialSystem.equicontinuous_pairing_of_integral
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : GelfandTriple (V := V) (H := H)} (trials : StableTrialSystem T)
    {a b : ℝ} (u : ℕ → Icc a b →ᵇ H)
    (hpair : ∀ k (v : trials.space k),
      ∃ g : ℕ → Lp ℝ 2 (volume.restrict (Ioc a b)), ∃ C : ℝ,
        (∀ n, k ≤ n → ‖g n‖ ≤ C) ∧
        ∀ n, k ≤ n → ∀ s t : Icc a b,
          inner ℝ (T.inclusion (v : V)) (u n t) -
            inner ℝ (T.inclusion (v : V)) (u n s) =
          ∫ r in (s : ℝ)..(t : ℝ), g n r)
    (v : Σ k, trials.space k) :
    ∃ N : ℕ, Equicontinuous
      (fun n : Ici N ↦ fun t ↦ inner ℝ (T.inclusion (v.2 : V)) (u n.val t)) := by
  obtain ⟨g, C, hg, hint⟩ := hpair v.1 v.2
  refine ⟨v.1, ?_⟩
  apply Metric.equicontinuous_of_continuity_modulus (fun r ↦ √r * C)
  · simpa using (Real.continuous_sqrt.tendsto 0).mul_const C
  · intro s t n
    have hnorm := norm_intervalIntegral_coeFn_L2_restrict_Ioc_le
      (g n.val) s.property t.property
    have hsub : |inner ℝ (T.inclusion (v.2 : V)) (u n.val s) -
        inner ℝ (T.inclusion (v.2 : V)) (u n.val t)| ≤ √|(t : ℝ) - s| * C := by
      rw [abs_sub_comm, hint n.val n.property s t]
      have hnorm' : |∫ r in (s : ℝ)..(t : ℝ), g n.val r| ≤
          √|(t : ℝ) - s| * ‖g n.val‖ := by
        simpa only [Real.norm_eq_abs] using hnorm
      exact hnorm'.trans
        (mul_le_mul_of_nonneg_left (hg n.val n.property) (Real.sqrt_nonneg _))
    simpa only [Real.dist_eq, Subtype.dist_eq, abs_sub_comm] using hsub

/-- A uniformly energy-bounded Galerkin sequence has a uniformly convergent subsequence
after a compact observation when every fixed trial test has a scalar integral identity
and a uniform L² bound for its scalar right-hand side, from its inclusion index onward.
Both the scalar right-hand side and its bound may depend on the test. No norm bound for
a full dual-valued derivative is required. The limit is asserted only in the observed
space; identifying its nonlinear equation is a separate step. -/
theorem StableTrialSystem.exists_uniform_subsequence_of_pairing_integrals
    {V H E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : GelfandTriple (V := V) (H := H)}
    (trials : StableTrialSystem T)
    (J : H →L[ℝ] E) (hJ : IsCompactOperator J)
    {a b : ℝ} (u : ℕ → Icc a b →ᵇ H) (M : ℝ)
    (hbound : ∀ n t, ‖u n t‖ ≤ M)
    (hpair : ∀ k (v : trials.space k),
      ∃ g : ℕ → Lp ℝ 2 (volume.restrict (Ioc a b)), ∃ C : ℝ,
        (∀ n, k ≤ n → ‖g n‖ ≤ C) ∧
        ∀ n, k ≤ n → ∀ s t : Icc a b,
          inner ℝ (T.inclusion (v : V)) (u n t) -
            inner ℝ (T.inclusion (v : V)) (u n s) =
          ∫ r in (s : ℝ)..(t : ℝ), g n r) :
    ∃ limit : Icc a b →ᵇ E, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n ↦ (u (φ n)).comp J J.lipschitzWith)
        atTop (𝓝 limit) := by
  have hcompact := isCompact_closure_range_compactOperator_of_eventually_equicontinuous_pairings
    J hJ _ trials.denseRange_inclusion_sigma u M hbound
    (trials.equicontinuous_pairing_of_integral u hpair)
  obtain ⟨limit, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  exact ⟨limit, φ, hφ, hlim⟩

end PDE.Analysis.Evolution
