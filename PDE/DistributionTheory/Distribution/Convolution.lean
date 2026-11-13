/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.LocalizedPushforward
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier
public import PDE.DistributionTheory.Distribution.TensorProduct
public import PDE.DistributionTheory.TestFunction.SmoothMultiplier
import PDE.DistributionTheory.Distribution.Support.LocalizedPushforward
import PDE.DistributionTheory.Distribution.Support.TensorProduct
public import PDE.DistributionTheory.TestFunction.CompactCutoff -- shake: keep

/-!
# Convolution of compactly carried distributions

For two scalar distributions `S` and `T` on `E` with compact carriers, the convolution `S * T`
is the image of the tensor product `S ⊗ T` on `E × E` under the addition map
`(x, y) ↦ x + y`. Addition need not be proper, so a pushforward along it is not available for
arbitrary distributions. When `S ⊗ T` vanishes outside a compact product set `K × L`, multiplying
by a test-function cutoff `χ` equal to one near `K × L` makes the localized pushforward of
`PDE.DistributionTheory.Distribution.Support.LocalizedPushforward` available, and the result does
not depend on `χ`. This is the standard construction of the convolution of distributions when
one factor has compact support, specialized to the case where both do; see Hörmander,
Chapter IV, or Friedlander and Joshi, Chapter 5.

A compact carrier and a cutoff are auxiliary choices, not part of the convolution's value.
The definition fixes them with `Classical.choose`. Two cutoffs equal to one near the same
carrier differ only where the tensor product distribution vanishes.
`convolution_eq_convolutionWithCutoff_tensorProduct` turns this observation into an equality
for any admissible carriers and normalized product cutoffs. Later computations can therefore
choose them to suit the test function at hand.

## Main results

* `convolutionWithCutoff`: the localized pushforward of `S ⊗ T` along addition for a given cutoff.
* `convolution`: the canonical convolution of two compactly carried distributions.
* `convolution_eq_convolutionWithCutoff_tensorProduct`: cutoff independence.
* `HasCompactCarrier.convolution`: the convolution is again compactly carried.
* `dsupport_convolution_subset_add_image`: the support of `S * T` lies in the Minkowski sum
  `K + L` of carriers of the factors (the theorem of supports, in its inclusion form).
* `convolution_delta_zero_left`, `convolution_delta_delta`: `δ₀ * T = T` and `δₓ * δᵧ = δₓ₊ᵧ`.

## Implementation notes

Carriers are used rather than the support `dsupport` because `HasCompactCarrier` is the
hypothesis that `IsVanishingOn.tensorProduct_compl` and the localized pushforward use
directly. The test-function cutoffs on `E × E` are taken to be tensor products `χ ⊗ ψ` of
cutoffs on `E`, so that only the one-variable cutoff existence theorem
`TestFunction.exists_eq_one_on_compact_finiteDimensional` is needed.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Classics in
  Mathematics, Springer, 2003, Chapter IV, "Convolution".
  <https://doi.org/10.1007/978-3-642-61497-2_5>
* F. G. Friedlander and M. Joshi, *Introduction to the Theory of Distributions*, 2nd ed.,
  Cambridge University Press, 1998, Chapter 5, "Convolution".
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace Distribution

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Addition on the product `E × E`, the map along which convolutions are pushed forward. -/
def addition : E × E → E :=
  fun p ↦ p.1 + p.2

omit [FiniteDimensional ℝ E] in
/-- Addition on `E × E` is smooth. -/
theorem addition_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) (addition : E × E → E) :=
  contDiff_add

/-- Push the localized tensor product of two distributions forward along addition. -/
def convolutionWithCutoff
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (χ : 𝓓((⊤ : Opens (E × E)), ℝ)) :
    𝓓'((⊤ : Opens E), ℝ) :=
  pushforwardLocalizedCLM addition addition_contDiff χ (tensorProduct S T)

/-- A localized convolution acts by testing the tensor product against the cutoff pullback
of the test function along addition. -/
@[simp]
theorem convolutionWithCutoff_apply
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (χ : 𝓓((⊤ : Opens (E × E)), ℝ))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    convolutionWithCutoff S T χ φ =
      tensorProduct S T
        (TestFunction.precompLocalized addition addition_contDiff χ φ) :=
  rfl

/-- A compact carrier chosen for a compactly carried distribution. -/
def chosenCarrier
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T) :
    Set E :=
  Classical.choose hT

omit [FiniteDimensional ℝ E] in
/-- The chosen carrier is compact. -/
theorem chosenCarrier_isCompact
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T) :
    IsCompact (chosenCarrier T hT) :=
  (Classical.choose_spec hT).1

omit [FiniteDimensional ℝ E] in
private theorem isVanishingOn_chosenCarrier_compl
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T) :
    IsVanishingOn T (chosenCarrier T hT)ᶜ :=
  (Classical.choose_spec hT).2

/-- A test function equal to one near the chosen carrier of a compactly carried
distribution. -/
def chosenCutoff
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T) :
    𝓓((⊤ : Opens E), ℝ) :=
  Classical.choose
    (TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ (chosenCarrier_isCompact T hT) (subset_univ _))

private theorem chosenCutoff_eq_one_near
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T)
    (x : E) (hx : x ∈ chosenCarrier T hT) :
    (chosenCutoff T hT : E → ℝ) =ᶠ[𝓝 x] 1 :=
  (Classical.choose_spec
    (TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ (chosenCarrier_isCompact T hT) (subset_univ _))).2.2.1 x hx

omit [FiniteDimensional ℝ E] in
/-- A tensor product of test functions that are locally `1` near `K` and near `L` is locally `1`
near every point of `K ×ˢ L`. -/
theorem tensorProduct_eq_one_near
    {K L : Set E}
    (χ ψ : 𝓓((⊤ : Opens E), ℝ))
    (hχ : ∀ x ∈ K, (χ : E → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ y ∈ L, (ψ : E → ℝ) =ᶠ[𝓝 y] 1)
    (p : E × E) (hp : p ∈ K ×ˢ L) :
    (TestFunction.tensorProduct χ ψ : E × E → ℝ) =ᶠ[𝓝 p] 1 := by
  filter_upwards [(hχ p.1 hp.1).prodMk_nhds (hψ p.2 hp.2)] with q hq
  simp [hq.1, hq.2]

/-- The convolution of two compactly carried scalar distributions. -/
def convolution
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    𝓓'((⊤ : Opens E), ℝ) :=
  convolutionWithCutoff S T
    (TestFunction.tensorProduct (chosenCutoff S hS) (chosenCutoff T hT))

/-- The canonical convolution agrees with every product-cutoff presentation built from compact
carriers of its two factors. -/
theorem convolution_eq_convolutionWithCutoff_tensorProduct
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T)
    {K L : Set E}
    (hK : IsCompact K) (hL : IsCompact L)
    (hSK : IsVanishingOn S Kᶜ)
    (hTL : IsVanishingOn T Lᶜ)
    (χ ψ : 𝓓((⊤ : Opens E), ℝ))
    (hχ : ∀ x ∈ K, (χ : E → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ y ∈ L, (ψ : E → ℝ) =ᶠ[𝓝 y] 1) :
    convolution S T hS hT =
      convolutionWithCutoff S T (TestFunction.tensorProduct χ ψ) := by
  unfold convolution convolutionWithCutoff
  apply pushforwardLocalizedCLM_eq_of_eq_one_near_carriers
    (IsVanishingOn.tensorProduct_compl
      (chosenCarrier_isCompact S hS) (chosenCarrier_isCompact T hT)
      (isVanishingOn_chosenCarrier_compl S hS)
      (isVanishingOn_chosenCarrier_compl T hT))
    (IsVanishingOn.tensorProduct_compl hK hL hSK hTL)
    addition addition_contDiff
  · exact tensorProduct_eq_one_near
      (chosenCutoff S hS) (chosenCutoff T hT)
      (fun x hx ↦ chosenCutoff_eq_one_near S hS x hx)
      (fun y hy ↦ chosenCutoff_eq_one_near T hT y hy)
  · exact tensorProduct_eq_one_near χ ψ hχ hψ

/-- Convolution preserves compact carriers. -/
theorem HasCompactCarrier.convolution
    {S T : 𝓓'((⊤ : Opens E), ℝ)}
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    HasCompactCarrier (_root_.Distribution.convolution S T hS hT) := by
  change HasCompactCarrier
    (_root_.Distribution.pushforwardLocalizedCLM addition addition_contDiff _
      (_root_.Distribution.tensorProduct S T))
  exact (hS.tensorProduct hT).pushforwardLocalizedCLM
    addition addition_contDiff _

/-- If `K` and `L` carry the two factors, then the support of their convolution lies in the
Minkowski sum of `K` and `L`. -/
theorem dsupport_convolution_subset_add_image
    (S T : 𝓓'((⊤ : Opens E), ℝ))
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T)
    {K L : Set E}
    (hK : IsCompact K) (hL : IsCompact L)
    (hSK : IsVanishingOn S Kᶜ)
    (hTL : IsVanishingOn T Lᶜ)
    (χ ψ : 𝓓((⊤ : Opens E), ℝ))
    (hχ : ∀ x ∈ K, (χ : E → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ y ∈ L, (ψ : E → ℝ) =ᶠ[𝓝 y] 1) :
    dsupport (convolution S T hS hT) ⊆
      addition '' (K ×ˢ L) := by
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    S T hS hT hK hL hSK hTL χ ψ hχ hψ]
  exact dsupport_pushforwardLocalizedCLM_subset_image
    (IsVanishingOn.tensorProduct_compl hK hL hSK hTL)
    (hK.prod hL) addition addition_contDiff _

omit [FiniteDimensional ℝ E] in
/-- A Dirac mass has a compact carrier. -/
theorem hasCompactCarrier_delta (x : E) :
    HasCompactCarrier (delta x : 𝓓'((⊤ : Opens E), ℝ)) :=
  ⟨{x}, isCompact_singleton, isVanishingOn_delta x⟩

/-- The Dirac mass at the origin is a left identity for compact-carrier convolution. -/
theorem convolution_delta_zero_left
    (T : 𝓓'((⊤ : Opens E), ℝ))
    (hT : HasCompactCarrier T) :
    convolution (delta 0) T (hasCompactCarrier_delta 0) hT = T := by
  rcases hT with ⟨L, hL, hTL⟩
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ (isCompact_singleton : IsCompact ({0} : Set E))
      (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ hL (subset_univ _)
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    (delta 0) T (hasCompactCarrier_delta 0) ⟨L, hL, hTL⟩
    isCompact_singleton hL (isVanishingOn_delta 0) hTL
    χ ψ hχ hψ]
  ext φ
  rw [convolutionWithCutoff_apply, tensorProduct_apply, delta_apply,
    TestFunction.applyDistributionToSliceRight_apply]
  change T
      (TestFunction.sliceRight 0
        (TestFunction.precompLocalized (fun p : E × E ↦ p.1 + p.2)
          contDiff_add (TestFunction.tensorProduct χ ψ) φ)) =
    T φ
  have hχ0 : χ 0 = 1 :=
    (hχ 0 (mem_singleton 0)).eq_of_nhds
  let g : 𝓓((⊤ : Opens E), ℝ) :=
    TestFunction.smoothMultiplierCLM (fun y ↦ ψ y) ψ.contDiff φ
  have hslice :
      TestFunction.sliceRight 0
          (TestFunction.precompLocalized (fun p : E × E ↦ p.1 + p.2)
            contDiff_add (TestFunction.tensorProduct χ ψ) φ) =
        g := by
    ext y
    simp [g, hχ0]
  rw [hslice]
  have hdiff : T (g - φ) = 0 := by
    apply hTL
    intro y hy
    by_contra hyL
    have hzero : ((g - φ : 𝓓((⊤ : Opens E), ℝ)) : E → ℝ) =ᶠ[𝓝 y] 0 := by
      filter_upwards [hψ y (by simpa using hyL)] with z hz
      have hψz : ψ z = 1 := by
        simpa using hz
      simp [g, hψz]
    exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hy
  rw [map_sub, sub_eq_zero] at hdiff
  exact hdiff

/-- The convolution of two Dirac masses is the Dirac mass at their sum. -/
@[simp]
theorem convolution_delta_delta (x y : E) :
    convolution (delta x) (delta y)
      (hasCompactCarrier_delta x) (hasCompactCarrier_delta y) =
      delta (x + y) := by
  obtain ⟨χ, -, -, hχ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ (isCompact_singleton : IsCompact ({x} : Set E))
      (subset_univ _)
  obtain ⟨ψ, -, -, hψ, -⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional
      isOpen_univ (isCompact_singleton : IsCompact ({y} : Set E))
      (subset_univ _)
  rw [convolution_eq_convolutionWithCutoff_tensorProduct
    (delta x) (delta y)
    (hasCompactCarrier_delta x) (hasCompactCarrier_delta y)
    isCompact_singleton isCompact_singleton
    (isVanishingOn_delta x) (isVanishingOn_delta y)
    χ ψ hχ hψ]
  have hχx : χ x = 1 :=
    (hχ x (mem_singleton x)).eq_of_nhds
  have hψy : ψ y = 1 :=
    (hψ y (mem_singleton y)).eq_of_nhds
  ext φ
  simp [convolutionWithCutoff, addition, hχx, hψy]

end Distribution
