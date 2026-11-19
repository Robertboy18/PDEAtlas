/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Bibliography
import Blueprint.Chapters.Sobolev.Approximation
import Blueprint.Chapters.Sobolev.Trace
import Blueprint.Commands.Figures
import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.Membership
import PDE.Spaces.Sobolev.Fractional.Domain.GagliardoFourier
import PDE.Spaces.Sobolev.Fractional.Domain.Restriction
import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure
import PDE.Spaces.Sobolev.Fractional.Domain.SupportedClosure.Nontrivial
import PDE.Spaces.Sobolev.Fractional.Integer.NormComparison
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.BesselComparison
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Equivalence
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Identification
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.Real
import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.SchwartzAgreement
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Operator
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.TraceSpace
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Gagliardo
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Range
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.Lifting.RightInverse
import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.TraceSpace.FiniteExponent
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Gagliardo
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Fractional.Lifting.RightInverse
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Space
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Operator
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.LocalTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Lifting
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Identification
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.AtlasIndependence
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.ChartTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.ChartTransport
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Compatibility
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Lifting
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.LocalTrace
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.FiniteExponent.Range

/-!
# Fourier and fractional Sobolev spaces

The whole-space Bessel-potential scale, its real subspace, its proved
equivalences with integer weak-derivative graph spaces and the completed
whole-space Gagliardo space, the three domain-level fractional
constructions, and the fractional trace theorems on the half-space.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Fourier and Fractional Sobolev Spaces" =>

The Fourier definition is the natural whole-space model of fractional and
negative Sobolev regularity.  It starts from a tempered distribution $`u`,
multiplies its Fourier transform by the Bessel weight
$`(1+\lVert\xi\rVert^2)^{s/2}`, and asks that the result be square integrable.
This gives one Hilbert space $`H^s(\mathbb R^n)` for every real order $`s`,
including negative and nonintegral orders.

At large frequencies the weight behaves like $`|\xi|^s`: positive order
penalizes rapid oscillation, while negative order allows more of it. The
$`1` in $`1+|\xi|^2` also controls the low frequencies. For a Schwartz
function, the order-one norm makes the connection with weak derivatives
explicit:

$$`
\begin{aligned}
\|u\|_{H^1_{\mathrm{Fourier}}}^2
 &=\int_{\mathbb R^n}(1+|\xi|^2)|\widehat u(\xi)|^2\,d\xi\\
 &=\|u\|_2^2+(2\pi)^{-2}\|\nabla u\|_2^2.
\end{aligned}
`

Negative orders have an equally concrete example. The Fourier transform of
the point mass $`\delta_0` is the constant function $`1`, so, for $`n>0`,
its squared $`H^s` norm is finite exactly when

$$`
\int_{\mathbb R^n}(1+|\xi|^2)^s\,d\xi<\infty.
`

The integrand is bounded near zero; the tail has the same integrability as
$`\int_1^\infty r^{n-1+2s}\,dr`. Thus $`\delta_0\in H^s` exactly for
$`s<-n/2`. Negative regularity can accommodate a point source even though
that source has no function representative.

Three representatives must be kept distinct throughout the formal theory.

1. `toLp u` is the $`L^2` representative of the Bessel potential
   $`(1-(2\pi)^{-2}\Delta)^{s/2}u`.
2. `𝓕 (toLp u)` is the Fourier transform of `toLp u`; almost everywhere it
   is the weighted Fourier transform
   $`(1+\lVert\xi\rVert^2)^{s/2}\widehat u(\xi)`.
3. When $`s\geq 0`, `toL2Fun hs u` is the physical $`L^2` function represented
   by the distribution $`u` itself.

The first exists for every real order.  The third exists only at nonnegative
order, because a negative-order Sobolev element need not be represented by a
locally integrable function at all.  Confusing these representatives would
silently erase the distinction between applying a Bessel potential to a
distribution and merely viewing that distribution as a function.

The Fourier transform in Mathlib uses the derivative multiplier
$`2\pi i\xi_j`.  Consequently, the symbol
$`(1+\lVert\xi\rVert^2)^{1/2}` corresponds to
$`(1-(2\pi)^{-2}\Delta)^{1/2}`, not to $`(1-\Delta)^{1/2}`.  This convention
is carried through every operator estimate and explains why the Fourier norm
and the project's integer graph norm are equivalent but, away from order
zero, not equal.

Several Sobolev scales are in use at once. The Zulip thread
[Frequency-side Sobolev definitions](https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/Frequency-side.20Sobolev.20definitions.html)
records overlapping definitions being developed at the same time:
$`H^s` through the Fourier multiplier, $`W^{k,p}` through weak derivatives, and
the Sobolev–Slobodeckij and Besov scales. The comparisons proved here are
$`H^k(\mathbb R^n;\mathbb R)\simeq W^{k,2}(\mathbb R^n;\mathbb R)`
for natural $`k`, and the equivalence of the completed whole-space Gagliardo
space with real $`H^s` for $`0<s<1`, both with explicit norm bounds (for the
second, when $`n\geq1`). Mathlib's general Bessel-potential definition uses a
physical $`L^p` representative; its weighted Fourier characterization is
proved at $`p=2`. We keep these definitions distinct and state comparisons
with their precise orders and exponents.

:::group "sobolev.fourier"
Fourier and fractional Sobolev spaces
:::

# The whole-space Hilbert scale

:::definition "sobolev.bessel_symbol" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.besselSymbol") (uses := "foundations.distributions.distribution")
For $`s\in\mathbb R`, the order-$`s` Bessel symbol is

$$`
J_s(\xi)=(1+\lVert\xi\rVert^2)^{s/2}.
`

The implementation is complex-valued because the Fourier theory of tempered
distributions is complex-linear, although $`J_s(\xi)` itself is a positive
real number.  The identities

$$`
J_s(\xi)J_{t-s}(\xi)=J_t(\xi),
\qquad
J_s(-\xi)=J_s(\xi)
`

are the algebraic facts behind the nested scale and the preservation of
real-valuedness.
:::

The symbol determines the space. A tempered distribution belongs to $`H^s`
exactly when $`J_s` times its Fourier transform is square integrable, and the
$`L^2` function so obtained, transported back to physical space, is the
representative on which the Hilbert structure is built.

:::definition "sobolev.fourier_space" (parent := "sobolev.fourier") (lean := "BesselPotentialSpace, BesselPotentialSpace.toLp, BesselPotentialSpace.toLpₗᵢ") (uses := "sobolev.bessel_symbol")
For every real order $`s`, the complex Bessel-potential space is

$$`
H^s(\mathbb R^n;\mathbb C)
  = \left\{u\in\mathcal S'(\mathbb R^n;\mathbb C):
      J_s\widehat u\in L^2(\mathbb R^n;\mathbb C)\right\}.
`

We use Mathlib's `BesselPotentialSpace` directly, with its notation
`H^{s}(ℝ^n)`. Mathlib supplies the norm, Hilbert structure, and completeness;
our derivative and domain results are built on this space.

The representative `toLp u` is characterized by

$$`
(1-(2\pi)^{-2}\Delta)^{s/2}u=\operatorname{toLp}(u)
`

as an identity of tempered distributions.  Applying the inverse Bessel
potential constructs `BesselPotentialSpace.ofLp`, and the two maps form the linear isometric
equivalence `BesselPotentialSpace.toLpₗᵢ`.  Thus every $`H^s` is complete and abstractly
isometric to $`L^2`, while the embedding of that abstract Hilbert space into
tempered distributions still depends essentially on $`s`.
:::

Because the inner product is transported along `toLp`, the norm identity that
follows is a definition rather than an estimate, and every constant appearing
later in the chapter is measured against it.

:::theorem "sobolev.bessel_norm" (parent := "sobolev.fourier") (lean := "BesselPotentialSpace.norm_toLp_eq") (uses := "sobolev.fourier_space")
The Sobolev norm is exactly the norm of the Bessel representative:

$$`
\lVert u\rVert_{H^s}
  =\left\lVert(1-(2\pi)^{-2}\Delta)^{s/2}u\right\rVert_{L^2}
  =\lVert\operatorname{toLp}(u)\rVert_{L^2}.
`
:::

:::proof "sobolev.bessel_norm"
Mathlib transports the inner product from $`L^2` along `toLp`.
Injectivity follows by applying the inverse Bessel potential.  The norm
identity is therefore immediate from the transported inner product structure.
:::

The Bessel representative lives in physical space. Multiplier estimates are
more transparent on the frequency side, so we use the $`L^2` Fourier transform
`𝓕 (toLp u)`.

:::definition "sobolev.fourier_representative" (parent := "sobolev.fourier") (lean := "MeasureTheory.Lp.fourierTransformₗᵢ") (uses := "sobolev.fourier_space")
The Fourier representative is

$$`
\mathcal F(\operatorname{toLp}(u))
  =J_s\,\widehat u
`

in $`L^2(\mathbb R^n;\mathbb C)`.  This identity is understood through
the canonical embedding of $`L^2` into tempered distributions.  Plancherel
composed with `BesselPotentialSpace.toLpₗᵢ` gives another linear isometric equivalence

$$`
H^s(\mathbb R^n;\mathbb C)\simeq_{\mathrm{iso}}L^2(\mathbb R^n;\mathbb C).
`
:::

Plancherel is an isometry of $`L^2`, so passing from the Bessel representative
to the Fourier representative costs nothing in norm, and the defining norm can
equally be computed on the frequency side.

:::theorem "sobolev.fourier_norm" (parent := "sobolev.fourier") (lean := "BesselPotentialSpace.norm_fourier_toLp_eq") (uses := "sobolev.bessel_norm, sobolev.fourier_representative")
Plancherel gives the exact Fourier-side norm formula

$$`
\lVert u\rVert_{H^s}
  =\lVert\mathcal F(\operatorname{toLp}(u))\rVert_{L^2}
  =\left\lVert J_s\,\widehat u\right\rVert_{L^2}.
`
:::

:::proof "sobolev.fourier_norm"
Apply the Bessel norm identity and then the $`L^2` Plancherel isometry to
`toLp u`.
:::

The first consequence of the frequency-side formula is the nesting of the
scale. Lowering the order from $`s` to $`t` multiplies the Fourier
representative by $`J_{t-s}`, and the symbol identity $`J_sJ_{t-s}=J_t`
recorded with the definition of the symbol is what makes this multiplication
act as the identity on underlying distributions.

:::theorem "sobolev.fourier_scale_inclusion" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_inclCLM_le_one, SobolevSpace.Fractional.inclCLM") (uses := "sobolev.fourier_norm")
If $`t\leq s`, then the identity on underlying tempered distributions defines
a continuous inclusion

$$`
\iota_{s,t}:H^s(\mathbb R^n;\mathbb C)
  \longrightarrow H^t(\mathbb R^n;\mathbb C),
\qquad
\lVert\iota_{s,t}\rVert\leq 1.
`

On Fourier representatives this lowers the order by multiplication with
$`J_{t-s}`.  Since $`t-s\leq 0`, that multiplier has pointwise norm at most
one.
:::

:::proof "sobolev.fourier_scale_inclusion"
Factor the target weight as $`J_t=J_sJ_{t-s}`.  The symbol $`J_{t-s}` is an
$`L^\infty` multiplier of norm at most one, so multiplication by it is a
contraction on $`L^2`.  Transfer the estimate back through the Fourier
isometries.
:::

# Differential operators and physical representatives

:::theorem "sobolev.fourier_operators" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_lineDerivCLM_le, SobolevSpace.Fractional.lineDerivCLM, SobolevSpace.Fractional.laplacianCLM, SobolevSpace.Fractional.norm_laplacianCLM_le") (uses := "sobolev.fourier_norm")
For every direction $`m\in\mathbb R^n`, distributional directional
differentiation and the Laplacian extend to bounded maps

$$`
\partial_m:H^s\longrightarrow H^{s-1},
\qquad
\Delta:H^s\longrightarrow H^{s-2},
`

with operator bounds

$$`
\lVert\partial_m\rVert\leq 2\pi\lVert m\rVert,
\qquad
\lVert\Delta\rVert\leq (2\pi)^2.
`

The constants come from the Mathlib Fourier symbols
$`2\pi i\langle\xi,m\rangle` and $`-(2\pi)^2\lVert\xi\rVert^2`.
:::

:::proof "sobolev.fourier_operators"
After shifting the Bessel order, divide each unbounded polynomial symbol by
the appropriate Bessel factor.  The reduced symbols

$$`
\frac{\langle\xi,m\rangle}{(1+\lVert\xi\rVert^2)^{1/2}}
\quad\text{and}\quad
\frac{\lVert\xi\rVert^2}{1+\lVert\xi\rVert^2}
`

are bounded respectively by $`\lVert m\rVert` and $`1`.  Multiplication by
their $`L^\infty` classes is bounded on $`L^2`, and the remaining Fourier
normalization contributes $`2\pi` or $`(2\pi)^2`.
:::

Differentiation lowers the order by one or two, so before weak derivatives of
a Sobolev element can be discussed as functions the element itself must be
read as a function. For $`s\geq0` the inclusion into $`H^0` of the preceding
section does this: at order zero the Bessel potential is the identity and
`toLp` is the function itself.

:::definition "sobolev.physical_l2_representative" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toL2Fun, SobolevSpace.Fractional.toL2FunCLM") (uses := "sobolev.fourier_scale_inclusion")
For $`s\geq 0`, the physical $`L^2` representative is obtained by first
including $`H^s` into $`H^0` and then using the order-zero Bessel
representative:

$$`
\operatorname{toL2Fun}:H^s(\mathbb R^n;\mathbb C)
  \longrightarrow L^2(\mathbb R^n;\mathbb C).
`

This is different from `toLp`: the latter represents
$`(1-(2\pi)^{-2}\Delta)^{s/2}u`, whereas `toL2Fun` represents $`u` itself.
:::

:::theorem "sobolev.physical_l2_properties" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toDistr_eq_toL2Fun, SobolevSpace.Fractional.norm_toL2Fun_le, SobolevSpace.Fractional.toL2Fun_injective") (uses := "sobolev.physical_l2_representative")
For $`s\geq 0`, `toL2Fun` has the three properties needed by the weak calculus:

* its induced tempered distribution is exactly the original Sobolev element;
* it is norm-decreasing,
  $`\lVert\operatorname{toL2Fun}(u)\rVert_2\leq\lVert u\rVert_{H^s}`;
* it is injective.

Thus an element of nonnegative-order $`H^s` can safely be treated as an
$`L^2` function modulo almost-everywhere equality.
:::

:::proof "sobolev.physical_l2_properties"
The inclusion $`H^s\to H^0` preserves the underlying tempered distribution and
is a contraction.  At order zero the Bessel potential is the identity.
Injectivity follows because two $`L^2` representatives inducing the same
tempered distribution are equal.
:::

# The canonical real subspace

:::definition "sobolev.fourier_real_space" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.IsRealL2, SobolevSpace.Fractional.imaginaryPartL2, SobolevSpace.Fractional.imaginaryPartHs, SobolevSpace.Fractional.hsRealSubmodule, SobolevSpace.Fractional.HsSpaceReal") (uses := "sobolev.fourier_space")
An $`L^2(\mathbb R^n;\mathbb C)` function is real when its imaginary part
vanishes almost everywhere.  The real Sobolev space is the real submodule

$$`
H^s(\mathbb R^n;\mathbb R)
  =\left\{u\in H^s(\mathbb R^n;\mathbb C):
      \operatorname{toLp}(u)\text{ is real a.e.}\right\}.
`

It is an $`\mathbb R`-submodule, not a $`\mathbb C`-submodule: multiplication
by $`i` does not preserve real-valuedness.  It is the kernel of the bounded
imaginary-part map, hence a closed and complete real Hilbert subspace.
The subtype `HsSpaceReal` is the real structure used by the integer bridge
and the restriction space; realness of the physical representative is
expressed by the characterization theorems below.
:::

Realness is defined through the Bessel representative `toLp u`, whereas the
weak calculus sees the physical representative `toL2Fun u`. On the frequency
side the two differ by multiplication with the symbol $`J_{-s}`, so comparing
them calls for a frequency-side description of real-valuedness.

:::theorem "sobolev.fourier_real_hermitian" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.fourier_star, SobolevSpace.Fractional.isRealL2_iff_isHermitian_fourier") (uses := "sobolev.fourier_real_space")
Real-valuedness in physical space is equivalent to Hermitian symmetry in
frequency space:

$$`
f\text{ is real a.e.}
\quad\Longleftrightarrow\quad
\widehat f(-\xi)=\overline{\widehat f(\xi)}
\quad\text{a.e.}
`
:::

:::proof "sobolev.fourier_real_hermitian"
The $`L^2` Fourier transform intertwines complex conjugation with conjugation
and reflection in frequency.  Real-valued functions are exactly the fixed
points of complex conjugation, so applying the Fourier equivalence gives the
stated Hermitian-symmetry characterization.
:::

Since $`J_{-s}` is real, even, and nowhere zero, multiplication by it
preserves Hermitian symmetry in both directions. Realness of the Bessel
representative and realness of the physical representative are therefore the
same condition whenever $`s\geq0`.

:::theorem "sobolev.fourier_real_representatives" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.isRealL2_toL2Fun_iff, SobolevSpace.Fractional.mem_HsRealSubmodule_iff_toL2Fun, SobolevSpace.Fractional.HsSpaceReal.isRealL2_toL2Fun, SobolevSpace.Fractional.HsSpaceReal.toL2FunCLM, SobolevSpace.Fractional.HsSpaceReal.toL2FunCLM_apply_ae") (uses := "sobolev.fourier_real_hermitian, sobolev.physical_l2_representative")
When $`s\geq 0`, the Bessel representative is real if and only if the physical
$`L^2` representative is real.  Consequently,

$$`
u\in H^s(\mathbb R^n;\mathbb R)
\quad\Longleftrightarrow\quad
\operatorname{toL2Fun}(u)\text{ is real a.e.}
`

The physical representative of an element in the real subspace therefore
belongs to real $`L^2`; this realization is a bounded real-linear map.
:::

:::proof "sobolev.fourier_real_representatives"
Lowering from order $`s` to order zero multiplies the Fourier representative
by the positive, even, nonvanishing symbol $`J_{-s}`.  Such a multiplier
preserves and reflects Hermitian symmetry.  Apply the Fourier characterization
of real-valuedness on both sides.
:::

Read from right to left, the equivalence is a constructor: an element known to
have a real physical representative belongs to the real subspace, with no
separate argument about its Bessel representative.

:::definition "sobolev.fourier_real_constructor" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.HsSpaceReal.ofPhysical") (uses := "sobolev.fourier_real_representatives")
For $`s\geq 0`, an element $`u\in H^s(\mathbb R^n;\mathbb C)` together with a
proof that its physical representative is real can be packaged directly as

$$`
\operatorname{ofPhysical}(u)\in H^s(\mathbb R^n;\mathbb R).
`

The reverse maps and the concrete whole-space extensions are built with this
constructor.
:::

# Integration by parts and weak derivatives

:::theorem "sobolev.fourier_integration_by_parts" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.integral_lineDeriv_smul_toL2Fun, SobolevSpace.Fractional.integral_partialDeriv_smul_toL2Fun") (uses := "sobolev.fourier_operators, sobolev.physical_l2_properties")
Let $`s\geq 1`, $`u\in H^s(\mathbb R^n;\mathbb C)`, and
$`\varphi` be a Schwartz test function.  Then

$$`
\int_{\mathbb R^n}\varphi\,\partial_m u
  =-\int_{\mathbb R^n}(\partial_m\varphi)\,u,
`

where $`u` and $`\partial_m u` are interpreted through their physical
$`L^2` representatives.  A second theorem specializes this identity to the
project's compactly supported real test functions and coordinate derivative
`partialDeriv`, exactly matching the sign convention used by
`HasWeakDerivativeOn`.
:::

:::proof "sobolev.fourier_integration_by_parts"
Pair the tempered distribution $`\partial_m u` against the test function.
By definition of distributional differentiation this is the negative pairing
of $`u` against $`\partial_m\varphi`.  Replace both pairings by integrals of
the physical $`L^2` representatives.  Complexifying a compactly supported real
test function gives the coordinate form.
:::

After taking real parts, the integration-by-parts identity is the defining
equation of `HasWeakDerivativeOn`. The realness theorems of the previous
section guarantee that nothing is lost in taking real parts when the physical
representative of $`u` is real, since directional differentiation preserves
realness.

:::theorem "sobolev.fourier_first_weak_derivative" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.hasWeakDerivativeOn_reOfL2") (uses := "sobolev.fourier_integration_by_parts, sobolev.fourier_real_representatives")
Suppose $`s\geq 1` and the physical representative of $`u\in H^s` is real.
For every coordinate $`i`, its real part has the weak derivative represented
by the real part of the physical representative of $`\partial_i u`:

$$`
\operatorname{re}(\operatorname{toL2Fun}(\partial_i u))
  =D_i\operatorname{re}(\operatorname{toL2Fun}(u))
`

in the `HasWeakDerivativeOn` sense on all of $`\mathbb R^n`.
:::

:::proof "sobolev.fourier_first_weak_derivative"
The integration-by-parts identity gives the required test-function equation.
Directional differentiation preserves real-valuedness, so both complex
$`L^2` representatives are almost everywhere complexifications of their real
parts.  Taking real parts converts the complex identity into the real weak
derivative relation.
:::

Each application of the first-order theorem lowers the order by one and
preserves realness of the physical representative, so it can be applied again
as long as the current order is at least one. The condition $`|\alpha|\leq s`
is exactly what keeps every intermediate order in range.

:::theorem "sobolev.fourier_iterated_weak_derivative" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.exists_hasWeakDerivativeOn_list") (uses := "sobolev.fourier_first_weak_derivative")
Let $`\alpha` be a word of coordinate directions with
$`\lvert\alpha\rvert\leq s`.  If $`u\in H^s` has a real physical
representative, then there is a real-represented element
$`v\in H^{s-\lvert\alpha\rvert}` whose physical representative is the weak
$`\alpha`-derivative of that of $`u`.

In Lean the target order is an existential $`t` together with the equation
$`t=s-\lvert\alpha\rvert`, which avoids rewriting along casts of real
numbers.
:::

:::proof "sobolev.fourier_iterated_weak_derivative"
Induct on the derivative word from the right.  The empty word uses the
function itself.  At each successor step, apply the first-order theorem in the
current Sobolev order, appending one coordinate direction to the derivative word.
:::

# Integer orders and graph spaces

At a natural order $`k`, the preceding derivative theorem produces all weak
derivatives of length at most $`k`.  The project stores these derivatives in
the symmetric graph-space tuple indexed by `DerivIndex n k`.  The central
result of this section is a two-sided, continuous, real-linear equivalence
between that graph model and the canonical real part of Fourier $`H^k`.

:::definition "sobolev.integer_fourier_forward" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toWkpSpace, SobolevSpace.Fractional.toWkpSpaceLinear") (uses := "sobolev.fourier_iterated_weak_derivative, sobolev.graph_space")
For $`u\in H^k(\mathbb R^n;\mathbb R)`, `toWkpSpace` forms the graph tuple

$$`
\bigl(D^\alpha u\bigr)_{\lvert\alpha\rvert\leq k}
  \in W^{k,2}(\mathbb R^n;\mathbb R).
`

The base coordinate is the physical $`L^2` representative of $`u`; every
other coordinate is a chosen $`L^2` representative of the corresponding weak
derivative.  The chosen weak-derivative identities place the tuple in the
graph space.  Uniqueness identifies each coordinate independently of the
choice and proves linearity.  On `HsSpaceReal`, the construction is bundled
as the real-linear map `toWkpSpaceLinear`.
:::

Each coordinate derivative costs a factor $`2\pi` in the operator bound of the
differentiation section, so a word of length $`j` costs
$`(2\pi)^j\leq(2\pi)^k`. The graph norm sums the squares of finitely many such
coordinates, which accounts for the square root of the number of derivative
indices.

:::theorem "sobolev.integer_fourier_forward_bound" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_toWkpSpace_le, SobolevSpace.Fractional.toWkpSpaceNormBound, SobolevSpace.Fractional.toWkpSpaceCLM") (uses := "sobolev.integer_fourier_forward, sobolev.fourier_operators")
The forward graph-space map is bounded by

$$`
\lVert\operatorname{toWkpSpace}(u)\rVert_{W^{k,2}}
\leq
\sqrt{\#\operatorname{DerivIndex}(n,k)}\,
(2\pi)^k\lVert u\rVert_{H^k}.
`

The implementation records the displayed constant as
`toWkpSpaceNormBound n k` and packages the map as a continuous real-linear map.
:::

:::proof "sobolev.integer_fourier_forward_bound"
Each coordinate of derivative length $`j\leq k` is bounded by
$`(2\pi)^j\lVert u\rVert_{H^k}`, hence by
$`(2\pi)^k\lVert u\rVert_{H^k}`.  The graph norm is the Euclidean
$`\ell^2` norm of finitely many coordinates, so summing the common square
bound contributes the square root of the number of derivative indices.
:::

The forward map only unpacks information already present in $`u`. The reverse
direction must recover Bessel-weighted integrability of $`\widehat u` from the
weak-derivative relations stored in a graph tuple, and this is the substantive
analytic content of the integer bridge.

:::definition "sobolev.integer_fourier_reverse" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.ofWkpSpace") (uses := "sobolev.integer_fourier_forward, sobolev.global_density")
For $`U\in W^{k,2}(\mathbb R^n;\mathbb R)`, `ofWkpSpace U` is the tempered
distribution induced by the complexification of the base $`L^2` coordinate.
The weak derivatives stored in the remaining coordinates prove that this
distribution belongs to Fourier $`H^k`.
:::

The key input is the Fourier transform of a pure $`k`-th coordinate
derivative.

:::theorem "sobolev.integer_fourier_symbol_identity" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.pureSymbol_mul_fourier_ae, SobolevSpace.Fractional.besselWeightBound") (uses := "sobolev.integer_fourier_reverse, sobolev.global_density")
For each coordinate direction $`i`, the Fourier transform of the pure
$`k`-th derivative is almost everywhere

$$`
(2\pi i\xi_i)^k\widehat u(\xi).
`

Together with a pointwise domination of the Bessel weight by the base
frequency and the pure coordinate powers, this yields the explicit factor

$$`
B_{n,k}=2^{k-1}\bigl(1+n^{k-1}\bigr)
`

for $`k\geq 1`.
:::

:::proof "sobolev.integer_fourier_symbol_identity"
Approximate the graph-space element by smooth compactly supported functions.
For the approximants the identity is classical.  Plancherel gives convergence
of the transformed base and derivative coordinates in $`L^2`.  Embed them in
tempered distributions, where multiplication by the polynomial symbol is
continuous, and pass the identity to the limit there.  Equality of the induced
distributions then gives the almost-everywhere multiplier identity.
An elementary power-mean estimate bounds
$`(1+\lVert\xi\rVert^2)^{k/2}` using $`1` and the pure powers
$`\lvert\xi_i\rvert^k`.
:::

With both maps defined, they must be shown to be inverse to each other. In one
direction this is uniqueness of weak derivatives; in the other it is the fact
that the two constructions share the same base representative.

:::theorem "sobolev.integer_fourier_round_trips" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toWkpSpace_ofWkpSpace, SobolevSpace.Fractional.ofWkpSpace_toWkpSpace") (uses := "sobolev.integer_fourier_forward, sobolev.integer_fourier_reverse")
The forward and reverse constructions are mutually inverse:

$$`
\operatorname{toWkpSpace}(\operatorname{ofWkpSpace}(U))=U,
\qquad
\operatorname{ofWkpSpace}(\operatorname{toWkpSpace}(u))=u.
`
:::

:::proof "sobolev.integer_fourier_round_trips"
Starting from a graph tuple, extracting its base coordinate and then taking
all weak derivatives recovers every coordinate by uniqueness of weak
derivatives.  Starting from a real Fourier-Sobolev element, its graph tuple
has the same base physical representative, so rebuilding the induced
tempered distribution recovers the original element.
:::

Mutual inversion together with linearity of the forward map packages the two
constructions as a linear equivalence; the real constructor of the previous
section is what lands the reverse map in the canonical real subspace.

:::definition "sobolev.integer_fourier_linear_equivalence" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toWkpSpaceEquiv") (uses := "sobolev.integer_fourier_round_trips, sobolev.fourier_real_constructor")
For every natural number $`k`, the mutually inverse maps define a real-linear
equivalence

$$`
H^k(\mathbb R^n;\mathbb R)
\simeq_{\mathbb R}
W^{k,2}(\mathbb R^n;\mathbb R).
`
:::

Continuity of the inverse is the remaining point. At order zero there is
nothing to estimate, since both norms are the $`L^2` norm of the base
coordinate, and the equivalence is isometric.

:::theorem "sobolev.integer_fourier_zero_norm" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_toWkpSpace_order_zero") (uses := "sobolev.integer_fourier_linear_equivalence")
At order zero, the forward conversion preserves the norm exactly:

$$`
\lVert\operatorname{toWkpSpace}(u)\rVert_{W^{0,2}}
  = \lVert u\rVert_{H^0}.
`
:::

:::proof "sobolev.integer_fourier_zero_norm"
The forward bound specializes to constant one because there is only the base
coordinate.  The reverse map is a contraction at order zero, and the two maps
are inverse, giving the opposite inequality.
:::

For positive order the symbol identity gives the inverse bound, since the base
coordinate and the pure $`k`-th derivatives are coordinates of the graph
tuple.

:::theorem "sobolev.integer_fourier_reverse_bound" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_ofWkpSpace_le") (uses := "sobolev.integer_fourier_symbol_identity, sobolev.integer_fourier_round_trips")
For every natural order $`k` and
$`U\in W^{k,2}(\mathbb R^n;\mathbb R)`, the inverse satisfies

$$`
\lVert\operatorname{ofWkpSpace}(U)\rVert_{H^k}
  \leq
  2^{k-1}(1+n^{k-1})(n+1)
  \lVert U\rVert_{W^{k,2}}.
`

The exponents use natural-number subtraction.  Thus at $`k=0` the displayed
constant evaluates to the valid but loose value $`2(n+1)`.  The separate
order-zero theorem above is the sharp statement.
:::

:::proof "sobolev.integer_fourier_reverse_bound"
The Bessel-weight estimate controls the weighted Fourier transform by the
Fourier transforms of the base coordinate and the $`n` pure $`k`-th
derivatives.  Plancherel converts those terms back to their $`L^2` norms, and
each graph coordinate has norm at most $`\lVert U\rVert`.  Summing the base
term and $`n` derivative terms contributes the factor $`n+1`.
:::

The two bounds upgrade the linear equivalence to a topological one.

:::definition "sobolev.integer_fourier_equivalence" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.toWkpSpaceCLE") (uses := "sobolev.integer_fourier_forward_bound, sobolev.integer_fourier_reverse_bound, sobolev.integer_fourier_linear_equivalence")
The linear equivalence upgrades to a continuous linear equivalence:

$$`
H^k(\mathbb R^n;\mathbb R)
\simeq_{\mathrm{top},\mathbb R}
W^{k,2}(\mathbb R^n;\mathbb R).
`

The equivalence is topological, not isometric. Already at first order the
Fourier convention gives the identity

$$`
\lVert u\rVert_{H^1}^2
  =\lVert u\rVert_{L^2}^2
    +(2\pi)^{-2}\sum_{j=1}^n\lVert\partial_j u\rVert_{L^2}^2,
`

whereas the graph norm aggregates derivative coordinates without the
$`(2\pi)^{-2}` factor.
:::

# Fractional spaces on a domain

There is no single canonical definition of $`H^s(\Omega)` on an arbitrary
set for every real $`s`. The library therefore keeps three constructions
separate: restrictions of whole-space elements, the intrinsic
Gagliardo–Slobodeckij space, and the closure of supported Schwartz
functions.

# Restrictions of whole-space elements

:::definition "sobolev.fractional_restriction" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.hsRestrictionCLM, SobolevSpace.Fractional.hsRestrictionKernel, SobolevSpace.Fractional.HsRestrictionSpace, SobolevSpace.Fractional.MemHsRestriction, SobolevSpace.Fractional.hsRestrictionSubmodule") (uses := "sobolev.physical_l2_representative, sobolev.fourier_real_space")
For $`s\geq 0`, restriction of the real physical representative defines a
bounded map

$$`
R_\Omega:H^s(\mathbb R^n;\mathbb R)\longrightarrow L^2(\Omega).
`

The completed restriction space is the Hilbert quotient

$$`
H^s_{\mathrm{res}}(\Omega)
  = H^s(\mathbb R^n;\mathbb R)/\ker R_\Omega.
`

Thus two whole-space elements determine the same class precisely when their
physical representatives agree almost everywhere on $`\Omega`.  The quotient
norm is the infimum of the whole-space norms of all extensions.

For representative-level statements, a raw real function
$`f:\mathbb R^n\to\mathbb R` satisfies `MemHsRestriction` when there is a
whole-space element $`U\in H^s(\mathbb R^n;\mathbb R)` such that

$$`
\operatorname{re}(\operatorname{toL2Fun}(U))=f
\quad\text{a.e. on }\Omega.
`

These raw functions form `hsRestrictionSubmodule`.
:::

Because $`R_\Omega` is continuous, its kernel is closed and the quotient is a
Hilbert space in its own right. Orthogonal decomposition then singles out one
extension of each class, the one orthogonal to the kernel, and this extension
realizes the quotient norm.

:::theorem "sobolev.fractional_restriction_hilbert" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.HsRestrictionSpace.toLp_injective, SobolevSpace.Fractional.HsRestrictionSpace.ofWholeSpace_minimalExtension, SobolevSpace.Fractional.HsRestrictionSpace.norm_minimalExtension, SobolevSpace.Fractional.HsRestrictionSpace.toLp_minimalExtension, SobolevSpace.Fractional.HsRestrictionSpace.minimalExtension_mem_orthogonal, SobolevSpace.Fractional.HsRestrictionSpace.norm_minimalExtension_le_of_toLp_eq, SobolevSpace.Fractional.HsRestrictionSpace.minimalExtension_eq_of_mem_orthogonal, SobolevSpace.Fractional.memHsRestriction_iff_exists_toLp, SobolevSpace.Fractional.HsRestrictionSpace.ofWholeSpace, SobolevSpace.Fractional.HsRestrictionSpace.toLp, SobolevSpace.Fractional.HsRestrictionSpace.minimalExtension") (uses := "sobolev.fractional_restriction")
Every quotient class $`q` has a unique representative
$`E_{\min}q\in(\ker R_\Omega)^\perp`.  It satisfies

$$`
R_\Omega(E_{\min}q)=\operatorname{toLp}(q),\qquad
\lVert E_{\min}q\rVert_{H^s}=\lVert q\rVert_{H^s_{\mathrm{res}}(\Omega)},
`

where $`\operatorname{toLp}(q)` is the quotient class's $`L^2(\Omega)`
realization. The extension has no larger norm than any other whole-space
extension with the same $`L^2(\Omega)` value. The induced map from the quotient into $`L^2(\Omega)`
is injective.  Raw membership is equivalent to almost-everywhere agreement
with the $`L^2(\Omega)` realization of some quotient class.
:::

:::proof "sobolev.fractional_restriction_hilbert"
The restriction kernel is closed because $`R_\Omega` is continuous.  Orthogonal
decomposition in the real Hilbert space $`H^s(\mathbb R^n;\mathbb R)` identifies
the kernel quotient with its orthogonal complement.  The orthogonal
representative preserves the quotient norm and is the unique least-norm
extension.
:::

Shrinking the domain enlarges the kernel: whatever vanishes almost everywhere
on $`\Omega_2` vanishes on $`\Omega_1\subseteq\Omega_2`. The identity of
$`H^s(\mathbb R^n;\mathbb R)` therefore descends to a map between the two
quotients, and the minimal-extension theory just established controls its
norm.

:::theorem "sobolev.fractional_restriction_functorial" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.HsRestrictionSpace.norm_restrictCLM_apply_le, SobolevSpace.Fractional.HsRestrictionSpace.norm_restrictCLM_le_one, SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM_surjective, SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM_self, SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM_comp, SobolevSpace.Fractional.HsRestrictionSpace.norm_minimalExtension_restrictCLM_le, SobolevSpace.Fractional.restrictDomainL2, SobolevSpace.Fractional.restrictDomainL2_hsRestrictionCLM, SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM, SobolevSpace.Fractional.HsRestrictionSpace.restrictCLM_ofWholeSpace, SobolevSpace.Fractional.HsRestrictionSpace.toLp_restrictCLM, SobolevSpace.Fractional.HsRestrictionSpace.toLp_restrictCLM_apply_ae") (uses := "sobolev.fractional_restriction_hilbert")
If $`\Omega_1\subseteq\Omega_2`, there is a canonical surjective contraction

$$`
\operatorname{res}_{\Omega_1}^{\Omega_2}:
H^s_{\mathrm{res}}(\Omega_2)\longrightarrow
H^s_{\mathrm{res}}(\Omega_1).
`

It sends the class of a whole-space representative to the class of the same
representative on the smaller domain.  On $`L^2` realizations it is the
canonical restriction
$`L^2(\Omega_2)\to L^2(\Omega_1)`.  Restriction to the same domain is the
identity, restrictions compose along chains of inclusions, and the
least-norm extension of the restricted class has norm at most the norm of the
original class.
:::

:::proof "sobolev.fractional_restriction_functorial"
Vanishing almost everywhere on $`\Omega_2` implies vanishing almost everywhere
on $`\Omega_1`.  Thus the identity map on whole-space $`H^s` sends
$`\ker R_{\Omega_2}` into $`\ker R_{\Omega_1}` and descends through the two
kernel quotients.  The quotient norm decreases because the identity is
contractive on representatives.  Every smaller-domain class has a
whole-space representative, whose class on $`\Omega_2` supplies a preimage.
The identity and composition laws are checked on these representatives.
:::

At the level of raw functions the same monotonicity holds, and real Schwartz
functions show that the membership predicate is never vacuous.

:::theorem "sobolev.fractional_restriction_properties" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.MemHsRestriction.mono, SobolevSpace.Fractional.memHsRestriction_reOfSchwartz") (uses := "sobolev.fractional_restriction_hilbert")
Restriction membership is monotone with respect to the domain:

$$`
\Omega_1\subseteq\Omega_2,\quad
f\in H^s_{\mathrm{res}}(\Omega_2)
\quad\Longrightarrow\quad
f\in H^s_{\mathrm{res}}(\Omega_1).
`

Every real-valued Schwartz function supplies a concrete member on every
domain.  Membership depends only on the almost-everywhere class for Lebesgue
measure restricted to $`\Omega`.  When $`\Omega` is measurable, changing
values outside $`\Omega` does not affect membership.  The ambient submodule
still contains raw functions rather than quotient classes.
:::

:::proof "sobolev.fractional_restriction_properties"
The same whole-space witness works on a smaller domain because restricted
Lebesgue measure is monotone.  For a real-valued Schwartz function, use its
canonical whole-space $`H^s` element; its physical representative is the
Schwartz function's own $`L^2` class.
:::

# The Gagliardo–Slobodeckij condition

Fractional regularity can also be measured by comparing values at pairs of
points. For $`0<s<1`, the intrinsic squared seminorm is

$$`
[u]_{s,\Omega}^2
 =\int_{\Omega\times\Omega}
   \frac{|u(x)-u(y)|^2}{|x-y|^{n+2s}}\,dx\,dy.
`

Nearby pairs receive the greatest weight. For a smooth compactly supported
function, the numerator is bounded by a constant times $`|x-y|^2` near
the diagonal. Radial integration of the separation variable then gives
$`\int_0^1 r^{1-2s}\,dr`, finite precisely when $`s<1`.
For distant pairs on the whole space, the $`L^2` bound on translations
leaves the tail $`\int_1^\infty r^{-1-2s}\,dr`, finite when $`s>0`.
These two calculations explain the interval $`0<s<1` in which first
differences measure fractional Sobolev regularity.

:::definition "sobolev.gagliardo_difference_quotient" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.diffQuot") (uses := "sobolev.fractional_restriction")
For a raw real function $`u:\mathbb R^n\to\mathbb R`, define

$$`
Q_{s,u}(x,y)
  =\frac{u(x)-u(y)}
    {\lVert x-y\rVert^{n/2+s}}.
`

Its square has exactly the classical Gagliardo kernel

$$`
\lvert Q_{s,u}(x,y)\rvert^2
  =\frac{\lvert u(x)-u(y)\rvert^2}
    {\lVert x-y\rVert^{n+2s}}.
`

The numerator vanishes on the diagonal, so the implemented quotient is zero
there for every $`s`; no separate diagonal convention is needed.  The map
$`u\mapsto Q_{s,u}` is linear even at points where the denominator vanishes.
:::

Square integrability of $`Q_{s,u}` over $`\Omega\times\Omega` is the Gagliardo
condition. Its formal counterpart has three layers: a predicate on raw
functions, a partially defined operator on $`L^2` classes, and a completed
graph space.

:::definition "sobolev.gagliardo_space" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.MemGagliardo, SobolevSpace.Fractional.gagliardoSubmodule, SobolevSpace.Fractional.gagliardoOperator, SobolevSpace.Fractional.GagliardoSpace, SobolevSpace.Fractional.gagliardoSq") (uses := "sobolev.gagliardo_difference_quotient")
The Gagliardo condition on $`\Omega` is

$$`
u\in L^2(\Omega)
\quad\text{and}\quad
Q_{s,u}\in L^2(\Omega\times\Omega).
`

For $`0<s<1`, this is the usual Sobolev–Slobodeckij membership condition.
The corresponding raw functions form `gagliardoSubmodule`.  On almost-everywhere
classes, the difference quotient is the partially defined linear operator

$$`
D_s:\operatorname{dom}(D_s)\subseteq L^2(\Omega)
  \longrightarrow L^2(\Omega\times\Omega),\qquad D_su=Q_{s,u}.
`

The completed intrinsic space `GagliardoSpace` is the graph of $`D_s` inside
the Hilbert product

$$`
L^2(\Omega)\mathbin{\oplus_2}L^2(\Omega\times\Omega).
`

The extended-real integral `gagliardoSq` records the square of the seminorm,
while raw membership is phrased with `MemLp` so that measurability and closure
under linear operations come from Mathlib's $`L^p` API.
:::

Two formulations of the same finiteness condition coexist: membership of
$`Q_{s,u}` in $`L^2`, and finiteness of the extended-real integral
`gagliardoSq`. Their agreement, established next, is what allows the
whole-space Fourier identity below to be transferred to the membership
predicate.

:::theorem "sobolev.gagliardo_seminorm_membership" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.gagliardoSq_eq_eLpNorm'_sq, SobolevSpace.Fractional.memGagliardo_iff") (uses := "sobolev.gagliardo_space")
For every real $`s` and every set $`\Omega`, `gagliardoSq` is exactly the
square of the raw extended $`L^2` seminorm `eLpNorm'` of $`Q_{s,u}`. Consequently,
`MemGagliardo` is equivalent to square integrability of $`u` on $`\Omega`
together with finiteness of `gagliardoSq`.

No separate measurability assumption is needed: the $`L^2` hypothesis on
$`u` makes both coordinate pullbacks almost everywhere strongly measurable,
and division by the measurable distance power preserves that property.
Under this hypothesis, `eLpNorm'` agrees with `eLpNorm` for the difference quotient.
:::

:::proof "sobolev.gagliardo_seminorm_membership"
Mathlib's formula expressing an $`L^2` seminorm squared as a lintegral gives
the first identity. The forward implication extracts finiteness from
`MemLp`; the reverse implication combines the finite lintegral with the
measurability inherited from the base $`L^2` function.
:::

Completeness of the graph space is equivalent to closedness of $`D_s`, and
closedness is a pointwise matter: along a subsequence converging almost
everywhere, the $`L^2` limit of the difference quotients of $`u_k` is the
difference quotient of the limit of the $`u_k`.

:::theorem "sobolev.gagliardo_hilbert" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.gagliardoOperator_isClosed, SobolevSpace.Fractional.isClosed_gagliardoGraph, SobolevSpace.Fractional.GagliardoSpace.toLp, SobolevSpace.Fractional.GagliardoSpace.differenceQuotient, SobolevSpace.Fractional.GagliardoSpace.toLp_injective, SobolevSpace.Fractional.GagliardoSpace.range_toLp, SobolevSpace.Fractional.GagliardoSpace.ofLp, SobolevSpace.Fractional.GagliardoSpace.ofFunction, SobolevSpace.Fractional.GagliardoSpace.differenceQuotient_apply_ae, SobolevSpace.Fractional.GagliardoSpace.norm_sq_eq, SobolevSpace.Fractional.GagliardoSpace.inner_eq, SobolevSpace.Fractional.GagliardoSpace.memGagliardo_iff_exists_gagliardoSpace") (uses := "sobolev.gagliardo_space")
The operator $`D_s` is closed for every real $`s` and every set $`\Omega`.
Consequently `GagliardoSpace` is a complete real Hilbert space.  Its two
continuous coordinate maps satisfy

$$`
\lVert u\rVert_{\mathrm{Gag}}^2
  =\lVert u\rVert_{L^2(\Omega)}^2
   +\lVert D_su\rVert_{L^2(\Omega\times\Omega)}^2
`

and

$$`
\langle u,v\rangle_{\mathrm{Gag}}
  =\langle u,v\rangle_{L^2(\Omega)}
   +\langle D_su,D_sv\rangle_{L^2(\Omega\times\Omega)}.
`

The first coordinate is injective and its range is exactly
$`\operatorname{dom}(D_s)`.  A raw function satisfies `MemGagliardo` exactly
when it agrees almost everywhere on $`\Omega` with the first coordinate of
an element of `GagliardoSpace`.
:::

:::proof "sobolev.gagliardo_hilbert"
Suppose graph elements $`(u_k,D_su_k)` converge in the product $`L^2` space.
From $`u_k\to u` in $`L^2(\Omega)`, choose a subsequence converging pointwise
almost everywhere.  From convergence of the second coordinates, choose a
further subsequence converging pointwise almost everywhere on
$`\Omega\times\Omega`.  Pulling the first convergence through both product
projections shows that the pointwise limit of the difference quotients is
$`Q_{s,u}`.  Uniqueness of limits identifies it with the second $`L^2`
coordinate, so the graph is closed.  A closed subspace of the Hilbert
$`\ell^2` product is complete, and the norm and inner-product formulas are
the product formulas.  The graph relation gives injectivity and the
raw-function characterization.
:::

The same three layers are defined for every exponent $`1\leq p\leq\infty`
and every real normed target $`F`. The quotient becomes
$`(u(x)-u(y))/\lVert x-y\rVert^{n/p+s}`, both $`L^2` spaces become $`L^p`
spaces, and the graph of $`D_s` is closed for the same reason, so the graph
space is a Banach space whenever $`F` is complete. The Hilbert case above is
$`p=2`, $`F=\mathbb R`. The trace theorems at the end of the chapter use the
exponent $`p` and order $`1-1/p`.

Both coordinates of a graph element are $`L^2` functions on a restricted
measure, so shrinking $`\Omega` restricts both, and restriction of the base
coordinate is compatible with forming the difference quotient. This yields the
same functorial contraction structure that the restriction space carries.

:::theorem "sobolev.gagliardo_restriction" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.gagliardoProductMeasure_mono, SobolevSpace.Fractional.MemGagliardo.mono, SobolevSpace.Fractional.gagliardoSubmodule_mono, MeasureTheory.Lp.restrictionCLMOfLE, SobolevSpace.Fractional.GagliardoSpace.restrictCLM, SobolevSpace.Fractional.GagliardoSpace.toLp_restrictCLM, SobolevSpace.Fractional.GagliardoSpace.differenceQuotient_restrictCLM, SobolevSpace.Fractional.GagliardoSpace.restrictCLM_ofFunction, SobolevSpace.Fractional.GagliardoSpace.norm_restrictCLM_apply_le, SobolevSpace.Fractional.GagliardoSpace.norm_restrictCLM_le_one, SobolevSpace.Fractional.GagliardoSpace.restrictCLM_self, SobolevSpace.Fractional.GagliardoSpace.restrictCLM_comp") (uses := "sobolev.gagliardo_hilbert")
If $`\Omega_1\subseteq\Omega_2`, restriction of representatives defines a
continuous linear contraction

$$`
\rho_{\Omega_2,\Omega_1}:
  \operatorname{GagliardoSpace}(n,s,\Omega_2)
  \longrightarrow
  \operatorname{GagliardoSpace}(n,s,\Omega_1),
\qquad
\lVert\rho_{\Omega_2,\Omega_1}\rVert\leq 1.
`

Its first coordinate is the canonical restriction
$`L^2(\Omega_2)\to L^2(\Omega_1)`, and its second coordinate is the canonical
restriction
$`L^2(\Omega_2\times\Omega_2)\to L^2(\Omega_1\times\Omega_1)`.  Packaging a
raw function by `ofFunction` commutes with this map.  Restriction to the same
domain is the identity, and restrictions compose along chains of domain
inclusions.
:::

:::proof "sobolev.gagliardo_restriction"
Restricted Lebesgue measure and its product measure are monotone under
$`\Omega_1\subseteq\Omega_2`.  Mathlib's canonical restriction maps on
$`L^2` are therefore contractions.  Almost-everywhere equality of the first
coordinates implies almost-everywhere equality of their difference
quotients, so the restricted pair remains in the graph of $`D_s`.  Applying
the two coordinate contraction estimates to the graph norm proves the norm
bound.  Identity, composition, and compatibility with `ofFunction` follow
from equality of the first $`L^2` coordinates.
:::

The definition is stated for every real $`s`, but only for $`0<s<1` does the
kernel behave like a fractional derivative. A few elementary members and one
degenerate exponent make the point.

:::theorem "sobolev.gagliardo_scope" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.memGagliardo_const, SobolevSpace.Fractional.memGagliardo_of_eqOn_zero, SobolevSpace.Fractional.memGagliardo_neg_half_iff") (uses := "sobolev.gagliardo_hilbert")
On a finite-measure domain, every constant belongs because its difference
quotient vanishes. On a measurable domain $`\Omega`, every function vanishing
on $`\Omega` also belongs, regardless of its values outside $`\Omega`. At
$`s=-n/2` the denominator exponent is zero and

$$`
\operatorname{MemGagliardo}(n,-n/2,\Omega,u)
\quad\Longleftrightarrow\quad
u\in L^2(\Omega)
`

for finite-measure $`\Omega`.  This concrete degeneracy is why the formal
definition is named `MemGagliardo`, not unconditionally `MemHs`.
:::

:::proof "sobolev.gagliardo_scope"
For constants, and for functions vanishing on a measurable $`\Omega`, the
difference quotient is zero almost everywhere on $`\Omega\times\Omega`.
At $`s=-n/2`, it reduces to $`u(x)-u(y)`. On a finite-measure product domain,
the two pullbacks of an
$`L^2(\Omega)` function are in $`L^2`, and their difference is in $`L^2`;
the converse is the base $`L^2` clause of the definition.
:::

The seminorm detects every continuous function that is not constant on an
open set. Continuity is needed because the condition is stated for raw
functions: the indicator of a single point is not constant, yet its seminorm
is zero.

:::theorem "sobolev.gagliardo_seminorm_positive" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.gagliardoSq_mono, SobolevSpace.Fractional.gagliardoSq_pos_of_isOpen, SobolevSpace.Fractional.gagliardoSq_univ_pos") (uses := "sobolev.gagliardo_space")
For every real $`s`, the seminorm is monotone in the set:
$`[u]_{s,\Omega_1}^2\leq[u]_{s,\Omega_2}^2` when
$`\Omega_1\subseteq\Omega_2`. If $`\Omega` is open and a continuous real
function $`v` takes different values at two points of $`\Omega`, then

$$`
[v]_{s,\Omega}^2>0.
`

In particular a continuous real function on $`\mathbb R^n` that is not
constant has positive seminorm on $`\mathbb R^n`.
:::

:::proof "sobolev.gagliardo_seminorm_positive"
Monotonicity holds because the integrand is nonnegative and the restricted
product measure grows with the set. If $`v(x)\neq v(y)`, continuity gives a
radius $`\rho>0` such that both balls of radius $`\rho` lie in $`\Omega` and
$`v(a)\neq v(b)` for all $`a` in the first ball and $`b` in the second. The
integrand is positive on the product of the two balls, which has positive
measure.
:::

# The whole-space Gagliardo–Fourier identity

:::definition "sobolev.gagliardo_fourier_quantities" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.GagliardoKernel.gagKernel, SobolevSpace.Fractional.GagliardoKernel.gagJ, SobolevSpace.Fractional.gagDouble, SobolevSpace.Fractional.fourierSq") (uses := "sobolev.gagliardo_space")
For $`\xi,h\in\mathbb R^n`, the Fourier-side increment kernel is

$$`
K_{n,s}(\xi,h)
  =\frac{\lvert e^{2\pi i\langle h,\xi\rangle}-1\rvert^2}
    {\lVert h\rVert^{n+2s}},
\qquad
J_{n,s}(\xi)=\int_{\mathbb R^n}K_{n,s}(\xi,h)\,dh.
`

The extended-real quantities `gagDouble` and `fourierSq` are respectively the
complex whole-space Gagliardo seminorm squared and the homogeneous Fourier
seminorm squared. They are kept separate from the inhomogeneous Bessel norm.
:::

The kernel is integrable in $`h` for $`0<s<1`: near $`h=0` the character
differs from one by at most a constant times
$`\lvert\langle h,\xi\rangle\rvert`, so the singularity is integrable when
$`s<1`, while at infinity the numerator is bounded and the denominator is
integrable when $`s>0`. Homogeneity in $`\xi` then reduces $`J_{n,s}` to a
single constant.

:::theorem "sobolev.gagliardo_kernel_profile" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.GagliardoKernel.integrable_gagKernel, SobolevSpace.Fractional.GagliardoKernel.gagJ_pos, SobolevSpace.Fractional.GagliardoKernel.gagJ_eq_mul_rpow") (uses := "sobolev.gagliardo_fourier_quantities")
Assume $`1\leq n` and $`0<s<1`. The kernel is integrable in $`h`,
$`J_{n,s}(\xi)` is positive for $`\xi\neq0`, and for every unit vector $`e`,

$$`
J_{n,s}(\xi)=J_{n,s}(e)\,\lVert\xi\rVert^{2s}.
`

The constant is left as the integral $`J_{n,s}(e)` at a unit vector.
:::

:::proof "sobolev.gagliardo_kernel_profile"
Near the origin, the Fourier character differs from one by at most a constant
times $`\lvert\langle h,\xi\rangle\rvert`; at infinity its norm is at most
two. Radial power-integrability gives the two endpoint conditions. Dilation
gives the factor $`\lVert\xi\rVert^{2s}`, while invariance under linear
isometries makes the remaining value constant on the unit sphere. Positivity
comes from an open slab on which the character is not one.
:::

Writing the double integral in terms of the increment $`h=y-x`, Plancherel
evaluates the inner integral through the multiplier
$`e^{2\pi i\langle h,\xi\rangle}-1`, and Tonelli exchanges the order of
integration so that the kernel profile of the previous theorem appears as the
factor in front of $`\lvert\widehat u(\xi)\rvert^2`.

:::theorem "sobolev.gagliardo_fourier_identity" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.gagDouble_eq_gagJ_mul_fourierSq, SobolevSpace.Fractional.gagliardoSq_univ_eq_gagJ_mul_fourierSq, SobolevSpace.Fractional.gagliardoSq_univ_lt_top_iff, SobolevSpace.Fractional.memGagliardo_univ_iff_fourierSq_lt_top") (uses := "sobolev.gagliardo_seminorm_membership, sobolev.gagliardo_kernel_profile")
For $`1\leq n`, $`0<s<1`, a unit vector $`e`, and
$`u\in L^2(\mathbb R^n;\mathbb C)`,

$$`
\iint_{\mathbb R^n\times\mathbb R^n}
  \frac{\lvert u(x)-u(y)\rvert^2}{\lVert x-y\rVert^{n+2s}}\,dx\,dy
=J_{n,s}(e)
  \int_{\mathbb R^n}\lVert\xi\rVert^{2s}
    \lvert\widehat u(\xi)\rvert^2\,d\xi.
`

The equality is in $`[0,\infty]`, so no finiteness assumption is hidden.
For a real function whose complexification lies in $`L^2`, the same formula
holds for `gagliardoSq`, and `MemGagliardo` on the whole space is equivalent
to finiteness of the homogeneous Fourier seminorm.

This is the normalization of Proposition 3.4 in
{Informal.citet "di-nezza-palatucci-valdinoci-2012"}[] corresponding to
Mathlib's $`2\pi` Fourier character.
:::

:::proof "sobolev.gagliardo_fourier_identity"
Rewrite the double integral using the increment $`h=y-x`. For each fixed
$`h`, translation on $`L^2` is an isometry and its Fourier transform is
multiplication by $`e^{2\pi i\langle h,\xi\rangle}`. Plancherel evaluates the
inner integral, Tonelli exchanges the nonnegative $`h` and $`\xi` integrals,
and the kernel-profile theorem supplies the factor
$`J_{n,s}(e)\lVert\xi\rVert^{2s}`. Positivity and finiteness of the named
constant give the finiteness equivalences.
:::

# The completed whole-space equivalence

The graph space already retains the physical $`L^2` coordinate. This term
controls the low frequencies that the homogeneous Fourier seminorm misses,
so the raw identity yields a comparison of the complete inhomogeneous spaces.

:::theorem "sobolev.gagliardo_fourier_equivalence" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.GagliardoSpace.norm_sq_eq_fourier, SobolevSpace.Fractional.gagliardoFourierConstant, SobolevSpace.Fractional.gagliardoFourierConstant_pos, SobolevSpace.Fractional.GagliardoSpace.toL2CLM, SobolevSpace.Fractional.GagliardoSpace.equivHsSpaceReal, SobolevSpace.Fractional.GagliardoSpace.toL2FunCLM_equivHsSpaceReal, SobolevSpace.Fractional.GagliardoSpace.toL2CLM_equivHsSpaceReal_symm, SobolevSpace.Fractional.GagliardoSpace.norm_equivHsSpaceReal_le, SobolevSpace.Fractional.GagliardoSpace.norm_equivHsSpaceReal_symm_le") (uses := "sobolev.gagliardo_hilbert, sobolev.fourier_real_representatives, sobolev.gagliardo_fourier_quantities")
Assume $`0<s<1`. In every dimension $`n` there is a continuous real-linear
equivalence $`T` from the whole-space Gagliardo space to real $`H^s`.
For $`n\geq1` set
$`J=J_{n,s}(e_0)>0`, where $`e_0` is the first Euclidean unit vector; this is
`gagliardoFourierConstant n s hn`.

Both directions of $`T` preserve the physical real $`L^2` class:

$$`
i_H(Tu)=i_G(u),\qquad i_G(T^{-1}v)=i_H(v),
`

where $`i_G` is `GagliardoSpace.toL2CLM` and $`i_H` is
`HsSpaceReal.toL2FunCLM`. The exact graph-norm identity is

$$`
\|u\|_{\mathrm{Gag}}^2
 =\|i_Gu\|_2^2
  +J\bigl\|\,|\xi|^s\widehat{i_Gu}\,\bigr\|_2^2.
`

For $`n\geq1` the explicit, nonoptimal bounds are

$$`
\|Tu\|_{H^s}\leq(1+J^{-1/2})\|u\|_{\mathrm{Gag}},
\qquad
\|T^{-1}v\|_{\mathrm{Gag}}\leq(1+J^{1/2})\|v\|_{H^s}.
`

The constant $`J` carries Mathlib's $`2\pi` Fourier convention.
:::

:::proof "sobolev.gagliardo_fourier_equivalence" (uses := "sobolev.gagliardo_fourier_identity, sobolev.fourier_norm, sobolev.physical_l2_properties, sobolev.fourier_real_constructor")
For $`w_s(\xi)=(1+|\xi|^2)^{s/2}`, the pointwise bounds
$`|\xi|^s\leq w_s(\xi)\leq1+|\xi|^s` show that a physical $`L^2`
function has Bessel regularity exactly when its homogeneous weighted Fourier
transform lies in $`L^2`. The raw Gagliardo identity therefore identifies
the ranges of the two physical $`L^2` maps. Realizing each physical class in
the other space gives $`T`; injectivity of the physical maps proves
linearity and the inverse laws.

Applying the raw identity to the stored difference-quotient coordinate gives
the exact graph-norm formula. Each graph coordinate is bounded by the graph
norm, while the physical and homogeneous Fourier norms are bounded by the
Bessel norm. The triangle inequality and $`J>0` give the two displayed
bounds, proving continuity in both directions on the complete spaces.
:::

On the Fourier side the comparison with the Bessel norm is sharper, because
the weights $`(1+r^2)^s` and $`1+r^{2s}` differ by at most a factor of two.

:::theorem "sobolev.gagliardo_bessel_norm_comparison" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.norm_sq_two_sided_gagDouble, SobolevSpace.Fractional.norm_sq_two_sided_gagDouble_div_two, SobolevSpace.Fractional.ofReal_norm_sq_le_add_fourierSq, SobolevSpace.Fractional.add_fourierSq_le_two_mul_norm_sq") (uses := "sobolev.gagliardo_fourier_identity, sobolev.fourier_norm, sobolev.physical_l2_representative")
Assume $`n\geq1` and $`0<s<1`, let $`J=J_{n,s}(e_0)` as above, and let
$`f` be the physical $`L^2` representative of $`u\in H^s(\mathbb R^n)`.
With

$$`
N(u)=\lVert f\rVert_{L^2}^2
  +J^{-1}\iint_{\mathbb R^n\times\mathbb R^n}
    \frac{\lvert f(x)-f(y)\rvert^2}{\lVert x-y\rVert^{n+2s}}\,dx\,dy,
`

the Bessel norm satisfies

$$`
\lVert u\rVert_{H^s}^2\leq N(u)\leq 2\,\lVert u\rVert_{H^s}^2.
`

With the homogeneous integral
$`\int\lVert\xi\rVert^{2s}\lvert\widehat f(\xi)\rvert^2\,d\xi` in place of
the Gagliardo term, the left inequality holds for $`0\leq s\leq1` and the
right one for every $`s\geq0`.
:::

:::proof "sobolev.gagliardo_bessel_norm_comparison"
By Plancherel, $`\lVert u\rVert_{H^s}^2` is the integral of
$`(1+\lVert\xi\rVert^2)^s\lvert\widehat f(\xi)\rvert^2`, and by the
Gagliardo-Fourier identity $`N(u)` is the integral of
$`(1+\lVert\xi\rVert^{2s})\lvert\widehat f(\xi)\rvert^2`. For $`r\geq0` and
$`0\leq s\leq1`,

$$`
(1+r^2)^s\leq 1+r^{2s}\leq 2\,(1+r^2)^s.
`

The left inequality is subadditivity of $`t\mapsto t^s`, and the right one
adds $`1\leq(1+r^2)^s` and $`r^{2s}\leq(1+r^2)^s`.
:::

The same Fourier argument identifies the two conditions for raw functions,
not only for $`L^2` classes and complete spaces.

:::theorem "sobolev.gagliardo_function_identification" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.memGagliardo_univ_iff_exists_hsSpace, SobolevSpace.Fractional.memGagliardo_univ_iff_exists_hsSpaceReal, SobolevSpace.Fractional.exists_toL2Fun_eq, SobolevSpace.Fractional.memGagliardo_univ_mono") (uses := "sobolev.gagliardo_fourier_identity, sobolev.physical_l2_representative, sobolev.fourier_real_space, sobolev.fourier_scale_inclusion")
Let $`0<s<1`. A real function $`v` on $`\mathbb R^n` satisfies the
Gagliardo condition on $`\mathbb R^n` if and only if its complexification
agrees almost everywhere with the physical $`L^2` representative of some
$`u\in H^s(\mathbb R^n)`, and $`u` can then be taken in
$`H^s(\mathbb R^n;\mathbb R)`. Consequently the condition is monotone in the
order: for $`0<s\leq t<1`, a function satisfying it at order $`t` satisfies
it at order $`s`.

The step from Fourier data to $`H^s` holds for $`0\leq s\leq2`: an $`L^2`
function $`F` with
$`\int\lVert\xi\rVert^{2s}\lvert\widehat F(\xi)\rvert^2\,d\xi<\infty` is the
physical representative of an element of $`H^s(\mathbb R^n)`.

This is the identification of Proposition 3.4 in
{Informal.citet "di-nezza-palatucci-valdinoci-2012"}[], stated for raw
functions.
:::

:::proof "sobolev.gagliardo_function_identification"
By the Gagliardo-Fourier identity, the Gagliardo condition on $`\mathbb R^n`
is square integrability together with a finite homogeneous Fourier integral.
For $`0\leq s\leq2` the pointwise bounds
$`\lVert\xi\rVert^s\leq(1+\lVert\xi\rVert^2)^{s/2}\leq1+\lVert\xi\rVert^s`
show that such an $`L^2` function has Bessel regularity of order $`s`, and
conversely. An $`L^2` function that agrees almost everywhere with a real
function is real, so the element lies in the real subspace. For monotonicity,
include $`H^t` in $`H^s`; the inclusion preserves the physical
representative.
:::

Smooth compactly supported functions are concrete members, and positivity of
the seminorm shows that some of them have nonzero seminorm.

:::theorem "sobolev.gagliardo_nonconstant_member" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.memGagliardo_univ_of_hasCompactSupport, SobolevSpace.Fractional.gagliardoSq_univ_lt_top_of_hasCompactSupport, SobolevSpace.Fractional.memGagliardo_univ_of_schwartz, SobolevSpace.Fractional.exists_gagliardoSq_univ_pos_lt_top, SobolevSpace.Fractional.exists_nonconstant_memGagliardo_univ") (uses := "sobolev.gagliardo_fourier_identity, sobolev.gagliardo_seminorm_positive")
Let $`0<s<1`. Every smooth compactly supported real function on
$`\mathbb R^n`, and every real function whose complexification is a Schwartz
function, satisfies the Gagliardo condition on $`\mathbb R^n` and has finite
seminorm there. For $`n\geq1` some smooth compactly supported function that
is not constant has positive and finite seminorm on $`\mathbb R^n`.
:::

:::proof "sobolev.gagliardo_nonconstant_member"
A Schwartz function lies in $`H^s(\mathbb R^n)`, so its homogeneous Fourier
integral is finite and the Gagliardo-Fourier identity makes its Gagliardo
double integral finite. A smooth compactly supported function is a Schwartz
function. For the last statement take a bump function equal to one near the
origin and zero far from it. It is continuous and not constant, so its
seminorm is positive.
:::

# Supported closure inside the whole-space scale

:::definition "sobolev.fractional_supported_closure" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.schwartzSupportedInSet, SobolevSpace.Fractional.hsSupportedClosureSubmodule, SobolevSpace.Fractional.HsSupportedClosureSpace") (uses := "sobolev.fourier_space")
For every real $`s`, let

$$`
\widetilde H^s_{\mathcal S}(\Omega)
  =\overline{\operatorname{span}_{\mathbb C}
    \left\{\varphi\in\mathcal S(\mathbb R^n):
      \operatorname{tsupp}\varphi\subseteq\Omega\right\}}^{\,H^s(\mathbb R^n)}.
`

This is a complex closed subspace of the whole-space Fourier model.  Its
elements remain whole-space tempered distributions; it is not a raw function
space on $`\Omega`.
:::

:::theorem "sobolev.fractional_supported_closure_properties" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.isClosed_hsSupportedClosureSubmodule, SobolevSpace.Fractional.hsSupportedClosureSubmodule_mono") (uses := "sobolev.fractional_supported_closure")
The supported closure is a closed, hence complete, subspace of $`H^s`.
It is monotone in the support set:

$$`
\Omega_1\subseteq\Omega_2
\quad\Longrightarrow\quad
\widetilde H^s_{\mathcal S}(\Omega_1)
\subseteq
\widetilde H^s_{\mathcal S}(\Omega_2).
`
:::

:::proof "sobolev.fractional_supported_closure_properties"
Closedness is built into `Submodule.topologicalClosure`.  Completeness follows
from being a closed subspace of the Hilbert space $`H^s`.  Domain monotonicity
holds first for every supported Schwartz generator, then for its complex span,
and finally for the topological closure.
:::

Closedness is what gives access to the Hilbert-space operations: the inclusion
along $`\Omega_1\subseteq\Omega_2` is an isometry because it does not change
the underlying whole-space element, and completeness supplies the orthogonal
projection from $`H^s` onto the closure.

:::theorem "sobolev.fractional_supported_closure_hilbert_api" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.mem_hsSupportedClosureSubmodule_iff, SobolevSpace.Fractional.HsSupportedClosureSpace.toHs, SobolevSpace.Fractional.HsSupportedClosureSpace.ofSchwartz, SobolevSpace.Fractional.HsSupportedClosureSpace.inclusionCLM, SobolevSpace.Fractional.HsSupportedClosureSpace.norm_coe_inclusionCLM_apply, SobolevSpace.Fractional.HsSupportedClosureSpace.inclusionCLM_refl, SobolevSpace.Fractional.HsSupportedClosureSpace.inclusionCLM_comp, SobolevSpace.Fractional.HsSupportedClosureSpace.exists_span_approx, SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection, SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection_coe, SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection_coe_of_subset, SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection_comp_of_subset, SobolevSpace.Fractional.HsSupportedClosureSpace.norm_orthogonalProjection_apply_le, SobolevSpace.Fractional.HsSupportedClosureSpace.sub_coe_orthogonalProjection_mem_orthogonal, SobolevSpace.Fractional.HsSupportedClosureSpace.orthogonalProjection_eq_iff, SobolevSpace.Fractional.HsSupportedClosureSpace.norm_sub_coe_orthogonalProjection_eq_iInf") (uses := "sobolev.fractional_supported_closure_properties")
The supported closure carries its canonical Hilbert-subspace operations.
Every element is an $`H^s`-norm limit of the complex span of supported
Schwartz functions.  If $`\Omega_1\subseteq\Omega_2`, the induced map

$$`
\widetilde H^s_{\mathcal S}(\Omega_1)
\longrightarrow
\widetilde H^s_{\mathcal S}(\Omega_2)
`

is isometric, fixes the underlying whole-space element, and composes
functorially along chains of support-set inclusions.

The orthogonal projection

$$`
P_\Omega:H^s(\mathbb R^n)\longrightarrow
\widetilde H^s_{\mathcal S}(\Omega)
`

is contractive, fixes the supported closure, and has orthogonal residual.
It is the best approximation in the ambient $`H^s` norm.  For nested support
sets, projecting first onto the larger closure does not change the subsequent
projection onto the smaller one.
:::

:::proof "sobolev.fractional_supported_closure_hilbert_api"
The approximation statement is the metric characterization of membership in
the topological closure of the supported Schwartz span.  Support-set inclusion
acts by codomain restriction of the canonical submodule embedding, so it
preserves norms definitionally and its identity and composition laws follow
by subtype extensionality.  Completeness of the closed subspace supplies
Mathlib's orthogonal projection.  Its standard projection theorem gives the
contraction, fixed-point, orthogonal-residual, and best-approximation
properties; monotonicity of the closed submodules gives the nested-projection
law.
:::

The supported closure is nonzero as soon as $`\Omega` has an interior point.

:::theorem "sobolev.fractional_supported_closure_nontrivial" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.ofSchwartzLinear_injective, SobolevSpace.Fractional.exists_ne_zero_mem_hsSupportedClosure, SobolevSpace.Fractional.hsSupportedClosureSubmodule_ne_bot, SobolevSpace.Fractional.nontrivial_hsSupportedClosureSpace, SobolevSpace.Fractional.hsSupportedClosureSubmodule_empty") (uses := "sobolev.fractional_supported_closure_properties")
For every real $`s`, distinct Schwartz functions define distinct elements of
$`H^s(\mathbb R^n)`. If $`\Omega` has nonempty interior, then
$`\widetilde H^s_{\mathcal S}(\Omega)` contains a nonzero element, so it is
not the zero subspace. For $`\Omega=\varnothing` it is the zero subspace.
:::

:::proof "sobolev.fractional_supported_closure_nontrivial"
The maps from Schwartz functions to $`L^2` and from $`L^2` to tempered
distributions are injective. A smooth bump centred at an interior point of
$`\Omega`, supported in a ball contained in $`\Omega`, is a nonzero Schwartz
function with support in $`\Omega`. For the empty set the only such Schwartz
function is zero, and the zero subspace is closed.
:::

# Separation of the three domain models

The three constructions are different spaces in general; identifying them
takes additional theorems and geometric hypotheses.

The constant function $`u=1` on $`(0,1)` shows why the choice of extension
matters. Its intrinsic difference seminorm is zero. It also has a smooth
compactly supported extension equal to one near $`[0,1]`, so it belongs to
every nonnegative-order restriction space. Its extension by zero, however,
has jumps at the endpoints. For $`0<s<1`, pairs lying across the left
endpoint contribute

$$`
\int_0^1\int_{-\infty}^0
  \frac{1}{|x-y|^{1+2s}}\,dy\,dx
 =\frac{1}{2s}\int_0^1x^{-2s}\,dx,
`

which is finite exactly when $`s<1/2`; the right endpoint contributes the
same amount. Membership through some whole-space extension and membership of
the zero extension therefore impose different boundary requirements.

{leanpde_figure "gagliardo-boundary-energy"}

The figure locates the energy. The difference $`|u(x)-u(y)|` is nonzero only
on strips that touch the diagonal at the two endpoints, and cutting out the
points within $`\delta` of an endpoint leaves a finite energy that stays
bounded as $`\delta\to0` only when $`s<1/2`.

* `HsRestrictionSpace` is the complete real Hilbert quotient of whole-space
  $`H^s` by equality almost everywhere on $`\Omega`, available for
  $`s\geq 0`; `hsRestrictionSubmodule` is its raw-function membership
  interface.  The quotient spaces carry functorial surjective contractions
  to subdomains.
* `GagliardoSpace` is the complete real Hilbert graph space of the intrinsic
  difference quotient; its intended Sobolev meaning is $`0<s<1`.
  `gagliardoSubmodule` is its raw-function membership interface, and
  both interfaces carry functorial contractive restriction to subdomains.
* `hsSupportedClosureSubmodule` is a complex, complete, closed subspace of the
  whole-space Hilbert space, available for every real $`s`; it has isometric
  support-set inclusions and canonical orthogonal projection.

The completed whole-space theorem above compares `GagliardoSpace` on
$`\mathbb R^n` with `HsSpaceReal`. On a half-space the domain comparison
also holds: reflect the function evenly across the boundary.
Folding points onto the same side contracts their distance, which controls
the difference quotient. The resulting extension has norm at most $`2`;
the whole-space theorem then identifies the intrinsic and restriction
spaces for $`0<s<1`. On a domain with a $`C^1` extension atlas, reflected
chart extensions glued by the partition of unity give the same
identification by a continuous linear equivalence.
Identifying the supported closure with an intrinsic $`H^s_0(\Omega)` or with
the kernel of a trace map depends on the boundary regularity and on the
order $`s`.

:::theorem "sobolev.gagliardo_half_space_reflection" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.Extension.foldUpper, SobolevSpace.Fractional.Extension.lintegral_norm_sq_comp_foldUpper, SobolevSpace.Fractional.Extension.gagliardoSq_comp_foldUpper_le, SobolevSpace.Fractional.Extension.memGagliardo_comp_foldUpper, SobolevSpace.Fractional.Extension.evenReflectionCLM, SobolevSpace.Fractional.Extension.norm_evenReflectionCLM_le_rpow, SobolevSpace.Fractional.Extension.restrictCLM_comp_evenReflectionCLM") (uses := "sobolev.gagliardo_space, sobolev.gagliardo_restriction")
Let $`n\geq1` and let $`\phi:\mathbb R^n\to\mathbb R^n` replace the last
coordinate by its absolute value, so that $`u\circ\phi` is the even
reflection of a function $`u` on the upper half-space $`\mathbb R^n_+`. If
$`u` is real and almost everywhere strongly measurable on $`\mathbb R^n_+`
and $`n/2+s\geq0`, then

$$`
\int_{\mathbb R^n}|u\circ\phi|^2=2\int_{\mathbb R^n_+}|u|^2,
\qquad
[u\circ\phi]_{s,\mathbb R^n}^2\leq4\,[u]_{s,\mathbb R^n_+}^2.
`

For $`1\leq p<\infty`, $`n/p+s\geq0` and functions with values in a real
normed space, even reflection is a bounded linear map from the Gagliardo
space of exponent $`p` on $`\mathbb R^n_+` to the one on $`\mathbb R^n`, of
norm at most $`4^{1/p}`, and restricting the reflection back to
$`\mathbb R^n_+` gives the identity.
:::

:::proof "sobolev.gagliardo_half_space_reflection"
The fold does not increase distances, so for $`n/p+s\geq0` the difference
quotient of $`u\circ\phi` at $`(x,y)` is at most that of $`u` at
$`(\phi(x),\phi(y))`. The fold carries Lebesgue measure on $`\mathbb R^n` to
twice Lebesgue measure on $`\mathbb R^n_+`, because the boundary hyperplane
is null and reflection preserves measure, and folding both variables carries
the product measure to four times the product measure on
$`\mathbb R^n_+\times\mathbb R^n_+`. Changing variables gives the factors
$`2` and $`4`. Both are at most $`4`, so the graph norm grows by at most
$`4^{1/p}`.
:::

For raw functions the inclusion of the restriction condition in the
Gagliardo condition holds on every set, and the two conditions agree on the
whole space and on the half-space.

:::theorem "sobolev.gagliardo_restriction_comparison" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.memGagliardo_of_memHsRestriction, SobolevSpace.Fractional.hsRestrictionSubmodule_le_gagliardoSubmodule, SobolevSpace.Fractional.memGagliardo_univ_iff_memHsRestriction, SobolevSpace.Fractional.gagliardoSubmodule_univ_eq_hsRestrictionSubmodule, SobolevSpace.Fractional.memGagliardo_upper_iff_memHsRestriction, SobolevSpace.Fractional.gagliardoSubmodule_upper_eq_hsRestrictionSubmodule, SobolevSpace.Fractional.exists_nonconstant_memHsRestriction_univ, SobolevSpace.Fractional.exists_gagliardoSq_upper_pos_lt_top") (uses := "sobolev.fractional_restriction_hilbert, sobolev.gagliardo_hilbert, sobolev.gagliardo_function_identification, sobolev.gagliardo_nonconstant_member, sobolev.gagliardo_half_space_reflection")
Let $`0<s<1`. For every set $`\Omega\subseteq\mathbb R^n`, the restriction
to $`\Omega` of a real function in $`H^s(\mathbb R^n)` satisfies the
Gagliardo condition on $`\Omega`:

$$`
\operatorname{hsRestrictionSubmodule}(n,s,\Omega)
\subseteq
\operatorname{gagliardoSubmodule}(n,s,\Omega).
`

The two submodules are equal for $`\Omega=\mathbb R^n` and, when $`n\geq1`,
for the upper half-space $`\mathbb R^n_+`. For $`n\geq1` some function that
is not constant lies in both on $`\mathbb R^n` with positive and finite
seminorm, and some function satisfies the Gagliardo condition on
$`\mathbb R^n_+` with positive and finite seminorm there.
:::

:::proof "sobolev.gagliardo_restriction_comparison"
A restriction class is realized in the Gagliardo space of $`\Omega` by
`HsRestrictionSpace.toGagliardoCLM`, which restricts to $`\Omega` the
whole-space Gagliardo element of its minimal extension; this gives the
inclusion. On $`\mathbb R^n` the reverse inclusion is the function-level
identification after taking real parts. On $`\mathbb R^n_+` it is the
even-reflection equivalence `GagliardoSpace.halfSpaceEquivHsRestrictionSpace`.
The half-space member is a bump function centred at the origin. Its
seminorm on $`\mathbb R^n_+` is positive by continuity and at most its
seminorm on $`\mathbb R^n`, which is finite.
:::

# Traces into fractional spaces

The trace chapter constructs the flat trace
$`\operatorname{Tr}_+:H^1(\mathbb R^{n+1}_+)\to L^2(\mathbb R^n)` and its
$`W^{1,p}` analogue, and introduces their intrinsic trace spaces as kernel
quotients. The fractional scales of this chapter identify those flat ranges.
At $`p=2` the range is the Fourier space $`H^{1/2}(\mathbb R^n)`; for
$`1<p<\infty` it is the Gagliardo space of order $`1-1/p`.

The Fourier route starts on the whole space. For a Schwartz function $`u` on
$`\mathbb R^{n+1}`, the Fourier transform of $`y\mapsto u(y,0)` is the
integral of $`\widehat u(\eta,\tau)` over the normal frequency $`\tau`.
Cauchy–Schwarz against the weight $`(1+|\eta|^2+\tau^2)^{-s}` gives

$$`
\int_{\mathbb R}(1+|\eta|^2+\tau^2)^{-s}\,d\tau
  =c_s\,(1+|\eta|^2)^{1/2-s},
`

finite exactly when $`s>1/2`. This loses half a derivative, and no more.
The trace constant is $`\kappa_s=c_s^{1/2}`, called `traceConstant s` in Lean.

:::theorem "sobolev.hyperplane_trace_fourier" (parent := "sobolev.fourier") (lean := "SobolevSpace.Fractional.Trace.GeneralOrder.wholeSpaceTraceRealCLM_surjective, SobolevSpace.Fractional.Trace.GeneralOrder.wholeSpaceTraceRealCLM, SobolevSpace.Fractional.Trace.GeneralOrder.wholeSpaceLiftingRealCLM, SobolevSpace.Fractional.Trace.GeneralOrder.norm_wholeSpaceTraceRealCLM_apply_le, SobolevSpace.Fractional.Trace.GeneralOrder.norm_wholeSpaceLiftingRealCLM, SobolevSpace.Fractional.Trace.GeneralOrder.wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM, SobolevSpace.Fractional.Trace.GeneralOrder.toL2FunCLM_wholeSpaceTraceRealCLM_ofSchwartz") (uses := "sobolev.fourier_real_space")
Let $`s>1/2`. There are bounded real-linear maps

$$`
T_s:H^s(\mathbb R^{n+1};\mathbb R)\to H^{s-1/2}(\mathbb R^n;\mathbb R),
\qquad
L_s:H^{s-1/2}(\mathbb R^n;\mathbb R)\to H^s(\mathbb R^{n+1};\mathbb R),
`

with $`\|T_su\|\leq\kappa_s\|u\|`, $`\|L_sv\|=\kappa_s^{-1}\|v\|` and
$`T_sL_s=\mathrm{id}`. In particular $`T_s` is surjective. If $`u` is
represented by a Schwartz function $`f`, the physical representative of
$`T_su` is $`y\mapsto\operatorname{Re}f(y,0)` almost everywhere.
:::

:::proof "sobolev.hyperplane_trace_fourier"
In weighted Fourier coordinates, integration against a unit $`L^2` normal
kernel is contractive; multiplying by $`\kappa_s` gives the physical trace.
The corresponding kernel lifting is isometric before multiplication by
$`\kappa_s^{-1}`. Fubini and the unit normalization give the right-inverse
identity and the exact lifting norm. Agreement with pointwise restriction
for Schwartz functions uses the Fourier slice identity. Both maps preserve
Hermitian symmetry of the Fourier transform, so they restrict to the real
subspaces.
:::

On the half-space, even reflection carries $`H^1(\mathbb R^{n+1}_+)` into
$`H^1(\mathbb R^{n+1})`, where the integer-order comparison of this chapter
identifies it with Fourier $`H^1`. Applying $`T_1` then gives a trace with
values in $`H^{1/2}`.

:::theorem "sobolev.half_space_trace_h_half" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.HalfSpace.Fractional.fractionalTrace_surjective, SobolevSpace.Trace.HalfSpace.Fractional.fractionalTrace, SobolevSpace.Trace.HalfSpace.Fractional.fractionalLifting, SobolevSpace.Trace.HalfSpace.Fractional.physical_fractionalTrace, SobolevSpace.Trace.HalfSpace.Fractional.fractionalTrace_restrict, SobolevSpace.Trace.HalfSpace.Fractional.fractionalTrace_fractionalLifting, SobolevSpace.Trace.HalfSpace.Fractional.norm_fractionalTrace_le, SobolevSpace.Trace.HalfSpace.Fractional.norm_fractionalLifting_le, SobolevSpace.Trace.HalfSpace.Fractional.ker_fractionalTrace") (uses := "sobolev.hyperplane_trace_fourier, sobolev.flat_trace, sobolev.integer_fourier_equivalence")
There are bounded linear maps

$$`
\operatorname{Tr}^{1/2}:H^1(\mathbb R^{n+1}_+)\to H^{1/2}(\mathbb R^n;\mathbb R),
\qquad
E^{1/2}:H^{1/2}(\mathbb R^n;\mathbb R)\to H^1(\mathbb R^{n+1}_+)
`

such that the physical $`L^2` representative of $`\operatorname{Tr}^{1/2}u`
is $`\operatorname{Tr}_+u`, and $`\operatorname{Tr}^{1/2}E^{1/2}=\mathrm{id}`.
So every element of real $`H^{1/2}(\mathbb R^n)` is the trace of a half-space
$`H^1` function, and $`\operatorname{Tr}^{1/2}` has the same kernel as
$`\operatorname{Tr}_+`. On restrictions of whole-space functions,
$`\operatorname{Tr}^{1/2}` agrees with $`T_1`. Both norm bounds are explicit
products of the constants of the maps involved.
:::

:::proof "sobolev.half_space_trace_h_half"
The trace is the composite of even reflection, the integer-order
equivalence and $`T_1`. Its physical value is $`\operatorname{Tr}_+u`
because the reflected function restricts back to $`u` and the whole-space
trace of a restriction is its half-space trace. The
lifting is $`L_1` followed by restriction to the half-space. Injectivity of
the physical representative on $`H^{1/2}` turns the physical identity into
the kernel identity.
:::

:::theorem "sobolev.hilbert_trace_space_identification" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.HalfSpace.Fractional.trace_fractionalLifting, SobolevSpace.Trace.HalfSpace.Fractional.range_trace_eq_range_fractionalL2, SobolevSpace.Trace.HalfSpace.Fractional.traceSpaceEquiv, SobolevSpace.Trace.HalfSpace.Fractional.physical_traceSpaceEquiv, SobolevSpace.Trace.HalfSpace.Fractional.norm_traceSpaceEquiv_le, SobolevSpace.Trace.HalfSpace.Fractional.norm_traceSpaceEquiv_symm_le, SobolevSpace.Trace.HalfSpace.Fractional.traceSpace_norm_comparisons") (uses := "sobolev.hilbert_trace_space, sobolev.half_space_trace_h_half")
The range of $`\operatorname{Tr}_+` in $`L^2(\mathbb R^n)` is exactly the
set of physical representatives of real $`H^{1/2}(\mathbb R^n)`. The
quotient $`\mathcal T^{1/2}(\mathbb R^n)` of the trace chapter is
isomorphic to $`H^{1/2}(\mathbb R^n;\mathbb R)` by a continuous linear
equivalence compatible with the two boundary realizations in $`L^2`, and the
quotient norm and the Bessel norm bound each other with explicit constants.
:::

:::proof "sobolev.hilbert_trace_space_identification"
Since $`\operatorname{Tr}^{1/2}` and $`\operatorname{Tr}_+` have the same
kernel, $`\operatorname{Tr}^{1/2}` descends to the quotient; the lifting
followed by the quotient map is its inverse. The forward bound applies the
trace bound to the minimal representative, and the reverse bound uses
$`E^{1/2}v` as one representative of the class of $`v`.
:::

For $`p\neq2` there is no Fourier characterization to use, and the boundary
space is the Gagliardo space of order $`1-1/p` with exponent $`p`. Its
defining energy for a trace $`g=\operatorname{Tr}_pu` is

$$`
\int_{\mathbb R^n}\int_{\mathbb R^n}
  \frac{|g(x)-g(y)|^p}{|x-y|^{n+p-1}}\,dx\,dy .
`

For smooth $`u`, split $`g(x)-g(y)` through the two points at height
$`|x-y|` above $`x` and $`y`. The two vertical pieces are controlled by
Hardy's inequality in the normal variable and the horizontal piece by a
translation estimate. Density and Fatou's lemma pass the bound to
$`W^{1,p}`.

:::theorem "sobolev.flat_trace_gagliardo" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.HalfSpace.exists_trace_fractional_bound, SobolevSpace.Trace.HalfSpace.lintegral_traceLp_sub_rpow_div_lt_top, SobolevSpace.Trace.HalfSpace.memGagliardo_traceLp, SobolevSpace.Trace.HalfSpace.traceGagliardo, SobolevSpace.Trace.HalfSpace.toLp_traceGagliardo, SobolevSpace.Trace.HalfSpace.exists_norm_traceGagliardo_le, SobolevSpace.Trace.HalfSpace.toLp_traceGagliardo_two_apply_ae") (uses := "sobolev.flat_trace_finite_exponent, sobolev.gagliardo_space")
Let $`1<p<\infty` and $`n\geq0`; the case $`n=0` is trivial, since the energy
vanishes on a one-point boundary. There is a constant $`C` such that for
every $`u\in W^{1,p}(\mathbb R^{n+1}_+)` the energy above is at most
$`C\sum_i\|\partial_iu\|_p^p`. Consequently $`\operatorname{Tr}_pu` satisfies
the Gagliardo condition of order $`1-1/p`, and the trace defines a bounded
linear map

$$`
W^{1,p}(\mathbb R^{n+1}_+)\longrightarrow
\operatorname{GagliardoSpace}(n,1-1/p,\mathbb R^n;p)
`

whose first coordinate is the physical $`L^p` trace and whose norm is at
most $`(p+C)^{1/p}`, with the same $`C` as in the energy bound. At $`p=2` it
agrees with the Hilbert trace $`\operatorname{Tr}_+`.
:::

:::proof "sobolev.flat_trace_gagliardo"
The smooth estimate is the splitting described above. For general $`u`,
approximate by smooth compactly supported functions, pass to an almost
everywhere convergent subsequence of traces, and apply Fatou's lemma to the
energy integral. The norm bound adds the $`L^p` trace estimate to the
energy estimate.
:::

The inverse direction is an explicit extension. Given boundary data $`g`,
set

$$`
(E_\mu g)(x,t)=\chi(t)\,(\mu_t*g)(x),
`

where $`\mu_t` is a mollifier at scale $`t` and $`\chi` is a cutoff equal
to one near $`t=0` and vanishing for $`t\geq2`. The slices converge to $`g`
in $`L^p` as $`t\to0`, and the derivatives of $`E_\mu g` are controlled by
the Gagliardo energy of $`g`.

:::theorem "sobolev.flat_trace_gagliardo_lifting" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.HalfSpace.traceGagliardo_surjective, SobolevSpace.Trace.HalfSpace.mollifiedLifting, SobolevSpace.Trace.HalfSpace.traceLp_mollifiedLifting_ae, SobolevSpace.Trace.HalfSpace.traceGagliardo_mollifiedLifting, SobolevSpace.Trace.HalfSpace.traceGagliardo_comp_mollifiedLifting, SobolevSpace.Trace.HalfSpace.memGagliardo_iff_exists_traceLp, SobolevSpace.Trace.HalfSpace.range_restrict_traceLp_eq_gagliardoDomain") (uses := "sobolev.flat_trace_gagliardo")
Let $`1<p<\infty`. For every mollifier $`\mu`, $`E_\mu` is a bounded linear
map from the Gagliardo space of order $`1-1/p` into
$`W^{1,p}(\mathbb R^{n+1}_+)`, and it is a right inverse of the trace of the
previous theorem. Hence that trace is surjective, and a function
$`g:\mathbb R^n\to\mathbb R` satisfies the Gagliardo condition of order
$`1-1/p` if and only if it agrees almost everywhere with the trace of some
$`u\in W^{1,p}(\mathbb R^{n+1}_+)`.
:::

:::proof "sobolev.flat_trace_gagliardo_lifting"
The slices of $`E_\mu g` converge to $`g` in $`L^p`, which identifies the
trace. The tangential derivatives are zero-mean kernel fields times the
cutoff, and the Gagliardo energy of $`g` bounds them. The normal derivative
has one more term, from the derivative of the cutoff, which the $`L^p` norm
of $`g` bounds.
:::

:::theorem "sobolev.flat_lp_trace_space_identification" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.HalfSpace.ker_traceGagliardo, SobolevSpace.Trace.HalfSpace.lpTraceSpaceEquivGagliardo, SobolevSpace.Trace.HalfSpace.lpTraceSpaceEquivGagliardo_traceLpClass, SobolevSpace.Trace.HalfSpace.lpTraceSpaceEquivGagliardo_symm_apply, SobolevSpace.Trace.HalfSpace.toLp_lpTraceSpaceEquivGagliardo, SobolevSpace.Trace.HalfSpace.norm_lpTraceSpaceEquivGagliardo_le, SobolevSpace.Trace.HalfSpace.norm_lpTraceSpaceEquivGagliardo_symm_le") (uses := "sobolev.flat_lp_trace_space, sobolev.flat_trace_gagliardo_lifting")
For $`1<p<\infty`, the finite-exponent trace quotient of the trace chapter
is isomorphic, by a continuous linear equivalence, to
$`\operatorname{GagliardoSpace}(n,1-1/p,\mathbb R^n;p)`. The equivalence
sends the class of $`u` to its fractional trace, its $`L^p` coordinate is the
physical boundary realization, and its norm and the norm of its inverse are
bounded by the norms of the trace and of the standard mollified lifting.
:::

:::proof "sobolev.flat_lp_trace_space_identification"
The fractional trace and the physical trace have the same kernel, so the
fractional trace descends to the quotient. The standard lifting followed by
the quotient map is its inverse by the right-inverse identity and injectivity
of the quotient's boundary realization.
:::

The estimate, the lifting and the right-inverse identity use only the norm
and the linear structure of the target, so they hold for boundary data in a
Banach space.

:::theorem "sobolev.vector_flat_trace_gagliardo" (parent := "sobolev.fourier") (lean := "SobolevSpace.VectorValued.Trace.HalfSpace.exists_trace_fractional_bound, SobolevSpace.VectorValued.Trace.HalfSpace.memGagliardo_traceLp, SobolevSpace.VectorValued.Trace.HalfSpace.traceGagliardo, SobolevSpace.VectorValued.Trace.HalfSpace.toLp_traceGagliardo, SobolevSpace.VectorValued.Trace.HalfSpace.exists_norm_traceGagliardo_le, SobolevSpace.VectorValued.Trace.HalfSpace.traceGagliardo_eq_zero_iff, SobolevSpace.VectorValued.Trace.HalfSpace.mollifiedLifting, SobolevSpace.VectorValued.Trace.HalfSpace.traceGagliardo_comp_mollifiedLifting, SobolevSpace.VectorValued.Trace.HalfSpace.traceGagliardo_surjective") (uses := "sobolev.flat_trace_gagliardo, sobolev.flat_trace_gagliardo_lifting")
Let $`F` be a real Banach space and $`1<p<\infty`. The trace of
$`W^{1,p}(\mathbb R^{n+1}_+;F)` satisfies the Gagliardo condition of order
$`1-1/p` with values in $`F`, and defines a bounded linear map into
$`\operatorname{GagliardoSpace}(n,1-1/p,\mathbb R^n;p;F)` whose kernel is the
kernel of the physical trace. For every mollifier the $`F`-valued mollified
lifting is a bounded right inverse, so this trace is surjective.
:::

:::proof "sobolev.vector_flat_trace_gagliardo"
For a boundary difference $`g(x)-g(y)` with $`r=|x-y|`, pass through the
points at height $`r` above $`x` and above $`y`. The two vertical legs are
controlled by Hardy's inequality in the normal variable, applied to the real
function $`t\mapsto\|\partial_tu(\cdot,t)\|_F`, and the horizontal leg at
height $`r` by a tangential translation estimate. Integrating against
$`r^{-n-(1-1/p)p}` gives the fractional energy bound for compactly supported
$`C^1` functions, with a constant depending only on $`n` and $`p`. Compact
smooth density, an almost everywhere convergent subsequence of boundary
values, and Fatou's lemma for nonnegative integrands extend the bound to the
Sobolev trace; Fatou keeps the constant. The lifting is the cutoff
mollification of the scalar case with a Bochner integral in place of the
real one. No approximation property of $`F` is used.
:::

# Traces on curved boundaries

On a $`C^1` domain the half-space theory is applied in each boundary chart.
The data are a surface function together with one $`H^{1/2}` function per
chart, and they must agree: the $`i`th coordinate must represent the
localized pullback $`\Lambda_ig` of the surface function to the flat
boundary. Nothing in this space refers to an interior extension.

:::definition "sobolev.c1_half_order_boundary_space" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.HalfOrderBoundarySpace, SobolevSpace.Trace.C1.Fractional.BoundaryChartData, SobolevSpace.Trace.C1.Fractional.coordinateCompatibility, SobolevSpace.Trace.C1.Fractional.halfOrderBoundarySubmodule, SobolevSpace.Trace.C1.Fractional.boundaryValue, SobolevSpace.Trace.C1.Fractional.chartValue, SobolevSpace.Trace.C1.Fractional.boundaryValue_injective, SobolevSpace.Trace.C1.Fractional.norm_sq_halfOrderBoundarySpace, SobolevSpace.Trace.C1.Fractional.mem_range_boundaryValue_iff") (uses := "sobolev.surface_measure, sobolev.extension.atlas")
Let $`\Omega\subseteq\mathbb R^{m+1}` carry an operational $`C^1` atlas with
$`N` boundary charts. The chartwise half-order boundary space is the closed
subspace of the Hilbert product

$$`
L^2(\partial\Omega,d\sigma)\times\prod_{i=1}^NH^{1/2}(\mathbb R^m;\mathbb R)
`

of tuples $`(g,v_1,\dots,v_N)` in which each $`v_i` represents
$`\Lambda_ig`. Its norm satisfies

$$`
\|(g,v)\|^2=\|g\|_{L^2(\partial\Omega)}^2+\sum_{i=1}^N\|v_i\|_{H^{1/2}}^2 .
`

The boundary-value map $`(g,v)\mapsto g` is injective, and $`g` lies in its
range exactly when every $`\Lambda_ig` lies in real $`H^{1/2}(\mathbb R^m)`.
:::

Injectivity is the reason this space is concrete: the chart coordinates are
determined by the surface function, so the space is a set of functions on
$`\partial\Omega` with a stronger norm.

The trace into this space is assembled from the flat fractional trace in each
chart, and the lifting runs the flat Fourier lifting backwards through each
chart and sums.

:::theorem "sobolev.c1_fractional_trace" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.fractionalTrace_surjective, SobolevSpace.Trace.C1.Fractional.fractionalTrace, SobolevSpace.Trace.C1.Fractional.localFractionalTrace, SobolevSpace.Trace.C1.Fractional.norm_fractionalTrace_sq, SobolevSpace.Trace.C1.Fractional.ker_fractionalTrace, SobolevSpace.Trace.C1.Fractional.lifting, SobolevSpace.Trace.C1.Fractional.trace_lifting, SobolevSpace.Trace.C1.Fractional.norm_lifting_le, SobolevSpace.Trace.C1.Fractional.range_trace_eq_range_boundaryValue, SobolevSpace.Trace.C1.Fractional.mem_range_trace_iff") (uses := "sobolev.c1_half_order_boundary_space, sobolev.trace_operator, sobolev.half_space_trace_h_half")
On an operational $`C^1` domain there is a bounded linear map

$$`
\operatorname{Tr}^{1/2}:H^1(\Omega)\to\text{(chartwise half-order boundary space)}
`

whose surface component is the trace $`\operatorname{Tr}u` and whose $`i`th
chart component is the flat fractional trace of the flattened $`i`th piece of
$`u`. Its norm is given by

$$`
\|\operatorname{Tr}^{1/2}u\|^2
 =\|\operatorname{Tr}u\|_{L^2(\partial\Omega)}^2
 +\sum_{i=1}^N\|\operatorname{Tr}^{1/2}_iu\|_{H^{1/2}}^2,
`

and its kernel is $`\ker\operatorname{Tr}`. A bounded lifting $`L` with
$`\operatorname{Tr}(Lg)=g` makes $`\operatorname{Tr}^{1/2}` surjective. So
$`g\in L^2(\partial\Omega)` is the trace of an $`H^1(\Omega)` function if and
only if every localized chart coordinate $`\Lambda_ig` lies in
$`H^{1/2}(\mathbb R^m)`.
:::

:::proof "sobolev.c1_fractional_trace"
The chart component is the half-space fractional trace of
{uses "sobolev.half_space_trace_h_half"}[] composed with the $`i`th
flattening operator. Its physical representative is the localized flat trace,
which is the compatibility condition, so the tuple lies in the closed
subspace. The norm identity is the product norm, and the kernel statement
follows from injectivity of the boundary-value map.

The lifting sums, over the charts, the whole-space Fourier lifting of
$`v_i`, restricted to the half-space and transported back to $`\Omega` by
the prepared chart operator. The boundary cutoffs sum to one on
$`\partial\Omega`, so the traces of the pieces add up to $`g`. The bound on
$`L` is explicit: each piece costs at most
$`\|P_i\|\,\|J\|\,\pi^{-1/2}\|v_i\|`, where $`P_i` is the prepared chart
operator and $`J` the half-space $`H^1` graph identification.
:::

With the trace and the lifting in hand, the
{bpref "sobolev.c1_hilbert_trace_space"}[intrinsic trace quotient] can be
compared with the chartwise space, and two atlases can be compared with each
other.

:::theorem "sobolev.c1_half_order_identification" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.boundaryValue_traceSpaceEquiv, SobolevSpace.Trace.C1.Fractional.traceSpaceEquiv, SobolevSpace.Trace.C1.Fractional.traceSpaceEquiv_symm_apply, SobolevSpace.Trace.C1.Fractional.norm_traceSpaceEquiv_le, SobolevSpace.Trace.C1.Fractional.norm_le_norm_traceSpaceEquiv, SobolevSpace.Trace.C1.Fractional.atlasEquiv_fractionalTrace, SobolevSpace.Trace.C1.Fractional.boundaryValue_atlasEquiv, SobolevSpace.Trace.C1.Fractional.atlasEquiv, SobolevSpace.Trace.C1.Fractional.atlasEquiv_trans, SobolevSpace.Trace.C1.Fractional.atlasEquiv_symm, SobolevSpace.Trace.C1.Fractional.norm_atlasEquiv_le, SobolevSpace.Trace.C1.Fractional.range_boundaryValue_eq_of_atlases") (uses := "sobolev.c1_hilbert_trace_space, sobolev.c1_fractional_trace, sobolev.hilbert_trace_space_identification")
The quotient $`H^1(\Omega)/\ker\operatorname{Tr}` is isomorphic, as a Banach
space, to the chartwise half-order boundary space, by an isomorphism that
preserves surface values. The two norms are comparable:

$$`
\|\Phi q\|\le\|\operatorname{Tr}^{1/2}\|\,\|q\|,
\qquad
\|q\|\le\|L\|\,\|\Phi q\| .
`

For two operational atlases $`A` and $`B` of the same domain, the map
$`\operatorname{Tr}^{1/2}_B\circ L_A` is an isomorphism between their
chartwise spaces. It preserves surface values, sends $`\operatorname{Tr}^{1/2}_Au`
to $`\operatorname{Tr}^{1/2}_Bu`, composes along a third atlas, is inverted by
exchanging $`A` and $`B`, and has norm at most
$`\|\operatorname{Tr}^{1/2}_B\|\,\|L_A\|`. In particular both atlases admit
the same surface functions.
:::

:::proof "sobolev.c1_half_order_identification"
The fractional trace has the same kernel as $`\operatorname{Tr}`, so it
descends to the quotient. The class of $`Lg` is an inverse, because
$`\operatorname{Tr}^{1/2}(Lg)=g` by injectivity of the boundary-value map.
The two bounds are the operator bound of $`\operatorname{Tr}^{1/2}` on the
minimal representative and the quotient norm of $`Lg`.

For the change of atlas, the physical $`H^1` trace does not depend on the
atlas (the case $`p=2` of {uses "sobolev.trace_atlas_independence"}[]).
Tracing $`L_Ag` with $`B` therefore returns the surface function of $`g`, and
since surface values determine chart coordinates in either space, the two
composites are mutually inverse.
:::

This is the curved-boundary form of the
{bpref "sobolev.hilbert_trace_space_identification"}[half-space identification]. Here the fractional
condition is imposed chart by chart instead of by a single Fourier
transform on the boundary.

For $`1<p<\infty` the range of $`\operatorname{Tr}_p` is characterized chart
by chart through Gagliardo spaces, and the three results below are the local
pieces. In each chart the boundary datum is
multiplied by the partition function $`\psi_i`, pulled back to the flat
boundary $`\mathbb R^m`, and extended by zero off the chart. Call the result
$`\Lambda_ig`. The first result says that $`\Lambda_i\operatorname{Tr}_pu`
always has fractional regularity of order $`1-1/p`.

:::theorem "sobolev.c1_lp_local_fractional_trace" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.FiniteExponent.memGagliardo_localizedBoundaryCoordinates_traceLp, SobolevSpace.Trace.C1.Fractional.FiniteExponent.localTrace, SobolevSpace.Trace.C1.Fractional.FiniteExponent.toLp_localTrace_apply_ae, SobolevSpace.Trace.C1.Fractional.FiniteExponent.toLp_localTrace, SobolevSpace.Trace.C1.Fractional.FiniteExponent.norm_localTrace_le, SobolevSpace.Trace.C1.Fractional.FiniteExponent.localPhysicalTraceLp_eq_boundaryCutoff, SobolevSpace.Trace.C1.Fractional.FiniteExponent.localizedBoundaryCoordinates_traceLp, SobolevSpace.Trace.C1.Fractional.FiniteExponent.toLp_localTrace_eq_localizedBoundaryCoordinates") (uses := "sobolev.trace_operator_finite_exponent, sobolev.flat_trace_gagliardo, sobolev.extension.atlas")
Let $`\Omega\subseteq\mathbb R^{m+1}` carry an operational $`C^1` atlas and
let $`p>1` be real. For every chart $`i` there is a bounded linear map

$$`
\operatorname{Tr}^{(i)}_p:W^{1,p}(\Omega)\longrightarrow
\operatorname{GagliardoSpace}(m,1-1/p,\mathbb R^m;p),
`

the flat fractional trace of the flattened $`i`th piece of $`u`, with norm at
most the product of the norms of the flat trace and of the flattening
operator. Its $`L^p` coordinate is $`\Lambda_i\operatorname{Tr}_pu`. The
chart contribution of the physical trace is $`\psi_i\operatorname{Tr}_pu`.
In particular $`\Lambda_i\operatorname{Tr}_pu` satisfies the Gagliardo
condition of order $`1-1/p` for every $`u\in W^{1,p}(\Omega)`.
:::

:::proof "sobolev.c1_lp_local_fractional_trace"
Flattening sends the $`i`th piece of $`u` to $`W^{1,p}` of the upper
half-space, and {uses "sobolev.flat_trace_gagliardo"}[] gives its trace in
the Gagliardo space. The work is in identifying the base coordinate. The
physical trace is assembled from the same partition pieces, so the flat trace
of the flattened piece and the zero-extended chart coordinates of
$`\operatorname{Tr}_pu` agree almost everywhere. The comparison transports
the flat surface measure through the chart, and it also has to cover the
complement of the chart target, where both sides vanish.
:::

The second result runs the same charts in the other direction. The prepared
chart operator $`T_i` takes a field on $`\mathbb R^{m+1}`, restricts it to the
chart target, pulls it back through the chart after a cutoff, and restricts
to $`\Omega`. Its trace is computed from the flat trace.

:::theorem "sobolev.c1_lp_chart_transport" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.FiniteExponent.traceLp_chartTransport, SobolevSpace.Trace.C1.Fractional.FiniteExponent.traceLp_apply_ae_of_contDiff, SobolevSpace.Trace.C1.Fractional.FiniteExponent.chartTransport, SobolevSpace.Trace.C1.Fractional.FiniteExponent.flatTargetCutoff, SobolevSpace.Trace.C1.Fractional.FiniteExponent.flatTargetCutoff_apply_ae, SobolevSpace.Trace.C1.Fractional.FiniteExponent.chartTransport_base_apply_ae, SobolevSpace.Trace.C1.Fractional.FiniteExponent.flatTargetCutoff_lift_localizedBoundaryCoordinates") (uses := "sobolev.trace_operator_finite_exponent, sobolev.flat_trace_finite_exponent, sobolev.global_density")
Let $`p>1` be real.

1. If the base function of $`u\in W^{1,p}(\Omega)` has a $`C^1`
   representative $`f` on $`\mathbb R^{m+1}`, then $`\operatorname{Tr}_pu=f`
   almost everywhere on $`\partial\Omega`. No support condition on $`f` is
   needed.
2. For every $`u\in W^{1,p}(\mathbb R^{m+1})`, the trace of $`T_iu` is the flat
   trace of $`u` on $`\{x_{m+1}=0\}`, multiplied by an auxiliary cutoff
   $`\eta_i` on the chart target and moved to $`\partial\Omega` through the
   chart.
3. The cutoff $`\eta_i` fixes every localized datum $`\Lambda_ig`, since
   $`\eta_i=1` on the chart image of the support of $`\psi_i`.
:::

:::proof "sobolev.c1_lp_chart_transport"
For a compactly supported smooth $`u` both sides of the second statement are
restrictions of continuous functions, and the first statement identifies
them. Both sides are bounded linear in $`u`, and smooth compactly supported
functions are dense in $`W^{1,p}(\mathbb R^{m+1})` by
{uses "sobolev.global_density"}[], so the identity extends. The last
statement is a pointwise check that separates the points of the chart target
where $`\psi_i` vanishes.
:::

Composing the flat lifting with reflection across $`\{x_{m+1}=0\}` and with
$`T_i` gives a lifting for one chart.

:::theorem "sobolev.c1_lp_local_lifting" (parent := "sobolev.fourier") (lean := "SobolevSpace.Trace.C1.Fractional.FiniteExponent.traceLp_localLifting_localizedBoundaryCoordinates, SobolevSpace.Trace.C1.Fractional.FiniteExponent.localLifting, SobolevSpace.Trace.C1.Fractional.FiniteExponent.traceLp_localLifting, SobolevSpace.Trace.C1.Fractional.FiniteExponent.norm_localLifting_le, SobolevSpace.Trace.C1.Fractional.FiniteExponent.lifting_apply") (uses := "sobolev.c1_lp_chart_transport, sobolev.flat_trace_gagliardo_lifting, sobolev.c1_lp_local_fractional_trace")
Let $`p>1` be real. For each chart $`i` the map

$$`
L_i=T_i\circ E\circ E_\mu:
\operatorname{GagliardoSpace}(m,1-1/p,\mathbb R^m;p)\longrightarrow
W^{1,p}(\Omega),
`

with $`E_\mu` the standard mollified lifting and $`E` extension by reflection,
is bounded, with $`\|L_i\|\le\|T_i\|\,\|E\|\,\|E_\mu\|`. The trace of
$`L_iv` is the chart image of $`\eta_i` times $`v`. If $`v` represents
$`\Lambda_ig` for a surface datum $`g`, then
$`\operatorname{Tr}_p(L_iv)=\psi_ig`. The full lifting is
$`L(v_1,\dots,v_N)=\sum_iL_iv_i`.
:::

:::proof "sobolev.c1_lp_local_lifting"
The mollified lifting has flat trace $`v` by
{uses "sobolev.flat_trace_gagliardo_lifting"}[], and reflection does not
change the trace on the flat boundary. The chart-transport identity then
gives the trace of $`L_iv`. When $`v` represents $`\Lambda_ig`, the cutoff
$`\eta_i` acts as the identity, and moving $`\Lambda_ig` back through the
chart returns $`\psi_ig`.
:::

Summing over the charts, $`\sum_i\psi_i=1` on $`\partial\Omega` gives
$`\operatorname{Tr}_p(Lv)=g` whenever each $`v_i` represents $`\Lambda_ig`.
With the local trace this proves the range characterization stated with the
{bpref "sobolev.c1_lp_trace_space"}[finite-exponent trace space].
