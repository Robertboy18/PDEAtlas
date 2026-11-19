/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

import Blueprint.Chapters.Foundations.Distributions
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Distribution.Support
import PDE.DistributionTheory.TemperedDistribution.AffinePushforward
import PDE.DistributionTheory.TemperedDistribution.Convolution
import PDE.DistributionTheory.TemperedDistribution.Pushforward
import PDE.DistributionTheory.TemperedDistribution.Sobolev
import PDE.DistributionTheory.TemperedDistribution.Translation

/-!
# Tempered distributions

The Fourier and support structure inherited directly from
Mathlib's tempered-distribution API, together with our convolution and
geometric transport operations.
-/

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option verso.blueprint.autoDeps false
set_option verso.blueprint.externalCode.strictResolve true
set_option verso.blueprint.subNumberingPrefix "first"
-- Verso directive attributes cannot be split across lines, while blank lines
-- delimit Markdown paragraphs and display blocks inside the enclosing command.
set_option linter.style.emptyLine false
set_option linter.style.longLine false

-- Verso documents are introduced by `#doc`.
set_option linter.hashCommand false in
#doc (Manual) "Tempered Distributions" =>

# Fourier analysis on the Schwartz dual

Compactly supported test functions are the right probes for local questions.
Fourier analysis instead uses the Schwartz space, whose functions and
derivatives decay faster than every polynomial. Its continuous dual is the
space of tempered distributions. Mathlib supplies the space, its Fourier
transform and its support theory. Convolution with Schwartz functions,
translation and pushforward are built on top of it.

For example, the Gaussian $`e^{-|x|^2}` is a Schwartz function: every
derivative is a polynomial times the same Gaussian, so it still decays
faster than any inverse power. A polynomial need not decay at all, but it
defines a tempered distribution because integrating it against a Schwartz
probe is controlled by the probe's decay. Dirac masses and their derivatives
are tempered too. “Tempered” therefore restricts growth at infinity rather
than requiring pointwise smoothness.

The Fourier convention matters when turning differentiation into algebra.
For integrable functions the kernel is $`e^{-2\pi i x\cdot\xi}`, giving

$$`
\widehat{\partial_j u}(\xi)=2\pi i\xi_j\widehat u(\xi),
\qquad
\widehat{-\Delta u}(\xi)=4\pi^2|\xi|^2\widehat u(\xi).
`

The transposed operators extend these identities to tempered distributions.
The Sobolev chapter uses this frequency weight to measure derivatives of
noninteger order.

:::definition "foundations.distributions.tempered" (parent := "foundations.distributions") (lean := "TemperedDistribution") (uses := "foundations.distributions.distribution")
A tempered distribution on a real normed space $`E`, with values in a complex
topological vector space $`F`, is a continuous complex
linear functional on the Schwartz space:

$$`
  \mathcal S'(E;F)
  :=\mathcal S(E;\mathbb C)\longrightarrow_{\mathrm{cont},\mathbb C}F.
`

Mathlib equips this dual with the topology of pointwise convergence, which
is weaker than the strong dual topologies common in functional analysis.
Continuity statements about tempered distributions refer to this topology.
:::

The reason to pass to the Schwartz dual is that the Fourier transform preserves
$`\mathcal S`, so its transpose acts on $`\mathcal S'`. On a finite-dimensional
inner-product space the transform is invertible on $`\mathcal S`, and the
transposed maps inherit invertibility.

:::definition "foundations.distributions.tempered_fourier_equiv" (parent := "foundations.distributions") (lean := "FourierTransform.fourierCLE, FourierTransform.fourierCLE_apply, FourierTransform.fourierCLE_symm_apply") (uses := "foundations.distributions.tempered")
On a finite-dimensional real inner-product space, Fourier transform and inverse
Fourier transform form a continuous complex-linear equivalence

$$`
  \mathcal F:\mathcal S'(E;F)\simeq_{\mathrm{cont},\mathbb C}
  \mathcal S'(E;F).
`

Its forward map is $`T\mapsto\mathcal FT` and its inverse is
$`T\mapsto\mathcal F^{-1}T`.
:::

Both composites being the identity is what the word equivalence records. The two
laws are stated separately because the two directions are used separately, for
instance when convolution is defined through $`\mathcal F^{-1}` and then
transformed back.

:::theorem "foundations.distributions.tempered_fourier_inversion" (parent := "foundations.distributions") (lean := "FourierPair.fourierInv_fourier_eq, FourierInvPair.fourier_fourierInv_eq") (uses := "foundations.distributions.tempered_fourier_equiv")
For every tempered distribution $`T`,

$$`
  \mathcal F^{-1}(\mathcal FT)=T,
  \qquad
  \mathcal F(\mathcal F^{-1}T)=T.
`
:::

:::proof "foundations.distributions.tempered_fourier_inversion"
Mathlib first proves that Fourier transform and inverse Fourier transform form
both a `FourierPair` and a `FourierInvPair` on tempered distributions. The two
generic pair identities are precisely the displayed inverse equations, and
they are the inverse laws used by the continuous linear equivalence.
:::

The equivalence is characterized by its pairing with Schwartz functions.

:::theorem "foundations.distributions.tempered_fourier_action" (parent := "foundations.distributions") (lean := "TemperedDistribution.fourier_apply") (uses := "foundations.distributions.tempered_fourier_equiv")
Fourier transform on tempered distributions is the transpose of Fourier
transform on Schwartz functions:

$$`
  \langle\mathcal FT,\varphi\rangle
  =\langle T,\mathcal F\varphi\rangle.
`

This equation fixes Mathlib's convention: the transpose uses the forward
Schwartz transform itself, with no hidden inverse transform or reflection.
:::

:::proof "foundations.distributions.tempered_fourier_action"
This is the defining evaluation rule for Mathlib's Fourier-transform instance
on the pointwise continuous dual of Schwartz space.
:::

The derivative rule is the reason Fourier analysis is useful for
constant-coefficient equations: differentiation becomes multiplication by a
linear symbol.

:::theorem "foundations.distributions.tempered_fourier_derivative" (parent := "foundations.distributions") (lean := "TemperedDistribution.fourier_lineDerivOp_eq") (uses := "foundations.distributions.tempered_fourier_action, foundations.distributions.derivative_action")
For a complex normed space $`F`, $`T\in\mathcal S'(E;F)`, and a direction
$`m\in E`, distributional differentiation becomes multiplication by the
Fourier variable:

$$`
  \mathcal F(D_mT)
  =2\pi i\,(\xi\mapsto\langle\xi,m\rangle)\,\mathcal FT,
`

where multiplication is understood as the canonical multiplier operator on
tempered distributions.
:::

:::proof "foundations.distributions.tempered_fourier_derivative"
Move the distributional derivative onto a Schwartz test function, apply the
Schwartz-space Fourier derivative rule, and transpose multiplication by the
linear coordinate $`\xi\mapsto\langle\xi,m\rangle`. Mathlib states the
result as an equality of tempered distributions.
:::

# Convolution and translation

:::definition "foundations.distributions.schwartz_convolution" (parent := "foundations.distributions") (lean := "SchwartzMap.convolution, SchwartzMap.convolution_apply, SchwartzMap.convolution_continuous_left") (uses := "foundations.distributions.tempered_fourier_equiv")
For complex-valued Schwartz functions $`f,g\in\mathcal S(E)`, their
convolution

$$`
  (f*g)(x)=\int_E f(t)g(x-t)\,dt
`

is again a Schwartz function. For fixed $`g`, the map $`f\mapsto f*g` is
continuous and complex linear.
:::

The convolution theorem is what identifies the Fourier-side definition of
$`T*\varphi` with the integral convolution when $`T` is itself a Schwartz
function.

:::theorem "foundations.distributions.schwartz_fourier_convolution" (parent := "foundations.distributions") (lean := "SchwartzMap.fourier_convolution") (uses := "foundations.distributions.schwartz_convolution, foundations.distributions.tempered_fourier_equiv")
The Fourier transform converts convolution of Schwartz functions into
pointwise multiplication:

$$`
  \mathcal F(f*g)=(\mathcal Ff)(\mathcal Fg).
`
:::

:::proof "foundations.distributions.schwartz_fourier_convolution"
Mathlib defines Schwartz convolution through inverse Fourier transform of the
pointwise product. Fourier inversion therefore reduces the displayed identity
to the corresponding pairing identity in Schwartz space.
:::

Defining $`T*\varphi` on the Fourier side avoids any integral representation
of $`T` and makes the Fourier characterization hold by construction.

:::definition "foundations.distributions.tempered_schwartz_convolution" (parent := "foundations.distributions") (lean := "TemperedDistribution.convolutionSchwartzCLM") (uses := "foundations.distributions.schwartz_convolution, foundations.distributions.tempered_fourier_equiv")
For a scalar Schwartz function $`\varphi` and a tempered distribution $`T`,
their convolution is the tempered distribution defined by

$$`
  T*\varphi
  :=\mathcal F^{-1}\bigl((\mathcal FT)(\mathcal F\varphi)\bigr).
`

For fixed $`\varphi`, the map $`T\mapsto T*\varphi` is continuous and complex
linear.
:::

:::theorem "foundations.distributions.tempered_schwartz_fourier" (parent := "foundations.distributions") (lean := "TemperedDistribution.fourier_convolutionSchwartzCLM") (uses := "foundations.distributions.tempered_schwartz_convolution")
Convolution with a Schwartz function has the expected Fourier characterization:

$$`
  \mathcal F(T*\varphi)
  =(\mathcal FT)(\mathcal F\varphi).
`
:::

:::proof "foundations.distributions.tempered_schwartz_fourier"
Apply Fourier transform to the defining inverse Fourier transform and use the
Fourier inversion law on tempered distributions. The remaining factor is
Mathlib's continuous multiplier action by the Schwartz function
$`\mathcal F\varphi`.
:::

A Fourier-side definition needs a compatibility check: it must agree with the
integral convolution when both objects are functions. Injectivity of the Fourier
transform reduces the check to the Schwartz convolution theorem.

:::theorem "foundations.distributions.tempered_schwartz_convolution_compat" (parent := "foundations.distributions") (lean := "TemperedDistribution.convolutionSchwartzCLM_toTemperedDistributionCLM_eq") (uses := "foundations.distributions.tempered_schwartz_convolution, foundations.distributions.schwartz_fourier_convolution")
If $`f` and $`\varphi` are Schwartz functions and $`T_f` is the regular
tempered distribution induced by $`f`, then

$$`
  T_f*\varphi=T_{f*\varphi}.
`
:::

:::proof "foundations.distributions.tempered_schwartz_convolution_compat"
Fourier transform is injective on tempered distributions. After transforming
both sides, the left side is the regular distribution $`T_{\mathcal F f}`
multiplied by the Schwartz function $`\mathcal F\varphi`. Its pairing integral
is that of the density $`(\mathcal Ff)(\mathcal F\varphi)`, which Mathlib's
Schwartz convolution theorem also gives on the right. Associativity and
commutativity of complex multiplication identify the two pairing integrals.
:::

:::theorem "foundations.distributions.tempered_schwartz_convolution_derivative" (parent := "foundations.distributions") (lean := "TemperedDistribution.lineDerivOp_convolutionSchwartzCLM") (uses := "foundations.distributions.tempered_schwartz_fourier, foundations.distributions.tempered_fourier_derivative")
For $`T\in\mathcal S'(E;F)` with $`F` a complex normed space,
distributional differentiation commutes with convolution by a scalar
Schwartz function:

$$`
  D_m(T*\varphi)=(D_mT)*\varphi.
`
:::

:::proof "foundations.distributions.tempered_schwartz_convolution_derivative"
Apply the injective Fourier transform. Both sides become multiplication of
$`\mathcal FT` by the Fourier derivative symbol and by $`\mathcal F\varphi`.
The two scalar multipliers commute pointwise.
:::

Translation is the second transport operation, and its sign convention is
fixed by the pairing.

:::definition "foundations.distributions.tempered_translation" (parent := "foundations.distributions") (lean := "TemperedDistribution.translateCLM, TemperedDistribution.translateCLE, TemperedDistribution.translateCLM_apply_apply") (uses := "foundations.distributions.tempered")
For $`a\in E`, translation of a tempered distribution is the continuous
complex-linear equivalence determined by

$$`
  \langle\tau_aT,\varphi\rangle
  =\langle T,\varphi(\,\cdot-a)\rangle.
`

For a regular distribution induced by $`u`, this convention corresponds to
$`(\tau_a u)(x)=u(x+a)`.
:::

:::theorem "foundations.distributions.tempered_translation_laws" (parent := "foundations.distributions") (lean := "TemperedDistribution.translateCLM_zero, TemperedDistribution.translateCLM_apply_translateCLM, TemperedDistribution.translateCLE_symm_apply") (uses := "foundations.distributions.tempered_translation")
Tempered translations form an additive action and translation by $`-a` is the
inverse of translation by $`a`:

$$`
  \tau_0=\operatorname{id},
  \qquad
  \tau_a\tau_b=\tau_{a+b},
  \qquad
  \tau_a^{-1}=\tau_{-a}.
`
:::

:::proof "foundations.distributions.tempered_translation_laws"
On Schwartz test functions, two successive precompositions by subtraction of
$`a` and $`b` equal precomposition by subtraction of $`a+b`. Transposing this
identity gives the composition law. The zero and inverse laws are its
specializations.
:::

Constant-coefficient operators commute with translations, and the directional
derivative is the basic instance.

:::theorem "foundations.distributions.tempered_translation_derivative" (parent := "foundations.distributions") (lean := "TemperedDistribution.lineDerivOp_translateCLM") (uses := "foundations.distributions.tempered_translation, foundations.distributions.derivative_action")
Distributional directional derivatives commute with translation:

$$`
  D_m(\tau_aT)=\tau_a(D_mT).
`
:::

:::proof "foundations.distributions.tempered_translation_derivative"
Move the derivative onto a Schwartz test function. Mathlib's Fréchet chain rule
for the translated test function identifies its directional derivative with
the translation of the original directional derivative. Transposing this
identity gives the displayed formula.
:::

The support law makes the sign convention visible geometrically. Vanishing sets
correspond exactly under $`x\mapsto x-a`, so the law is an equality rather than
an inclusion.

:::theorem "foundations.distributions.tempered_translation_support" (parent := "foundations.distributions") (lean := "TemperedDistribution.isVanishingOn_translateCLM_iff, TemperedDistribution.dsupport_translateCLM") (uses := "foundations.distributions.tempered_translation, foundations.distributions.support")
Under the convention $`(\tau_a u)(x)=u(x+a)`, translation moves support by
$`x\mapsto x-a`:

$$`
  \operatorname{supp}_{\mathcal S'}(\tau_aT)
  =
  \{x-a:x\in\operatorname{supp}_{\mathcal S'}T\}.
`
:::

:::proof "foundations.distributions.tempered_translation_support"
A translated distribution vanishes on an open set precisely when the original
distribution vanishes on its preimage under $`x\mapsto x-a`. Applying this
equivalence to neighborhoods and then taking complements gives the exact
support image.
:::

# Linear pushforward

:::definition "foundations.distributions.tempered_linear_pushforward" (parent := "foundations.distributions") (lean := "TemperedDistribution.pushforwardCLM, TemperedDistribution.pushforwardCLE, TemperedDistribution.pushforwardCLM_apply_apply") (uses := "foundations.distributions.tempered")
Every continuous real-linear equivalence $`A:D\simeq E` induces a continuous
complex-linear equivalence

$$`
  A_*:\mathcal S'(D;F)\simeq_{\mathrm{cont},\mathbb C}
  \mathcal S'(E;F)
`

characterized by

$$`
  \langle A_*T,\varphi\rangle=\langle T,\varphi\circ A\rangle.
`

No Jacobian factor belongs in this defining distributional pairing. A
Jacobian appears only after one chooses volume measures and rewrites the
pushforward of a regular distribution as another density.
:::

Pushforward is contravariant on test functions and hence covariant on
distributions.

:::theorem "foundations.distributions.tempered_linear_pushforward_functorial" (parent := "foundations.distributions") (lean := "TemperedDistribution.pushforwardCLM_refl, TemperedDistribution.pushforwardCLM_trans, TemperedDistribution.pushforwardCLE_symm_apply") (uses := "foundations.distributions.tempered_linear_pushforward")
Linear pushforward preserves identities and composition, and pushforward by
$`A^{-1}` is inverse to pushforward by $`A`:

$$`
  (\operatorname{id})_*=\operatorname{id},
  \qquad
  B_*(A_*T)=(B\circ A)_*T,
  \qquad
  (A_*)^{-1}=(A^{-1})_*.
`
:::

:::proof "foundations.distributions.tempered_linear_pushforward_functorial"
Each identity follows after evaluating on a Schwartz function. Identity and
composition reduce to the corresponding laws for precomposition, while the
inverse law uses $`A^{-1}\circ A=\operatorname{id}`.
:::

Differentiating a pushforward requires transporting the direction back through
$`A`: since $`\varphi\circ A` is differentiated along $`A^{-1}m` when $`\varphi`
is differentiated along $`m`, the distributional statement carries $`A^{-1}m`.

:::theorem "foundations.distributions.tempered_linear_pushforward_derivative" (parent := "foundations.distributions") (lean := "TemperedDistribution.lineDerivOp_pushforwardCLM") (uses := "foundations.distributions.tempered_linear_pushforward, foundations.distributions.derivative_action")
Directional derivatives transform contravariantly under linear pushforward:

$$`
  D_m(A_*T)=A_*\bigl(D_{A^{-1}m}T\bigr).
`
:::

:::proof "foundations.distributions.tempered_linear_pushforward_derivative"
Evaluate both sides on a Schwartz function and move the distributional
derivative onto that test function. The ordinary chain rule gives
$`D_{A^{-1}m}(\varphi\circ A)=(D_m\varphi)\circ A`, which is exactly the
displayed identity after transposition.
:::

Equality rather than inclusion is special to invertible transport: the smooth
proper pushforward of ordinary distributions gives only an inclusion.

:::theorem "foundations.distributions.tempered_linear_pushforward_support" (parent := "foundations.distributions") (lean := "TemperedDistribution.isVanishingOn_pushforwardCLM_iff, TemperedDistribution.dsupport_pushforwardCLM") (uses := "foundations.distributions.tempered_linear_pushforward, foundations.distributions.support")
Linear pushforward carries distributional support to its geometric image:

$$`
  \operatorname{supp}_{\mathcal S'}(A_*T)
  =A\bigl(\operatorname{supp}_{\mathcal S'}T\bigr).
`
:::

:::proof "foundations.distributions.tempered_linear_pushforward_support"
A pushforward vanishes on an open set $`U` precisely when the original
distribution vanishes on $`A^{-1}(U)`. Since $`A` is a homeomorphism, it maps
the family of open vanishing sets, and hence their union, to the corresponding
family and union for $`A_*T`. Taking complements gives the support identity.
:::

# Affine pushforward

:::definition "foundations.distributions.tempered_affine_pushforward" (parent := "foundations.distributions") (lean := "TemperedDistribution.affinePushforwardCLM, TemperedDistribution.affinePushforwardCLE, TemperedDistribution.affinePushforwardCLM_apply_apply") (uses := "foundations.distributions.tempered_translation, foundations.distributions.tempered_linear_pushforward")
Every continuous real-affine equivalence $`A:D\simeq_{\mathrm{aff}}E` induces a
continuous complex-linear equivalence

$$`
  A_*:\mathcal S'(D;F)\simeq_{\mathrm{cont},\mathbb C}
  \mathcal S'(E;F)
`

characterized by

$$`
  \langle A_*T,\varphi\rangle=\langle T,\varphi\circ A\rangle.
`

The construction composes the linear pushforward with distributional
translation; Schwartz precomposition is assembled from Mathlib's corresponding
linear and translation operators. Internally, if $`L` is the linear part, the
factorization is $`\tau_{-A(0)}\circ L_*`. This sign is forced by the
translation convention: $`\tau_b` moves support by $`x\mapsto x-b`, so
the parameter $`-A(0)` adds the affine offset $`A(0)`.
:::

For $`A(x)=L_Ax+a` and $`B(y)=L_By+b`, the composite has linear part
$`L_BL_A` and offset $`L_Ba+b`.

:::theorem "foundations.distributions.tempered_affine_pushforward_functorial" (parent := "foundations.distributions") (lean := "TemperedDistribution.affinePushforwardCLM_refl, TemperedDistribution.affinePushforwardCLM_trans, TemperedDistribution.affinePushforwardCLE_symm_apply") (uses := "foundations.distributions.tempered_affine_pushforward")
Affine pushforward preserves identities and composition, and pushforward by
$`A^{-1}` is inverse to pushforward by $`A`:

$$`
  (\operatorname{id})_*=\operatorname{id},
  \qquad
  B_*(A_*T)=(B\circ A)_*T,
  \qquad
  (A_*)^{-1}=(A^{-1})_*.
`
:::

:::proof "foundations.distributions.tempered_affine_pushforward_functorial"
Evaluate each distribution on a Schwartz function. The statements reduce to
identity, composition, and inverse laws for precomposition by continuous affine
equivalences.
:::

The derivative rule sees only the linear part of $`A`, because translation
commutes with directional derivatives.

:::theorem "foundations.distributions.tempered_affine_pushforward_derivative" (parent := "foundations.distributions") (lean := "TemperedDistribution.lineDerivOp_affinePushforwardCLM") (uses := "foundations.distributions.tempered_affine_pushforward, foundations.distributions.tempered_translation_derivative, foundations.distributions.tempered_linear_pushforward_derivative")
If $`L` is the continuous linear part of $`A`, directional derivatives
transform contravariantly:

$$`
  D_m(A_*T)=A_*\bigl(D_{L^{-1}m}T\bigr).
`
:::

:::proof "foundations.distributions.tempered_affine_pushforward_derivative"
Write affine pushforward as linear pushforward followed by translation.
Translation commutes with directional derivatives, while the linear
pushforward chain rule replaces $`m` by $`L^{-1}m`. Combining the two identities
gives the formula.
:::

Supports, by contrast, see both parts of $`A`.

:::theorem "foundations.distributions.tempered_affine_pushforward_support" (parent := "foundations.distributions") (lean := "TemperedDistribution.dsupport_affinePushforwardCLM") (uses := "foundations.distributions.tempered_affine_pushforward, foundations.distributions.tempered_translation_support, foundations.distributions.tempered_linear_pushforward_support")
Affine pushforward carries distributional support to its geometric image:

$$`
  \operatorname{supp}_{\mathcal S'}(A_*T)
  =A\bigl(\operatorname{supp}_{\mathcal S'}T\bigr).
`
:::

:::proof "foundations.distributions.tempered_affine_pushforward_support"
The linear part maps support to its linear image, and the following translation
moves that image by $`A(0)`. The affine decomposition
$`A(x)=Lx+A(0)` identifies the resulting set with the image under $`A`.
:::

# Distributional support

:::definition "foundations.distributions.support" (parent := "foundations.distributions") (lean := "Distribution.IsVanishingOn, Distribution.dsupport") (uses := "foundations.distributions.tempered")
A distribution-like functional vanishes on a set $`U` when it annihilates
every test function whose topological support lies in $`U`. The definition
allows arbitrary $`U`. The complement of its support is the union of all
open vanishing sets; equivalently, distributional support is the
intersection of all closed sets whose complements are vanishing sets:

$$`
  \operatorname{supp}_{\mathcal D'}T
  :=\bigcap\{K:K\text{ closed and }T|_{K^c}=0\}.
`

Mathlib's definition is abstract enough to apply to both classical and
tempered distributions. The probe space is the one present in the functional
itself: ordinary distributions are tested by $`\mathcal D`, while tempered
distributions are tested by $`\mathcal S`.
:::

Closedness is the property that lets support arguments pass to complements and
work with open vanishing sets.

:::theorem "foundations.distributions.support_closed" (parent := "foundations.distributions") (lean := "Distribution.isClosed_dsupport") (uses := "foundations.distributions.support")
The distributional support of every distribution is closed:

$$`
  \operatorname{IsClosed}
    \bigl(\operatorname{supp}_{\mathcal D'}T\bigr).
`
:::

:::proof "foundations.distributions.support_closed"
Every set appearing in the defining intersection is closed, and an arbitrary
intersection of closed sets is closed.
:::

The derivative support law is the tempered counterpart of the statement for
ordinary distributions, and the one-term case of the constant-coefficient
support theorem.

:::theorem "foundations.distributions.derivative_support" (parent := "foundations.distributions") (lean := "Distribution.TemperedDistribution.dsupport_lineDerivOp_subset") (uses := "foundations.distributions.support, foundations.distributions.derivative_action")
For $`T\in\mathcal S'(E;F)` with $`F` a complex normed space,
distributional differentiation cannot enlarge support:

$$`
  \operatorname{supp}_{\mathcal S'}(D_mT)
  \subseteq
  \operatorname{supp}_{\mathcal S'}T.
`
:::

:::proof "foundations.distributions.derivative_support"
If $`T` vanishes on an open set, then it annihilates the derivative of every
test function supported there because differentiation preserves the support
inclusion. The derivative distribution therefore vanishes on every open set
where $`T` vanishes, which gives the support inclusion.
:::

The Dirac mass is the test case in which the support is computed exactly rather
than bounded. The inclusion in $`\{x\}` uses only vanishing away from $`x`; the
reverse inclusion needs a Schwartz function not vanishing at $`x` with support
inside an arbitrary neighborhood, which is where finite-dimensionality of $`E`
is used.

:::theorem "foundations.distributions.tempered_dirac_support" (parent := "foundations.distributions") (lean := "Distribution.TemperedDistribution.dsupport_delta") (uses := "foundations.distributions.support, foundations.distributions.dirac")
In finite dimensions the support of the tempered Dirac distribution at $`x` is exactly the
singleton $`\{x\}`:

$$`
  \operatorname{supp}_{\mathcal S'}\delta_x=\{x\}.
`
:::

:::proof "foundations.distributions.tempered_dirac_support"
The Dirac mass vanishes on the complement of $`\{x\}`, so its support is
contained in that singleton. Every neighborhood of $`x` contains a smooth
compactly supported function that is nonzero at $`x`; evaluating the Dirac
mass on this function proves the reverse inclusion.
:::

# Regularity from the Laplacian

The Fourier transform turns the Laplacian into multiplication by
$`-4\pi^2\lvert\xi\rvert^2` in Mathlib's normalization, where the phase is
$`e^{-2\pi i\langle x,\xi\rangle}`. The Bessel potential of order two, with
symbol $`1+\lvert\xi\rvert^2`, is then a combination of the identity and the
Laplacian. As a consequence, the
{bpref "sobolev.fourier_space"}[Bessel-potential scale] $`H^{s,p}` measures
regularity in steps of two derivatives by the Laplacian alone. This is the
whole-space form of elliptic regularity, and it needs no estimate beyond the
definition of the scale.

:::theorem "foundations.distributions.tempered_bessel_laplacian" (parent := "foundations.distributions") (lean := "TemperedDistribution.besselPotential_two_eq") (uses := "foundations.distributions.tempered_fourier_derivative, foundations.operators.laplacian")
For every tempered distribution $`u` with values in a complex normed space,

$$`
J^2u=u-(2\pi)^{-2}\,\Delta u ,
`

where $`J^2` is the Bessel potential of order two.
:::

:::proof "foundations.distributions.tempered_bessel_laplacian"
Both sides are Fourier multipliers. The symbol of $`J^2` is
$`(1+\lvert\xi\rvert^2)^{2/2}=1+\lvert\xi\rvert^2`, and the symbol of
$`-(2\pi)^{-2}\Delta` is $`\lvert\xi\rvert^2`. Multipliers add, so the two
operators agree.
:::

:::theorem "foundations.distributions.tempered_laplacian_regularity" (parent := "foundations.distributions") (lean := "TemperedDistribution.MemSobolev.add_two_of_laplacian, TemperedDistribution.memSobolev_add_two_iff, TemperedDistribution.exists_lp_second_derivative_of_laplacian, TemperedDistribution.exists_lp_besselPotential_two_of_laplacian") (uses := "foundations.distributions.tempered_bessel_laplacian")
Let $`1\le p\le\infty` and $`s\in\mathbb R`. If a tempered distribution
$`u` and its Laplacian both lie in $`H^{s,p}`, then $`u\in H^{s+2,p}`. For
$`p=2` and Hilbert-space values the converse also holds:

$$`
u\in H^{s+2,2}\iff u\in H^{s,2}\text{ and }\Delta u\in H^{s,2}.
`

In particular, if $`u,f\in L^2` and $`\Delta u=f` in the sense of
distributions, then every second directional derivative
$`\partial_v\partial_wu` is an $`L^2` function.
:::

:::proof "foundations.distributions.tempered_laplacian_regularity"
By the Bessel identity, $`J^2u=u-(2\pi)^{-2}\Delta u`, which lies in
$`H^{s,p}` as a combination of two members. Lifting by $`J^2` adds two to
the order, so $`u\in H^{s+2,p}`. For $`p=2` the converse is the statement
that $`\Delta` maps $`H^{s+2,2}` to $`H^{s,2}`, since its symbol is
bounded by a multiple of $`1+\lvert\xi\rvert^2`. For the second derivatives,
$`L^2` is $`H^{0,2}`, so $`u\in H^{2,2}`, and the symbol
$`\xi_v\xi_w/(1+\lvert\xi\rvert^2)` of $`\partial_v\partial_wJ^{-2}` is
bounded.
:::

The hypothesis is only that $`u` and $`\Delta u` are in $`L^2`, with no
assumption on first derivatives. For $`p=1` and $`p=\infty` the implication
holds, but membership in $`H^{s+2,p}` there does not put the second partial
derivatives in $`L^p`. On a bounded domain the same conclusion needs cutoffs and the estimates of
the elliptic regularity chapter.
