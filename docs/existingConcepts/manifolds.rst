Manifolds in Mathlib
===================

The Definition of a manifold
-----------------------------

We will discuss how manifolds can be described in Mathlib.
To do this, let's dive straight in and define a manifold ``M`` in Mathlib.
Don't worry, we will break down the various variables and type classes:

.. code-block::

  import Mathlib.Geometry.Manifold.IsManifold.Basic

  variable
    (n : WithTop ℕ∞)
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] [CompleteSpace E]


Let's go through the different variables that are defined here:

``(n : WithTop ℕ∞)``
  is the a smoothness parameter. It can vary from ``n = 0`` for a topological manifold, i.e. no differentiable structure to `n = ∞` for a smooth manifold and `n = ω` for an analytic manifold.

``{𝕜 : Type*} [NontriviallyNormedField 𝕜]``
  is the field over which we work, i.e. the real or complex numbers, but also p-adic numbers. All statements about manifolds should work with an arbitrary, nontrivial, normed field as long as possible.

``{H : Type*} [TopologicalSpace H]``

``{E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]``

``{I : ModelWithCorners 𝕜 E H}``
  See https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/Basic.html#ModelWithCorners

``{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]``
  To start with, ``M`` is a
  `TopologicalSpace <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Defs/Basic.html#TopologicalSpace>`_,
  which means we have a proper topology.

  The type class ``ChartedSpace`` defines an atlas on the topological space,
  i.e. a set of (partial) homoemorphisms from ``M`` to the model space such that the domains cover the whole space.
  This doesn't define a manifold structure yet, because it doesn't define how the charts are "glued together".

  To do so, we need the type class ``IsManifold``,
  which states that the coordinate transformations of the charted space form a groupoid of differentiable maps.


When working with several manifolds at the time, it's best to call them ``M``, ``M'``, or ``M''`` or use subscripts ``M₁``, ``M₂``, etc.
and use the same convention for the underlying objects like ``I``, ``I'`` and so on. Otherwise it's easy to loose track of the dependencies, causing errors.


Charted spaces
---------------------

Charted spaces define an atlas on the topological space, i.e. a set of partial homeomorphisms from ``M`` to the model space ``H`` such that the domains cover the whole space. They are defined in file `Mathlib.Geometry.Manifold.ChartedSpace <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ChartedSpace.html>`_, see `ChartedSpace <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ChartedSpace.html#ChartedSpace>`_ for the actual definition.

In many cases, you may not need to work with the charts themself because there is a growing API for differentiable manifolds which hide the details. However, even with the perfect API it sometimes becomes necessary to move from a manifold to the model space and proof a statement there.

Also, note that the definition of the atlas and the definition of the smooth structure are separated in Mathlib: a charted space on its own has no information about smoothness at all. As an extreme example, any topological space can be considered as a charted space by choosing an atlas with only one element: the identity on the topological space.

The type class `ModelWithCorners` adds conditions to the model space

Only when smoothness is added using the type class ``IsManifold I n M``, conditions on the chart are imposed. This also means that the charts are maps from the charted space to the model space ``H`` - not the model vector space ``E``, which we use for the definition of a manifold.

This additional step from ``H`` to ``E`` is done using "extended charts", which are defined in `ExtChartAt <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.html>`_. "Extended" here refers to the fact that they extend the original charts (maps from ``M`` to the model ``H``) to ``E``.

Hence the API for extended charts becomes very important if you want to move between the manifold and the vector space.
To do so, you may need the following parts of the API (and please consult the linked documentation for more):

`extChartAt I x <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.html#extChartAt>`_
  This is the extended chart at ``x``, mapping ``M`` to ``E``. It is of type `PartialEquiv <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Equiv/PartialEquiv.html#PartialEquiv>`_, in contrast to ``chartAt H x``, which is a `PartialHomeomorph <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/PartialHomeomorph.html#PartialHomeomorph>`_

`(extChartAt I x).symm`
  This is the inverse function **TODO** Add the correct "I" and "x" here. How is it really used in an example?

`(extChartAt I x).source`:
  The domain of the extended chart (of course the same domain as the chart ``(chartAt I x).source``).

`(extChartAt I x).target`:
  The codomain of the extended chart, which is a subset of ``E`` (the codomain of the chart ``(chart I x).target`` is a subset in the model space ``H``)

`writtenInExtChartAt I I' f x <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/IsManifold/ExtChartAt.html#writtenInExtChartAt>`_
  For a function ``f : M → M'``, this conjugates ``f`` with the extended charts at ``x`` and ``f x``, so that we get a map in coordinates between the model vector spaces, i.e. a map ``E → E'``.





The tangent space of manifolds
--------------------------------

Based on the differentiable structure given by ``IsManifold``, we can define the tangent bundle of ``M``.


Maps between manifolds
---------------------------

We now consider differentiable maps between manifolds. There are two parts in Mathlib that deal with differentiability of functions: [`MFDeriv`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html), which defines the Fréchet derivative of functions and [`ContMDiff`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html).

### C^n functions between manifolds
We first consider `ContMDiff`: a function between two manifolds is differentiable, if the function is differentiable when we read the function in charts. This doesn't make any statement about what the derivate at a certain point is, only that when the function is read as a function in local charts, the function is differentiable. Because this is a local property, the statements about differentiability come in different flavours; in all cases, `n` can be finite, or `∞`, or `ω` for smooth and analytic functions.

[ContMDiffWithinAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html#ContMDiffWithinAt)
: `ContMDiffWithinAt I I' n f s x` is the proposition that the function `f: M → N` is `n`-times differentiable in the set `s` at `x`.

[ContMDiffAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html#ContMDiffAt)
: `ContMDiffAt I I' n f x` is the proposition that the function `f: M → N` is `n`-times differentiable at `x`. It is the same proposition as `ContMDiffWithinAt I I' n f Set.univ x`.

[ContMDiffOn](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html#ContMDiffOn)
: `ContMDiffOn I I' n f s` is the proposition that the function `f: M → N` is `n`-times differentiable at all points in the set s. Similar to `ContMDiffAt`, this is expressed in terms of `ContMDiffWithinAt` as `∀ x ∈ s, ContMDiffWithinAt I I' n f s x`.

[ContMDiff](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiff/Defs.html#ContMDiff)
: `ContMDiff I I' n f` is the proposition that the function `f: M → N` is `n`-times differentiable at all points in `M`. Again, this is based on `ContMDiffAt` as `∀ (x : M), ContMDiffAt I I' n f x` and hence proven by `ContMDiffWithinAt`.



The space of all differentiable functions
---------------------------------------------

In file ``ContMDiffMap <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiffMap.html#ContMDiffMap>``_ , the space of all differentiable functions  ``f: M → N`` with smoothness parameter ``n`` is introduced as
`ContMDiffMap I I' M M' n <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/ContMDiffMap.html#ContMDiffMap>`_ .
As a shorter notation, we can use ``C^n⟮I, M; I', N⟯`` and for functions with values in `𝕜` we can write `C^n⟮I, M; 𝕜⟯`.

The same file also proofs that certain standard functions are in `C^n⟮I, M; I', N⟯` and `C^n⟮I, M; 𝕜⟯`, namely:

* the identity on a manifold: ``ContMDiffMap.id : C^n⟮I, M; I, M⟯``
* the constant function from a manifold to ``𝕜``: ``ContMDiffMap.const : C^n⟮I, M; 𝕜⟯``
  * the composition of two functions (as differentiable functions): ``ContMDiffMap.comp``
* the projections from a product of manifolds to the first and second factor: ``ContMDiffMap.fst : C^n⟮I', M × M'; I, M⟯`` and ``ContMDiffMap.fst : C^n⟮I', M × M'; I, M⟯``
* the cartesian product ``x ↦ (f x, g x)`` of two functions: ``ContMDiffMap.prodMk :  C^n⟮I', M × M'; I, M⟯```




The Fréchet derivative
--------------------------

The Fréchet derivative is the derivative of a differentiable function at a point as a linear map between the tangent spaces of the two manifolds. Given a function :math:`f: M \to N`, the Fréchet derivative `f'` at a point `x` is a linear map :math:`f': T_xM → T_xN`.

Please note that the Fréchet derivative is only the first derivative. Since :math:`f': TM \to TM'` is a map between the two tangent bundles and not the original manifolds, The second derivative `f''` would be a map between the tangent bundles of the tangent bundles and so on. When we do calculus on vector spaces, this is not a problem, because we identify the tangent space at a point with the vector space itself. However, because the tangent bundle is usually not trivial, this is not possible on manifolds. To have a notion of higher order derivatives, we will introduce [linear connections](connections.html).

Similar to `ContMDiff`, the propositions for the Fréchet derivative come in different variations:



API to check whether a function is differentiable
--------------------------------------------------

[MDifferentiableWithinAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#MDifferentiableWithinAt)
: MDifferentiableWithinAt I I' f s x indicates that the function f between manifolds has a derivative at the point x within the set s.

[MDifferentiableAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#MDifferentiableAt)
: `MDifferentiableAt I I' f x` indicates that the function f between manifolds has a derivative at the point x.

[MDifferentiableOn](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#MDifferentiableOn)
: `MDifferentiableOn I I' f s` indicates that the function f between manifolds has a derivative within s at all points of s. This proposition is true if `MDifferentiableWithinAt` is true for all points in `s`.

[MDifferentiable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#MDifferentiable)
: `MDifferentiable I I' f` indicates that the function f between manifolds has a derivative everywhere.

#### API to check whether a function has a given derivative

[HasMFDerivWithinAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#HasMFDerivWithinAt)
: `HasMFDerivWithinAt I I' f s x f'` indicates that the function f between manifolds has, at the point x and within the set s, the derivative f'.

[HasMFDerivAt](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#HasMFDerivAt)
: `HasMFDerivAt I I' f x f'` indicates that the function f between manifolds has, at the point x, the derivative f'.
**TODO** Warum hier kein Set?

#### API to provide the derivative

[mfderivWithin](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#mfderivWithin)
: `mfderivWithin I I' f s x` is the derivative of f at x within the set s.

[mfderiv](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#mfderiv)
:  `mfderiv I I' f x` is the derivative of f at x.


#### API to provide the derivative as a map of tangent bundles

The following two definitions give the derivative of a function as a map of tangent bundles. They simply reformulate `mderiv` and `mderivWithin` in terms of the tangent bundles `TangentBundle I M` and `TangentBundle I' M'`.

[tangentMapWithin](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#tangentMapWithin)
: The derivative within a set, as a map between the tangent bundles.

[tangentMap](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/MFDeriv/Defs.html#tangentMap)
: `tangentMap f` is the derivative, as a map between the tangent bundles.





Curves on manifolds
---------------------------

Trick für die Ableitung:

.. code-block::
    lemma IsIntegralCurveAt.hasMFDerivAt (h : IsIntegralCurveAt γ v t₀) :
        HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t₀))) :=
      have ⟨_, hs, h⟩ := isIntegralCurveAt_iff.mp h
      h t₀ (mem_of_mem_nhds hs)

Hier wird "1" als lineare Abbildung von R nach R aufgefasst und mit dem Vektor an :math:`\gamma(t_0)` multiplizert
