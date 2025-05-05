Vector fields on Manifolds
============================

A vector field on a differentiable manifold is a differentiable map :math:`X:M \to TM` such that :math:`X_p \in T_pM` for each :math:`p \in M`. In Mathlib, this is expressed as a "pi function": ``X : Π (x : M), TangentSpace I x`` where ``I`` is the ``ModelWithCorners`` on which ``M`` is modelled.

This is a general pattern for maps with values in the fibres of a bundle - similar to vector fields, sections in bundles are also expressed as pi functions, which we will see when we discuss vector bundles on differentiable manifolds.

Since ``X`` is just a differentiable function between ``M`` and the total space of the tangent bundle, we can apply the API for differentiable functions. For example, to state that ``X`` is indeed differentiable at ``x : M``, we can **almost** write ``MDifferentiableAt I I.tangent X x`` (doesn't work).

There is a catch, though: the pi function ``X : Π (x : M), TangentSpace I x`` formally has values in the tangent space at a point and is not a function from ``M`` to the tangent bundle. But exactly this would be necessary to talk about differentiability.

Hence the correct formulation is ``MDifferentiableAt I I.tangent (fun (y : M) ↦ (X y : TangentBundle I M)) x``.

Please note that:

#. We have to coerce ``X`` to a function into the tangent bundle, so that ``X`` is a proper map between differentiable manifolds.
#. The ModelWithCorners ``I`` offers a nice abbreviation ``I.tangent`` to denote the ModelWithCorners for the tangent space.


Pullbacks of vector fields
===========================

Given a local diffeomorphism :math:`f: M \to M'` between two manifolds and a vector field  :math:`X'` on :math:`M'`, we can pull back this vector field so that we get a new vector field :math:`X` on :math:`M`. Such a pullback is defined as :math:`X_p := df^{-1} \cdot Y_{f(p)}`, where :math:`df : TM \to TM'` is the Fréchet derivative of :math:`f`. This pullback of a vector field is usually written as :math:`f^*X'`.

In Mathlib, the definition of a pullback is as follows:

.. code-block::

    def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) : TangentSpace I x :=
        (mfderiv I I' f x).inverse (V (f x))

As you can see, ``V`` is a vector field on ``M'``, i.e. a pi function from the points in ``M'`` to the tangent space at that point. This vector field is evaluatated at ``f x`` and pulled back with the inverse of the Fréchet derivative ``mfderiv I I' f x``.

This definition and various theorems on pullbacks of differentiable vector fields can be found in the file `Mathlib.Geometry.Manifold.VectorField.Pullback <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/Pullback.html>`_


Lie brackets of vector fields
================================

If we have two differentiable vector fields :math:`X` and :math:`Y`on :math:`M`, the lie bracket of these vector fields can be defined as the unique vector field :math:`[X,Y]` which acts on the ring of differentiable functions as :math:`[X,Y] \cdot f = X \cdot Y \cdot f - Y \cdot X \cdot f`. There are other definitions of the Lie bracket, but this corresponds to the definition used by Mathlib.

In Mathlib, the Lie bracket is first defined on vector spaces in `Mathlib.Analysis.Calculus.VectorField <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/VectorField.html>`_ as:

.. code-block::

    def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
        fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)

There is also a definition ``lieBracket`` which is the same, but defined on the whole vector space.

To define the Lie bracket for vector fields, the two vector fields are pushed forward to the model space using a chart, then the lie bracket is applied in the underlying model and the result is pulled back to the manifold, see `Mathlib.Geometry.Manifold.VectorField.LieBracket <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/LieBracket.html>`_:

.. code-block::

    def mlieBracketWithin (V W : Π (x : M), TangentSpace I x) (s : Set M) (x₀ : M) : TangentSpace I x₀ :=
        mpullback I 𝓘(𝕜, E) (extChartAt I x₀)
            (lieBracketWithin 𝕜
            (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I))
            (mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm W (range I))
            ((extChartAt I x₀).symm ⁻¹' s ∩ range I)) x₀

Here the pullback mechanism is applied twice: as a "push forward" of the two vector fields from the manifold to the model space ``mpullbackWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm V (range I)`` (given the fact that ``(extChartAt I x₀).symm`` is the inverse of the chart, a push forward is the same as the pull back by the inverse ) and a pullback from the model space back to the manifold.

Similar to the lie bracket on vector spaces, there is a second variant where the set s is extended to the full manifold:

.. code-block::

    def mlieBracket (V W : Π (x : M), TangentSpace I x) (x₀ : M) : TangentSpace I x₀ :=
        mlieBracketWithin I V W univ x₀


As you can see from these examples, the lie bracket is always evaluatated at a point. However, since they become functions if the point is omitted, you get the lie bracket as a vector field by ``mlieBracket 𝕜 V W``. Hence the Leibniz identity (aka Jacobi identity) :math:`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` can be written as:

.. code-block::

    mlieBracket I U (mlieBracket I V W) =
      mlieBracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W)

Here the terms in bracket are functions ``Π (x : M), TangentSpace I x`` because the base point has been omitted.
It is proven in `VectorField.leibniz_identity_mlieBracket <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/LieBracket.html#VectorField.leibniz_identity_mlieBracket>`_ that the Leibniz identity is indeed true on manifolds.

Various facts are proven for Lie brackets, for example that the Lie bracket of two differentiable vector fields is again differentiable (ContMDiffAt.mlieBracket_vectorField `<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/LieBracket.html#ContMDiffAt.mlieBracket_vectorField>`_ ) or that it is ``𝕜``-linear in both components and that it is skew symmetric.

