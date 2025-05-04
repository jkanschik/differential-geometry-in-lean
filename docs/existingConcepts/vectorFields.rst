Vector fields on Manifolds
============================

A vector field on a differentiable manifold is a differentiable map :math:`X:M \to TM` such that at each point :math:`x_0 \in M` the vector :math:`X(x_0)`lies in the tangent space :math:`T_{x_0}M` at this point. In Mathlib, this is expressed as a "pi function": ``X : Π (x : M), TangentSpace I x`` where ``I`` is the ``ModelWithCorners`` on which ``M`` is modelled.

This is a general pattern for maps with values in the fibres of a bundle - similar to vector fields, sections in bundles are also expressed as pi functions, which we will see when we discuss vector bundles on differentiable manifolds.

Since ``X`` is just a differentiable function between ``M`` and the total space of the tangent bundle, we can apply the API for differentiable functions. For example, to state that ``X`` is indeed differentiable at ``x : M``, we can **almost** write ``MDifferentiableAt I I.tangent X x``. There is a catch, though: the pi function ``X : Π (x : M), TangentSpace I x`` formally has values in the tangent space at a point and is not a function from ``M`` to the tangent bundle. But exactly this would be necessary to talk about differentiability.

Hence the correct formulation is ``MDifferentiableAt I I.tangent (fun (y : M) ↦ (X y : TangentBundle I M)) x``.

Please note that:

#. We have to coerce ``X`` to a function into the tangent bundle, so that ``X`` is a proper map between differentiable manifolds.
#. The ModelWithCorners ``I`` offers a nice abbreviation ``I.tangent`` to denote the ModelWithCorners for the tangent space.


Pullbacks of vector fields
---------------------------

Given a local diffeomorphism :math:`f: M \to M'` between two manifolds, we can pull back a vector field :math:`X'` on :math:`M'` so that we get a new vector field :math:`X` on :math:`M`. Such a pullback is defined as :math:`X_p := df^{-1} \cdot Y_{f(p)}`, where :math:`df : TM \to TM'` is the Fréchet derivative of :math:`f`.

In Mathlib, the definition of a pullback is as follows:

.. code-block::

    def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) : TangentSpace I x :=
        (mfderiv I I' f x).inverse (V (f x))

As you can see, ``V`` is a vector field on ``M'``, i.e. a pi function from the points in ``M'`` to the tangent space at that point. This vector field is evalutated with ``V (f x)`` and pulled back with the invers of the Fréchet derivative ``mfderiv I I' f x``.

This definition and various theorems on pullbacks of differentiable vector fields can be found in the file `Mathlib.Geometry.Manifold.VectorField.Pullback <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Geometry/Manifold/VectorField/Pullback.html>`_


Pullbacks missing from Mathlib
----------------------------------

