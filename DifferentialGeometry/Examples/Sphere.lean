import Mathlib.Data.Set.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2


/-

  Before doing any explicit examples on the sphere, it might be useful to recap how to proof statements about derivatives in Mathlib.

-/
section

open Real

/-
  Proof that the function x ↦ sin(x) * exp(x) is differentiable on ℝ

  Differentiable just means that there exists a derivative at each point in ℝ,
  the derivative may not be unique and we don't know the derivative.
-/
example : Differentiable ℝ fun x => sin x * exp x := by
  -- A product is differentiable if the factors are differentiable
  -- Creates two goals, one for each factor
  apply Differentiable.mul
  . apply differentiable_sin
  . apply differentiable_exp


/-
  Explicit proof that the derivative of `-cos x` is `sin x`
-/
example (x₀ : ℝ) : deriv (fun x => -cos x) x₀ = sin x₀ := by
  -- The derivative of `x => - f x` is `x => - f' x`
  rw [deriv.neg]
  -- The derivative of `cos x` is `-sin x`
  rw [Real.deriv_cos]
  -- Finally, `- - sin x = sin x`
  rw [neg_neg]

/-
  Since all the theorems used for the explicit proof are also simps,
  we can just use `simp` to proof the statement:
-/
example (x₀ : ℝ) : deriv (fun x => -cos x) x₀ = sin x₀ := by
  simp

/-
  Explicit proof that at the real number x₀ : ℝ, `(cos x₀ + sin x₀) * exp x₀` is a derivative of `sin x * exp x`
-/
example (x₀ : ℝ) : deriv (fun x => sin x * exp x) x₀ = (cos x₀ + sin x₀) * exp x₀ := by
  -- rewrite using the product rule; creates two additional goals: both factors (sin x and exp x) need to be differentiable
  rw [deriv_mul]
  . rw [Real.deriv_sin]
    rw [Real.deriv_exp]
    rw [add_mul]
  . apply differentiableAt_sin
  . apply differentiableAt_exp

/-
  Same, but much shorter using simp to simplify the derivatives and linarith to reorganize the result.
-/
example (x₀ : ℝ) : deriv (fun x => sin x * exp x) x₀ = (cos x₀ + sin x₀) * exp x₀ := by
  simp
  linarith

open ContDiff Set

/-
  For higher smoothness parameters like C^∞ and C^ω, `ContDiff****` is used;
  as an example, this is a proof that `1 / x` is (real-)analytical on the set of the positive reals.
-/
example : ContDiffOn ℝ ω (fun x : ℝ => 1 / x) (Set.Ioi 0) := by
  -- The quotient of two functions (here x => 1 and x => x) is analytic if the both functions are analytic and the denominator is not 0.
  apply ContDiffOn.div
  . apply contDiffOn_const
  . apply contDiffOn_id
  . simp
    exact fun x a ↦ ne_of_gt a

end

/-
  In the next section we look at functions and their derivatives in euclidian spaces.
-/

noncomputable section

open Real Matrix ContDiff
/-
  The euclidian space ℝ^n in Mathlib is denoted by `EuclideanSpace ℝ (Fin n)`
  and for example a point in ℝ^3 is given by `![1, 1, 2] : EuclideanSpace ℝ (Fin 3)`.
  We can therefore write a curve in ℝ^3 as follows:
-/

def c : ℝ → EuclideanSpace ℝ (Fin 3) := fun t => ![cos t, sin t, 0]

/-
  This function is analytic (over ℝ) everywhere:
-/
example : ContDiff ℝ ω c := by
  sorry

/-
  We can also define a matrix which depends on a parameter (if you want, a differentiable curve in a Lie group).
  For example, the following is the rotation around the third axis
-/
def ψ : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
  fun t => !![cos t, sin t, 0; -sin t,cos t, 0; 0, 0, 1]

/-
  This function is actually a one-parameter subgroup of the orthogonal group:
-/
example (s t : ℝ) : ψ (s + t) = ψ s * ψ t := by sorry

/- The orbit of the vector ![1, 0, 0] under this operation is the curve c -/
example (t: ℝ) : c t = ψ t *ᵥ ![1, 0, 0] := by sorry


end
