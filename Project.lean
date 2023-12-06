import Project.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.Algebra.RingQuot
import Mathlib.Algebra.Lie.UniversalEnveloping
--import Mathlib.Algebra.DirectSum.Decomposition
--import Mathlib.Algebra.Module.GradedModule
--import Mathlib


--https://leanprover-community.github.io/mathlib4_docs
--Mathlib.Algebra.Lie.Basic: Lie Algebra
--Mathlib.RingTheory.GradedAlgebra.Basic: Graded Algebra
--Mathlib.LinearAlgebra.TensorAlgebra.Basic: Tensor Algebra
--Mathlib.Algebra.Lie.UniversalEnveloping: Universal Enveloping Algebra

--Our first step is to set up the idea of a filtered algebra.

--Filtered Algebra code is based on code by Eric Wieser
--https://github.com/pygae/lean-ga/blob/0947a6d21cf5a724732c29dabbc7f543edb66d4e/src/for_mathlib/algebra/filtration.lean

--Should I pull the function out?

structure FilteredAlgebra (R : Type*) (A : Type*)
[CommRing R] [Ring A] [Algebra R A] :=
(toFun : ℕ → Submodule R A)
(mono' : Monotone toFun)
(complete' : ∀ x, ∃ i, x ∈ toFun i)
(mapAdd' : ∀ n m, toFun (n + m) = toFun n * toFun m)

--coefun

instance directSumExpansion {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) → DirectSum ℕ (fun m => 𝒜 m) := by
  intro x
  unfold DirectSum at *
  rcases x with ⟨toFun, support'⟩
  constructor
  rotate_left
  intro j
  by_cases g : j > n
  exact 0
  simp at g
  --have a : Fin (n+1) := {val := j, isLt := Nat.lt_succ.mpr g}
  --have f := toFun a
  have i := toFun {val := j, isLt := Nat.lt_succ.mpr g}
  simp at i
  simp
  exact i
  --simp at f
  --simp
  --exact Fintype.lift 𝒜 (Fin.cast_le g) f
  simp
  apply Trunc.mk
  --refine Trunc.mk ?mk'.support'.a
  constructor
  rotate_left
  exact Multiset.range n
  intro j
  simp --alt?
  --THINK FROM HERE
  by_cases g : j < n
  left
  --simp
  exact g
  right
  simp at *
  intro h
  have k : j = n := by exact Nat.le_antisymm h g
  --have k' := Nat.le_antisymm h g
  symm at k
  subst k
  sorry

--/-
theorem graded_implies_filtered {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : FilteredAlgebra R A where
  toFun := fun n => sorry --(DirectSum (Fin (n+1)) (fun m => 𝒜 m))
  mono' := sorry
  complete' := sorry
  mapAdd' := sorry

--probably actually an instance of a function
theorem filtered_from_graded (R : Type*) (A : Type*)
[CommRing R] [Ring A] [Algebra R A] (F : FilteredAlgebra R A) :
GradedAlgebra (ℕ → Submodule R A) := by
sorry
--/


--Our second step is to set up the idea of a symmetric algebra.

--Largely taken from
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/UniversalEnveloping.html#UniversalEnvelopingAlgebra
--https://github.com/leanprover-community/mathlib4/blob/006b23a50533766ff9714eda094f2b6da8a9f513//Mathlib/Algebra/Lie/UniversalEnveloping.lean#L61-L62

universe u₁ u₂

variable (R : Type u₁) (L : Type u₂)

variable [CommRing R] [AddCommMonoid L] [Module R L]

local notation "ιₜ" => TensorAlgebra.ι R

namespace SymmetricAlgebra

inductive Rel : TensorAlgebra R L → TensorAlgebra R L → Prop
  | symm (x y : L) : Rel (ιₜ x * ιₜ y) (ιₜ y * ιₜ x)

end SymmetricAlgebra

def SymmetricAlgebra :=
  RingQuot (SymmetricAlgebra.Rel R L)

namespace SymmetricAlgebra

instance instInhabited : Inhabited (SymmetricAlgebra R L) :=
  inferInstanceAs (Inhabited (RingQuot (SymmetricAlgebra.Rel R L)))

--/-
instance instRing : Ring (SymmetricAlgebra R L) :=
  inferInstanceAs (Ring (RingQuot (SymmetricAlgebra.Rel R L)))

instance instAlgebra : Algebra R (SymmetricAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (SymmetricAlgebra.Rel R L)))
--/

end SymmetricAlgebra




--END GOAL:
--construct an isomorphism from the filtration on gr(U(g)) to S(g)
--by filter
--maybe show ∀ (n : ℕ), gr(U(g)) n ≅ S(g) n
--on the grading functions

/-
theorem PBW {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [g : LieAlgebra R L]
  : filtered_from_graded UniversalEnvelopingAlgebra g = SymmetricAlgebra g
  := sorry
-/
