import Project.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
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
[CommSemiring R] [Semiring A] [Algebra R A] :=
(to_fun : ℕ → Submodule R A)
(mono' : Monotone to_fun)
(complete' : ∀ x, ∃ i, x ∈ to_fun i)
(map_add' : ∀ n m, to_fun (n + m) = to_fun n * to_fun m)

/-
theorem graded_implies_filtered {R : Type*} {A : Type*}
[CommSemiring R] [Semiring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : FilteredAlgebra R A where
  to_fun := sorry
  mono' := sorry
  complete' := sorry
  map_add' := sorry

theorem filtered_from_graded (R : Type*) (A : Type*)
[CommSemiring R] [Semiring A] [Algebra R A] (F : FilteredAlgebra R A) :
GradedAlgebra (ℕ → Submodule R A) := by
sorry
--/


--Largely taken from
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/UniversalEnveloping.html#UniversalEnvelopingAlgebra
--https://github.com/leanprover-community/mathlib4/blob/006b23a50533766ff9714eda094f2b6da8a9f513//Mathlib/Algebra/Lie/UniversalEnveloping.lean#L61-L62

universe u₁ u₂

variable (R : Type u₁) (L : Type u₂)

variable [CommSemiring R] [AddCommMonoid L] [Module R L]

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

instance instRing : Ring (SymmetricAlgebra R L) := by
  --inferInstanceAs (Ring (RingQuot (SymmetricAlgebra.Rel R L)))


instance instAlgebra : Algebra R (SymmetricAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (SymmetricAlgebra.Rel R L)))


end SymmetricAlgebra
