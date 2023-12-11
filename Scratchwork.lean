import Project.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
--import Mathlib

def hello_world := hello ++ " world"

--https://leanprover-community.github.io/mathlib4_docs
--Mathlib.Algebra.Lie.Basic: Lie Algebra
--Mathlib.RingTheory.GradedAlgebra.Basic: Graded Algebra
--Mathlib.LinearAlgebra.TensorAlgebra.Basic: Tensor Algebra
--Mathlib.Algebra.Lie.UniversalEnveloping: Universal Enveloping Algebra

--just some examples:

--add_lie
example {L : Type v} {M : Type w}
  [LieRing L] [AddCommGroup M] [LieRingModule L M]
  (x : L) (y : L) (m : M) :
  ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ := by
  simp

--lie_jacobi
example {L : Type v} [LieRing L]
  (x : L) (y : L) (z : L) :
  ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  rw [leibniz_lie]
  rw [← lie_skew]
  simp
  rw [← lie_skew]
  simp
  rw [← lie_skew y x, lie_neg]
  exact add_left_neg ⁅z, ⁅x, y⁆⁆

--lieAlgebraSelfModule
example {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [LieAlgebra R L] :
  LieModule R L L := by
  constructor
  intro t x m
  rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg] --not me at this point
  intro t x m
  apply lie_smul

/-
instance {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [LieAlgebra R L] :
  ℕ → L := by
  intro n
  have t := TensorAlgebra R L
  sorry

--/

/-
example {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [LieAlgebra R L] :
  GradedAlgebra _ ℕ R L _ := by
  sorry
-/

variable (R : Type*) [CommSemiring R]

variable (M : Type*) [AddCommMonoid M] [Module R M]

def ι' : M →ₗ[R] TensorAlgebra R M :=
  { toFun := fun m => RingQuot.mkAlgHom R _ (FreeAlgebra.ι R m)
    map_add' := fun x y => by
      rw [← (RingQuot.mkAlgHom R (TensorAlgebra.Rel R M)).map_add]
      exact RingQuot.mkAlgHom_rel R TensorAlgebra.Rel.add
    map_smul' := fun r x => by
      rw [← (RingQuot.mkAlgHom R (TensorAlgebra.Rel R M)).map_smul]
      exact RingQuot.mkAlgHom_rel R TensorAlgebra.Rel.smul }

--The tensor algebra of the module M over the commutative semiring R.
--So the basis of M generates the TA, with R being for scalar mult.
--This is a function from the basis to the algebra.

--M →ₗ[R] DirectSum ℕ fun (i : ℕ) => ↥(LinearMap.range (TensorAlgebra.ι R) ^ i)
--GradedAlgebra fun (x : ℕ) => LinearMap.range (TensorAlgebra.ι R) ^ x

--The algebra is graded by...


--Plan for Submodule structure:
--Use LinearMap.range on a →ₗ[R] function
--Get that kind of function
