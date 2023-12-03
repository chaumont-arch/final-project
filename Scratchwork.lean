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
