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


def lift' {A : Type*} [Semiring A] [Algebra R A] : (M →ₗ[R] A) ≃ (TensorAlgebra R M →ₐ[R] A) :=
  { toFun :=
      RingQuot.liftAlgHom R ∘ fun f =>
        ⟨FreeAlgebra.lift R (⇑f), fun x y (h : TensorAlgebra.Rel R M x y) => by
          induction h <;>
            simp only [Algebra.smul_def, FreeAlgebra.lift_ι_apply, LinearMap.map_smulₛₗ,
              RingHom.id_apply, map_mul, AlgHom.commutes, map_add]⟩
    invFun := fun F => F.toLinearMap.comp (TensorAlgebra.ι R)
    left_inv := fun f => by
      rw [TensorAlgebra.ι]
      ext1 x
      exact (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply f x)
    right_inv := fun F =>
      RingQuot.ringQuot_ext' _ _ _ <|
        FreeAlgebra.hom_ext <| --val := ↑(FreeAlgebra.lift R) ↑f
          funext fun x => by
            rw [TensorAlgebra.ι]
            exact
              (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (FreeAlgebra.lift_ι_apply _ _) }

example {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [LieAlgebra R L] :
  LieModule R L L := by
  constructor
  intro t x m
  rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg] --not me at this point
  intro t x m
  apply lie_smul

#check ℕ

#check TensorAlgebra.lift

open scoped DirectSum

#check GradedAlgebra.ι

instance gradedAlgebra' :
    GradedAlgebra ((LinearMap.range (TensorAlgebra.ι R : M →ₗ[R] TensorAlgebra R M) ^ ·) : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom _ (TensorAlgebra.lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [TensorAlgebra.lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.coeAlgHom_of, Subtype.coe_mk])
    fun i x => by
    cases' x with x hx
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    -- porting note: use new `induction using` support that failed in Lean 3
    induction hx using Submodule.pow_induction_on_left' with
    | hr r =>
      rw [AlgHom.commutes, DirectSum.algebraMap_apply]; rfl
    | hadd x y i hx hy ihx ihy =>
      rw [AlgHom.map_add, ihx, ihy, ← map_add]; rfl
    | hmul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [AlgHom.map_mul, ih, TensorAlgebra.lift_ι_apply, GradedAlgebra.ι_apply R M, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)
