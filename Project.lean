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

structure FilteredAlgebra (R : Type*) (A : Type*)
[CommRing R] [Ring A] [Algebra R A] :=
(toFun : ℕ → Submodule R A)
(mono' : Monotone toFun)
(complete' : ∀ x, ∃ i, x ∈ toFun i)
(mapAdd' : ∀ n m, toFun (n + m) = toFun n * toFun m)


--The following lines are me playing around with grading maps.
--none of these ended up getting...

--Here we manually construct the map from the first n+1 grades to the direct sum.
instance SumOfGradesInTotal {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) → DirectSum ℕ (fun m => 𝒜 m) := by
  intro x
  unfold DirectSum at *
  rcases x with ⟨toFun', support'⟩
  constructor
  rotate_left

  intro j
  by_cases g : j > n
  exact 0
  simp at g
  have i := toFun' {val := j, isLt := Nat.lt_succ.mpr g}
  simp at i
  simp
  exact i
  simp
  apply Trunc.mk

  constructor
  rotate_left
  exact Multiset.range (Nat.succ n)
  intro j
  simp

  by_cases g : j > n
  rotate_left
  left
  simp at g
  cases g with
  | refl => left; rfl
  | step k => right; exact Nat.lt_succ.mpr k

  right
  intro h
  exfalso
  have g' : ¬j > n := Nat.not_lt.mpr h
  exact g' g

--This composes the above with the isomorphism from the direct sum of every grade into the underlying algebra.
def SumOfGradesInAlgebra {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) → A := by
  intro j
  have f := SumOfGradesInTotal 𝒜 j
  have g := DirectSum.decomposeAlgEquiv 𝒜
  have h := g.invFun
  apply h
  exact f

--This is just a proof of concept of DirectSum.IsInternal in a graded algebra.
theorem InternalSum {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]:
DirectSum.IsInternal 𝒜 := by
exact DirectSum.Decomposition.isInternal 𝒜

--Showing that SumOfGradesInAlgebra is R-linear.
instance SumOfGradesInAlgebra' {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) →ₗ[R] A := {
  toFun := SumOfGradesInAlgebra
  map_add' := sorry
  map_smul' := sorry
}

--An alternate form of the above, for testing purposes.
def SumOfGradesInAlgebra'' {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) →ₗ[R] A :=
  DirectSum.toModule R (Fin (n+1)) A _

theorem SumOfGradesInAlgebraAsSubmodule {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (n : ℕ) :
Submodule R A := by
  let dec := DirectSum.Decomposition 𝒜
  --let DSS := Submodule.span R (Set.range (DirectSum.toModule (fun i => ↥(𝒜 i)) n))
  sorry


--Here we set up the conversions between graded and filtered algebras.

def GradedToFiltered {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [i : GradedAlgebra 𝒜] : FilteredAlgebra R A := by
  constructor
  rotate_right
  intro n
  have im := DirectSum (Fin (n+1)) (fun m => 𝒜 m)
  have f := DirectSum.Decomposition 𝒜
  sorry
  sorry
  sorry
  sorry

def FilteredToGraded (R A : Type*)
[CommRing R] [Ring A] [Algebra R A] (F : FilteredAlgebra R A) :
GradedAlgebra ((LinearMap.range (inject : A →ₗ[R] Algebra R A) ^ ·) : ℕ → Submodule R _) := by
sorry


--Our second step is to set up the idea of a symmetric algebra.
--We also want to impose a grading structure on it.

--Largely taken from
--https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Lie/UniversalEnveloping.html#UniversalEnvelopingAlgebra
--https://github.com/leanprover-community/mathlib4/blob/006b23a50533766ff9714eda094f2b6da8a9f513//Mathlib/Algebra/Lie/UniversalEnveloping.lean#L61-L62
--and the existing code from TensorAlgebra.(Basic/Grading)

variable (R : Type*) [CommRing R]

variable (L : Type*) [AddCommMonoid L] [Module R L]

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

instance instRing : Ring (SymmetricAlgebra R L) :=
  inferInstanceAs (Ring (RingQuot (SymmetricAlgebra.Rel R L)))

instance instAlgebra : Algebra R (SymmetricAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (SymmetricAlgebra.Rel R L)))

--CommMonoid


--With the basic constructions of the symmetric algebra set up, we give it a grading.
--This is largely based on TensorAlgebra.Basic and TensorAlgebra.Grading.

variable {L}

--The canonical injection of L into Symmetric R L.

def symmetricι : L →ₗ[R] SymmetricAlgebra R L := {
  toFun := fun m => RingQuot.mkAlgHom R _ (TensorAlgebra.ι R m)
  map_add' := fun x y => by
      rw [← (RingQuot.mkAlgHom R (Rel R L)).map_add]
      refine AlgHom.congr_arg (RingQuot.mkAlgHom R (Rel R L)) ?h
      exact LinearMap.map_add ιₜ x y
  map_smul' := fun r x => by
      rw [← (RingQuot.mkAlgHom R (Rel R L)).map_smul]
      refine FunLike.congr_arg (RingQuot.mkAlgHom R (Rel R L)) ?h₂
      exact LinearMap.map_smul ιₜ r x
}

open scoped DirectSum

local notation "ιₛ" => symmetricι R

theorem ringQuot_mkAlgHom_tensorAlgebra_ι_eq_ι (m : L) :
    RingQuot.mkAlgHom R (Rel R L) (TensorAlgebra.ι R m) = ιₛ m := by
  rw [symmetricι]
  rfl

--This should probably be SymmetricLift but its too late to fix.
@[simps symm_apply]
def symlift {A : Type*} [CommSemiring A] [Algebra R A] : (L →ₗ[R] A) ≃ (SymmetricAlgebra R L →ₐ[R] A) :=
  { toFun :=
      RingQuot.liftAlgHom R ∘ fun f =>
        ⟨TensorAlgebra.lift R (f), fun x y (h : Rel R L x y) => by
          induction h <;>
            simp only [Algebra.smul_def, TensorAlgebra.lift_ι_apply, LinearMap.map_smulₛₗ, RingHom.id_apply, map_mul, AlgHom.commutes, map_add];
            exact mul_comm _ _
            ⟩
    invFun := fun F => F.toLinearMap.comp (ιₛ)
    left_inv := fun f => by
      rw [symmetricι]
      ext1 x
      exact (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (TensorAlgebra.lift_ι_apply f x)
    right_inv := fun F =>
      RingQuot.ringQuot_ext' _ _ _ <|
        TensorAlgebra.hom_ext <|
          LinearMap.ext fun x => by
            rw [symmetricι]
            exact
              (RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ _) }


--The same map as symmetricι, but interpreting "SymmetricAlgebra R L" as grades.
nonrec def SymGradι : L →ₗ[R] ⨁ i : ℕ, ↥((LinearMap.range (ιₛ : L →ₗ[R] SymmetricAlgebra R L)) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ιₛ : L →ₗ[_] _) ^ i)) 1 ∘ₗ
    (ιₛ).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

--The explicit image of an element of L under the above.
theorem SymGradι_apply (m : L) :
    SymGradι R m =
      DirectSum.lof R ℕ (fun (i : ℕ) => ↥(LinearMap.range (ιₛ : L →ₗ[R] SymmetricAlgebra R L) ^ i)) 1
        ⟨ιₛ m, by simpa only [pow_one] using LinearMap.mem_range_self _ m ⟩ := rfl

--An example of what symlift looks like in practice.
example {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A) :
  SymmetricAlgebra R L →ₐ[R] A := by
  exact symlift R f

--Showing that the composition of the lift of f with the injection returns f.
@[simp]
theorem sym_ι_comp_lift {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A) :
    (symlift R f).toLinearMap.comp ιₛ = f := by
  convert (symlift R).symm_apply_apply f

--As the above, but explicitly on an element.
@[simp]
theorem sym_lift_ι_apply {A : Type*} [CommSemiring A] [Algebra R A] (f : L →ₗ[R] A) (x) :
    symlift R f (ιₛ x) = f x := by
  conv_rhs => rw [← sym_ι_comp_lift R f]

#check GradedAlgebra.ofAlgHom
#check symlift
#check SymGradι

#check SymmetricAlgebra R L
#check CommSemiring --CommMonoid, Semiring
#check Ring --Semiring, AddCommGroup, AddGroupWithOne

#check symlift R --(L →ₗ[R] _) ≃ (SymmetricAlgebra R L →ₐ[R] _)
#check SymGradι R (L := L) --L →ₗ[R] ⨁ (i : ℕ), ↥(LinearMap.range ιₛ ^ i)
#check symlift R <| (SymGradι R (L := L))

--Building the actual grading on the symmetric algebra.
instance gradedAlgebraSym : --[CommRing R] [Module R L]:
    GradedAlgebra ((LinearMap.range (ιₛ : L →ₗ[R] SymmetricAlgebra R L) ^ ·) : ℕ → Submodule R _) :=
  GradedAlgebra.ofAlgHom (LinearMap.range (ιₛ : L →ₗ[R] SymmetricAlgebra R L) ^ ·)
    (symlift R (L := L) <| SymGradι R L) --its a problem with symlift?
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [sym_lift_ι_apply, SymGradι_apply R L, DirectSum.coeAlgHom_of, Subtype.coe_mk])
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
      rw [AlgHom.map_mul, ih, sym_lift_ι_apply, SymGradι_apply R L, DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end SymmetricAlgebra

instance filteredUniversal (R : Type*) (L : Type*)
[CommRing R] [Ring L] [LieRing L] [Algebra R L] [g : LieAlgebra R L] :
FilteredAlgebra R L := {
  toFun := by
    sorry
  mono' := sorry
  complete' := sorry
  mapAdd' := sorry
}

--END GOAL:
--construct an isomorphism from the filtration on gr(U(g)) to S(g)
--by filter
--maybe show ∀ (n : ℕ), gr(U(g)) n ≅ S(g) n
--on the grading functions

namespace Theorem

--the ≅ is probably not right/sufficient
--but it doesnt matter since im not going to get there

theorem PBW {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [LieAlgebra R L]
  : GradedUniversalEnvelopingAlgebra R L ≅ SymmetricAlgebra R L
  := sorry

end Theorem
