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

--bad notation but whatevers

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

--What does this get us?
theorem InternalSum {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]:
DirectSum.IsInternal 𝒜 := by
exact DirectSum.Decomposition.isInternal 𝒜

instance SumOfGradesInAlgebra' {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] :
DirectSum (Fin (n+1)) (fun m => 𝒜 m) →ₗ[R] A := {
  toFun := SumOfGradesInAlgebra
  map_add' := sorry
  map_smul' := sorry
}
--timing out

#check DirectSum.lof

theorem SumOfGradesInAlgebraAsSubmodule {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (n : ℕ) :
Submodule R A := by
  let dec := DirectSum.Decomposition 𝒜
  --let DSS := Submodule.span R (Set.range (DirectSum.toModule (fun i => ↥(𝒜 i)) n))

  sorry

--/-
def ToFiltered {R : Type*} {A : Type*}
[CommRing R] [Ring A] [Algebra R A]
(𝒜 : ℕ → Submodule R A) [i : GradedAlgebra 𝒜] : FilteredAlgebra R A := by
  constructor
  rotate_right
  --have s := fun n => DirectSum (Fin (n+1)) (fun m => 𝒜 m)
  --have s' := fun (n : ℕ) => LinearMap.range (𝒜 R) ^ n
  intro n
  have im := DirectSum (Fin (n+1)) (fun m => 𝒜 m)
  have f := DirectSum.Decomposition 𝒜
  sorry
  sorry
  sorry
  sorry
  /-
  where
  toFun := fun n => sorry --(DirectSum (Fin (n+1)) (fun m => 𝒜 m))
  mono' := sorry
  complete' := sorry
  mapAdd' := sorry
  -/

theorem FilteredFromGraded (R A : Type*)
[CommRing R] [Ring A] [Algebra R A] (F : FilteredAlgebra R A) :
GradedAlgebra (R := R) (A := A) (ι := ℕ) := by
sorry


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

instance instRing : Ring (SymmetricAlgebra R L) :=
  inferInstanceAs (Ring (RingQuot (SymmetricAlgebra.Rel R L)))

instance instAlgebra : Algebra R (SymmetricAlgebra R L) :=
  inferInstanceAs (Algebra R (RingQuot (SymmetricAlgebra.Rel R L)))

def SymmetricAlgebra.ι : L →ₗ[R] SymmetricAlgebra R L := {
  toFun := fun m => RingQuot.mkAlgHom R _ (TensorAlgebra.ι R m)
  map_add' := fun x y => by
      rw [← (RingQuot.mkAlgHom R (Rel R L)).map_add]
      refine AlgHom.congr_arg (RingQuot.mkAlgHom R (Rel R L)) ?h
      exact LinearMap.map_add ιₜ x y
      --exact RingQuot.mkAlgHom_rel R Rel.add
  map_smul' := fun r x => by
      rw [← (RingQuot.mkAlgHom R (Rel R L)).map_smul]
      --exact RingQuot.mkAlgHom_rel R Rel.smul
      refine FunLike.congr_arg (RingQuot.mkAlgHom R (Rel R L)) ?h₂
      exact LinearMap.map_smul ιₜ r x
}


/-
instance instGraded : GradedAlgebra (SymmetricAlgebra R L) :=
  inferInstanceAs (GradedAlgebra (RingQuot (SymmetricAlgebra.Rel R L)))
-/

/-
open scoped DirectSum

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

nonrec def GradedAlgebra.ι : M →ₗ[R] ⨁ i : ℕ, ↥(LinearMap.range (ιₜ : M →ₗ[_] _) ^ i) :=
  DirectSum.lof R ℕ (fun i => ↥(LinearMap.range (ιₜ R : M →ₗ[_] _) ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m
-/

end SymmetricAlgebra




--END GOAL:
--construct an isomorphism from the filtration on gr(U(g)) to S(g)
--by filter
--maybe show ∀ (n : ℕ), gr(U(g)) n ≅ S(g) n
--on the grading functions

/-
theorem PBW {R : Type u} {L : Type v}
  [CommRing R] [LieRing L] [g : LieAlgebra R L]
  : FilteredFromGraded UniversalEnvelopingAlgebra g ≅ SymmetricAlgebra g
  := sorry
-/

namespace Theorem



end Theorem
