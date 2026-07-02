
import AnabelianAlgorithms.Linter.NonstandardAxioms
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option linter.nonstandardAxioms false

/-
This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
Corresponding source file in that project: `Pi1/Mathlib/RingTheory/Ideal/Quotient/Operations.lean`.
-/
@[simp]
lemma Ideal.quotientInfRingEquivPiQuotient_mk {R ι : Type*} [Finite ι] [CommRing R]
    (I : ι → Ideal R) (hI : Pairwise (Function.onFun IsCoprime I)) (x : R) :
    Ideal.quotientInfRingEquivPiQuotient I hI x = fun _ ↦ Ideal.Quotient.mk _ x := rfl
