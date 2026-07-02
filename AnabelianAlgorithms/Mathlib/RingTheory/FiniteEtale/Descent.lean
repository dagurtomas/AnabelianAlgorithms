
import AnabelianAlgorithms.Linter.NonstandardAxioms
import Mathlib.RingTheory.Etale.Descent
import AnabelianAlgorithms.Mathlib.RingTheory.FiniteEtale.Basic

set_option linter.nonstandardAxioms false

/-
This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
Corresponding source file in that project: `Pi1/RingTheory/FiniteEtale/Descent.lean`.
-/
universe u v w

open TensorProduct

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S := by
  have : Algebra.Etale R S :=
    .of_etale_tensorProduct_of_faithfullyFlat T
  have : Module.Finite R S :=
    .of_finite_tensorProduct_of_faithfullyFlat T
  constructor
