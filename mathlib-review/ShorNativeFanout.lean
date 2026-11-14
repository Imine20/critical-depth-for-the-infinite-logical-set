import ShorPhysicalCode
import FaultShorSchedule

/-!
# A native gate for a Shor fanout block

The controlled additions with a common pivot act as one tensor-local
physical gate on the prescribed block of sites.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

private def wordBits (ι : Type*) : (ι → Fin 2) ≃ (ι → Bit) :=
  Equiv.piCongrRight fun _ => qubitBitEquiv

private def onQubitWords {ι : Type*} (e : Equiv.Perm (ι → Bit)) :
    Equiv.Perm (ι → Fin 2) :=
  ((wordBits ι).trans e).trans (wordBits ι).symm

private def blockParent {ι : Type*} [DecidableEq ι] (S : Finset ι) (pivot : ι) (i : ι) :
    Option ι :=
  if i ∈ S ∧ i ≠ pivot then some pivot else none

private theorem blockParent_pivot {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (pivot i a : ι) (ht : blockParent S pivot i = some a) :
    blockParent S pivot a = none := by
  by_cases hi : i ∈ S ∧ i ≠ pivot
  · simp [blockParent, hi] at ht
    simp [← ht, blockParent]
  · simp [blockParent, hi] at ht

/-- The reversible binary controlled additions from a single pivot to
all the other sites of the block. -/
def blockFanoutEquiv {ι : Type*} [DecidableEq ι] (S : Finset ι) (pivot : ι) :
    (ι → Bit) ≃ₗ[Bit] (ι → Bit) :=
  fanoutLinearEquiv (blockParent S pivot) (fun i a => blockParent_pivot S pivot i a)

theorem blockFanoutEquiv_apply {ι : Type*} [DecidableEq ι] (S : Finset ι) (pivot i : ι)
    (x : ι → Bit) :
    blockFanoutEquiv S pivot x i = if i ∈ S ∧ i ≠ pivot then x i + x pivot else x i := by
  change fanout (blockParent S pivot) x i = _
  by_cases hi : i ∈ S ∧ i ≠ pivot <;> simp [fanout, blockParent, hi]

/-- The matrix of the reversible fanout action is a tensor-local unitary in
the native qubit model. -/
def blockFanoutGate {n q : ℕ} (S : Finset (Fin n)) (pivot : S) (hS : S.card ≤ q) :
    ListGate n (fun _ => 2) q where
  support := S
  gate := basisPermutation (onQubitWords (blockFanoutEquiv S pivot.val).toEquiv)
  arity := hS
  locality := by
    classical
    let localMap := onQubitWords (blockFanoutEquiv (Finset.univ : Finset S) pivot).toEquiv
    apply basisPermutation_supportedOn S _ localMap
    · intro x i hi
      change qubitBitEquiv.symm (blockFanoutEquiv S pivot.val (fun j => qubitBitEquiv (x j)) i) = x i
      rw [blockFanoutEquiv_apply]
      simp [hi]
    · intro x
      funext i
      change qubitBitEquiv.symm
        (blockFanoutEquiv S pivot.val (fun j => qubitBitEquiv (x j)) i.val) =
        qubitBitEquiv.symm
          (blockFanoutEquiv Finset.univ pivot (fun j : S => qubitBitEquiv (x j.val)) i)
      rw [blockFanoutEquiv_apply, blockFanoutEquiv_apply]
      have hp : i.val ≠ pivot.val ↔ i ≠ pivot :=
        not_congr ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩
      simp [i.property, hp]
  unitary := basisPermutation_isUnitary _

/-- An arbitrary qubit subset disjoint from a fanout block is left pointwise
unchanged at the level of basis strings. -/
theorem blockFanout_fixes_outside {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (pivot : S) (x : ι → Bit) (i : ι) (hi : i ∉ S) :
    blockFanoutEquiv S pivot.val x i = x i := by
  simp [blockFanoutEquiv_apply, hi]

#print axioms blockFanoutGate
#print axioms blockFanout_fixes_outside

end CriticalDepth.FaultShorSaturation