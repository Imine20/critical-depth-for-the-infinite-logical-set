import ShorPhysicalCode
import FaultShorSchedule

/-!
# Site permutations as native gates

A permutation of the sites of a specified block gives a tensor-local
physical unitary. It fixes the full X mask of the block.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

/-- Output site i holds the bit formerly at site p⁻¹(i). -/
def permuteSites {ι α : Type*} (p : Equiv.Perm ι) : Equiv.Perm (ι → α) where
  toFun x i := x (p.symm i)
  invFun x i := x (p i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

private theorem extended_symm {ι : Type*} [DecidableEq ι] {S : Finset ι}
    (p : Equiv.Perm S) :
    (Equiv.Perm.ofSubtype p).symm = Equiv.Perm.ofSubtype p.symm := by
  change (Equiv.Perm.ofSubtype p)⁻¹ = Equiv.Perm.ofSubtype p⁻¹
  rw [map_inv]

def sitePermutationGate {n q : ℕ} (S : Finset (Fin n)) (p : Equiv.Perm S)
    (hS : S.card ≤ q) : ListGate n (fun _ => 2) q where
  support := S
  gate := basisPermutation (permuteSites (Equiv.Perm.ofSubtype p))
  arity := hS
  locality := by
    apply basisPermutation_supportedOn S _ (permuteSites p)
    · intro x i hi
      change x ((Equiv.Perm.ofSubtype p).symm i) = x i
      rw [extended_symm p, Equiv.Perm.ofSubtype_apply_of_not_mem p.symm hi]
    · intro x
      funext i
      change x ((Equiv.Perm.ofSubtype p).symm i.val) = x (p.symm i).val
      rw [extended_symm p, Equiv.Perm.ofSubtype_apply_coe]
  unitary := basisPermutation_isUnitary _

theorem permuteSites_fixes_fullMask {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (p : Equiv.Perm S) :
    permuteSites (Equiv.Perm.ofSubtype p) (mark S) = mark S := by
  funext i
  change (if (Equiv.Perm.ofSubtype p).symm i ∈ S then (1 : Bit) else 0) =
    if i ∈ S then 1 else 0
  rw [extended_symm p]
  have hm := Equiv.Perm.ofSubtype_apply_mem_iff_mem (p := fun j => j ∈ S) p.symm i
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, ite_eq_left (hm.mpr hi)]
  · simp only [ite_eq_right hi, ite_eq_right (fun hj => hi (hm.mp hj))]

#print axioms sitePermutationGate
#print axioms permuteSites_fixes_fullMask

end CriticalDepth.FaultShorSaturation