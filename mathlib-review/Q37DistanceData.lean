import Q37BinaryData

/-!
# Bounded-support signature checks for Q37

A signature stores its syndrome in the high bits and its logical parity in
the low bit. A radix check verifies that, among sums of at most three
single-site signatures, a given syndrome has only one logical parity.
The data are the final Q37 checks of Dua et al., arXiv:2610.06730v1,
Table 4 and equation (33).
-/

namespace CriticalDepth.Q37BinaryData

/-- Binary syndrome and logical-parity columns, packed into a single word. -/
def signatureColumns (checks : List Nat) (oppositeLogical : Nat) : List Nat :=
  (List.range 37).map fun i =>
    let site := 1 <<< i
    2 * syndrome checks site + dot oppositeLogical site

def halfSignatures (columns : List Nat) : List (Nat × Nat) :=
  (smallXorSums 3 columns).map fun packed =>
    (packed / 2, packed % 2)

def xSignatureColumns : List Nat :=
  [40961, 8194, 2, 4, 3200, 136,
   7168, 345089, 65857, 213056, 16384, 65536,
   131072, 17664, 262144, 36869, 9, 2048,
   2048, 48, 10240, 12288, 1040, 4160,
   38400, 41088, 14848, 192, 32, 164097,
   410113, 262912, 16384, 65536, 131072, 491520,
   262144]

def zSignatureColumns : List Nat :=
  [384, 65601, 65601, 128, 34305, 33025,
   140289, 36864, 280576, 67584, 131076, 327688,
   262160, 151552, 163872, 128, 33025, 131138,
   294914, 8192, 401472, 73857, 8192, 82944,
   16896, 262912, 131584, 263168, 8192, 266240,
   18432, 133120, 98308, 32776, 65552, 20480,
   32]

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem xSignatureColumns_eq :
    xSignatureColumns = signatureColumns zChecks logicalZ := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem zSignatureColumns_eq :
    zSignatureColumns = signatureColumns xChecks logicalX := by
  decide

/-- Split by a syndrome bit until all entries in each remaining bucket
must have the same logical parity. -/
def parityConsistent (bits : Nat) (entries : List (Nat × Nat)) : Bool :=
  match bits with
  | 0 =>
    match entries with
    | [] => true
    | first :: rest => rest.all (fun entry => entry.2 == first.2)
  | bit + 1 =>
    match entries with
    | [] => true
    | _ :: _ =>
      parityConsistent bit (entries.filter fun entry => entry.1.testBit bit) &&
        parityConsistent bit (entries.filter fun entry => !entry.1.testBit bit)

theorem parityConsistent_sound (bits : Nat) (entries : List (Nat × Nat))
    (hvalid : parityConsistent bits entries = true) :
    ∀ a ∈ entries, ∀ b ∈ entries, a.1 = b.1 → a.2 = b.2 := by
  induction bits generalizing entries with
  | zero =>
    cases entries with
    | nil => simp
    | cons first rest =>
      have hrest : ∀ x ∈ rest, x.2 = first.2 := by
        intro x hx
        exact beq_iff_eq.mp (List.all_eq_true.mp hvalid x hx)
      have hall : ∀ x ∈ first :: rest, x.2 = first.2 := by
        intro x hx
        rcases List.mem_cons.mp hx with h | h
        · exact congrArg Prod.snd h
        · exact hrest x h
      intro a ha b hb _
      exact (hall a ha).trans (hall b hb).symm
  | succ bit ih =>
    cases entries with
    | nil => simp
    | cons first rest =>
      let entries := first :: rest
      have hsplit :
          parityConsistent bit (entries.filter fun entry => entry.1.testBit bit) = true ∧
            parityConsistent bit (entries.filter fun entry => !entry.1.testBit bit) = true :=
        Bool.and_eq_true_iff.mp hvalid
      intro a ha b hb hsame
      cases hbit : a.1.testBit bit
      · have hbitB : b.1.testBit bit = false := hsame ▸ hbit
        exact ih _ hsplit.2 a
          (List.mem_filter.mpr ⟨ha, by simp [hbit]⟩) b
          (List.mem_filter.mpr ⟨hb, by simp [hbitB]⟩) hsame
      · have hbitB : b.1.testBit bit = true := hsame ▸ hbit
        exact ih _ hsplit.1 a
          (List.mem_filter.mpr ⟨ha, hbit⟩) b
          (List.mem_filter.mpr ⟨hb, hbitB⟩) hsame

-- Separate high-bit buckets so no kernel reduction has to process the
-- entire list of low-weight signatures in one proof.
def parityConsistentBucket (columns : List Nat) (bucket : Nat) : Bool :=
  parityConsistent 15 ((halfSignatures columns).filter fun entry =>
    entry.1 / 2 ^ 15 == bucket)

set_option maxRecDepth 25000 in
set_option maxHeartbeats 30000000 in
theorem x_half_signature_certificate :
    (List.range 8).all (parityConsistentBucket xSignatureColumns) = true := by
  decide

set_option maxRecDepth 25000 in
set_option maxHeartbeats 30000000 in
theorem z_half_signature_certificate :
    (List.range 8).all (parityConsistentBucket zSignatureColumns) = true := by
  decide

theorem parityConsistent_of_bucket_certificates {columns : List Nat}
    (certificate : (List.range 8).all (parityConsistentBucket columns) = true)
    {a b : Nat × Nat} (ha : a ∈ halfSignatures columns)
    (hb : b ∈ halfSignatures columns) (hbound : a.1 < 2 ^ 18)
    (hsame : a.1 = b.1) : a.2 = b.2 := by
  let bucket := a.1 / 2 ^ 15
  have hbucket : bucket < 8 := by
    dsimp only [bucket]
    omega
  have hvalid := List.all_eq_true.mp certificate bucket (List.mem_range.mpr hbucket)
  have hmemA : a ∈ (halfSignatures columns).filter
      (fun entry => entry.1 / 2 ^ 15 == bucket) := by
    exact List.mem_filter.mpr ⟨ha, by simp [bucket]⟩
  have hmemB : b ∈ (halfSignatures columns).filter
      (fun entry => entry.1 / 2 ^ 15 == bucket) := by
    exact List.mem_filter.mpr ⟨hb, by simp [bucket, ← hsame]⟩
  exact parityConsistent_sound 15 _ hvalid a hmemA b hmemB hsame

#print axioms xSignatureColumns_eq
#print axioms zSignatureColumns_eq
#print axioms parityConsistent_sound
#print axioms x_half_signature_certificate
#print axioms z_half_signature_certificate
#print axioms parityConsistent_of_bucket_certificates

end CriticalDepth.Q37BinaryData
