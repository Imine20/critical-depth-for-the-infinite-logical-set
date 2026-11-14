import Init

/-!
# Binary input data for the 37-qubit CSS example

The stabilizer rows come from Table 4, the logical rows from equation (33),
and the gate supports from equations (31), (32), and (35) of Dua et al.,
*Qubit CSS codes with Universal Transversal Gates*, https://arxiv.org/html/2610.06730v1.
Source qubit i is bit i - 1. The dual rows certify the two binary check ranks.

The finite checks concern the encoded data. Transport to complex Hilbert
spaces and extension from the small coefficient masks to all code cosets
require separate theorems.
-/

namespace CriticalDepth.Q37BinaryData

def xChecks : List Nat :=
  [393216, 4294968320, 8589936640, 17179873280, 68719493120,
   1179654, 2129929, 33620001, 117440528, 142606416,
   3221226240, 34896617600, 276299840, 35458654464, 12885246128,
   21485324806, 2215797824, 705960192]

def zChecks : List Nat :=
  [6, 32776, 65568, 4718592, 268959744,
   142607104, 167772208, 2684363008, 3305111552, 20979920,
   68550736, 94404672, 103809027, 5368718976, 34946973697,
   42949675904, 53150224896, 106300457088]

def xDual : List Nat :=
  [537010946, 539502344, 539494561, 536875177, 539517729,
   2621450, 8, 9, 538977137, 538977096,
   2621960, 169, 524288, 539493281, 41,
   2621448, 539501320, 536871081]

def zDual : List Nat :=
  [4, 8, 32895, 4207360, 4731648,
   7680, 32863, 5888, 16823048, 13056,
   45903, 32783, 6, 1024, 7,
   2048, 4096, 16256]

def logicalX : Nat := 2162806

def logicalZ : Nat := 1610711425

def parityBlocks : List Nat :=
  [98305, 393218, 1572868, 6291464, 25165840,
   100663328, 402653248, 536871040, 1073742080, 2147484160,
   4294968320, 8589936640, 17179873280, 34359746560, 68719493120]

def lineBlocks : List Nat :=
  [7, 32792, 65632, 35782656, 142868480,
   273154048, 84934656]

def weight (width word : Nat) : Nat :=
  (List.range width).foldl (fun total i => total + (word.testBit i).toNat) 0

def dot (a b : Nat) : Nat :=
  weight 37 (Nat.land a b) % 2

def syndrome (checks : List Nat) (word : Nat) : Nat :=
  checks.zipIdx.foldl (fun result (check, i) => result + (dot check word <<< i)) 0

def mutuallyDisjoint : List Nat → Bool
  | [] => true
  | first :: rest => rest.all (fun block => Nat.land first block == 0) &&
      mutuallyDisjoint rest

/-- All xor sums of at most the indicated number of input masks. -/
def smallXorSums (bound : Nat) (rows : List Nat) : List Nat :=
  match rows with
  | [] => [0]
  | first :: rest =>
      match bound with
      | 0 => [0]
      | k + 1 => smallXorSums (k + 1) rest ++
          (smallXorSums k rest).map (Nat.xor first)
termination_by structural rows

def phaseSamples (rows : List Nat) (logical : Nat) (blocks : List Nat)
    (degree modulus : Nat) : Bool :=
  let rowsInBlocks := rows.map (syndrome blocks)
  let logicalInBlocks := syndrome blocks logical
  (smallXorSums degree rowsInBlocks).all fun mask =>
    weight blocks.length mask % modulus == 0 &&
      weight blocks.length (Nat.xor mask logicalInBlocks) % modulus == modulus - 1

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem xDual_certificate :
    xChecks.length = 18 ∧ xDual.length = 18 ∧
      xDual.zipIdx.all (fun (dual, i) => syndrome xChecks dual == (1 <<< i)) = true := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem zDual_certificate :
    zChecks.length = 18 ∧ zDual.length = 18 ∧
      zDual.zipIdx.all (fun (dual, i) => syndrome zChecks dual == (1 <<< i)) = true := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem css_and_logical_certificate :
    xChecks.all (fun row => syndrome zChecks row == 0) = true ∧
      syndrome zChecks logicalX = 0 ∧ syndrome xChecks logicalZ = 0 ∧
      dot logicalX logicalZ = 1 ∧ weight 37 logicalX = 7 ∧ weight 37 logicalZ = 7 := by
  decide

theorem gate_partition_certificate :
    mutuallyDisjoint parityBlocks = true ∧ mutuallyDisjoint lineBlocks = true ∧
      parityBlocks.all (fun block => decide (weight 37 block ≤ 3)) = true ∧
      lineBlocks.all (fun block => weight 37 block == 3) = true ∧
      parityBlocks.foldl Nat.lor 0 = 2 ^ 37 - 1 := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem parity_phase_samples : phaseSamples xChecks logicalX parityBlocks 3 8 = true := by
  decide

set_option maxRecDepth 6000 in
set_option maxHeartbeats 25000000 in
theorem line_phase_samples : phaseSamples zChecks logicalZ lineBlocks 2 4 = true := by
  decide

#print axioms xDual_certificate
#print axioms zDual_certificate
#print axioms css_and_logical_certificate
#print axioms gate_partition_certificate
#print axioms parity_phase_samples
#print axioms line_phase_samples

end CriticalDepth.Q37BinaryData
