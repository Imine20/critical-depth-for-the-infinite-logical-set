import BinaryPermutationDiagonal
import Q37CheckSpaces
import BarePauliRotations

/-!
# The stated three-block physical compression of the Q37 logical Z
-/

namespace CriticalDepth.Q37BinaryData

open CriticalDepth.Manuscript CriticalDepth.ReviewV2
open CriticalDepth.FaultShorSaturation CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.Manuscript20261114 CriticalDepth.Manuscript20261114.CSSCode
open Matrix
open scoped BigOperators Kronecker

noncomputable section

/-- Zero-based forms of the three supports in the manuscript. -/
def q37CompressionBlocks : List (Finset (Fin 37)) :=
  [{0,15,16}, {7,29}, {8,30}]

theorem q37CompressionBlocks_disjoint :
    q37CompressionBlocks.Pairwise (fun A B => Disjoint A B) := by decide

/-- Computational action of CNOTs 16→1 and 17→1, 30→8, and 31→9
in the manuscript's one-based qubit labels. -/
def q37CompressionBits (x : Q37Word) (i : Fin 37) : CSSBit :=
  if i = 0 then x 0 + x 15 + x 16
  else if i = 7 then x 7 + x 29
  else if i = 8 then x 8 + x 30
  else x i

private def q37Cnot (control target : Fin 37) (x : Q37Word) (i : Fin 37) : CSSBit :=
  if i = target then x i + x control else x i

private def q37CnotEquiv (control target : Fin 37) (h : control ≠ target) : Equiv.Perm Q37Word where
  toFun := q37Cnot control target
  invFun := q37Cnot control target
  left_inv := by
    intro x
    funext i
    have hadd (a : CSSBit) : a+a=0 := by decide +revert
    by_cases hi : i=target
    · subst i
      simp [q37Cnot,h,add_assoc,hadd]
    · simp [q37Cnot,hi]
  right_inv := by
    intro x
    funext i
    have hadd (a : CSSBit) : a+a=0 := by decide +revert
    by_cases hi : i=target
    · subst i
      simp [q37Cnot,h,add_assoc,hadd]
    · simp [q37Cnot,hi]

private theorem q37Cnot_supported (control target : Fin 37) (h : control ≠ target)
    (S : Finset (Fin 37)) (hc : control ∈ S) (ht : target ∈ S) :
    SupportedOn (binaryWordOperator (q37CnotEquiv control target h)) S := by
  classical
  let W := LocalBasis (fun _ : Fin 37 => 2) S
  let ctrl : S := ⟨control,hc⟩
  let targ : S := ⟨target,ht⟩
  let T (x : W) (i : S) : Fin 2 :=
    if i.val = target then qubitBitEquiv.symm (qubitBitEquiv (x targ) + qubitBitEquiv (x ctrl))
    else x i
  have hT : Function.Involutive T := by
    intro x
    funext i
    have hadd (a : CSSBit) : a+a=0 := by decide +revert
    by_cases hi : i.val = target
    · have he : i = targ := Subtype.ext hi
      subst i
      simp [T,targ,ctrl,h,add_assoc,hadd]
    · simp [T,hi]
  let localE : Equiv.Perm W := ⟨T,T,hT,hT⟩
  unfold binaryWordOperator
  apply basisPermutation_supportedOn S _ localE
  · intro x i hi
    have hne : i ≠ target := fun he => hi (he.symm ▸ ht)
    change qubitBitEquiv.symm (q37Cnot control target (binaryWordEquiv 37 x) i) = x i
    simp [q37Cnot,hne,binaryWordEquiv]
  · intro x
    funext i
    change qubitBitEquiv.symm (q37Cnot control target (binaryWordEquiv 37 x) i.val) =
      T (fun j : S => x j.val) i
    by_cases hi : i.val = target
    · simp [q37Cnot,T,hi,binaryWordEquiv,targ,ctrl]
    · simp [q37Cnot,T,hi,binaryWordEquiv]

private def q37CnotA : Equiv.Perm Q37Word := q37CnotEquiv 15 0 (by decide)
private def q37CnotB : Equiv.Perm Q37Word := q37CnotEquiv 16 0 (by decide)
private def q37CnotC : Equiv.Perm Q37Word := q37CnotEquiv 29 7 (by decide)
private def q37CnotD : Equiv.Perm Q37Word := q37CnotEquiv 30 8 (by decide)

private def q37CnotBlockA : ListGate 37 (fun _ => 2) 3 where
  support := {0,15,16}
  gate := binaryWordOperator q37CnotB * binaryWordOperator q37CnotA
  arity := by decide
  locality := (q37Cnot_supported 16 0 (by decide) _ (by decide) (by decide)).mul_same
    (q37Cnot_supported 15 0 (by decide) _ (by decide) (by decide))
  unitary := unitary_mul (basisPermutation_isUnitary _) (basisPermutation_isUnitary _)

private def q37CnotBlockB : ListGate 37 (fun _ => 2) 3 where
  support := {7,29}
  gate := binaryWordOperator q37CnotC
  arity := by decide
  locality := q37Cnot_supported 29 7 (by decide) _ (by decide) (by decide)
  unitary := basisPermutation_isUnitary _

private def q37CnotBlockC : ListGate 37 (fun _ => 2) 3 where
  support := {8,30}
  gate := binaryWordOperator q37CnotD
  arity := by decide
  locality := q37Cnot_supported 30 8 (by decide) _ (by decide) (by decide)
  unitary := basisPermutation_isUnitary _

/-- Three disjoint gates, using the 3-site gate to perform both CNOTs
on the first group in a single layer. -/
def q37CompressionArbitraryLayer : ArbitraryLayer 37 (fun _ => 2) 3 where
  gates := [q37CnotBlockA,q37CnotBlockB,q37CnotBlockC]
  disjoint := by
    rw [← List.pairwise_map]
    change q37CompressionBlocks.Pairwise (fun A B => Disjoint A B)
    exact q37CompressionBlocks_disjoint

private theorem q37CompressionArbitraryLayer_eval :
    q37CompressionArbitraryLayer.eval =
      binaryWordOperator (((q37CnotA.trans q37CnotB).trans q37CnotC).trans q37CnotD) := by
  change binaryWordOperator q37CnotD * (binaryWordOperator q37CnotC *
    ((binaryWordOperator q37CnotB * binaryWordOperator q37CnotA) * 1)) = _
  rw [Matrix.mul_one, binaryWordOperator_mul, binaryWordOperator_mul, binaryWordOperator_mul]

private theorem q37CompressionBits_involutive : Function.Involutive q37CompressionBits := by
  intro x
  funext i
  have hadd (a : CSSBit) : a + a = 0 := by decide +revert
  by_cases h0 : i = 0
  · subst i
    simp only [q37CompressionBits, ite_eq_left rfl]
    exact (show (x 0 + x 15 + x 16) + x 15 + x 16 = x 0 by
      calc
        _ = x 0 + (x 15+x 15) + (x 16+x 16) := by abel
        _ = _ := by rw [hadd, hadd, add_zero, add_zero])
  · by_cases h7 : i = 7
    · subst i
      simp [q37CompressionBits, hadd, add_assoc]
    · by_cases h8 : i = 8
      · subst i
        simp [q37CompressionBits, hadd, add_assoc]
      · simp [q37CompressionBits, h0,h7,h8]

def q37CompressionBitsEquiv : Equiv.Perm Q37Word where
  toFun := q37CompressionBits
  invFun := q37CompressionBits
  left_inv := q37CompressionBits_involutive
  right_inv := q37CompressionBits_involutive

def q37CompressionGateOperator : Operator (QubitBasis 37) :=
  binaryWordOperator q37CompressionBitsEquiv

theorem q37Compression_follows_CNOTs :
    (((q37CnotA.trans q37CnotB).trans q37CnotC).trans q37CnotD) = q37CompressionBitsEquiv := by
  apply Equiv.ext
  intro x
  funext i
  change q37Cnot 30 8 (q37Cnot 29 7 (q37Cnot 16 0 (q37Cnot 15 0 x))) i =
    q37CompressionBits x i
  by_cases h0 : i = 0
  · subst i
    simp [q37Cnot,q37CompressionBits]
  · by_cases h7 : i = 7
    · subst i
      simp [q37Cnot,q37CompressionBits]
    · by_cases h8 : i = 8
      · subst i
        simp [q37Cnot,q37CompressionBits]
      · simp [q37Cnot,q37CompressionBits,h0,h7,h8]

/-- This is the same layer as the three named disjoint physical blocks,
in the fixed-length layer representation of the existing circuit API. -/
def q37CompressionLayer : Layer 37 (fun _ => 2) 3 :=
  q37CompressionArbitraryLayer.normalized

theorem q37CompressionLayer_eval : q37CompressionLayer.eval = q37CompressionGateOperator := by
  rw [q37CompressionLayer, ArbitraryLayer.normalized_eval]
  have h : filterNonemptyGates q37CompressionArbitraryLayer.gates = q37CompressionArbitraryLayer.gates := by
    have hA : q37CnotBlockA.support ≠ ∅ := by decide
    have hB : q37CnotBlockB.support ≠ ∅ := by decide
    have hC : q37CnotBlockC.support ≠ ∅ := by decide
    simp [q37CompressionArbitraryLayer,filterNonemptyGates,hA,hB,hC]
  rw [h]
  change q37CompressionArbitraryLayer.eval = _
  rw [q37CompressionArbitraryLayer_eval, q37Compression_follows_CNOTs]
  rfl

def q37CompressionPivots : Finset (Fin 37) := {0,7,8}

def q37CompressedWord : Q37Word := mark q37CompressionPivots

theorem q37Compression_dot (x : Q37Word) :
    dotProduct (q37CompressionBits x) q37LogicalZ = dotProduct x q37CompressedWord := by
  have hZ : q37LogicalZ = mark ({0,7,8,15,16,29,30} : Finset (Fin 37)) := by decide
  rw [hZ]
  unfold dotProduct q37CompressedWord q37CompressionPivots
  simp only [mark, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  have hf (S : Finset (Fin 37)) :
      (Finset.univ : Finset (Fin 37)).filter (fun i => i ∈ S) = S := by
    ext i
    simp
  rw [hf,hf]
  have hadd (a : CSSBit) : a + a = 0 := by decide +revert
  simp [q37CompressionBits, Finset.sum_insert]
  calc
    _ = x 0 + x 7 + x 8 + (x 15 + x 15) + (x 16 + x 16) +
        (x 29 + x 29) + (x 30 + x 30) := by abel
    _ = _ := by simp [hadd, add_comm, add_left_comm, add_assoc]

theorem q37Compression_conjugates_logicalZ :
    q37CompressionGateOperator * pauliMatrix 0 (cssZWord q37LogicalZ) *
      star q37CompressionGateOperator = pauliMatrix 0 (cssZWord q37CompressedWord) := by
  let e : Equiv.Perm (QubitBasis 37) := binaryWordPermutation q37CompressionBitsEquiv
  let f (x : QubitBasis 37) := cssSign (dotProduct (binaryWordEquiv 37 x) q37LogicalZ)
  let g (x : QubitBasis 37) := cssSign (dotProduct (binaryWordEquiv 37 x) q37CompressedWord)
  have hE (x : QubitBasis 37) :
      binaryWordEquiv 37 (e.symm x) = q37CompressionBits (binaryWordEquiv 37 x) :=
    (binaryWordEquiv 37).apply_symm_apply _
  have hF : (fun x => f (e.symm x)) = g := by
    funext x
    change cssSign (dotProduct (binaryWordEquiv 37 (e.symm x)) q37LogicalZ) =
      cssSign (dotProduct (binaryWordEquiv 37 x) q37CompressedWord)
    rw [hE, q37Compression_dot]
  have hLeft : pauliMatrix 0 (cssZWord q37LogicalZ) = Matrix.diagonal f :=
    cssZMatrix_eq_diagonal q37LogicalZ
  have hRight : pauliMatrix 0 (cssZWord q37CompressedWord) = Matrix.diagonal g :=
    cssZMatrix_eq_diagonal q37CompressedWord
  calc
    _ = basisPermutation e * Matrix.diagonal f * (basisPermutation e).conjTranspose :=
      congrArg (fun M : Operator (QubitBasis 37) =>
        basisPermutation e * M * (basisPermutation e).conjTranspose) hLeft
    _ = Matrix.diagonal (fun x => f (e.symm x)) :=
      basisPermutation_conjugates_diagonal e f
    _ = Matrix.diagonal g := congrArg Matrix.diagonal hF
    _ = _ := hRight.symm

theorem q37CompressionLayer_conjugates_logicalZ :
    q37CompressionLayer.eval * pauliMatrix 0 (cssZWord q37LogicalZ) *
      star q37CompressionLayer.eval = pauliMatrix 0 (cssZWord q37CompressedWord) := by
  rw [q37CompressionLayer_eval]
  exact q37Compression_conjugates_logicalZ

private theorem q37CompressedWord_support :
    (pauliSupport (cssZWord q37CompressedWord)).card ≤ 3 := by decide

/-- The named layer, a single middle rotation and the adjoint of the
same named layer evaluate to the physical logical-Z rotation. -/
theorem q37Compression_rotation_circuit (t : ℝ) :
    ∃ layers : List (Layer 37 (fun _ => 2) 3),
      layers.length = 3 ∧
      layerSequenceEval layers = rotation (pauliMatrix 0 (cssZWord q37LogicalZ)) t := by
  have h := affine_synthesis_from_compression [q37CompressionLayer]
    (cssZWord q37LogicalZ) (cssZWord q37CompressedWord) (by decide)
    (by simpa only [layerSequenceEval, Matrix.one_mul]
      using q37CompressionLayer_conjugates_logicalZ)
    q37CompressedWord_support (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ))
    (rotation_isUnitary (unphased_pauliMatrix_selfAdjoint _) (unphased_pauliMatrix_sq _) t)
  simpa only [rotation, List.length_singleton] using h

#print axioms q37CompressionBlocks_disjoint
#print axioms q37CompressionLayer_eval
#print axioms q37Compression_dot
#print axioms q37Compression_conjugates_logicalZ
#print axioms q37Compression_rotation_circuit

end

end CriticalDepth.Q37BinaryData
