import BinarySymplecticElimination
import PauliGroup

/-!
# Binary physical Pauli masks and their commutator form
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.PauliGroup Matrix
open scoped BigOperators

variable {n : ℕ}

abbrev PauliMask (n : ℕ) := (Fin n → PauliBit) × (Fin n → PauliBit)

def pauliToBits : SinglePauli → PauliBit × PauliBit
  | .I => (0,0)
  | .X => (1,0)
  | .Y => (1,1)
  | .Z => (0,1)

def bitsToPauli (a : PauliBit × PauliBit) : SinglePauli :=
  if a.1 = 0 then (if a.2 = 0 then .I else .Z) else (if a.2 = 0 then .X else .Y)

theorem pauliToBits_bitsToPauli (a : PauliBit × PauliBit) :
    pauliToBits (bitsToPauli a) = a := by decide +revert

theorem bitsToPauli_pauliToBits (p : SinglePauli) :
    bitsToPauli (pauliToBits p) = p := by decide +revert

def wordToMask (p : Fin n → SinglePauli) : PauliMask n :=
  (fun i => (pauliToBits (p i)).1, fun i => (pauliToBits (p i)).2)

def maskToWord (u : PauliMask n) : Fin n → SinglePauli :=
  fun i => bitsToPauli (u.1 i,u.2 i)

theorem wordToMask_maskToWord (u : PauliMask n) :
    wordToMask (maskToWord u) = u := by
  apply Prod.ext <;> funext i
  · exact congrArg Prod.fst (pauliToBits_bitsToPauli (u.1 i,u.2 i))
  · exact congrArg Prod.snd (pauliToBits_bitsToPauli (u.1 i,u.2 i))

theorem maskToWord_wordToMask (p : Fin n → SinglePauli) :
    maskToWord (wordToMask p) = p := by
  funext i
  exact bitsToPauli_pauliToBits (p i)

def pauliMaskForm (n : ℕ) : LinearMap.BilinForm PauliBit (PauliMask n) where
  toFun u :=
    { toFun := fun v => ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)
      map_add' v w := by
        change (∑ i, (u.1 i * (v.2 i + w.2 i) + u.2 i * (v.1 i + w.1 i))) =
          (∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)) + ∑ i, (u.1 i * w.2 i + u.2 i * w.1 i)
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      map_smul' r v := by
        change (∑ i, (u.1 i * (r * v.2 i) + u.2 i * (r * v.1 i))) =
          r * ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' u v := by
    apply LinearMap.ext; intro w
    change (∑ i, ((u.1 i + v.1 i) * w.2 i + (u.2 i + v.2 i) * w.1 i)) =
      (∑ i, (u.1 i * w.2 i + u.2 i * w.1 i)) + ∑ i, (v.1 i * w.2 i + v.2 i * w.1 i)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' r u := by
    apply LinearMap.ext; intro v
    change (∑ i, ((r * u.1 i) * v.2 i + (r * u.2 i) * v.1 i)) =
      r * ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem mask_pair_apply (u v : PauliMask n) :
    pauliMaskForm n u v = ∑ i, (u.1 i * v.2 i + u.2 i * v.1 i) := rfl

theorem pauliMaskForm_symmetric (u v : PauliMask n) :
    pauliMaskForm n u v = pauliMaskForm n v u := by
  rw [mask_pair_apply, mask_pair_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pauliMaskForm_isAlt (n : ℕ) : (pauliMaskForm n).IsAlt := by
  intro u
  rw [mask_pair_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [mul_comm (u.2 i), ← two_mul, show (2 : PauliBit) = 0 from by decide, zero_mul]

theorem pauliMaskForm_nondegenerate (n : ℕ) : (pauliMaskForm n).Nondegenerate := by
  classical
  have hleft : (pauliMaskForm n).SeparatingLeft := by
    intro u hu
    apply Prod.ext
    · funext i
      have h := hu (0, Pi.single i 1)
      simpa [mask_pair_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
    · funext i
      have h := hu (Pi.single i 1, 0)
      simpa [mask_pair_apply, Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
  refine ⟨hleft, fun v hv => hleft v ?_⟩
  intro u
  rw [pauliMaskForm_symmetric]
  exact hv u

def pauliBitSign (s : PauliBit) : ℂ := if s = 0 then 1 else -1

private theorem pauliBitSign_add (s t : PauliBit) :
    pauliBitSign (s+t) = pauliBitSign s * pauliBitSign t := by
  have h (x : PauliBit) : x = 0 ∨ x = 1 := by decide +revert
  have ht : (1 : PauliBit) + 1 = 0 := by decide
  rcases h s with rfl | rfl <;> rcases h t with rfl | rfl <;>
    simp [pauliBitSign, ht]

private theorem pauliBitSign_sum {ι : Type*} (S : Finset ι) (f : ι → PauliBit) :
    pauliBitSign (∑ i ∈ S, f i) = ∏ i ∈ S, pauliBitSign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [pauliBitSign]
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, pauliBitSign_add, ih]

private theorem singlePauli_sign_bits (p q : SinglePauli) :
    p.commutationSign q = pauliBitSign
      ((pauliToBits p).1 * (pauliToBits q).2 + (pauliToBits p).2 * (pauliToBits q).1) := by
  have h : (1 : PauliBit) + 1 = 0 := by decide
  cases p <;> cases q <;> simp [SinglePauli.commutationSign, pauliToBits, pauliBitSign, h]

theorem pauliMatrix_mask_commutator (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q =
      pauliBitSign (pauliMaskForm n (wordToMask p) (wordToMask q)) •
        (pauliMatrix b q * pauliMatrix a p) := by
  rw [mask_pair_apply, pauliBitSign_sum, pauliMatrix_commutation]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact singlePauli_sign_bits _ _

private theorem pauliBitSign_injective : Function.Injective pauliBitSign := by
  intro s t h
  have h01 (x : PauliBit) : x = 0 ∨ x = 1 := by decide +revert
  rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl <;>
    first | rfl | norm_num [pauliBitSign] at h

private theorem pauli_sign_unique {A : Operator (QubitBasis n)}
    (hA : IsUnitary A) {s t : PauliBit} (h : pauliBitSign s • A = pauliBitSign t • A) :
    s = t := by
  apply pauliBitSign_injective
  have he := congrArg (fun M : Operator (QubitBasis n) => M * A.conjTranspose) h
  rw [Matrix.smul_mul, Matrix.smul_mul, show A * A.conjTranspose = 1 from hA.2] at he
  let x : QubitBasis n := fun _ => 0
  have hx := congrArg (fun M : Operator (QubitBasis n) => M x x) he
  simpa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul] using hx

theorem pauliMatrix_commute_iff_maskForm_zero (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q = pauliMatrix b q * pauliMatrix a p ↔
      pauliMaskForm n (wordToMask p) (wordToMask q) = 0 := by
  rw [pauliMatrix_mask_commutator a b p q]
  constructor
  · intro h
    apply pauli_sign_unique (unitary_mul (pauliMatrix_isUnitary b q) (pauliMatrix_isUnitary a p))
    simpa [pauliBitSign] using h
  · intro h
    simp [h, pauliBitSign]

theorem wordToMask_of_pauli_product (a b c : Fin 4) (p q r : Fin n → SinglePauli)
    (h : pauliMatrix a p * pauliMatrix b q = pauliMatrix c r) :
    wordToMask r = wordToMask p + wordToMask q := by
  apply sub_eq_zero.mp
  apply (pauliMaskForm_nondegenerate n).1
  intro v
  let w := maskToWord v
  let P := pauliMatrix a p
  let Q := pauliMatrix b q
  let R := pauliMatrix c r
  let W := pauliMatrix 0 w
  have hw : wordToMask w = v := wordToMask_maskToWord v
  have hp : P * W = pauliBitSign (pauliMaskForm n (wordToMask p) v) • (W * P) := by
    simpa [P,W,hw] using pauliMatrix_mask_commutator a 0 p w
  have hq : Q * W = pauliBitSign (pauliMaskForm n (wordToMask q) v) • (W * Q) := by
    simpa [Q,W,hw] using pauliMatrix_mask_commutator b 0 q w
  have hr : R * W = pauliBitSign (pauliMaskForm n (wordToMask r) v) • (W * R) := by
    simpa [R,W,hw] using pauliMatrix_mask_commutator c 0 r w
  have he : (P * Q) * W =
      pauliBitSign (pauliMaskForm n (wordToMask p + wordToMask q) v) • (W * (P * Q)) := by
    have ha : pauliMaskForm n (wordToMask p + wordToMask q) v =
        pauliMaskForm n (wordToMask p) v + pauliMaskForm n (wordToMask q) v := by
      rw [map_add, LinearMap.add_apply]
    rw [Matrix.mul_assoc, hq, Matrix.mul_smul, ← Matrix.mul_assoc P W Q, hp,
      Matrix.smul_mul, smul_smul, Matrix.mul_assoc, ha,
      pauliBitSign_add, mul_comm (pauliBitSign (pauliMaskForm n (wordToMask q) v))]
  change P * Q = R at h
  rw [h, hr] at he
  have hm := pauli_sign_unique (unitary_mul (pauliMatrix_isUnitary 0 w) (pauliMatrix_isUnitary c r)) he
  change pauliMaskForm n (wordToMask r - (wordToMask p + wordToMask q)) v = 0
  rw [map_sub, LinearMap.sub_apply, hm, sub_self]

#print axioms pauliMaskForm_nondegenerate
#print axioms pauliMatrix_commute_iff_maskForm_zero
#print axioms wordToMask_of_pauli_product

end CriticalDepth.Manuscript20261114
