import StabilizerMinUnphased
import LogicalPauliOrbitBasis
import ConnectedPauliFrameSynthesis

/-!
# Generator depth for a selected minimum-weight stabilizer Pauli frame
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Matrix Relation
open scoped Kronecker ENat

noncomputable section

variable {n k : ℕ}

/-- The single-qubit X/Z directions and the ZZ directions of the chosen
logical graph. Edges with equal endpoints add no direction. -/
abbrev ConnectedFrameDirection (E : Fin k → Fin k → Prop) :=
  (Fin k ⊕ Fin k) ⊕ {ij : Fin k × Fin k // E ij.1 ij.2 ∧ ij.1 ≠ ij.2}

noncomputable instance connectedFrameDirectionFintype (E : Fin k → Fin k → Prop) :
    Fintype (ConnectedFrameDirection E) := Fintype.ofFinite _

def connectedFrameWord (E : Fin k → Fin k → Prop) :
    ConnectedFrameDirection E → Fin k → SinglePauli
  | .inl (.inl i) => singleSitePauli i .X
  | .inl (.inr i) => singleSitePauli i .Z
  | .inr ij => pairPauli ij.val.1 ij.val.2 .Z .Z

private theorem pauli_distinct_Z_product (i j : Fin k) (hij : i ≠ j) :
    pauliMatrix 0 (singleSitePauli i .Z) * pauliMatrix 0 (singleSitePauli j .Z) =
      pauliMatrix 0 (pairPauli i j .Z .Z) := by
  simp only [pauliMatrix_zero_eq_tensorEntries, ← tensorEntries_mul]
  congr 1
  funext l
  by_cases hi : l = i
  · subst l
    simp [singleSitePauli, pairPauli, hij, SinglePauli.matrix]
  · by_cases hj : l = j
    · subst l
      simp [singleSitePauli, pairPauli, hij.symm, SinglePauli.matrix]
    · simp [singleSitePauli, pairPauli, hi,hj, SinglePauli.matrix]

private theorem nonscalar_subspaceLogical_of_anticommute
    (A B : Operator (Fin (2^k))) (hA : A*A = 1) (hB : B*B = 1)
    (hab : A*B = -(B*A)) : ¬ IsScalar A := by
  rintro ⟨z,hz⟩
  rw [hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one] at hab
  have h := congrArg (fun M : Operator (Fin (2^k)) => M*B) hab
  rw [Matrix.neg_mul, Matrix.smul_mul, hB] at h
  let i : Fin (2^k) := ⟨0,by positivity⟩
  have he := congrArg (fun M : Operator (Fin (2^k)) => M i i) h
  have hz0 : z = 0 := by
    simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, mul_one] at he
    linear_combination (1/2 : ℂ) * he
  have hbad := congrArg (fun M : Operator (Fin (2^k)) => M i i) hA
  norm_num [hz,hz0,Matrix.one_apply_eq] at hbad

private theorem nonscalar_neg {A : Operator (Fin (2^k))} (ha : ¬ IsScalar A) :
    ¬ IsScalar (-A) := by
  rintro ⟨c,hc⟩
  exact ha ⟨-c, by simpa only [neg_neg, neg_smul] using congrArg Neg.neg hc⟩

variable (C : Code n (fun _ => 2) (2^k) 1)
variable {S : PhysicalStabilizer n}
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
  {v | ∀ U ∈ S, U.val.mulVec v = v})
variable (F : StabilizerPauliFrame S k)

private def compressedDirection {E : Fin k → Fin k → Prop} :
    ConnectedFrameDirection E → Operator (Fin (2^k))
  | .inl (.inl i) => F.logicalX C i
  | .inl (.inr i) => F.logicalZ C i
  | .inr ij => F.logicalZ C ij.val.1 * F.logicalZ C ij.val.2

include hspace in
private theorem compressedDirection_self {E : Fin k → Fin k → Prop}
    (a : ConnectedFrameDirection E) : star (compressedDirection C F a) = compressedDirection C F a := by
  rcases a with (i | i) | ⟨⟨i,j⟩,h⟩
  · exact F.xSelfAdjoint C i
  · exact F.zSelfAdjoint C i
  · simp only [compressedDirection, star_mul, F.zSelfAdjoint]
    exact (F.logicalZZ C hspace i j).symm

include hspace in
private theorem compressedDirection_square {E : Fin k → Fin k → Prop}
    (a : ConnectedFrameDirection E) : compressedDirection C F a * compressedDirection C F a = 1 := by
  rcases a with (i | i) | ⟨⟨i,j⟩,h⟩
  · exact F.xSquare C hspace i
  · exact F.zSquare C hspace i
  · let Z := F.logicalZ C i
    let W := F.logicalZ C j
    change (Z*W)*(Z*W) = 1
    calc
      _ = Z * (W*Z) * W := by simp only [mul_assoc]
      _ = Z * (Z*W) * W := by rw [show W*Z = Z*W from F.logicalZZ C hspace j i]
      _ = (Z*Z)*(W*W) := by simp only [mul_assoc]
      _ = 1 := by rw [show Z*Z = 1 from F.zSquare C hspace i,
        show W*W = 1 from F.zSquare C hspace j, one_mul]

include hspace in
private theorem compressedDirection_nonscalar {E : Fin k → Fin k → Prop}
    (a : ConnectedFrameDirection E) : ¬ IsScalar (compressedDirection C F a) := by
  let L := F.toLogicalPauliFrame C hspace
  rcases a with (i | i) | ⟨⟨i,j⟩,he,hij⟩
  · exact nonscalar_subspaceLogical_of_anticommute (F.logicalX C i) (F.logicalZ C i)
      (F.xSquare C hspace i) (F.zSquare C hspace i) (neg_eq_iff_eq_neg.mp (L.zx_same i).symm)
  · exact nonscalar_subspaceLogical_of_anticommute (F.logicalZ C i) (F.logicalX C i)
      (F.zSquare C hspace i) (F.xSquare C hspace i) (L.zx_same i)
  · apply nonscalar_subspaceLogical_of_anticommute _ (F.logicalX C i)
      (compressedDirection_square C hspace F (Sum.inr ⟨(i,j),he,hij⟩)) (F.xSquare C hspace i)
    change (L.Z i*L.Z j)*L.X i = -(L.X i*(L.Z i*L.Z j))
    rw [mul_assoc, (L.zx_other j i hij.symm).eq, ← mul_assoc, L.zx_same i, neg_mul, mul_assoc]

include hspace in
private theorem exists_physical_direction {E : Fin k → Fin k → Prop} (a : ConnectedFrameDirection E) :
    ∃ p : Fin n → SinglePauli,
      (∀ U ∈ S, U.val * pauliMatrix 0 p = pauliMatrix 0 p * U.val) ∧
      let A := compressedDirection C F a
      pauliMatrix 0 p * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1))) ∨
        pauliMatrix 0 p * C.encoding = C.encoding * ((-A) ⊗ₖ (1 : Operator (Fin 1))) := by
  rcases a with (i | i) | ⟨⟨i,j⟩,he,hij⟩
  · exact ⟨F.xWord i, F.xCentral i, Or.inl (F.xIntertwines C hspace i)⟩
  · exact ⟨F.zWord i, F.zCentral i, Or.inl (F.zIntertwines C hspace i)⟩
  · exact F.exists_zzWord C hspace i j

private theorem compressedDirection_conjugated {E : Fin k → Fin k → Prop}
    (e : QubitBasis k ≃ Fin (2^k)) (U : Matrix.unitaryGroup (Fin (2^k)) ℂ)
    (hX : ∀ i, F.logicalX C i = Unitary.conjStarAlgAut ℂ _ U
      (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (singleSitePauli i .X))))
    (hZ : ∀ i, F.logicalZ C i = Unitary.conjStarAlgAut ℂ _ U
      (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (singleSitePauli i .Z))))
    (a : ConnectedFrameDirection E) :
    compressedDirection C F a = Unitary.conjStarAlgAut ℂ _ U
      (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (connectedFrameWord E a))) := by
  rcases a with (i | i) | ⟨⟨i,j⟩,he,hij⟩
  · exact hX i
  · exact hZ i
  · change F.logicalZ C i * F.logicalZ C j = Unitary.conjStarAlgAut ℂ _ U
      (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (pairPauli i j .Z .Z)))
    rw [hZ i,hZ j, ← map_mul, ← map_mul, pauli_distinct_Z_product i j hij]

include hspace in
private theorem minimum_physical_direction (hS : ∀ U ∈ S, IsPauli U.val)
    {E : Fin k → Fin k → Prop} (a : ConnectedFrameDirection E) :
    ∃ p : PauliLabel n, ∃ r ∈ stabilizerCosetLabels S p,
      (∀ s ∈ stabilizerCosetLabels S p, (pauliSupport r.2).card ≤ (pauliSupport s.2).card) ∧
      let A := compressedDirection C F a
      pauliMatrix 0 r.2 * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1))) ∨
        pauliMatrix 0 r.2 * C.encoding = C.encoding * ((-A) ⊗ₖ (1 : Operator (Fin 1))) := by
  obtain ⟨p,hcomm,hint⟩ := exists_physical_direction C hspace F a
  let A := compressedDirection C F a
  change pauliMatrix 0 p * C.encoding = C.encoding * (A ⊗ₖ (1 : Operator (Fin 1))) ∨
      pauliMatrix 0 p * C.encoding = C.encoding * ((-A) ⊗ₖ (1 : Operator (Fin 1))) at hint
  rcases hint with h | h
  · obtain ⟨r,hr,hmin,he⟩ := exists_min_unphased_stabilizer_rep C S hS hspace p A hcomm h
    exact ⟨(0,p),r,hr,hmin,he⟩
  · obtain ⟨r,hr,hmin,he⟩ := exists_min_unphased_stabilizer_rep C S hS hspace p (-A) hcomm h
    exact ⟨(0,p),r,hr,hmin,by simpa only [neg_neg, or_comm] using he⟩

/-- For the chosen connected logical graph, there are minimum-weight
physical representatives with the exact generator-depth upper bound.
Their supports are minimized individually in the chosen stabilizer cosets.
The chosen logical basis identifies every selected direction up to sign. -/
theorem exists_stabilizer_connectedFrame_minimum_depth_with_basis {d : ℕ}
    (hk : 1 ≤ k) (hd : 2 ≤ d) (q : ℕ) (hq : 2 ≤ q)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j) :
    ∃ S : PhysicalStabilizer n, (∀ V ∈ S, IsPauli V.val) ∧
      Set.range (fun v => C.encoding.mulVec v) = {v | ∀ V ∈ S, V.val.mulVec v = v} ∧
      ∃ F0 : StabilizerPauliFrame S k,
      ∃ F : PauliRotationFamily C (ConnectedFrameDirection E),
      ∃ p : ConnectedFrameDirection E → PauliLabel n,
      ∃ r : ConnectedFrameDirection E → PauliLabel n,
        (∀ a, r a ∈ stabilizerCosetLabels S (p a)) ∧
        (∀ a, F.physical a = (r a).2) ∧
        (∀ a s, s ∈ stabilizerCosetLabels S (p a) →
          (pauliSupport (F.physical a)).card ≤ (pauliSupport s.2).card) ∧
        (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q ∧
        nativeExactDepth C.encoding q ≤ (Arithmetic.criticalDepth q F.maxWeight : ℕ∞) ∧
        Arithmetic.criticalDepth q F.maxWeight ≤ Arithmetic.criticalDepth q n ∧
        ∃ (e : QubitBasis k ≃ Fin (2^k)) (U : Matrix.unitaryGroup (Fin (2^k)) ℂ),
          ∀ a,
            let R := Unitary.conjStarAlgAut ℂ _ U
              (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (connectedFrameWord E a)))
            F.logical a = R ∨ F.logical a = -R := by
  classical
  letI : Nonempty (ConnectedFrameDirection E) := ⟨Sum.inl (Sum.inl ⟨0,by omega⟩)⟩
  obtain ⟨S,hS,hspace,⟨F0⟩⟩ := exists_stabilizerPauliFrame C hstab
  let L := F0.toLogicalPauliFrame C hspace
  let e : QubitBasis k ≃ Fin (2^k) :=
    Fintype.equivOfCardEq (by simp [QubitBasis, Fintype.card_fun])
  obtain ⟨U,hX,hZ⟩ := L.exists_unitary_tensor_basis e
  let A := compressedDirection C F0 (E := E)
  have hsign (a : ConnectedFrameDirection E) :
      ∃ p : PauliLabel n, ∃ r ∈ stabilizerCosetLabels S p,
        (∀ s ∈ stabilizerCosetLabels S p, (pauliSupport r.2).card ≤ (pauliSupport s.2).card) ∧
        (pauliMatrix 0 r.2 * C.encoding = C.encoding * (A a ⊗ₖ (1 : Operator (Fin 1))) ∨
         pauliMatrix 0 r.2 * C.encoding = C.encoding * ((-A a) ⊗ₖ (1 : Operator (Fin 1)))) :=
    minimum_physical_direction C hspace F0 hS a
  choose p r hr hm he using hsign
  let positive (a : ConnectedFrameDirection E) :=
    pauliMatrix 0 (r a).2 * C.encoding = C.encoding * (A a ⊗ₖ (1 : Operator (Fin 1)))
  let Q (a : ConnectedFrameDirection E) := if positive a then A a else -A a
  let F : PauliRotationFamily C (ConnectedFrameDirection E) :=
    { physical := fun a => (r a).2
      logical := Q
      encoded := fun a => by
        by_cases h : positive a
        · simpa only [Q, ite_eq_left h] using h
        · simpa only [Q, ite_eq_right h] using (he a).resolve_left h
      selfAdjoint := fun a => by
        have h : star (A a) = A a := compressedDirection_self C hspace F0 a
        by_cases hb : positive a <;> simp [Q,hb,h,star_neg]
      squareOne := fun a => by
        have h : A a * A a = 1 := compressedDirection_square C hspace F0 a
        by_cases hb : positive a <;> simp [Q,hb,h,neg_mul_neg] }
  have hF (a : ConnectedFrameDirection E) : ¬ IsScalar (F.logical a) := by
    have h := compressedDirection_nonscalar C hspace F0 a
    by_cases hb : positive a
    · simpa only [F,Q,ite_eq_left hb] using h
    · simpa only [F,Q,ite_eq_right hb] using nonscalar_neg h
  have hC (a : ConnectedFrameDirection E) :
      let R := Unitary.conjStarAlgAut ℂ _ U
        (reindexAlgEquiv ℂ ℂ e (pauliMatrix 0 (connectedFrameWord E a)))
      F.logical a = R ∨ F.logical a = -R := by
    have h := compressedDirection_conjugated C F0 e U hX hZ a
    by_cases hb : positive a
    · exact Or.inl (by simpa only [F,Q,ite_eq_left hb] using h)
    · exact Or.inr (by simpa only [F,Q,ite_eq_right hb] using congrArg Neg.neg h)
  have hDepth := exact_generator_depth_bounds_of_connectedPauliFrame C hk hd q hq hstab hdist F hF
    e U E hConnected
    (fun i => ⟨Sum.inl (Sum.inl i),hC _⟩)
    (fun i => ⟨Sum.inl (Sum.inr i),hC _⟩)
    (fun i j hij hne => ⟨Sum.inr ⟨(i,j),hij,hne⟩,hC _⟩)
  exact ⟨S,hS,hspace,F0,F,p,r,hr,fun _ => rfl,hm,hDepth.1,hDepth.2.1,hDepth.2.2,e,U,hC⟩

/-- Minimum-weight physical representatives and their generator-depth bounds. -/
theorem exists_stabilizer_connectedFrame_minimum_depth {d : ℕ}
    (hk : 1 ≤ k) (hd : 2 ≤ d) (q : ℕ) (hq : 2 ≤ q)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j) :
    ∃ S : PhysicalStabilizer n, (∀ V ∈ S, IsPauli V.val) ∧
      Set.range (fun v => C.encoding.mulVec v) = {v | ∀ V ∈ S, V.val.mulVec v = v} ∧
      ∃ F0 : StabilizerPauliFrame S k,
      ∃ F : PauliRotationFamily C (ConnectedFrameDirection E),
      ∃ p : ConnectedFrameDirection E → PauliLabel n,
      ∃ r : ConnectedFrameDirection E → PauliLabel n,
        (∀ a, r a ∈ stabilizerCosetLabels S (p a)) ∧
        (∀ a, F.physical a = (r a).2) ∧
        (∀ a s, s ∈ stabilizerCosetLabels S (p a) →
          (pauliSupport (F.physical a)).card ≤ (pauliSupport s.2).card) ∧
        (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q ∧
        nativeExactDepth C.encoding q ≤ (Arithmetic.criticalDepth q F.maxWeight : ℕ∞) ∧
        Arithmetic.criticalDepth q F.maxWeight ≤ Arithmetic.criticalDepth q n := by
  obtain ⟨S,hS,hspace,F0,F,p,r,hr,hphys,hm,hlo,hup,hn,_⟩ :=
    exists_stabilizer_connectedFrame_minimum_depth_with_basis C hk hd q hq hstab hdist E hConnected
  exact ⟨S,hS,hspace,F0,F,p,r,hr,hphys,hm,hlo,hup,hn⟩

#print axioms exists_stabilizer_connectedFrame_minimum_depth_with_basis
#print axioms exists_stabilizer_connectedFrame_minimum_depth

end

end CriticalDepth.Manuscript20261114
