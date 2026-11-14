import BinaryPauliMasks
import FaultStabilizerLogicalBasis

/-!
# Symplectic frame of a physical stabilizer code

The phase-free stabilizer masks form an isotropic subspace. A complement
inside the binary normalizer represents its logical quotient and inherits
a nondegenerate commutator pairing.
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.PauliGroup CriticalDepth.ReviewV2
open CriticalDepth.FaultStabilizerLogicalTrace CriticalDepth.FaultStabilizerLogicalBasis
open CriticalDepth.FaultStabilizerSyndrome CriticalDepth.FaultStabilizerTrace
open Matrix LinearMap Module

noncomputable section

variable {n k : ℕ}

abbrev PhysicalStabilizer (n : ℕ) := Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ)

def stabilizerMasks (S : PhysicalStabilizer n)
    (hS : ∀ U ∈ S, IsPauli U.val) : Submodule PauliBit (PauliMask n) where
  carrier := {w | ∃ U ∈ S, ∃ (phase : Fin 4) (p : Fin n → SinglePauli),
    U.val = pauliMatrix phase p ∧ wordToMask p = w}
  zero_mem' := by
    let p₀ : Fin n → SinglePauli := fun _ => .I
    have h₀ : pauliMatrix 0 p₀ = 1 := by
      rw [pauliMatrix_zero_eq_tensorEntries]
      exact tensorEntries_one (R := ℂ) (α := fun _ : Fin n => Fin 2)
    exact ⟨1, S.one_mem, 0, p₀, h₀.symm, rfl⟩
  add_mem' := by
    rintro a b ⟨U,hU,s,p,hUp,hpa⟩ ⟨V,hV,t,q,hVq,hqb⟩
    obtain ⟨c,r,hr⟩ := hS (U*V) (S.mul_mem hU hV)
    have hpq : pauliMatrix s p * pauliMatrix t q = pauliMatrix c r := by
      change U.val * V.val = _ at hr
      simpa only [hUp,hVq] using hr
    exact ⟨U*V, S.mul_mem hU hV, c, r, hr,
      (wordToMask_of_pauli_product _ _ _ _ _ _ hpq).trans (congrArg₂ (· + ·) hpa hqb)⟩
  smul_mem' := by
    intro c a ha
    have hc : c = 0 ∨ c = 1 := by decide +revert
    rcases hc with rfl | rfl
    · rw [zero_smul]
      let p₀ : Fin n → SinglePauli := fun _ => .I
      have h₀ : pauliMatrix 0 p₀ = 1 := by
        rw [pauliMatrix_zero_eq_tensorEntries]
        exact tensorEntries_one (R := ℂ) (α := fun _ : Fin n => Fin 2)
      exact ⟨1, S.one_mem, 0, p₀, h₀.symm, rfl⟩
    · simpa using ha

variable (C : Code n (fun _ => 2) (2 ^ k) 1)
variable (S : PhysicalStabilizer n)
variable (hS : ∀ U ∈ S, IsPauli U.val)
variable (hspace : Set.range (fun v => C.encoding.mulVec v) =
  {v | ∀ U ∈ S, U.val.mulVec v = v})

include C hS hspace in
private theorem stabilizerOperators_commute (U V : Matrix.unitaryGroup (QubitBasis n) ℂ)
    (hU : U ∈ S) (hV : V ∈ S) : U.val * V.val = V.val * U.val := by
  obtain ⟨a,p,hp⟩ := hS U hU
  obtain ⟨b,q,hq⟩ := hS V hV
  have hUp := encoding_fixed_of_fixedSpace C S hspace U hU
  have hVq := encoding_fixed_of_fixedSpace C S hspace V hV
  rcases pauliMatrix_commute_or_anticommute a b p q with h | h
  · simpa only [← hp,← hq] using h
  · have hr : U.val * V.val = -(V.val * U.val) := by simpa only [← hp,← hq] using h
    have hz := congrArg (fun A : Operator (QubitBasis n) => A * C.encoding) hr
    change (U.val * V.val) * C.encoding = -(V.val * U.val) * C.encoding at hz
    simp only [Matrix.neg_mul, Matrix.mul_assoc, hUp, hVq] at hz
    have he := congrArg (fun V => C.encoding.conjTranspose * V) hz
    simp only [Matrix.mul_neg, C.isometry] at he
    let i : Fin (2^k) × Fin 1 := (⟨0, by positivity⟩,0)
    have hbad := congrArg (fun M : Operator (Fin (2^k) × Fin 1) => M i i) he
    norm_num [Matrix.one_apply_eq, Matrix.neg_apply] at hbad

include C hS hspace in
theorem stabilizerMasks_isotropic :
    stabilizerMasks S hS ≤ (pauliMaskForm n).orthogonal (stabilizerMasks S hS) := by
  rintro x ⟨U,hU,a,p,hp,rfl⟩ y ⟨V,hV,b,q,hq,rfl⟩
  apply (pauliMatrix_commute_iff_maskForm_zero b a q p).mp
  simpa only [hq,hp] using stabilizerOperators_commute C S hS hspace V U hV hU

private theorem orthogonal_mask_iff (phase : Fin 4) (p : Fin n → SinglePauli) :
    wordToMask p ∈ (pauliMaskForm n).orthogonal (stabilizerMasks S hS) ↔
      ∀ U ∈ S, U.val * pauliMatrix phase p = pauliMatrix phase p * U.val := by
  constructor
  · intro h U hU
    obtain ⟨a,q,ha⟩ := hS U hU
    rw [ha, pauliMatrix_commute_iff_maskForm_zero]
    exact h _ ⟨U,hU,a,q,ha,rfl⟩
  · rintro h _ ⟨U,hU,a,q,ha,rfl⟩
    apply (pauliMatrix_commute_iff_maskForm_zero a phase q p).mp
    simpa only [ha] using h U hU

private def logicalMaskClass
    (x : (pauliMaskForm n).orthogonal (stabilizerMasks S hS)) : LogicalClass C S :=
  let p := maskToWord x.val
  let U : Matrix.unitaryGroup (QubitBasis n) ℂ := ⟨pauliMatrix 0 p, pauliMatrix_isUnitary 0 p⟩
  let P : CentralPauli S := ⟨⟨U, 0, p, rfl⟩,
    (orthogonal_mask_iff S hS 0 p).mp (by simpa only [p, wordToMask_maskToWord] using x.property)⟩
  Quotient.mk (logicalPauliSetoid C S) P

private theorem compress_phase_equiv (a : Fin 4) (p : Fin n → SinglePauli) :
    ProjectivelyEquivalent (compress C (pauliMatrix a p)) (compress C (pauliMatrix 0 p)) := by
  refine ⟨Complex.I ^ a.val, i_pow_unit_modulus a.val, ?_⟩
  rw [pauliMatrix_eq_phase_smul]
  exact (compressLinear C).map_smul _ _

variable (W : Submodule PauliBit ((pauliMaskForm n).orthogonal (stabilizerMasks S hS)))

include C hS hspace in
private theorem logicalMaskClass_surjective
    (hW : IsCompl ((stabilizerMasks S hS).comap
      ((pauliMaskForm n).orthogonal (stabilizerMasks S hS)).subtype) W) :
    Function.Surjective (fun x : W => logicalMaskClass C S hS x.val) := by
  intro c
  obtain ⟨P,rfl⟩ := Quotient.mk_surjective c
  obtain ⟨a,p,hp⟩ := P.val.property
  have hnorm : wordToMask p ∈ (pauliMaskForm n).orthogonal (stabilizerMasks S hS) := by
    apply (orthogonal_mask_iff S hS a p).mpr
    simpa only [← hp] using P.property
  let x : (pauliMaskForm n).orthogonal (stabilizerMasks S hS) := ⟨wordToMask p,hnorm⟩
  obtain ⟨y,z,hy,hz,hadd⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint x
  have hy' : y.val ∈ stabilizerMasks S hS := hy
  obtain ⟨U,hU,b,q,hUq,hq⟩ := hy'
  let pz := maskToWord z.val
  let s := pauliMatrix 0 pz
  obtain ⟨r,t,hrt⟩ := isPauli_mul (hS U hU) (show IsPauli s from ⟨0,pz,rfl⟩)
  have htt : pauliMatrix b q * pauliMatrix 0 pz = pauliMatrix r t := by
    simpa only [hUq,s] using hrt
  have ht := wordToMask_of_pauli_product _ _ _ _ _ _ htt
  have hwp : wordToMask p = wordToMask t := by
    have h := congrArg Subtype.val hadd
    change y.val + z.val = wordToMask p at h
    rw [ht,hq,show wordToMask pz = z.val from wordToMask_maskToWord _]
    exact h.symm
  have hpt : p = t := by
    simpa only [maskToWord_wordToMask] using congrArg maskToWord hwp
  refine ⟨⟨z,hz⟩, ?_⟩
  apply Quotient.sound
  change ProjectivelyEquivalent (compress C s) (compress C P.val.val.val)
  have hf := encoding_adjoint_fixed_of_fixed C U.val U.property
    (encoding_fixed_of_fixedSpace C S hspace U hU)
  have hcs : compress C (pauliMatrix r t) = compress C s := by
    rw [← hrt, compress, ← Matrix.mul_assoc C.encoding.conjTranspose U.val, hf]
    rfl
  have h₁ : ProjectivelyEquivalent (compress C s) (compress C (pauliMatrix 0 p)) := by
    rw [hpt, ← hcs]
    exact compress_phase_equiv C r t
  rw [hp]
  exact projectivelyEquivalent_trans h₁ (projectivelyEquivalent_symm (compress_phase_equiv C a p))

include C hS hspace in
private theorem logicalMaskComplement_finrank
    (hW : IsCompl ((stabilizerMasks S hS).comap
      ((pauliMaskForm n).orthogonal (stabilizerMasks S hS)).subtype) W) :
    2 * k ≤ finrank PauliBit W := by
  classical
  letI := Fintype.ofFinite W
  have hl : Fintype.card (LogicalClass C S) = (2 ^ k) * (2 ^ k) := by
    rw [← Module.finrank_eq_card_basis (logicalPauliBasis C S hS hspace)]
    simp [Module.finrank_matrix]
  have hw : Fintype.card W = 2 ^ finrank PauliBit W := by
    letI : Module.Free PauliBit W := Module.Free.of_divisionRing PauliBit W
    letI : Module.Finite PauliBit W := Module.Finite.of_finite
    let e := (Module.finBasis PauliBit W).equivFun
    rw [Fintype.card_congr e.toEquiv]
    simp [PauliBit, Fintype.card_fun]
  have h := Fintype.card_le_of_surjective _
    (logicalMaskClass_surjective C S hS hspace W hW)
  rw [hl,hw,← pow_add] at h
  have hk' := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp h
  omega

/-- A physical logical Pauli frame centralizes the stabilizer and has
the standard commutator sign on each pair of encoded axes. -/
structure StabilizerPauliFrame (S : PhysicalStabilizer n) (k : ℕ) where
  xWord : Fin k → Fin n → SinglePauli
  zWord : Fin k → Fin n → SinglePauli
  xCentral : ∀ i (U : Matrix.unitaryGroup (QubitBasis n) ℂ), U ∈ S →
    U.val * pauliMatrix 0 (xWord i) = pauliMatrix 0 (xWord i) * U.val
  zCentral : ∀ i (U : Matrix.unitaryGroup (QubitBasis n) ℂ), U ∈ S →
    U.val * pauliMatrix 0 (zWord i) = pauliMatrix 0 (zWord i) * U.val
  xx : ∀ i j, pauliMatrix 0 (xWord i) * pauliMatrix 0 (xWord j) =
    pauliMatrix 0 (xWord j) * pauliMatrix 0 (xWord i)
  zz : ∀ i j, pauliMatrix 0 (zWord i) * pauliMatrix 0 (zWord j) =
    pauliMatrix 0 (zWord j) * pauliMatrix 0 (zWord i)
  xz : ∀ i j, pauliMatrix 0 (xWord i) * pauliMatrix 0 (zWord j) =
    (if i = j then (-1 : ℂ) else 1) • (pauliMatrix 0 (zWord j) * pauliMatrix 0 (xWord i))

include C hS hspace in
theorem stabilizerPauliFrame_nonempty : Nonempty (StabilizerPauliFrame S k) := by
  classical
  let B := pauliMaskForm n
  let M := stabilizerMasks S hS
  let N := B.orthogonal M
  obtain ⟨W,hW⟩ := Submodule.exists_isCompl (M.comap N.subtype)
  let E := (B.restrict N).restrict W
  have hBsymm := pauliMaskForm_symmetric (n := n)
  have hBa := pauliMaskForm_isAlt n
  have hEalt : E.IsAlt := fun u => hBa.self_eq_zero u.val.val
  have hEnondeg : E.Nondegenerate := by
    have hLeft : E.SeparatingLeft := by
      intro x hx
      let u : N := x.val
      have hzero : ∀ y ∈ N, B y u.val = 0 := by
        intro y hy
        obtain ⟨a,b,ha,hb,hadd⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint
          (⟨y,hy⟩ : N)
        have he := congrArg Subtype.val hadd
        change a.val + b.val = y at he
        rw [← he, map_add, LinearMap.add_apply]
        have hapa : a.val ∈ M := ha
        have h₁ : B a.val u.val = 0 := u.property _ hapa
        have h₂ : B b.val u.val = 0 :=
          (hBsymm b.val u.val).trans (hx ⟨b,hb⟩)
        rw [h₁,h₂,zero_add]
      have hu : u.val ∈ M := by
        have hm : u.val ∈ B.orthogonal N := hzero
        have he : B.orthogonal N = M :=
          LinearMap.BilinForm.orthogonal_orthogonal (pauliMaskForm_nondegenerate n) hBa.isRefl M
        exact he ▸ hm
      have hu' : u ∈ M.comap N.subtype := hu
      exact Subtype.ext (Submodule.disjoint_def.mp hW.disjoint u hu' x.property)
    refine ⟨hLeft, fun x hx => hLeft x ?_⟩
    intro y
    change B x.val.val y.val.val = 0
    rw [hBsymm]
    exact hx y
  have hEnondeg' : LinearMap.BilinForm.Nondegenerate E := hEnondeg
  have hWdim : 2 * k ≤ finrank PauliBit W := logicalMaskComplement_finrank C S hS hspace W hW
  letI : FiniteDimensional PauliBit W := Module.Finite.of_finite
  obtain ⟨F⟩ := binarySymplecticFrame_nonempty k (V := W) E hEalt hEnondeg' hWdim
  let x (i : Fin k) : PauliMask n := (F.X i).val.val
  let z (i : Fin k) : PauliMask n := (F.Z i).val.val
  have hX (i) : wordToMask (maskToWord (x i)) = x i := wordToMask_maskToWord _
  have hZ (i) : wordToMask (maskToWord (z i)) = z i := wordToMask_maskToWord _
  refine ⟨⟨fun i => maskToWord (x i), fun i => maskToWord (z i), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i
    apply (orthogonal_mask_iff S hS 0 _).mp
    rw [hX]
    exact (F.X i).val.property
  · intro i
    apply (orthogonal_mask_iff S hS 0 _).mp
    rw [hZ]
    exact (F.Z i).val.property
  · intro i j
    apply (pauliMatrix_commute_iff_maskForm_zero _ _ _ _).mpr
    rw [hX,hX]
    exact F.xPair i j
  · intro i j
    apply (pauliMatrix_commute_iff_maskForm_zero _ _ _ _).mpr
    rw [hZ,hZ]
    exact F.zPair i j
  · intro i j
    rw [pauliMatrix_mask_commutator, hX,hZ,
      show B (x i) (z j) = if i = j then 1 else 0 from F.crossPair i j]
    by_cases h : i = j <;> simp [h, pauliBitSign]

theorem exists_stabilizerPauliFrame (h : IsStabilizer C) :
    ∃ S : PhysicalStabilizer n, (∀ U ∈ S, IsPauli U.val) ∧
      Set.range (fun v => C.encoding.mulVec v) = {v | ∀ U ∈ S, U.val.mulVec v = v} ∧
      Nonempty (StabilizerPauliFrame S k) := by
  obtain ⟨S,hS,hspace⟩ := h
  exact ⟨S,hS,hspace,stabilizerPauliFrame_nonempty C S hS hspace⟩

#print axioms stabilizerMasks_isotropic
#print axioms exists_stabilizerPauliFrame

end

end CriticalDepth.Manuscript20261114
