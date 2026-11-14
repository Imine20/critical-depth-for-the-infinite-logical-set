import BaconShorCoordinates
import ShorPhysicalCode

/-!
# The normalized Bacon--Shor subsystem encoding

A logical-and-gauge column is a uniform sum over its center-orbit
coordinate. The explicit word coordinates show that column supports
are pairwise disjoint and have equal cardinalities.
-/

namespace CriticalDepth.FaultShorSaturation.BaconShor

open CriticalDepth.Manuscript
open scoped BigOperators

noncomputable section

variable {m b : ℕ}

def orbitEmbedding (ℓ : Bit) (u : Interior m b) : CenterCoordinate b ↪ BaconMask m b :=
  ⟨fun t => baconWord ℓ u t, fun _ _ h => by
    simpa only [baconWord_topBits] using congrArg topBits h⟩

def orbitWords (ℓ : Bit) (u : Interior m b) : Finset (BaconMask m b) :=
  Finset.univ.map (orbitEmbedding ℓ u)

theorem orbitWords_mem (ℓ : Bit) (u : Interior m b) (x : BaconMask m b) :
    x ∈ orbitWords ℓ u ↔ ∃ t, baconWord ℓ u t = x := by
  unfold orbitWords
  constructor
  · intro hx
    obtain ⟨t, _, ht⟩ := Finset.mem_map.mp hx
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact Finset.mem_map.mpr ⟨t, Finset.mem_univ _, ht⟩

theorem orbitWords_unique (ℓ k : Bit) (u v : Interior m b) (x : BaconMask m b)
    (hx : x ∈ orbitWords ℓ u) (hy : x ∈ orbitWords k v) : ℓ = k ∧ u = v := by
  obtain ⟨t, ht⟩ := (orbitWords_mem ℓ u x).mp hx
  obtain ⟨s, hs⟩ := (orbitWords_mem k v x).mp hy
  have h := ht.trans hs.symm
  exact ⟨by simpa only [baconWord_rowParity] using
      congrArg (fun z => rowParity z 0) h,
    by simpa only [baconWord_gaugeBits] using congrArg gaugeBits h⟩

def orbitCount (b : ℕ) : ℕ := Fintype.card (CenterCoordinate b)

theorem orbitWords_card (ℓ : Bit) (u : Interior m b) : (orbitWords ℓ u).card = orbitCount b := by
  simp [orbitWords, orbitCount]

def orbitAmplitude (b : ℕ) : ℂ := (Real.sqrt ((orbitCount b : ℝ)⁻¹) : ℂ)

theorem orbitAmplitude_square (b : ℕ) :
    star (orbitAmplitude b) * orbitAmplitude b = (orbitCount b : ℂ)⁻¹ := by
  have hs : (Real.sqrt ((orbitCount b : ℝ)⁻¹)) ^ 2 =
      (orbitCount b : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hconj : star (orbitAmplitude b) = orbitAmplitude b := Complex.conj_ofReal _
  rw [hconj]
  simpa [pow_two, orbitAmplitude] using congrArg Complex.ofReal hs

def baconBinaryEncoding (m b : ℕ) : Matrix (BaconMask m b) (Bit × Interior m b) ℂ :=
  fun x a => if x ∈ orbitWords a.1 a.2 then orbitAmplitude b else 0

theorem baconBinaryEncoding_isometric :
    (baconBinaryEncoding m b).conjTranspose * baconBinaryEncoding m b = 1 := by
  classical
  ext a c
  change (∑ x : BaconMask m b, star (baconBinaryEncoding m b x a) * baconBinaryEncoding m b x c) =
    (1 : Matrix (Bit × Interior m b) (Bit × Interior m b) ℂ) a c
  by_cases h : a = c
  · subst c
    have hp (x : BaconMask m b) :
        star (baconBinaryEncoding m b x a) * baconBinaryEncoding m b x a =
          if x ∈ orbitWords a.1 a.2 then (orbitCount b : ℂ)⁻¹ else 0 := by
      by_cases hx : x ∈ orbitWords a.1 a.2
      · simpa only [baconBinaryEncoding, ite_eq_left hx] using orbitAmplitude_square b
      · simp [baconBinaryEncoding, hx]
    simp_rw [hp]
    rw [← Finset.sum_filter]
    have hf : (Finset.univ : Finset (BaconMask m b)).filter (fun x => x ∈ orbitWords a.1 a.2) =
        orbitWords a.1 a.2 := by ext; simp
    have hn : (orbitCount b : ℂ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (CenterCoordinate b)).ne'
    rw [hf, Finset.sum_const, nsmul_eq_mul, orbitWords_card, mul_inv_cancel₀ hn, Matrix.one_apply_eq]
  · have hp (x : BaconMask m b) :
        star (baconBinaryEncoding m b x a) * baconBinaryEncoding m b x c = 0 := by
      by_cases hx : x ∈ orbitWords a.1 a.2
      · have hy : x ∉ orbitWords c.1 c.2 := by
          intro hy
          obtain ⟨h₁, h₂⟩ := orbitWords_unique _ _ _ _ _ hx hy
          exact h (Prod.ext h₁ h₂)
        simp [baconBinaryEncoding, hy]
      · simp [baconBinaryEncoding, hx]
    simp_rw [hp]
    rw [Finset.sum_const_zero, Matrix.one_apply_ne h]

def gaugeTupleEquiv (m b : ℕ) : Fin (2 ^ (m * b)) ≃ Interior m b :=
  (finCongr (by simp [Interior, ← pow_mul, Nat.mul_comm])).trans
    (Fintype.equivFin _).symm

def baconPhysicalEncoding (m b : ℕ) :
    Matrix (QubitBasis ((m + 1) * (b + 1))) (Fin 2 × Fin (2 ^ (m * b))) ℂ :=
  fun x a => baconBinaryEncoding m b (shorBasisEquiv (m + 1) (b + 1) x)
    (qubitBitEquiv a.1, gaugeTupleEquiv m b a.2)

theorem baconPhysicalEncoding_isometric :
    (baconPhysicalEncoding m b).conjTranspose * baconPhysicalEncoding m b = 1 := by
  classical
  let e := Equiv.prodCongr qubitBitEquiv (gaugeTupleEquiv m b)
  ext a c
  let f (x : BaconMask m b) :=
    star (baconBinaryEncoding m b x (e a)) * baconBinaryEncoding m b x (e c)
  change (∑ x : QubitBasis ((m + 1) * (b + 1)), f (shorBasisEquiv (m + 1) (b + 1) x)) = _
  rw [(shorBasisEquiv (m + 1) (b + 1)).sum_comp f]
  change ((baconBinaryEncoding m b).conjTranspose * baconBinaryEncoding m b) (e a) (e c) = _
  rw [baconBinaryEncoding_isometric]
  by_cases h : a = c
  · subst c
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne (fun hh => h (e.injective hh)), Matrix.one_apply_ne h]

def baconShorCode (m b : ℕ) : Code ((m + 1) * (b + 1)) (fun _ => 2) 2 (2 ^ (m * b)) :=
  ⟨baconPhysicalEncoding m b, baconPhysicalEncoding_isometric⟩

#print axioms baconBinaryEncoding_isometric
#print axioms baconPhysicalEncoding_isometric
#print axioms baconShorCode

end

end CriticalDepth.FaultShorSaturation.BaconShor
