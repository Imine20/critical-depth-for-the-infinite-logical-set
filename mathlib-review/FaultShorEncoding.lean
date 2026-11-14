import FaultShorSaturation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Isometric encoding of the binary rectangular Shor code

The two columns are normalized uniform superpositions of strings with
common even parity and common odd parity, respectively. Construction uses
a single pivot column to enumerate each parity coset without duplicates.
-/

open scoped BigOperators

namespace CriticalDepth.FaultShorSaturation

variable {rows columns : ℕ}

/-- Computational bit strings with one freely chosen bit for each nonpivot
column. The pivot bit enforces the indicated parity in its row. -/
def parityWord (b : Bit) (u : Fin rows → Fin columns → Bit) : Mask rows (columns + 1)
  | (i, j) => Fin.cases (b - ∑ k, u i k) (u i) j

theorem rowParity_parityWord (b : Bit) (u : Fin rows → Fin columns → Bit) (i : Fin rows) :
    rowParity (parityWord b u) i = b := by
  rw [rowParity, Fin.sum_univ_succ]
  simp [parityWord]

def parityWordEmbedding (b : Bit) :
    (Fin rows → Fin columns → Bit) ↪ Mask rows (columns + 1) :=
  ⟨parityWord b, by
    intro u v h
    funext i j
    exact congrFun h (i, j.succ)⟩

/-- The computational basis words of the logical coset with parity `b`. -/
def parityWords (b : Bit) : Finset (Mask rows (columns + 1)) :=
  Finset.univ.map (parityWordEmbedding b)

theorem parityWords_mem_iff (b : Bit)
    (x : Mask rows (columns + 1)) :
    x ∈ parityWords b ↔ ∀ i, rowParity x i = b := by
  constructor
  · intro hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hx
    exact rowParity_parityWord b u
  · intro hx
    let u (i : Fin rows) (j : Fin columns) := x (i, j.succ)
    refine Finset.mem_map.mpr ⟨u, Finset.mem_univ _, ?_⟩
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun _ => rfl) j
    have h := hx i
    rw [rowParity, Fin.sum_univ_succ] at h
    change b - (∑ k : Fin columns, x (i, k.succ)) = x (i, 0)
    rw [← h, add_sub_cancel_right]

def parityWordCount (rows columns : ℕ) : ℕ :=
  Fintype.card (Fin rows → Fin columns → Bit)

theorem parityWordCount_pos (rows columns : ℕ) : 0 < parityWordCount rows columns :=
  Fintype.card_pos

theorem parityWords_card (b : Bit) :
    (parityWords (rows := rows) (columns := columns) b).card = parityWordCount rows columns := by
  simp [parityWords, parityWordCount]

/-- Both computational-basis coset columns have the same positive real
normalization. -/
noncomputable def shorAmplitude (rows columns : ℕ) : ℂ :=
  (Real.sqrt ((parityWordCount rows columns : ℝ)⁻¹) : ℂ)

theorem shorAmplitude_square (rows columns : ℕ) :
    star (shorAmplitude rows columns) * shorAmplitude rows columns =
      (parityWordCount rows columns : ℂ)⁻¹ := by
  have hsq : (Real.sqrt ((parityWordCount rows columns : ℝ)⁻¹)) ^ 2 =
      (parityWordCount rows columns : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hconj : star (shorAmplitude rows columns) = shorAmplitude rows columns := Complex.conj_ofReal _
  rw [hconj]
  have hc := congrArg Complex.ofReal hsq
  simpa [pow_two, shorAmplitude] using hc

/-- Concrete CSS encoding. Its row index is a binary computational-basis word,
and its two columns correspond to the common row parity. -/
noncomputable def shorEncoding (rows columns : ℕ) :
    Matrix (Mask rows (columns + 1)) Bit ℂ :=
  fun x b => if x ∈ parityWords b then shorAmplitude rows columns else 0

theorem shorEncoding_isometric [Nonempty (Fin rows)] :
    (shorEncoding rows columns).conjTranspose * shorEncoding rows columns = 1 := by
  classical
  ext a b
  change (∑ x, star (shorEncoding rows columns x a) * shorEncoding rows columns x b) = _
  by_cases hab : a = b
  · subst b
    have hpoint (x : Mask rows (columns + 1)) :
        star (shorEncoding rows columns x a) * shorEncoding rows columns x a =
          if x ∈ parityWords a then (parityWordCount rows columns : ℂ)⁻¹ else 0 := by
      by_cases hx : x ∈ parityWords a
      · simp only [shorEncoding, hx, ite_eq_left]
        exact shorAmplitude_square rows columns
      · simp [shorEncoding, hx]
    simp_rw [hpoint]
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter (fun x : Mask rows (columns + 1) => x ∈ parityWords a)) =
        parityWords (rows := rows) (columns := columns) a := by
      ext; simp
    rw [hf, Finset.sum_const, nsmul_eq_mul, parityWords_card]
    have hn : (parityWordCount rows columns : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (parityWordCount_pos rows columns))
    rw [mul_inv_cancel₀ hn, Matrix.one_apply_eq]
  · have hpoint (x : Mask rows (columns + 1)) :
        star (shorEncoding rows columns x a) * shorEncoding rows columns x b = 0 := by
      by_cases ha : x ∈ parityWords a
      · have hb : x ∉ parityWords b := by
          intro hb
          let i : Fin rows := Classical.choice inferInstance
          exact hab (((parityWords_mem_iff a x).mp ha i).symm.trans
            ((parityWords_mem_iff b x).mp hb i))
        simp [shorEncoding, hb]
      · simp [shorEncoding, ha]
    simp_rw [hpoint]
    simp [Matrix.one_apply, hab]

#print axioms parityWords_mem_iff
#print axioms shorEncoding_isometric

end CriticalDepth.FaultShorSaturation
