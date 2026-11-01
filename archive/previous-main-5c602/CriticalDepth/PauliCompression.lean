import CriticalDepth.PauliConjugation
import CriticalDepth.StabilizerWitness

/-!
# Parallel q-site Pauli compression

The buckets below are actual finite subsets of the original physical sites.
Their construction enumerates the active support, groups consecutive positions
by division by q, and retains the first physical site in each nonempty bucket.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators

variable {n : ℕ}

def rankBucket (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q b : ℕ) :
    Finset (Fin n) :=
  (Finset.univ.filter fun i : Fin S.card => i.val / q = b).image fun i => (e i).val

theorem rankBucket_subset (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q b : ℕ) :
    rankBucket S e q b ⊆ S := by
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  exact (e i).property

theorem rankBucket_disjoint (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q b c : ℕ) (hbc : b ≠ c) : Disjoint (rankBucket S e q b) (rankBucket S e q c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hy
  have hij : i = j := e.injective (Subtype.ext (hix.trans hjx.symm))
  have hib : i.val / q = b := (Finset.mem_filter.mp hi).2
  have hjc : j.val / q = c := (Finset.mem_filter.mp hj).2
  apply hbc
  exact hib.symm.trans ((congrArg (fun k : Fin S.card => k.val / q) hij).trans hjc)

theorem rankBucket_card_le (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q b : ℕ) (hq : 0 < q) : (rankBucket S e q b).card ≤ q := by
  classical
  let B : Finset (Fin S.card) := Finset.univ.filter fun i => i.val / q = b
  let remainder : B → Fin q := fun i => ⟨i.val.val % q, Nat.mod_lt _ hq⟩
  have hinj : Function.Injective remainder := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hrem : i.val.val % q = j.val.val % q := congrArg Fin.val hij
    have hi : i.val.val / q = b := (Finset.mem_filter.mp i.property).2
    have hj : j.val.val / q = b := (Finset.mem_filter.mp j.property).2
    have hid := Nat.mod_add_div i.val.val q
    have hjd := Nat.mod_add_div j.val.val q
    rw [hi] at hid
    rw [hj] at hjd
    omega
  calc
    (rankBucket S e q b).card ≤ B.card := by apply Finset.card_image_le
    _ ≤ q := by
      have hc := Fintype.card_le_of_injective remainder hinj
      simpa using hc

theorem mul_div_self_of_pos (b q : ℕ) (hq : 0 < q) : b * q / q = b := by
  have hlo : b ≤ b * q / q := by
    by_contra hn
    have hlt : b * q / q < b := by omega
    have hbad : b * q < b * q := (Nat.div_lt_iff_lt_mul hq).mp hlt
    exact (lt_irrefl _ hbad)
  have hhi : b * q / q < b + 1 := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    rw [Nat.add_mul, one_mul]
    omega
  omega

theorem bucket_first_lt (w q : ℕ) (hq : 0 < q)
    (b : Fin (Arithmetic.ceilDiv w q)) : b.val * q < w := by
  by_contra hn
  have hle : w ≤ b.val * q := by omega
  have hb : Arithmetic.ceilDiv w q ≤ b.val :=
    (Arithmetic.ceilDiv_le_iff w q b.val hq).mpr hle
  exact (Nat.not_le_of_gt b.isLt) hb

def bucketPivot (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ) (hq : 0 < q)
    (b : Fin (Arithmetic.ceilDiv S.card q)) : Fin n :=
  (e ⟨b.val * q, bucket_first_lt S.card q hq b⟩).val

theorem bucketPivot_mem (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ) (hq : 0 < q)
    (b : Fin (Arithmetic.ceilDiv S.card q)) :
    bucketPivot S e q hq b ∈ rankBucket S e q b.val := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨⟨b.val * q, bucket_first_lt S.card q hq b⟩, ?_, rfl⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, mul_div_self_of_pos b.val q hq⟩

theorem rankBucket_nonempty (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ)
    (hq : 0 < q) (b : Fin (Arithmetic.ceilDiv S.card q)) :
    (rankBucket S e q b.val).Nonempty :=
  ⟨bucketPivot S e q hq b, bucketPivot_mem S e q hq b⟩

theorem rankBucket_cover (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ)
    (hq : 0 < q) (x : Fin n) (hx : x ∈ S) :
    ∃ b : Fin (Arithmetic.ceilDiv S.card q), x ∈ rankBucket S e q b.val := by
  classical
  let i : Fin S.card := e.symm ⟨x, hx⟩
  have hw : S.card ≤ Arithmetic.ceilDiv S.card q * q :=
    (Arithmetic.ceilDiv_le_iff S.card q _ hq).mp (le_refl _)
  have hb : i.val / q < Arithmetic.ceilDiv S.card q := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    exact i.isLt.trans_le hw
  refine ⟨⟨i.val / q, hb⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, ?_⟩
  simp [i]

theorem bucketPivot_injective (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) : Function.Injective (bucketPivot S e q hq) := by
  classical
  intro b c hbc
  by_contra hne
  have hv : b.val ≠ c.val := fun h => hne (Fin.ext h)
  have hd := rankBucket_disjoint S e q b.val c.val hv
  have hb := bucketPivot_mem S e q hq b
  have hc : bucketPivot S e q hq b ∈ rankBucket S e q c.val := by
    rw [hbc]
    exact bucketPivot_mem S e q hq c
  exact Finset.disjoint_left.mp hd hb hc

theorem ceilDiv_support_le_sites (S : Finset (Fin n)) (q : ℕ) (hq : 1 ≤ q) :
    Arithmetic.ceilDiv S.card q ≤ n := by
  have hqpos : 0 < q := by omega
  have hcount : Arithmetic.ceilDiv S.card q ≤ S.card := by
    apply (Arithmetic.ceilDiv_le_iff S.card q S.card hqpos).mpr
    simpa using Nat.mul_le_mul_left S.card hq
  have hsites : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ S)
      _ = n := by simp
  exact hcount.trans hsites

def tensorEntriesMonoidHom (I : Type*) [Fintype I] [DecidableEq I] :
    (I → Operator (Fin 2)) →* Operator (I → Fin 2) where
  toFun := tensorEntries
  map_one' := tensorEntries_one
  map_mul' := tensorEntries_mul

private theorem monoidHom_list_prod {M N : Type*} [Monoid M] [Monoid N]
    (f : M →* N) (xs : List M) : f xs.prod = (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem pi_list_prod_apply {I M : Type*} [Monoid M]
    (xs : List (I → M)) (i : I) : xs.prod i = (xs.map fun f => f i).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

private theorem list_prod_eq_one_of_forall {J M : Type*} [Monoid M]
    (indices : List J) (f : J → M) (h : ∀ j ∈ indices, f j = 1) :
    (indices.map f).prod = 1 := by
  revert h
  induction indices with
  | nil => simp
  | cons j indices ih =>
      intro h
      have hj := h j (by simp)
      have hr : ∀ k ∈ indices, f k = 1 := by
        intro k hk
        exact h k (by simp [hk])
      simp [hj, ih hr]

private theorem list_prod_eq_selected {J M : Type*} [Monoid M]
    (indices : List J) (f : J → M) (j : J) (hn : indices.Nodup) (hj : j ∈ indices)
    (hother : ∀ k ∈ indices, k ≠ j → f k = 1) : (indices.map f).prod = f j := by
  classical
  revert hn hj hother
  induction indices with
  | nil => simp
  | cons i indices ih =>
      intro hn hj hother
      have hi : i ∉ indices := (List.nodup_cons.mp hn).1
      have hr : indices.Nodup := (List.nodup_cons.mp hn).2
      by_cases hij : i = j
      · subst i
        have htail : ∀ k ∈ indices, f k = 1 := by
          intro k hk
          apply hother k (by simp [hk])
          intro hkj
          subst k
          exact hi hk
        simp [list_prod_eq_one_of_forall indices f htail]
      · have hjtail : j ∈ indices := by
          rcases List.mem_cons.mp hj with hji | hjtail
          · exact False.elim (hij hji.symm)
          · exact hjtail
        have hfi : f i = 1 := hother i (by simp) hij
        have htail : ∀ k ∈ indices, k ≠ j → f k = 1 := by
          intro k hk hkj
          exact hother k (by simp [hk]) hkj
        simp only [List.map_cons, List.prod_cons, hfi, one_mul]
        exact ih hr hjtail htail

def maskPauli (p : Fin n → SinglePauli) (G : Finset (Fin n)) : Fin n → SinglePauli :=
  fun i => if i ∈ G then p i else .I

theorem maskPauli_supportedOn (p : Fin n → SinglePauli) (G : Finset (Fin n)) :
    SupportedOn (pauliMatrix (0 : Fin 4) (maskPauli p G)) G := by
  classical
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  simp [maskPauli, hi]

private def allSlots (n : ℕ) : List (Fin n) := List.ofFn fun i => i

private theorem allSlots_nodup (n : ℕ) : (allSlots n).Nodup := by
  unfold allSlots
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj hij
  have hij' := congrArg Fin.val hij
  simpa only [List.getElem_ofFn] using hij'

private theorem mem_allSlots (j : Fin n) : j ∈ allSlots n := by
  simp [allSlots]

/-- A disjoint cover factors the actual Pauli matrix into its masked block matrices. -/
theorem pauliMatrix_eq_masked_product (p : Fin n → SinglePauli)
    (G : Fin n → Finset (Fin n))
    (hdis : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hcover : ∀ x ∈ pauliSupport p, ∃ j, x ∈ G j) :
    pauliMatrix (0 : Fin 4) p =
      (List.ofFn fun j => pauliMatrix (0 : Fin 4) (maskPauli p (G j))).prod := by
  classical
  let F : Fin n → Fin n → Operator (Fin 2) :=
    fun j x => (maskPauli p (G j) x).matrix
  have hfamily : (fun x => (p x).matrix) = ((allSlots n).map F).prod := by
    funext x
    rw [pi_list_prod_apply]
    simp only [List.map_map, Function.comp_def]
    by_cases hpx : p x = .I
    · have hones : ∀ j ∈ allSlots n, F j x = 1 := by
        intro j _hj
        simp [F, maskPauli, hpx, SinglePauli.matrix]
      rw [list_prod_eq_one_of_forall (allSlots n) (fun j => F j x) hones]
      simp [hpx, SinglePauli.matrix]
    · have hx : x ∈ pauliSupport p := by simp [pauliSupport, hpx]
      obtain ⟨j, hxj⟩ := hcover x hx
      have hothers : ∀ k ∈ allSlots n, k ≠ j → F k x = 1 := by
        intro k _hk hkj
        have hxk : x ∉ G k := by
          intro hxk
          exact Finset.disjoint_left.mp (hdis k j hkj) hxk hxj
        simp [F, maskPauli, hxk, SinglePauli.matrix]
      have hs := list_prod_eq_selected (allSlots n) (fun k => F k x) j
        (allSlots_nodup n) (mem_allSlots j) hothers
      calc
        (p x).matrix = F j x := by simp [F, maskPauli, hxj]
        _ = ((allSlots n).map fun k => F k x).prod := hs.symm
  calc
    pauliMatrix (0 : Fin 4) p = tensorEntriesMonoidHom (Fin n) (fun x => (p x).matrix) :=
      pauliMatrix_zero_eq_tensorEntries p
    _ = tensorEntriesMonoidHom (Fin n) (((allSlots n).map F).prod) :=
      congrArg (tensorEntriesMonoidHom (Fin n)) hfamily
    _ = (((allSlots n).map F).map (tensorEntriesMonoidHom (Fin n))).prod :=
      monoidHom_list_prod _ _
    _ = (List.ofFn fun j => pauliMatrix (0 : Fin 4) (maskPauli p (G j))).prod := by
      simp [allSlots, List.map_ofFn, tensorEntriesMonoidHom,
        pauliMatrix_zero_eq_tensorEntries, F, Function.comp_def]

private theorem unitary_list_prod {dim : Fin n → ℕ}
    (gates : List (Operator (PhysicalBasis n dim))) (h : ∀ U ∈ gates, IsUnitary U) :
    IsUnitary gates.prod := by
  revert h
  induction gates with
  | nil =>
      intro h
      constructor <;> simp
  | cons U gates ih =>
      intro h
      apply unitary_mul (h U (by simp))
      apply ih
      intro V hV
      exact h V (by simp [hV])

theorem Layer.eval_isUnitary {q : ℕ} {dim : Fin n → ℕ} (L : Layer n dim q) :
    IsUnitary L.eval := by
  apply unitary_list_prod
  intro U hU
  have hU' : ∃ i, L.gate i = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  exact L.unitary i

def unitaryConjugationHom {α : Type*} [Fintype α] [DecidableEq α]
    (U : Operator α) (hU : IsUnitary U) : Operator α →* Operator α where
  toFun := fun P => U * P * star U
  map_one' := by simpa using hU.2
  map_mul' := by
    intro P Q
    calc
      U * (P * Q) * star U = U * P * (star U * U) * Q * star U := by
        rw [hU.1]
        simp only [mul_assoc, mul_one]
      _ = (U * P * star U) * (U * Q * star U) := by simp only [mul_assoc]

private theorem indexed_layer_conjugation {q : ℕ} {dim : Fin n → ℕ}
    (L : Layer n dim q) (indices : List (Fin n)) (hn : indices.Nodup) (j : Fin n)
    (P Q : Operator (PhysicalBasis n dim))
    (hP : SupportedOn P (L.support j)) (hQ : SupportedOn Q (L.support j))
    (hown : L.gate j * P * star (L.gate j) = Q) :
    (indices.map L.gate).prod * P * star ((indices.map L.gate).prod) =
      if j ∈ indices then Q else P := by
  classical
  revert hn
  induction indices with
  | nil =>
      intro hn
      simp
  | cons i indices ih =>
      intro hn
      have hi : i ∉ indices := (List.nodup_cons.mp hn).1
      have hr : indices.Nodup := (List.nodup_cons.mp hn).2
      have hinter :
          (L.gate i * (indices.map L.gate).prod) * P *
              star (L.gate i * (indices.map L.gate).prod) =
            L.gate i * ((indices.map L.gate).prod * P *
              star ((indices.map L.gate).prod)) * star (L.gate i) := by
        rw [star_mul]
        simp only [mul_assoc]
      simp only [List.map_cons, List.prod_cons]
      rw [hinter, ih hr]
      by_cases hij : i = j
      · subst i
        simpa [hi] using hown
      · have hji : j ≠ i := Ne.symm hij
        have hfixedP : L.gate i * P * star (L.gate i) = P :=
          hP.conjugate_disjoint (L.locality i) (L.disjoint j i hji) (L.unitary i)
        have hfixedQ : L.gate i * Q * star (L.gate i) = Q :=
          hQ.conjugate_disjoint (L.locality i) (L.disjoint j i hji) (L.unitary i)
        by_cases hjtail : j ∈ indices <;>
          simp [hjtail, hij, hji, hfixedP, hfixedQ]

/-- All other gates cancel, so a layer acts on a block by that block's own gate. -/
theorem Layer.eval_conjugate_of_gate {q : ℕ} {dim : Fin n → ℕ}
    (L : Layer n dim q) (j : Fin n) (P Q : Operator (PhysicalBasis n dim))
    (hP : SupportedOn P (L.support j)) (hQ : SupportedOn Q (L.support j))
    (hown : L.gate j * P * star (L.gate j) = Q) :
    L.eval * P * star L.eval = Q := by
  classical
  let indices := (allSlots n).reverse
  have hn : indices.Nodup := by
    simpa only [indices, List.nodup_reverse] using allSlots_nodup n
  have hj : j ∈ indices := by simp [indices, allSlots]
  have hg : indices.map L.gate = (List.ofFn L.gate).reverse := by
    simp [indices, allSlots, List.map_reverse, List.map_ofFn, Function.comp_def]
  have hh := indexed_layer_conjugation L indices hn j P Q hP hQ hown
  rw [hg] at hh
  simpa only [Layer.eval, hj, if_true] using hh

/-- Parallel block identities assemble to a conjugation of the full Pauli string. -/
theorem Layer.conjugate_pauli_of_masked_blocks {q : ℕ}
    (L : Layer n (fun _ => 2) q) (p p' : Fin n → SinglePauli)
    (hcover : ∀ x ∈ pauliSupport p, ∃ j, x ∈ L.support j)
    (hcover' : ∀ x ∈ pauliSupport p', ∃ j, x ∈ L.support j)
    (hblock : ∀ j,
      L.gate j * pauliMatrix (0 : Fin 4) (maskPauli p (L.support j)) * star (L.gate j) =
        pauliMatrix (0 : Fin 4) (maskPauli p' (L.support j))) :
    L.eval * pauliMatrix (0 : Fin 4) p * star L.eval = pauliMatrix (0 : Fin 4) p' := by
  classical
  let f := unitaryConjugationHom L.eval L.eval_isUnitary
  have hlocal : ∀ j,
      f (pauliMatrix (0 : Fin 4) (maskPauli p (L.support j))) =
        pauliMatrix (0 : Fin 4) (maskPauli p' (L.support j)) := by
    intro j
    exact L.eval_conjugate_of_gate j _ _
      (maskPauli_supportedOn p (L.support j)) (maskPauli_supportedOn p' (L.support j))
      (hblock j)
  change f (pauliMatrix (0 : Fin 4) p) = pauliMatrix (0 : Fin 4) p'
  rw [pauliMatrix_eq_masked_product p L.support L.disjoint hcover,
    monoidHom_list_prod]
  have hlist :
      (List.ofFn fun j => pauliMatrix (0 : Fin 4) (maskPauli p (L.support j))).map f =
        List.ofFn fun j => pauliMatrix (0 : Fin 4) (maskPauli p' (L.support j)) := by
    simp [List.map_ofFn, Function.comp_def, hlocal]
  rw [hlist]
  exact (pauliMatrix_eq_masked_product p' L.support L.disjoint hcover').symm

def paddedBucket (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ)
    (i : Fin n) : Finset (Fin n) :=
  if i.val < Arithmetic.ceilDiv S.card q then rankBucket S e q i.val else ∅

theorem paddedBucket_disjoint (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ)
    (i j : Fin n) (hij : i ≠ j) : Disjoint (paddedBucket S e q i) (paddedBucket S e q j) := by
  classical
  by_cases hi : i.val < Arithmetic.ceilDiv S.card q <;>
    by_cases hj : j.val < Arithmetic.ceilDiv S.card q
  · simp only [paddedBucket, hi, hj, if_true]
    exact rankBucket_disjoint S e q i.val j.val (fun h => hij (Fin.ext h))
  · simp [paddedBucket, hi, hj]
  · simp [paddedBucket, hi, hj]
  · simp [paddedBucket, hi, hj]

theorem paddedBucket_card_le (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) (i : Fin n) : (paddedBucket S e q i).card ≤ q := by
  classical
  by_cases hi : i.val < Arithmetic.ceilDiv S.card q
  · simpa only [paddedBucket, hi, if_true] using rankBucket_card_le S e q i.val hq
  · simp [paddedBucket, hi]

theorem paddedBucket_cover (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 1 ≤ q) (x : Fin n) (hx : x ∈ S) :
    ∃ i : Fin n, x ∈ paddedBucket S e q i := by
  classical
  obtain ⟨b, hb⟩ := rankBucket_cover S e q (by omega) x hx
  let i : Fin n := ⟨b.val, b.isLt.trans_le (ceilDiv_support_le_sites S q hq)⟩
  refine ⟨i, ?_⟩
  simpa only [paddedBucket, i, b.isLt, if_true] using hb

def bucketPivotSet (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ) (hq : 0 < q) :
    Finset (Fin n) := Finset.univ.image (bucketPivot S e q hq)

def bucketTarget (S : Finset (Fin n)) (e : Fin S.card ≃ S) (q : ℕ) (hq : 0 < q) :
    Fin n → SinglePauli := fun x => if x ∈ bucketPivotSet S e q hq then .Z else .I

theorem bucketTarget_support (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) : pauliSupport (bucketTarget S e q hq) = bucketPivotSet S e q hq := by
  classical
  ext x
  simp [pauliSupport, bucketTarget]

theorem bucketTarget_support_card (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) :
    (pauliSupport (bucketTarget S e q hq)).card = Arithmetic.ceilDiv S.card q := by
  classical
  rw [bucketTarget_support]
  have hc : (Finset.univ.image (bucketPivot S e q hq)).card =
      (Finset.univ : Finset (Fin (Arithmetic.ceilDiv S.card q))).card := by
    apply Finset.card_image_iff.mpr
    intro b _hb c _hc hbc
    exact bucketPivot_injective S e q hq hbc
  simpa only [bucketPivotSet, Finset.card_univ, Fintype.card_fin] using hc

theorem bucketTarget_support_subset (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) : pauliSupport (bucketTarget S e q hq) ⊆ S := by
  classical
  rw [bucketTarget_support]
  intro x hx
  obtain ⟨b, _hb, rfl⟩ := Finset.mem_image.mp hx
  exact rankBucket_subset S e q b.val (bucketPivot_mem S e q hq b)

theorem mask_bucketTarget_eq_single (S : Finset (Fin n)) (e : Fin S.card ≃ S)
    (q : ℕ) (hq : 0 < q) (b : Fin (Arithmetic.ceilDiv S.card q)) :
    maskPauli (bucketTarget S e q hq) (rankBucket S e q b.val) =
      singleSitePauli (bucketPivot S e q hq b) .Z := by
  classical
  funext x
  by_cases hxp : x = bucketPivot S e q hq b
  · subst x
    have hpivot : bucketPivot S e q hq b ∈ bucketPivotSet S e q hq :=
      Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    simp [maskPauli, bucketTarget, singleSitePauli, hpivot, bucketPivot_mem]
  · by_cases hxb : x ∈ rankBucket S e q b.val
    · have hn : x ∉ bucketPivotSet S e q hq := by
        intro hx
        obtain ⟨c, _hc, hcx⟩ := Finset.mem_image.mp hx
        by_cases hcb : c = b
        · subst c
          exact hxp hcx.symm
        · have hv : c.val ≠ b.val := fun h => hcb (Fin.ext h)
          have hmem : bucketPivot S e q hq c ∈ rankBucket S e q b.val := by
            rw [hcx]
            exact hxb
          exact Finset.disjoint_left.mp (rankBucket_disjoint S e q c.val b.val hv)
            (bucketPivot_mem S e q hq c) hmem
      simp [maskPauli, bucketTarget, singleSitePauli, hxb, hn, hxp]
    · simp [maskPauli, singleSitePauli, hxb, hxp]

theorem maskPauli_empty (p : Fin n → SinglePauli) : maskPauli p ∅ = fun _ => .I := by
  funext i
  simp [maskPauli]

/-- One actual parallel q-ary layer performs exactly one ceiling-division round. -/
theorem pauli_compression_layer (q : ℕ) (hq : 1 ≤ q) (p : Fin n → SinglePauli) :
    ∃ p' : Fin n → SinglePauli, ∃ L : Layer n (fun _ => 2) q,
      L.eval * pauliMatrix (0 : Fin 4) p * star L.eval = pauliMatrix (0 : Fin 4) p' ∧
        (pauliSupport p').card = Arithmetic.ceilDiv (pauliSupport p).card q := by
  classical
  let S := pauliSupport p
  let e : Fin S.card ≃ S := S.equivFin.symm
  have hqpos : 0 < q := by omega
  let G : Fin n → Finset (Fin n) := paddedBucket S e q
  let p' := bucketTarget S e q hqpos
  have hgate : ∀ i : Fin n, ∃ U : Operator (QubitBasis n), IsUnitary U ∧ SupportedOn U (G i) ∧
      U * pauliMatrix (0 : Fin 4) (maskPauli p (G i)) * star U =
        pauliMatrix (0 : Fin 4) (maskPauli p' (G i)) := by
    intro i
    by_cases hi : i.val < Arithmetic.ceilDiv S.card q
    · let b : Fin (Arithmetic.ceilDiv S.card q) := ⟨i.val, hi⟩
      let j := bucketPivot S e q hqpos b
      have hG : G i = rankBucket S e q b.val := by simp [G, paddedBucket, hi, b]
      have hj : j ∈ G i := by rw [hG]; exact bucketPivot_mem S e q hqpos b
      have hjS : j ∈ S := rankBucket_subset S e q b.val (by simpa only [hG] using hj)
      have hpj : p j ≠ .I := (Finset.mem_filter.mp hjS).2
      have hmaskj : maskPauli p (G i) j ≠ .I := by simpa [maskPauli, hj] using hpj
      have hout : ∀ x, x ∉ G i → maskPauli p (G i) x = .I := by
        intro x hx
        simp [maskPauli, hx]
      obtain ⟨U, hU, hsupp, hconj⟩ :=
        pauli_group_to_single_site (G i) (maskPauli p (G i)) hout j hj hmaskj
      refine ⟨U, hU, hsupp, ?_⟩
      have htarget : maskPauli p' (G i) = singleSitePauli j .Z := by
        rw [hG]
        exact mask_bucketTarget_eq_single S e q hqpos b
      rw [htarget]
      exact hconj
    · have hG : G i = ∅ := by simp [G, paddedBucket, hi]
      refine ⟨1, ⟨by simp, by simp⟩, supportedOn_one (G i), ?_⟩
      simp only [hG, maskPauli_empty, one_mul, star_one, mul_one]
  choose gate hunit hsupp hconj using hgate
  let L : Layer n (fun _ => 2) q :=
    { support := G
      gate := gate
      disjoint := paddedBucket_disjoint S e q
      arity := paddedBucket_card_le S e q hqpos
      locality := hsupp
      unitary := hunit }
  refine ⟨p', L, ?_, ?_⟩
  · apply L.conjugate_pauli_of_masked_blocks p p'
    · intro x hx
      exact paddedBucket_cover S e q hq x hx
    · intro x hx
      exact paddedBucket_cover S e q hq x (bucketTarget_support_subset S e q hqpos hx)
    · exact hconj
  · exact bucketTarget_support_card S e q hqpos

end CriticalDepth.Manuscript
