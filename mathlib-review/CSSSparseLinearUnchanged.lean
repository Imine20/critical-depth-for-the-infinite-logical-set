import CSSSparseLinearEquations

/-!
The unchanged rows of a candidate automorphism must belong to a proper fixed space.
-/

namespace CriticalDepth.Manuscript20261114.CSSCheckSpaces

open scoped BigOperators Matrix

local notation "𝔽" => ZMod 2
variable {n a : ℕ}

theorem card_sparse_automorphism_unchanged_bound
    (F : Matrix (Fin n) (Fin n) 𝔽) (S : Matrix (Fin a) (Fin a) 𝔽) (hS : S ≠ 1) :
    (Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => F * A = A * S).card ≤
      2 ^ (a * n - (n - (changedRows F).card)) := by
  classical
  let T : (Fin a → 𝔽) →ₗ[𝔽] Fin a → 𝔽 := S.vecMulLinear - LinearMap.id
  have hT : T ≠ 0 := by
    intro h
    apply hS
    ext i j
    have hi := congrFun (LinearMap.congr_fun h (Pi.single i 1)) j
    have he : (Pi.single i (1 : 𝔽)) ᵥ* S = Pi.single i 1 := by
      funext k
      exact sub_eq_zero.mp (congrFun (LinearMap.congr_fun h (Pi.single i 1)) k)
    rw [Matrix.single_one_vecMul] at he
    by_cases hj : i = j
    · subst j
      simpa [Matrix.one_apply, Pi.single_apply] using congrFun he i
    · simpa [Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj] using congrFun he j
  have hr : 1 ≤ Module.finrank 𝔽 T.range := by
    apply Submodule.one_le_finrank_iff.mpr
    intro he
    exact hT (LinearMap.range_eq_bot.mp he)
  have ha : 1 ≤ a := by
    have hle := LinearMap.finrank_range_le T
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
    exact hr.trans hle
  let U := (changedRows F)ᶜ
  have hcard : U.card = n - (changedRows F).card := by
    simp [U, Finset.card_compl]
  let Good := Finset.univ.filter fun A : Matrix (Fin n) (Fin a) 𝔽 => F * A = A * S
  let To := (U → T.ker) × ((changedRows F) → (Fin a → 𝔽))
  have hf (A : Good) (i : U) : A.val.row i.val ∈ T.ker := by
    have hrow : F.row i.val = (1 : Matrix (Fin n) (Fin n) 𝔽).row i.val := by
      by_contra hn
      exact (Finset.mem_compl.mp i.property) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
    have he := congrArg (fun M : Matrix (Fin n) (Fin a) 𝔽 => M.row i.val)
      (Finset.mem_filter.mp A.property).2
    rw [Matrix.row_mul_eq_vecMul_row, Matrix.row_mul_eq_vecMul_row, hrow] at he
    have hid : (1 : Matrix (Fin n) (Fin n) 𝔽).row i.val ᵥ* A.val = A.val.row i.val := by
      rw [← Matrix.row_mul_eq_vecMul_row, Matrix.one_mul]
    rw [hid] at he
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr he.symm)
  let f (A : Good) : To := (fun i => ⟨A.val.row i.val, hf A i⟩, fun i => A.val.row i.val)
  have hinj : Function.Injective f := by
    intro A B he
    apply Subtype.ext
    ext i j
    by_cases hi : i ∈ changedRows F
    · exact congrFun (congrFun (congrArg Prod.snd he) ⟨i, hi⟩) j
    · have he' := congrFun (congrArg Prod.fst he) ⟨i, Finset.mem_compl.mpr hi⟩
      exact congrFun (congrArg (fun x : T.ker => x.val) he') j
  have hK := card_binary_linearMap_kernel_bound T a 1
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) hr
  have h := Nat.card_le_card_of_injective f hinj
  letI : Fintype T.ker := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_eq_fintype_card,
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, Fintype.card_coe,
    Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  rw [Nat.card_eq_fintype_card] at hK
  change Good.card ≤ _
  have haU : U.card + (changedRows F).card = n := by
    have hle : (changedRows F).card ≤ n := by simpa using Finset.card_le_univ (changedRows F)
    omega
  calc
    _ ≤ Fintype.card T.ker ^ U.card * (2 ^ a) ^ (changedRows F).card := h
    _ ≤ (2 ^ (a - 1)) ^ U.card * (2 ^ a) ^ (changedRows F).card :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hK _)
    _ = _ := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      rw [← hcard]
      have haN := congrArg (fun x : ℕ => a * x) haU
      rw [Nat.mul_add] at haN
      have hh : (a - 1) * U.card + U.card = a * U.card := by
        rw [← Nat.succ_mul, show (a - 1).succ = a by omega]
      omega

#print axioms card_sparse_automorphism_unchanged_bound

end CriticalDepth.Manuscript20261114.CSSCheckSpaces