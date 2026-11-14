import ShorRowAction
import FaultCircuitSupport

/-!
# Coordinate formulas for rectangular Shor row actions

These formulas identify the physical permutation from its columnwise
binary action. They also transport a physical tensor X mask through a
suffix of the circuit.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary
open CriticalDepth.FaultCircuitSupport

variable {rows columns n q : ℕ}

@[simp] theorem shorWordLinearEquiv_apply
    (x : Fin (rows * columns) → Bit) (i : Fin rows) (j : Fin columns) :
    shorWordLinearEquiv rows columns x (i, j) = x ((shorSiteEquiv rows columns).symm (i, j)) :=
  rfl

@[simp] theorem shorWordLinearEquiv_symm_apply (x : Mask rows columns)
    (i : Fin rows) (j : Fin columns) :
    (shorWordLinearEquiv rows columns).symm x ((shorSiteEquiv rows columns).symm (i, j)) =
      x (i, j) := by
  exact congrFun ((shorWordLinearEquiv rows columns).apply_symm_apply x) (i, j)

theorem acrossColumnsPhysicalLinearEquiv_apply
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (x : Fin (rows * columns) → Bit) (i : Fin rows) (j : Fin columns) :
    acrossColumnsPhysicalLinearEquiv (columns := columns) T x
        ((shorSiteEquiv rows columns).symm (i, j)) =
      T (fun k => x ((shorSiteEquiv rows columns).symm (k, j))) i := by
  change (shorWordLinearEquiv rows columns).symm
    (acrossColumnsLinearEquiv (columns := columns) T (shorWordLinearEquiv rows columns x))
    ((shorSiteEquiv rows columns).symm (i, j)) = _
  rw [shorWordLinearEquiv_symm_apply]
  rfl

/-- Identical actions on every column identify a physical row map. -/
theorem eq_acrossColumnsPhysicalLinearEquiv
    (U : (Fin (rows * columns) → Bit) ≃ₗ[Bit] (Fin (rows * columns) → Bit))
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (hU : ∀ x i j, U x ((shorSiteEquiv rows columns).symm (i, j)) =
      T (fun k => x ((shorSiteEquiv rows columns).symm (k, j))) i) :
    U = acrossColumnsPhysicalLinearEquiv (columns := columns) T := by
  apply LinearEquiv.ext
  intro x
  funext a
  obtain ⟨⟨i, j⟩, rfl⟩ := (shorSiteEquiv rows columns).symm.surjective a
  rw [hU, acrossColumnsPhysicalLinearEquiv_apply]

/-- If a physical linear equivalence acts by the same function in each
column, that common column action is a linear equivalence. -/
theorem exists_acrossColumnsPhysicalLinearEquiv_of_action
    (U : (Fin (rows * columns) → Bit) ≃ₗ[Bit] (Fin (rows * columns) → Bit))
    (F : (Fin rows → Bit) → (Fin rows → Bit)) (j₀ : Fin columns)
    (hU : ∀ x i j, U x ((shorSiteEquiv rows columns).symm (i, j)) =
      F (fun k => x ((shorSiteEquiv rows columns).symm (k, j))) i) :
    ∃ T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit),
      (∀ z, T z = F z) ∧ U = acrossColumnsPhysicalLinearEquiv (columns := columns) T := by
  let e := shorSiteEquiv rows columns
  let pack (z : Fin rows → Bit) (a : Fin (rows * columns)) : Bit := z (e a).1
  have hpack (z : Fin rows → Bit) (i : Fin rows) (j : Fin columns) :
      pack z (e.symm (i, j)) = z i := by
    simp only [pack, Equiv.apply_symm_apply]
  have hrun (z : Fin rows → Bit) (i : Fin rows) (j : Fin columns) :
      U (pack z) (e.symm (i, j)) = F z i := by
    have hz : (fun k => pack z (e.symm (k, j))) = z := funext fun k => hpack z k j
    exact (hU (pack z) i j).trans (congrArg (fun y => F y i) hz)
  have hAdd (x y : Fin rows → Bit) : F (x + y) = F x + F y := by
    funext i
    calc
      _ = U (pack (x + y)) (e.symm (i, j₀)) := (hrun _ i j₀).symm
      _ = U (pack x) (e.symm (i, j₀)) + U (pack y) (e.symm (i, j₀)) :=
        congrFun (U.map_add (pack x) (pack y)) _
      _ = _ := by rw [hrun, hrun]; rfl
  have hSmul (a : Bit) (x : Fin rows → Bit) : F (a • x) = a • F x := by
    funext i
    calc
      _ = U (pack (a • x)) (e.symm (i, j₀)) := (hrun _ i j₀).symm
      _ = a • U (pack x) (e.symm (i, j₀)) := congrFun (U.map_smul a (pack x)) _
      _ = _ := by rw [hrun]; rfl
  let f : (Fin rows → Bit) →ₗ[Bit] (Fin rows → Bit) :=
    ⟨⟨F, hAdd⟩, hSmul⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have h : U (pack x) = U (pack y) := by
      funext a
      obtain ⟨⟨i, j⟩, rfl⟩ := e.symm.surjective a
      rw [hrun, hrun, hxy]
    have hp := U.injective h
    funext i
    rw [← hpack x i j₀, ← hpack y i j₀, hp]
  have hsurj : Function.Surjective F := by
    intro z
    obtain ⟨x, hx⟩ := U.surjective (pack z)
    refine ⟨fun k => x (e.symm (k, j₀)), ?_⟩
    funext i
    rw [← hU x i j₀, hx, hpack]
  let T := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  exact ⟨T, fun _ => rfl, eq_acrossColumnsPhysicalLinearEquiv U T hU⟩

theorem acrossColumnsPhysicalLinearEquiv_fixes_one_iff
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit)) (j₀ : Fin columns) :
    acrossColumnsPhysicalLinearEquiv (columns := columns) T 1 = 1 ↔ T 1 = 1 := by
  constructor
  · intro h
    funext i
    exact (acrossColumnsPhysicalLinearEquiv_apply T 1 i j₀).symm.trans
      (congrFun h ((shorSiteEquiv rows columns).symm (i, j₀)))
  · intro h
    funext a
    obtain ⟨⟨i, j⟩, rfl⟩ := (shorSiteEquiv rows columns).symm.surjective a
    exact (acrossColumnsPhysicalLinearEquiv_apply T 1 i j).trans (congrFun h i)

theorem shorWordLinearEquiv_acrossColumns
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (x : Mask rows columns) :
    shorWordLinearEquiv rows columns (acrossColumnsPhysicalLinearEquiv (columns := columns) T
      ((shorWordLinearEquiv rows columns).symm x)) = acrossColumns T.toLinearMap x := by
  change shorWordLinearEquiv rows columns ((shorWordLinearEquiv rows columns).symm
    (acrossColumnsLinearEquiv (columns := columns) T
      (shorWordLinearEquiv rows columns ((shorWordLinearEquiv rows columns).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem propagate_binaryWordOperator_physicalXWord
    (T : (Fin (rows * columns) → Bit) ≃ₗ[Bit] (Fin (rows * columns) → Bit))
    (a : Mask rows columns) :
    propagate (binaryWordOperator T.toEquiv) (pauliMatrix 0 (physicalXWord a)) =
      pauliMatrix 0 (physicalXWord
        (shorWordLinearEquiv rows columns (T ((shorWordLinearEquiv rows columns).symm a)))) :=
  binaryWordOperator_conjugates_physicalXWord T a

theorem propagate_acrossColumnsPhysical_physicalXWord
    (T : (Fin rows → Bit) ≃ₗ[Bit] (Fin rows → Bit))
    (a : Mask rows columns) :
    propagate (binaryWordOperator (acrossColumnsPhysicalLinearEquiv (columns := columns) T).toEquiv)
      (pauliMatrix 0 (physicalXWord a)) =
      pauliMatrix 0 (physicalXWord (acrossColumns T.toLinearMap a)) := by
  rw [propagate_binaryWordOperator_physicalXWord, shorWordLinearEquiv_acrossColumns]

theorem listGateEval_append_binary (left right : List (ListGate n (fun _ => 2) q)) :
    listGateEval (left ++ right) = listGateEval right * listGateEval left := by
  simp [listGateEval, List.reverse_append, List.prod_append]

theorem binaryWordOperator_trans (f g : (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit)) :
    binaryWordOperator (f.trans g).toEquiv = binaryWordOperator g.toEquiv * binaryWordOperator f.toEquiv :=
  (binaryWordOperator_mul _ _).symm

#print axioms eq_acrossColumnsPhysicalLinearEquiv
#print axioms exists_acrossColumnsPhysicalLinearEquiv_of_action
#print axioms propagate_acrossColumnsPhysical_physicalXWord
#print axioms listGateEval_append_binary

end CriticalDepth.FaultShorSaturation
