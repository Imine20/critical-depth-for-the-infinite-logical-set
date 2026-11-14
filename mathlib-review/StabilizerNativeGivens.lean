import StabilizerFrameSynthesis
import LogicalFrameRotationTransport
import ExactGivensNativeTarget

/-!
# Exact native synthesis using selected minimum-weight stabilizer representatives
-/

namespace CriticalDepth.Manuscript20261114

open CriticalDepth.Manuscript CriticalDepth.ReviewV2 Relation
open scoped Kronecker ENat

noncomputable section

variable {n k d : ℕ}

/-- A stabilizer code admits one fixed family of minimum-weight directions
for the chosen connected graph. Each target unitary is then implemented
on the original encoding using a finite word of those directions, with
complete circuit depth bounded by the word length times the maximum
compression depth. -/
theorem exists_stabilizer_native_exact_givens
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hk : 1 ≤ k) (hd : 2 ≤ d) (q : ℕ) (hq : 2 ≤ q)
    (hstab : IsStabilizer C) (hdist : HasActualDistance C d)
    (E : Fin k → Fin k → Prop) (hConnected : ∀ i j, ReflTransGen E i j) :
    ∃ (S : PhysicalStabilizer n) (F : PauliRotationFamily C (ConnectedFrameDirection E))
      (p rep : ConnectedFrameDirection E → PauliLabel n),
      (∀ V ∈ S, IsPauli V.val) ∧
      Set.range (fun v => C.encoding.mulVec v) = {v | ∀ V ∈ S, V.val.mulVec v = v} ∧
      (∀ a, rep a ∈ stabilizerCosetLabels S (p a)) ∧
      (∀ a, F.physical a = (rep a).2) ∧
      (∀ a s, s ∈ stabilizerCosetLabels S (p a) →
        (pauliSupport (F.physical a)).card ≤ (pauliSupport s.2).card) ∧
      (Arithmetic.criticalDepth q d : ℕ∞) ≤ nativeExactDepth C.encoding q ∧
      nativeExactDepth C.encoding q ≤ (Arithmetic.criticalDepth q F.maxWeight : ℕ∞) ∧
      Arithmetic.criticalDepth q F.maxWeight ≤ Arithmetic.criticalDepth q n ∧
      ∀ A : Matrix.unitaryGroup (Fin (2 ^ k)) ℂ,
        ∃ R : List (PU (Fin (2 ^ k))),
          (∀ V ∈ R, V ∈ F.alphabet) ∧ R.prod = projectiveMk (Fin (2 ^ k)) A ∧
          ∃ s ≤ R.length * Arithmetic.criticalDepth q F.maxWeight,
            ∃ c : NativeCircuit n (fun _ => 2) s, NativeCircuitAllowed q c ∧
              (nativeCircuitEval c).val * C.encoding =
                C.encoding * (A.val ⊗ₖ (1 : Operator (Fin 1))) := by
  classical
  obtain ⟨S, hS, hspace, F0, F, p, rep, hr, hPhysical, hMin, hLo, hUp, hN, e, U, hC⟩ :=
    exists_stabilizer_connectedFrame_minimum_depth_with_basis C hk hd q hq hstab hdist E hConnected
  have hDepth : Arithmetic.criticalDepth q d ≤ Arithmetic.criticalDepth q F.maxWeight := by
    exact_mod_cast hLo.trans hUp
  have hWeight : 2 ≤ F.maxWeight := by
    by_contra! h
    have hp : 1 ≤ Arithmetic.criticalDepth q d := one_le_criticalDepth_of_two_le q d hq hd
    have hc : Nat.clog q F.maxWeight = 0 := Nat.clog_of_right_le_one (by omega) q
    have hz : Arithmetic.criticalDepth q F.maxWeight = 0 := by
      simp [Arithmetic.criticalDepth, hc]
    exact Nat.not_succ_le_zero 0 (by simpa [hz] using hp.trans hDepth)
  have hn : 0 < n := by
    have h := F.maxWeight_le_n
    omega
  let P := logicalFrameProjective e U
  have hX (i : Fin k) (t : ℝ) :
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (singleSitePauli i .X) t)) ∈
        Subgroup.closure F.alphabet :=
    Subgroup.subset_closure (F.logicalFrameProjective_rotation_mem_alphabet e U _
      (Sum.inl (Sum.inl i)) (hC (Sum.inl (Sum.inl i))) t)
  have hZ (i : Fin k) (t : ℝ) :
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (singleSitePauli i .Z) t)) ∈
        Subgroup.closure F.alphabet :=
    Subgroup.subset_closure (F.logicalFrameProjective_rotation_mem_alphabet e U _
      (Sum.inl (Sum.inr i)) (hC (Sum.inl (Sum.inr i))) t)
  have hZZ (i j : Fin k) (hij : E i j) (hne : i ≠ j) (t : ℝ) :
      P (projectiveMk (QubitBasis k) (tensorPauliRotation (pairPauli i j .Z .Z) t)) ∈
        Subgroup.closure F.alphabet :=
    Subgroup.subset_closure (F.logicalFrameProjective_rotation_mem_alphabet e U _
      (Sum.inr ⟨(i,j),hij,hne⟩) (hC (Sum.inr ⟨(i,j),hij,hne⟩)) t)
  refine ⟨S, F, p, rep, hS, hspace, hr, hPhysical, hMin, hLo, hUp, hN, ?_⟩
  intro A
  obtain ⟨_, _, R, _, _, _, hR, hProd, hCircuit⟩ :=
    F.exists_native_exact_givens_of_connected_axes e P hn q hq hWeight E hConnected hX hZ hZZ A
  exact ⟨R, hR, hProd, hCircuit⟩

#print axioms exists_stabilizer_native_exact_givens

end

end CriticalDepth.Manuscript20261114
