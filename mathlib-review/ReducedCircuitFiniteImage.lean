import ReducedCircuitIsomorphism

/-! The finite projective evaluations are preserved by removing inverse variables. -/

namespace CriticalDepth.Manuscript

noncomputable section

variable {n K g h q d : ℕ} {dim : Fin n → ℕ}

def forwardCircuitConjugationCoordinates (C : Code n dim K g)
    (support : GateIndex n h → Finset (Fin n)) (i : Fin K) (j : Fin g)
    (φ : ForwardCircuitRing support C →ₐ[ℂ] ℂ) :
    Matrix (Fin K × Fin K) (Fin K × Fin K) ℂ :=
  circuitConjugationCoordinates C support (φ.comp (circuitPresentationEquiv support C i j).symm.toAlgHom)

theorem forwardCircuitConjugationCoordinates_range_eq (C : Code n dim K g)
    (support : GateIndex n h → Finset (Fin n)) (i : Fin K) (j : Fin g) :
    Set.range (forwardCircuitConjugationCoordinates C support i j) =
      Set.range (circuitConjugationCoordinates (𝕂 := ℂ) C support) := by
  let e := circuitPresentationEquiv support C i j
  ext A
  constructor
  · rintro ⟨φ, rfl⟩
    exact ⟨φ.comp e.symm.toAlgHom, rfl⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨φ.comp e.toAlgHom, ?_⟩
    unfold forwardCircuitConjugationCoordinates
    congr 1
    apply AlgHom.ext
    intro x
    change φ (e (e.symm x)) = φ x
    rw [e.apply_symm_apply]

theorem forwardCircuitConjugationCoordinates_range_finite
    (C : Code n dim K g) (hDetect : DetectsBelow C d) (i : Fin K) (j : Fin g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (L : Fin h → Layer n dim q) :
    (Set.range (forwardCircuitConjugationCoordinates C (layoutSupport L) i j)).Finite := by
  rw [forwardCircuitConjugationCoordinates_range_eq]
  have hj := j.isLt
  exact circuitConjugationCoordinates_range_finite C hDetect (by omega) hq hcone L

#print axioms forwardCircuitConjugationCoordinates_range_finite

end
end CriticalDepth.Manuscript
