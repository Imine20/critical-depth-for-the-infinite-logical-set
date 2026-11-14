import ReducedCircuitInverses

/-!
The full and reduced circuit presentations define the same coordinate algebra.
-/

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

noncomputable section

variable {n K g h : ℕ} {dim : Fin n → ℕ}
variable (support : GateIndex n h → Finset (Fin n)) (C : Code n dim K g)

abbrev fullCircuitEvaluation :
    CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ]
      CircuitCoordinateRing (C := C) (support := support) :=
  Ideal.Quotient.mkₐ ℂ (circuitIdeal support C)

def toFullCircuitRing :
    ForwardCircuitRing support C →ₐ[ℂ] CircuitCoordinateRing (C := C) (support := support) := by
  let a := fullCircuitEvaluation support C
  let b := a.comp (includeForward support)
  apply Ideal.Quotient.liftₐ (forwardCircuitIdeal support C) b
  have hspan : forwardCircuitIdeal support C ≤ RingHom.ker b.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    change b (omitInverse support p) = 0
    have he : a p = (b.comp (omitInverse support)) p :=
      circuitMaps_agree_on_forwardRelations support C a (b.comp (omitInverse support))
        (by
          rw [AlgHom.comp_assoc, omitInverse_includeForward, AlgHom.comp_id]) hp
    rw [← show a p = b (omitInverse support p) from he]
    change Ideal.Quotient.mk (circuitIdeal support C) p = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    rcases hp with hp | hp
    · simp only [circuitRelations, Set.mem_union]
      tauto
    · rcases hp with hp | hp <;> (simp only [circuitRelations, Set.mem_union]; tauto)
  exact fun p hp => hspan hp

@[simp] theorem toFullCircuitRing_mk (p : ForwardCircuitPolynomial (dim := dim) (K := K)
    (g := g) support) :
    toFullCircuitRing support C (Ideal.Quotient.mk (forwardCircuitIdeal support C) p) =
      fullCircuitEvaluation support C (includeForward support p) := by
  rfl

def circuitInverseSubstitution (i : Fin K) (j : Fin g) :
    CircuitPolynomial (dim := dim) (K := K) (g := g) support →ₐ[ℂ]
      ForwardCircuitRing support C :=
  MvPolynomial.aeval fun
    | .inr (.inl (true, a, b)) => forwardLogicalInverse support C j a b
    | .inr (.inr (true, a, b)) => forwardGaugeInverse support C i a b
    | v => forwardCircuitEvaluation support C (MvPolynomial.X v)

theorem circuitInverseSubstitution_include (i : Fin K) (j : Fin g) :
    (circuitInverseSubstitution support C i j).comp (includeForward support) =
      Ideal.Quotient.mkₐ ℂ (forwardCircuitIdeal support C) := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with v | v
  · simp [circuitInverseSubstitution, includeForward, includeForwardVariable, omitInverse]
  · rcases v with v | v <;>
      simp [circuitInverseSubstitution, includeForward, includeForwardVariable, omitInverse]

def toForwardCircuitRing (i : Fin K) (j : Fin g) :
    CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] ForwardCircuitRing support C := by
  let a := circuitInverseSubstitution support C i j
  apply Ideal.Quotient.liftₐ (circuitIdeal support C) a
  suffices hs : circuitIdeal support C ≤ RingHom.ker a.toRingHom from fun p hp => hs hp
  apply Ideal.span_le.mpr
  intro p hp
  change a p = 0
  have hcases :
      p ∈ gateInverseEntries (dim := dim) (K := K) (g := g) support ∪ encodingEntries support C ∨
      p ∈ inverseRelationEntries support (logicalPolynomial support false)
        (logicalPolynomial support true) ∨
      p ∈ inverseRelationEntries support (gaugePolynomial support false)
        (gaugePolynomial support true) := by
    simp only [circuitRelations, encodingEntries, Set.mem_union] at hp ⊢
    tauto
  have he : a.comp (includeForward support) =
      (forwardCircuitEvaluation support C).comp (includeForward support) := by
    dsimp only [a]
    rw [circuitInverseSubstitution_include]
    change _ = (Ideal.Quotient.mkₐ ℂ (forwardCircuitIdeal support C)).comp
      ((omitInverse support).comp (includeForward support))
    rw [omitInverse_includeForward, AlgHom.comp_id]
  have oneOfProduct {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
      (hAB : A.map a * B.map a = 1 ∧ B.map a * A.map a = 1)
      (hm : p ∈ inverseRelationEntries support A B) : a p = 0 := by
    have hzero (X Y : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
        (hmul : X.map a * Y.map a = 1) (hf : p ∈ matrixRelationEntries support (X * Y) 1) :
        a p = 0 := by
      obtain ⟨⟨x, y⟩, rfl⟩ := hf
      rw [map_sub, sub_eq_zero]
      have ee : (X * Y).map a = (1 : Matrix ι ι _).map a := by
        rw [solutionMap_mul, solutionMap_one, hmul]
      exact congrFun (congrFun ee x) y
    rcases hm with hl | hr
    · exact hzero A B hAB.1 hl
    · exact hzero B A hAB.2 hr
  have hW (x : Fin K) (y : Fin K) :
      a ((logicalPolynomial support false) x y) = forwardLogical support C x y := by
    simp [a, circuitInverseSubstitution, logicalPolynomial]
  have hZ (x : Fin g) (y : Fin g) :
      a ((gaugePolynomial support false) x y) = forwardGauge support C x y := by
    simp [a, circuitInverseSubstitution, gaugePolynomial]
  have hWi : (logicalPolynomial support true).map a = forwardLogicalInverse support C j := by
    ext x y
    simp [a, circuitInverseSubstitution, logicalPolynomial]
  have hZi : (gaugePolynomial support true).map a = forwardGaugeInverse support C i := by
    ext x y
    simp [a, circuitInverseSubstitution, gaugePolynomial]
  obtain ⟨hW₁, hW₂, hZ₁, hZ₂⟩ := forwardFactorInverses_spec support C i j
  rcases hcases with hf | h | h
  · rw [circuitMaps_agree_on_forwardRelations support C a (forwardCircuitEvaluation support C) he hf]
    exact forwardCircuitEvaluation_relation support C hf
  · apply oneOfProduct _ _ _ h
    rw [hWi, show (logicalPolynomial support false).map a = forwardLogical support C from
      funext fun x => funext fun y => hW x y]
    exact ⟨hW₁, hW₂⟩
  · apply oneOfProduct _ _ _ h
    rw [hZi, show (gaugePolynomial support false).map a = forwardGauge support C from
      funext fun x => funext fun y => hZ x y]
    exact ⟨hZ₁, hZ₂⟩

@[simp] theorem toForwardCircuitRing_mk (i : Fin K) (j : Fin g)
    (p : CircuitPolynomial (dim := dim) (K := K) (g := g) support) :
    toForwardCircuitRing support C i j (fullCircuitEvaluation support C p) =
      circuitInverseSubstitution support C i j p := by
  rfl

/-- Recovered inverse coordinates give the exact isomorphism of the two quotient rings. -/
def circuitPresentationEquiv (i : Fin K) (j : Fin g) :
    ForwardCircuitRing support C ≃ₐ[ℂ] CircuitCoordinateRing (C := C) (support := support) := by
  let f := toFullCircuitRing support C
  let r := toForwardCircuitRing support C i j
  have hf : Function.LeftInverse r f := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change r (toFullCircuitRing support C (Ideal.Quotient.mk (forwardCircuitIdeal support C) p)) = _
    rw [toFullCircuitRing_mk, toForwardCircuitRing_mk]
    exact DFunLike.congr_fun (circuitInverseSubstitution_include support C i j) p
  have hfullW :
      (logicalPolynomial support false).map (f.comp (circuitInverseSubstitution support C i j)) =
        (logicalPolynomial support false).map (fullCircuitEvaluation support C) := by
    ext a b
    simpa [f, logicalPolynomial, includeForward, includeForwardVariable] using
      congrArg f (DFunLike.congr_fun (circuitInverseSubstitution_include support C i j)
        (MvPolynomial.X (.inr (.inl (a, b)))))
  have hfullZ :
      (gaugePolynomial support false).map (f.comp (circuitInverseSubstitution support C i j)) =
        (gaugePolynomial support false).map (fullCircuitEvaluation support C) := by
    ext a b
    simpa [f, gaugePolynomial, includeForward, includeForwardVariable] using
      congrArg f (DFunLike.congr_fun (circuitInverseSubstitution_include support C i j)
        (MvPolynomial.X (.inr (.inr (a, b)))))
  have hfull_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
      (A B : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
      (hAB : inverseRelationEntries support A B ⊆ circuitRelations support C) :
      A.map (fullCircuitEvaluation support C) * B.map (fullCircuitEvaluation support C) = 1 ∧
        B.map (fullCircuitEvaluation support C) * A.map (fullCircuitEvaluation support C) = 1 := by
    have h (P Q : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support))
        (hs : matrixRelationEntries support (P * Q) 1 ⊆ circuitRelations support C) :
        P.map (fullCircuitEvaluation support C) * Q.map (fullCircuitEvaluation support C) = 1 := by
      rw [← solutionMap_mul, ← solutionMap_one (fullCircuitEvaluation support C)]
      ext a b
      let B := fullCircuitEvaluation support C
      change B ((P * Q) a b) = B ((1 : Matrix ι ι _) a b)
      rw [← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (hs ⟨(a, b), rfl⟩))
    exact ⟨h A B (fun p hp => hAB (Or.inl hp)), h B A (fun p hp => hAB (Or.inr hp))⟩
  have hWi :=
    hfull_inverse (logicalPolynomial (dim := dim) (K := K) (g := g) support false)
      (logicalPolynomial (dim := dim) (K := K) (g := g) support true)
      (fun _ hp => Or.inl (Or.inl (Or.inl (Or.inr hp))))
  have hZi :=
    hfull_inverse (gaugePolynomial (dim := dim) (K := K) (g := g) support false)
      (gaugePolynomial (dim := dim) (K := K) (g := g) support true)
      (fun _ hp => Or.inl (Or.inl (Or.inr hp)))
  have hOther (A B : Matrix (Fin K) (Fin K) (ForwardCircuitRing support C)) (hAB : A * B = 1) :
      A.map f * B.map f = 1 := by rw [← solutionMap_mul, hAB, solutionMap_one]
  have hOtherG (A B : Matrix (Fin g) (Fin g) (ForwardCircuitRing support C)) (hAB : A * B = 1) :
      A.map f * B.map f = 1 := by rw [← solutionMap_mul, hAB, solutionMap_one]
  let a := f.comp (circuitInverseSubstitution support C i j)
  let b := fullCircuitEvaluation support C
  have hW : (logicalPolynomial support true).map a = (logicalPolynomial support true).map b := by
    have hAB := hOther _ _ (forwardFactorInverses_spec support C i j).2.1
    have hA : (logicalPolynomial support true).map a = (forwardLogicalInverse support C j).map f := by
      ext x y
      simp [a, circuitInverseSubstitution, logicalPolynomial]
    have hB : (logicalPolynomial support false).map a = (forwardLogical support C).map f := by
      ext x y
      simp [a, circuitInverseSubstitution, logicalPolynomial]
    rw [← hA, ← hB, hfullW] at hAB
    exact left_inv_eq_right_inv hAB hWi.1
  have hZ : (gaugePolynomial support true).map a = (gaugePolynomial support true).map b := by
    have hAB := hOtherG _ _ (forwardFactorInverses_spec support C i j).2.2.2
    have hA : (gaugePolynomial support true).map a = (forwardGaugeInverse support C i).map f := by
      ext x y
      simp [a, circuitInverseSubstitution, gaugePolynomial]
    have hB : (gaugePolynomial support false).map a = (forwardGauge support C).map f := by
      ext x y
      simp [a, circuitInverseSubstitution, gaugePolynomial]
    rw [← hA, ← hB, hfullZ] at hAB
    exact left_inv_eq_right_inv hAB hZi.1
  have ha : a = b := by
    apply MvPolynomial.algHom_ext
    intro v
    rcases v with v | v
    · simpa [a, b, f, includeForward, includeForwardVariable] using
        congrArg f (DFunLike.congr_fun (circuitInverseSubstitution_include support C i j)
          (MvPolynomial.X (.inl v)))
    · rcases v with ⟨u, x, y⟩ | ⟨u, x, y⟩
      · cases u
        · exact congrFun (congrFun hfullW x) y
        · exact congrFun (congrFun hW x) y
      · cases u
        · exact congrFun (congrFun hfullZ x) y
        · exact congrFun (congrFun hZ x) y
  have hr : Function.RightInverse r f := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f (toForwardCircuitRing support C i j (fullCircuitEvaluation support C p)) = b p
    rw [toForwardCircuitRing_mk]
    exact DFunLike.congr_fun ha p
  exact AlgEquiv.ofBijective f ⟨hf.injective, hr.surjective⟩

#print axioms circuitPresentationEquiv

end
end CriticalDepth.Manuscript
