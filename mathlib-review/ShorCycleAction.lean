import ShorCyclePacking

/-!
Action of a product of disjoint native site cycles.
-/

namespace CriticalDepth.FaultShorSaturation

open CriticalDepth.Manuscript CriticalDepth.BinaryPermutationUnitary

variable {n q : ℕ}

def runSiteCycles {α : Type*} (blocks : List (SiteCycleBlock n q)) (v : Fin n → α) :
    Fin n → α := blocks.foldl (fun x B => B.run x) v

theorem runSiteCycles_off_sites {α : Type*} (blocks : List (SiteCycleBlock n q))
    (v : Fin n → α) (i : Fin n) (hoff : ∀ B ∈ blocks, i ∉ B.sites) :
    runSiteCycles blocks v i = v i := by
  induction blocks generalizing v with
  | nil => rfl
  | cons B rest ih =>
    change runSiteCycles rest (B.run v) i = v i
    exact (ih _ (fun G hG => hoff G (List.mem_cons_of_mem _ hG))).trans
      (B.run_off_site v i (hoff B (List.mem_cons_self ..)))

theorem runSiteCycles_on_site {α : Type*} (blocks : List (SiteCycleBlock n q))
    (hdis : blocks.Pairwise fun A B => Disjoint A.sites B.sites)
    (v : Fin n → α) (B : SiteCycleBlock n q) (hB : B ∈ blocks) (j : Fin q) :
    runSiteCycles blocks v (B.order j).val = v (B.order ((finRotate q).symm j)).val := by
  induction blocks generalizing v with
  | nil => simp at hB
  | cons G rest ih =>
    change runSiteCycles rest (G.run v) (B.order j).val = _
    obtain ⟨hG, hrest⟩ := List.pairwise_cons.mp hdis
    rcases List.mem_cons.mp hB with rfl | hm
    · rw [runSiteCycles_off_sites, B.run_on_site]
      intro H hH hbad
      exact Finset.disjoint_left.mp (hG H hH) (B.order j).property hbad
    · rw [ih hrest _ hm]
      exact G.run_off_site v _ (fun hbad =>
        Finset.disjoint_left.mp (hG B hm) hbad (B.order _).property)

theorem runSiteCycles_fixes {α : Type*} (blocks : List (SiteCycleBlock n q))
    (v : Fin n → α) (huniform : ∀ B ∈ blocks, ∀ i ∈ B.sites, ∀ j ∈ B.sites, v i = v j) :
    runSiteCycles blocks v = v := by
  induction blocks with
  | nil => rfl
  | cons B rest ih =>
    have hB : B.run v = v := by
      funext i
      by_cases hi : i ∈ B.sites
      · let j := B.order.symm ⟨i, hi⟩
        have he : (B.order j).val = i := congrArg Subtype.val (B.order.apply_symm_apply ⟨i, hi⟩)
        rw [← he, B.run_on_site]
        exact huniform B (List.mem_cons_self ..) _ (B.order _).property _ (B.order _).property
      · exact B.run_off_site v i hi
    change runSiteCycles rest (B.run v) = v
    rw [hB]
    exact ih (fun G hg => huniform G (List.mem_cons_of_mem _ hg))

def siteCyclesWordEquiv {α : Type*} :
    List (SiteCycleBlock n q) → Equiv.Perm (Fin n → α)
  | [] => Equiv.refl _
  | B :: rest => B.run.trans (siteCyclesWordEquiv rest)

theorem siteCyclesWordEquiv_apply {α : Type*} (blocks : List (SiteCycleBlock n q))
    (v : Fin n → α) :
    siteCyclesWordEquiv blocks v = runSiteCycles blocks v := by
  induction blocks generalizing v with
  | nil => rfl
  | cons B rest ih =>
    exact ih (B.run v)

theorem siteCyclesWordEquiv_add (blocks : List (SiteCycleBlock n q))
    (x y : Fin n → Bit) :
    siteCyclesWordEquiv blocks (x + y) =
      siteCyclesWordEquiv blocks x + siteCyclesWordEquiv blocks y := by
  induction blocks generalizing x y with
  | nil => rfl
  | cons B rest ih =>
    change siteCyclesWordEquiv rest (B.run (x + y)) = _
    have h : B.run (x + y) = B.run x + B.run y := rfl
    rw [h]
    exact ih _ _

theorem siteCyclesWordEquiv_smul (blocks : List (SiteCycleBlock n q))
    (t : Bit) (x : Fin n → Bit) :
    siteCyclesWordEquiv blocks (t • x) = t • siteCyclesWordEquiv blocks x := by
  induction blocks generalizing x with
  | nil => rfl
  | cons B rest ih =>
    change siteCyclesWordEquiv rest (B.run (t • x)) = _
    have h : B.run (t • x) = t • B.run x := rfl
    rw [h]
    exact ih _

def siteCyclesLinearEquiv (blocks : List (SiteCycleBlock n q)) :
    (Fin n → Bit) ≃ₗ[Bit] (Fin n → Bit) :=
  { siteCyclesWordEquiv blocks with
    map_add' := siteCyclesWordEquiv_add blocks
    map_smul' := siteCyclesWordEquiv_smul blocks }

theorem listGateEval_siteCycleBlocks (blocks : List (SiteCycleBlock n q)) :
    listGateEval (blocks.map SiteCycleBlock.gate) = basisPermutation (siteCyclesWordEquiv blocks) := by
  induction blocks with
  | nil =>
    ext x y
    simp [siteCyclesWordEquiv, basisPermutation_apply, Matrix.one_apply] <;> rfl
  | cons B rest ih =>
    change listGateEval (B.gate :: rest.map SiteCycleBlock.gate) = _
    rw [listGateEval_cons, ih]
    change basisPermutation (siteCyclesWordEquiv rest) * basisPermutation B.run = _
    rw [basisPermutation_mul]
    rfl

#print axioms runSiteCycles_on_site
#print axioms runSiteCycles_fixes
#print axioms listGateEval_siteCycleBlocks

end CriticalDepth.FaultShorSaturation