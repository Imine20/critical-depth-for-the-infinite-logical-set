import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.FieldTheory.Differential.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.DenseEmbedding
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Basic
import Lean
import Lean.Util.CollectAxioms

/-!
# Mathlib-based critical-depth formalization

Lean 4.35.0, compiler eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.

This file inlines every mathematical project proof and every new transport,
period, closed-circle and application proof. Its imports are only Mathlib and
Lean standard-library modules; no local compiled module is a dependency.
The selected public interfaces are NativeTheoremOne, NativeTheoremTwo,
theoremOne_arbitrary_carriers and critical_circle_joint_witness.

The foundational objects in those interfaces are Mathlib matrices, unitary
groups, quotient groups, tensor products, linear isometries, subgroups, Circle
and topological group equivalences. The paper-specific predicates are defined
explicitly. Earlier matrix/quotient views remain as compatibility lemmas and
internal proof representations, with proved bridges to the native objects.

Source blocks retain their mathematical bodies and public names. Import lines
are hoisted and per-file sections close earlier implicit EOF scopes. Historical
comments retain earlier provenance and must not be used as a current version
binding. The final V2 driver audits the completed own-module environment; no
mathematics follows that driver. Source hashes, correspondence and trusted
public-dependency boundaries are recorded separately in the review package.
-/


/- ===== Source block: Arithmetic; SHA-256 86dcf32c19428fdbc0b500972cf3b9369b0ee483adcdaf49039322dfb6214272 ===== -/
section Merged_Arithmetic
/-!
# Arithmetic dependencies for the critical-depth manuscript

The source manuscript is bound separately by its SHA-256 manifest. This module
proves only integer threshold, light-cone, and support-count arithmetic. It does
not define quantum codes or circuits and does not prove either main theorem.

For positive arity, `ceilDiv w q` is the usual ceiling of `w / q`. The explicit
zero case makes the iteration meaningful for an empty support as well.
-/

namespace CriticalDepth.Arithmetic

def ceilHalf (h : ℕ) : ℕ := (h + 1) / 2

def criticalDepth (q d : ℕ) : ℕ := 2 * Nat.clog q d - 1

/-- Bridge from the discrete ceiling logarithm to the manuscript's real formula. -/
theorem clog_eq_natCeil_log (q d : ℕ) :
    Nat.clog q d = ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ := by
  simpa only [Real.logb] using (Real.natCeil_logb_natCast q d).symm

theorem criticalDepth_eq_log (q d : ℕ) :
    criticalDepth q d = 2 * ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ - 1 := by
  unfold criticalDepth
  rw [clog_eq_natCeil_log]

/-- The strict depth threshold is exactly the strict two-sided cone bound. -/
theorem below_threshold_iff (q d h : ℕ) (hq : 2 ≤ q) :
    h < criticalDepth q d ↔ q ^ ceilHalf h < d := by
  have hq' : 1 < q := by omega
  change h < 2 * Nat.clog q d - 1 ↔ q ^ ((h + 1) / 2) < d
  rw [← Nat.lt_clog_iff_pow_lt hq']
  omega

theorem below_threshold_log_iff (q d h : ℕ) (hq : 2 ≤ q) :
    h < 2 * ⌈Real.log (d : ℝ) / Real.log (q : ℝ)⌉₊ - 1 ↔
      q ^ ceilHalf h < d := by
  rw [← criticalDepth_eq_log]
  exact below_threshold_iff q d h hq

/-- Unary gates satisfy the cone inequality at every finite depth, without `log₁`. -/
theorem unary_cone_bound (d h : ℕ) (hd : 2 ≤ d) :
    (1 : ℕ) ^ ceilHalf h < d := by
  simpa only [one_pow] using (show 1 < d by omega)

/-- One of the forward and backward layer counts is at most `ceil(h/2)`. -/
theorem layer_min_le_ceilHalf (h ℓ : ℕ) (_hℓ : 1 ≤ ℓ) (hℓh : ℓ ≤ h) :
    min ℓ (h - ℓ + 1) ≤ ceilHalf h := by
  unfold ceilHalf
  by_cases ha : ℓ ≤ (h + 1) / 2
  · exact (min_le_left _ _).trans ha
  · have hb : h - ℓ + 1 ≤ (h + 1) / 2 := by omega
    exact (min_le_right _ _).trans hb

def ceilDiv (w q : ℕ) : ℕ := if w = 0 then 0 else (w - 1) / q + 1

@[simp] theorem ceilDiv_zero (q : ℕ) : ceilDiv 0 q = 0 := by
  simp [ceilDiv]

@[simp] theorem ceilDiv_one (w : ℕ) : ceilDiv w 1 = w := by
  cases w <;> simp [ceilDiv]

theorem ceilDiv_of_pos {w : ℕ} (hw : 0 < w) (q : ℕ) :
    ceilDiv w q = (w - 1) / q + 1 := by
  simp [ceilDiv, Nat.ne_of_gt hw]

theorem ceilDiv_pos {w : ℕ} (hw : 0 < w) (q : ℕ) : 0 < ceilDiv w q := by
  rw [ceilDiv_of_pos hw]
  exact Nat.succ_pos _

/-- Ceiling divisions compose by multiplying their denominators. -/
theorem ceilDiv_comp (w a b : ℕ) :
    ceilDiv (ceilDiv w a) b = ceilDiv w (a * b) := by
  by_cases hw : w = 0
  · simp [hw]
  · have hw' : 0 < w := by omega
    rw [ceilDiv_of_pos (ceilDiv_pos hw' a), ceilDiv_of_pos hw',
      ceilDiv_of_pos hw']
    simp only [Nat.add_sub_cancel_right]
    rw [Nat.div_div_eq_div_mul]

/-- The characteristic inequality for ordinary ceiling division. -/
theorem ceilDiv_le_iff (w q m : ℕ) (hq : 0 < q) :
    ceilDiv w q ≤ m ↔ w ≤ m * q := by
  by_cases hw : w = 0
  · simp [hw]
  · have hw' : 0 < w := by omega
    rw [ceilDiv_of_pos hw']
    constructor
    · intro h
      have hd : (w - 1) / q < m := by omega
      have hm : w - 1 < m * q := (Nat.div_lt_iff_lt_mul hq).mp hd
      omega
    · intro h
      have hm : w - 1 < m * q := by omega
      have hd : (w - 1) / q < m := (Nat.div_lt_iff_lt_mul hq).mpr hm
      omega

/-- The support count resulting from one ceiling-division compression per round. -/
def compressedWeight (q d : ℕ) : ℕ → ℕ
  | 0 => d
  | r + 1 => ceilDiv (compressedWeight q d r) q

theorem compressedWeight_eq_ceilDiv_pow (q d r : ℕ) :
    compressedWeight q d r = ceilDiv d (q ^ r) := by
  induction r with
  | zero => simp [compressedWeight]
  | succ r ih =>
      rw [compressedWeight, ih, ceilDiv_comp, pow_succ]

theorem compressedWeight_eq (q d r : ℕ) (hd : 0 < d) :
    compressedWeight q d r = (d - 1) / q ^ r + 1 := by
  rw [compressedWeight_eq_ceilDiv_pow, ceilDiv_of_pos hd]

theorem compressedWeight_pos (q d r : ℕ) (hd : 0 < d) :
    0 < compressedWeight q d r := by
  rw [compressedWeight_eq_ceilDiv_pow]
  exact ceilDiv_pos hd _

theorem compressedWeight_le_iff (q d r m : ℕ) (hq : 0 < q) :
    compressedWeight q d r ≤ m ↔ d ≤ m * q ^ r := by
  rw [compressedWeight_eq_ceilDiv_pow]
  exact ceilDiv_le_iff d (q ^ r) m (pow_pos hq r)

theorem clog_pos_of_two_le (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    0 < Nat.clog q d := by
  have hq' : 1 < q := by omega
  have hp : d ≤ q ^ Nat.clog q d :=
    (Nat.clog_le_iff_le_pow hq').mp (le_refl _)
  by_contra hn
  have hz : Nat.clog q d = 0 := by omega
  rw [hz] at hp
  simp only [pow_zero] at hp
  omega

theorem clog_eq_one_of_distance_le_arity (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d)
    (hdq : d ≤ q) : Nat.clog q d = 1 := by
  have hm : 0 < Nat.clog q d := clog_pos_of_two_le q d hq hd
  have hu : Nat.clog q d ≤ 1 := (Nat.clog_le_iff_le_pow (by omega : 1 < q)).mpr
    (by simpa only [pow_one] using hdq)
  omega

/-- `ceil(log_q d)-1` compression rounds leave at most `q` active sites. -/
theorem compressedWeight_at_clog_pred_le (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    compressedWeight q d (Nat.clog q d - 1) ≤ q := by
  have hq' : 1 < q := by omega
  have hp : d ≤ q ^ Nat.clog q d :=
    (Nat.clog_le_iff_le_pow hq').mp (le_refl _)
  have hm : 0 < Nat.clog q d := clog_pos_of_two_le q d hq hd
  have hs : Nat.clog q d - 1 + 1 = Nat.clog q d := by omega
  have hp' : d ≤ q ^ (Nat.clog q d - 1 + 1) := by
    rw [hs]
    exact hp
  rw [pow_succ] at hp'
  apply (compressedWeight_le_iff q d (Nat.clog q d - 1) q (by omega)).mpr
  simpa only [Nat.mul_comm] using hp'

/-- Compression, one rotation layer, and uncomputation give the stated count. -/
theorem synthesis_depth_count (m : ℕ) (hm : 0 < m) :
    (m - 1) + 1 + (m - 1) = 2 * m - 1 := by
  omega

theorem synthesis_depth_at_clog (q d : ℕ) (hq : 2 ≤ q) (hd : 2 ≤ d) :
    (Nat.clog q d - 1) + 1 + (Nat.clog q d - 1) = criticalDepth q d := by
  unfold criticalDepth
  exact synthesis_depth_count _ (clog_pos_of_two_le q d hq hd)

end CriticalDepth.Arithmetic
end Merged_Arithmetic

/- ===== Source block: ComponentConstants; SHA-256 29b9660fc056c6e80bf9f4afb60f150d09003fdd7726fd0496522f0520074beb ===== -/
section Merged_ComponentConstants
/-!
# Integrality from scalar values on prime components

If an element agrees with a base scalar modulo every minimal prime of a
Noetherian algebra, a product of the corresponding linear polynomials has
nilpotent value at that element. A power of that monic polynomial is an
annihilating polynomial. Nilpotents in the coordinate algebra are therefore
allowed; no reducedness assumption is imposed.
-/

namespace CriticalDepth

open Polynomial

universe u v

/-- Scalar values modulo the finitely many minimal prime components give
an integral element. The scalar witness may depend on the component. -/
theorem isIntegral_of_scalar_mod_minimalPrimes
    (F : Type u) (R : Type v)
    [Field F] [CommRing R] [Algebra F R] [IsNoetherianRing R]
    (r : R)
    (h : ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∃ c : F, r - algebraMap F R c ∈ p) :
    IsIntegral F r := by
  classical
  let primes := (⊥ : Ideal R).minimalPrimes
  have hfinite : primes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R (⊥ : Ideal R)
  let ps : Finset (Ideal R) := hfinite.toFinset
  let c : Ideal R → F := fun p =>
    if hp : p ∈ primes then Classical.choose (h p hp) else 0
  have hc (p : Ideal R) (hp : p ∈ primes) :
      r - algebraMap F R (c p) ∈ p := by
    simpa only [c, dif_pos hp] using Classical.choose_spec (h p hp)
  let P : F[X] := ∏ p ∈ ps, (X - C (c p))
  have hmonic_aux (s : Finset (Ideal R)) :
      (∏ p ∈ s, (X - C (c p)) : F[X]).Monic := by
    induction s using Finset.induction with
    | empty => simp
    | @insert p s hps ih =>
        rw [Finset.prod_insert hps]
        exact (monic_X_sub_C (c p)).mul ih
  have hmonic : P.Monic := hmonic_aux ps
  have hmem (p : Ideal R) (hp : p ∈ primes) : aeval r P ∈ p := by
    have hp_ps : p ∈ ps := by simpa [ps] using hp
    have hprod (s : Finset (Ideal R)) :
        p ∈ s → (∏ q ∈ s, (r - algebraMap F R (c q))) ∈ p := by
      induction s using Finset.induction with
      | empty => intro hps; simp at hps
      | @insert q s hqs ih =>
          intro hps
          rw [Finset.prod_insert hqs]
          rcases Finset.mem_insert.mp hps with hpq | hps
          · subst q
            exact p.mul_mem_right _ (hc p hp)
          · exact p.mul_mem_left _ (ih hps)
    simpa only [P, map_prod, map_sub, aeval_X, aeval_C] using hprod ps hp_ps
  have hrad : aeval r P ∈ (⊥ : Ideal R).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    exact Ideal.mem_sInf.mpr hmem
  change ∃ N : ℕ, (aeval r P) ^ N ∈ (⊥ : Ideal R) at hrad
  obtain ⟨N, hN⟩ := hrad
  have hzero : (aeval r P) ^ N = 0 := by simpa using hN
  refine ⟨P ^ N, hmonic.pow N, ?_⟩
  change aeval r (P ^ N) = 0
  rw [map_pow]
  exact hzero

end CriticalDepth
end Merged_ComponentConstants

/- ===== Source block: DerivationExtension; SHA-256 5d42a69eeb51e53b3b6105149752dd3cdcff5449fd7f45cbd57f333525a30611 ===== -/
section Merged_DerivationExtension
/-!
# Extending derivations through a formally etale algebra

The extension below is obtained from the universal property of Kahler
differentials and the base-change equivalence for a formally etale map.
It is an algebraic ingredient of the proposed proof of finiteness of the
logical image; this module does not assert either manuscript theorem.
-/

namespace CriticalDepth

universe u v w

variable (R : Type u) (S : Type v) (T : Type w)
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T]
variable [IsScalarTower R S T] [Algebra.FormallyEtale S T]

/-- Extend an `R`-derivation from `S` to `T` through a formally etale map.
The codomain is already `T`, so the tensor base change can be evaluated
directly in that codomain. -/
noncomputable def extendDerivationFormallyEtale
    (d : Derivation R S T) : Derivation R T T :=
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

/-- The extended derivation agrees with the given derivation on scalars
coming from `S`. -/
theorem extendDerivationFormallyEtale_algebraMap
    (d : Derivation R S T) (s : S) :
    extendDerivationFormallyEtale R S T d (algebraMap S T s) = d s := by
  change (d.liftKaehlerDifferential.liftBaseChange T)
      ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
        (KaehlerDifferential.D R T (algebraMap S T s))) = d s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

section PolynomialCoordinates

variable (σ : Type v)
variable [Algebra (MvPolynomial σ R) T]
variable [IsScalarTower R (MvPolynomial σ R) T]
variable [Algebra.FormallyEtale (MvPolynomial σ R) T]

/-- The partial derivation in one polynomial coordinate, extended through
a formally etale algebra. No finiteness assumption on the variable type
is needed. -/
noncomputable def polynomialCoordinateDerivation
    (i : σ) : Derivation R T T :=
  extendDerivationFormallyEtale R (MvPolynomial σ R) T
    ((Algebra.linearMap (MvPolynomial σ R) T).compDer (MvPolynomial.pderiv i))

/-- The extended partial derivation sends its chosen coordinate to one. -/
theorem polynomialCoordinateDerivation_X (i : σ) :
    polynomialCoordinateDerivation R T σ i
      (algebraMap (MvPolynomial σ R) T (MvPolynomial.X i)) = 1 := by
  rw [polynomialCoordinateDerivation,
    extendDerivationFormallyEtale_algebraMap]
  change algebraMap (MvPolynomial σ R) T
      (MvPolynomial.pderiv i (MvPolynomial.X i)) = 1
  rw [MvPolynomial.pderiv_X_self, map_one]

/-- A polynomial coordinate cannot be annihilated by every base-linear
derivation after a formally etale extension to a nontrivial ring. -/
theorem not_all_derivations_vanish_on_polynomial_coordinate
    [Nontrivial T] (i : σ) :
    ¬ ∀ d : Derivation R T T,
      d (algebraMap (MvPolynomial σ R) T (MvPolynomial.X i)) = 0 := by
  intro h
  have hz := h (polynomialCoordinateDerivation R T σ i)
  rw [polynomialCoordinateDerivation_X] at hz
  exact one_ne_zero hz

end PolynomialCoordinates

section PolynomialPresentations

variable (σ : Type v)

/-- Transport a polynomial partial derivation through an algebra
equivalence, with values in the target algebra. -/
noncomputable def polynomialCoordinateDerivationOnAlgebra
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) : Derivation R S T :=
  Derivation.mk'
    (((Algebra.linearMap S T).restrictScalars R).comp
      (e.toLinearMap.comp
        ((MvPolynomial.pderiv i).toLinearMap.comp e.symm.toLinearMap)))
    (by
      intro a b
      change algebraMap S T (e (MvPolynomial.pderiv i (e.symm (a * b)))) =
        a • algebraMap S T (e (MvPolynomial.pderiv i (e.symm b))) +
        b • algebraMap S T (e (MvPolynomial.pderiv i (e.symm a)))
      rw [map_mul, (MvPolynomial.pderiv i).leibniz]
      simp [Algebra.smul_def])

theorem polynomialCoordinateDerivationOnAlgebra_X
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) :
    polynomialCoordinateDerivationOnAlgebra R S T σ e i
      (e (MvPolynomial.X i)) = 1 := by
  change algebraMap S T
      (e (MvPolynomial.pderiv i (e.symm (e (MvPolynomial.X i))))) = 1
  simp

/-- Extend a transported polynomial coordinate derivation through the
formally etale map from the presented algebra to its target. -/
noncomputable def polynomialCoordinateDerivationViaEquiv
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) : Derivation R T T :=
  extendDerivationFormallyEtale R S T
    (polynomialCoordinateDerivationOnAlgebra R S T σ e i)

theorem polynomialCoordinateDerivationViaEquiv_X
    (e : MvPolynomial σ R ≃ₐ[R] S) (i : σ) :
    polynomialCoordinateDerivationViaEquiv R S T σ e i
      (algebraMap S T (e (MvPolynomial.X i))) = 1 := by
  rw [polynomialCoordinateDerivationViaEquiv,
    extendDerivationFormallyEtale_algebraMap,
    polynomialCoordinateDerivationOnAlgebra_X]

end PolynomialPresentations

end CriticalDepth
end Merged_DerivationExtension

/- ===== Source block: IntegralImage; SHA-256 c67d112265d72337cab336507da0e2d0682577a6ce1a68427548bb900fcef573 ===== -/
section Merged_IntegralImage
/-!
Integral coordinates have a finite evaluation image over a field. This is a
finishing lemma for the proposed algebraic proof of manuscript Theorem 1.
Integrality of the actual circuit coordinates remains a separate obligation;
the lemma does not assume or assert the manuscript's finite-image conclusion.
-/

noncomputable section

namespace CriticalDepth

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

theorem integral_evaluation_range_finite (r : R) (hr : IsIntegral F r) :
    (Set.range fun f : R →ₐ[F] F => f r).Finite := by
  obtain ⟨p, hp, hpr⟩ := hr
  apply (Polynomial.finite_setOfPred_isRoot hp.ne_zero).subset
  rintro z ⟨f, rfl⟩
  change Polynomial.aeval (f r) p = 0
  rw [Polynomial.aeval_algHom_apply]
  change f (Polynomial.eval₂ (algebraMap F R) r p) = 0
  rw [hpr, map_zero]

theorem integral_coordinate_evaluation_image_finite {ι : Type*} [Fintype ι]
    (r : ι → R) (hr : ∀ i, IsIntegral F (r i)) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  classical
  let S : ι → Set F := fun i => Set.range fun f : R →ₐ[F] F => f (r i)
  have hS : ∀ i, (S i).Finite := fun i => integral_evaluation_range_finite (r i) (hr i)
  letI (i : ι) : Fintype (S i) := (hS i).fintype
  have hfinite : (Set.range fun v : (i : ι) → S i => fun i => (v i).1).Finite :=
    Set.finite_range _
  apply hfinite.subset
  rintro v ⟨f, rfl⟩
  exact ⟨fun i => ⟨f (r i), ⟨f, rfl⟩⟩, rfl⟩

end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_IntegralImage

/- ===== Source block: MatrixCore; SHA-256 6e7a8bd257b20b7874e3cbe556f9b16ec57ef74efc01c12cecdd9c5b10ca0c61 ===== -/
section Merged_MatrixCore
/-!
Concrete matrix conventions shared by the critical-depth development.

`ProjectivelyEquivalent` removes exactly one global unit-modulus complex
scalar. `IsScalar` does not allow different phases on separate sectors.
-/

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Operator (ι : Type*) := Matrix ι ι ℂ

def IsScalar (A : Operator ι) : Prop :=
  ∃ z : ℂ, A = z • (1 : Operator ι)

def ProjectivelyEquivalent (A B : Operator ι) : Prop :=
  ∃ z : ℂ, star z * z = 1 ∧ A = z • B

/-- Both inverse equations are recorded, with the adjoint on the left first. -/
def IsUnitary (A : Operator ι) : Prop :=
  star A * A = 1 ∧ A * star A = 1

def affine (P : Operator ι) (a b : ℂ) : Operator ι :=
  a • (1 : Operator ι) + b • P

theorem projectivelyEquivalent_refl (A : Operator ι) :
    ProjectivelyEquivalent A A := by
  exact ⟨1, by simp, by simp⟩

theorem projectivelyEquivalent_symm {A B : Operator ι}
    (h : ProjectivelyEquivalent A B) : ProjectivelyEquivalent B A := by
  obtain ⟨z, hz, hAB⟩ := h
  refine ⟨star z, ?_, ?_⟩
  · simpa [mul_comm] using hz
  · calc
      B = (star z * z) • B := by rw [hz]; simp
      _ = star z • (z • B) := by rw [smul_smul]
      _ = star z • A := by rw [hAB]

theorem projectivelyEquivalent_trans {A B C : Operator ι}
    (hAB : ProjectivelyEquivalent A B) (hBC : ProjectivelyEquivalent B C) :
    ProjectivelyEquivalent A C := by
  obtain ⟨z, hz, hAB⟩ := hAB
  obtain ⟨w, hw, hBC⟩ := hBC
  refine ⟨z * w, ?_, ?_⟩
  · calc
      star (z * w) * (z * w) = (star z * z) * (star w * w) := by
        rw [star_mul]
        ring
      _ = 1 := by rw [hz, hw]; simp
  · rw [hAB, hBC, smul_smul]

def projectiveSetoid (ι : Type*) [Fintype ι] [DecidableEq ι] : Setoid (Operator ι) where
  r := ProjectivelyEquivalent
  iseqv := ⟨projectivelyEquivalent_refl, projectivelyEquivalent_symm,
    projectivelyEquivalent_trans⟩

abbrev ProjectiveOperator (ι : Type*) [Fintype ι] [DecidableEq ι] :=
  Quotient (projectiveSetoid ι)

def projectiveClass (A : Operator ι) : ProjectiveOperator ι :=
  Quotient.mk (projectiveSetoid ι) A

theorem projectivelyEquivalent_one_isScalar {A : Operator ι}
    (h : ProjectivelyEquivalent A 1) : IsScalar A := by
  obtain ⟨z, _, hz⟩ := h
  exact ⟨z, hz⟩

theorem isScalar_of_smul {P : Operator ι} {z : ℂ} (hz : z ≠ 0)
    (h : IsScalar (z • P)) : IsScalar P := by
  obtain ⟨a, ha⟩ := h
  refine ⟨z⁻¹ * a, ?_⟩
  calc
    P = z⁻¹ • (z • P) := by simp [smul_smul, hz]
    _ = z⁻¹ • (a • (1 : Operator ι)) := by rw [ha]
    _ = (z⁻¹ * a) • (1 : Operator ι) := by rw [smul_smul]

/-- A nonscalar matrix and the identity are linearly independent. -/
theorem affine_eq_zero_coefficients {P : Operator ι} (hP : ¬ IsScalar P)
    {a b : ℂ} (h : affine P a b = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    apply hP
    have hbp : b • P = -(a • (1 : Operator ι)) := by
      have hh := congrArg (fun X : Operator ι => X - a • (1 : Operator ι)) h
      simpa [affine, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh
    refine ⟨-(b⁻¹ * a), ?_⟩
    calc
      P = b⁻¹ • (b • P) := by simp [smul_smul, hb]
      _ = b⁻¹ • (-(a • (1 : Operator ι))) := by rw [hbp]
      _ = (-(b⁻¹ * a)) • (1 : Operator ι) := by simp [smul_smul]
  subst b
  constructor
  · by_contra ha
    have hone : (1 : Operator ι) = 0 := by
      have hh := congrArg (fun X : Operator ι => a⁻¹ • X) h
      simpa [affine, smul_smul, ha] using hh
    apply hP
    refine ⟨0, ?_⟩
    have hzero : P = 0 := by
      calc
        P = P * 1 := by simp
        _ = P * 0 := by rw [hone]
        _ = 0 := by simp
    simpa using hzero
  · rfl

theorem affine_coefficients_unique {P : Operator ι} (hP : ¬ IsScalar P)
    {a b c d : ℂ} (h : affine P a b = affine P c d) : a = c ∧ b = d := by
  have hzero : affine P (a - c) (b - d) = 0 := by
    calc
      affine P (a - c) (b - d) = affine P a b - affine P c d := by
        simp only [affine, sub_smul]
        abel
      _ = 0 := sub_eq_zero.mpr h
  obtain ⟨ha, hb⟩ := affine_eq_zero_coefficients hP hzero
  exact ⟨sub_eq_zero.mp ha, sub_eq_zero.mp hb⟩

theorem affine_mul {P : Operator ι} (hP : P * P = 1)
    (a b c d : ℂ) :
    affine P a b * affine P c d = affine P (a * c + b * d) (a * d + b * c) := by
  simp only [affine, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    smul_add, smul_smul, mul_one, one_mul, hP, add_smul]
  simp only [mul_comm c a, mul_comm c b, mul_comm d a, mul_comm d b]
  abel

theorem star_affine {P : Operator ι} (hP : star P = P) (a b : ℂ) :
    star (affine P a b) = affine P (star a) (star b) := by
  simp [affine, hP]

end CriticalDepth
end Merged_MatrixCore

/- ===== Source block: MatrixDerivation; SHA-256 3219508fb614599074fd555a84a1d0cb5ea9073df3c606cfe3c9b7de8043837d ===== -/
section Merged_MatrixDerivation
/-!
Entrywise relative derivations and the algebraic gate-insertion product rule.
No differentiability or conjugation on an extension field is assumed here.
This supplies algebraic identities for the proposed alternative proof route;
the circuit-coordinate application remains a separate proof obligation.
-/

namespace CriticalDepth

open Matrix
open scoped BigOperators

variable {F A ι κ μ : Type*} [Field F] [CommRing A] [Algebra F A]

def matrixDerivation (D : Derivation F A A) (M : Matrix ι κ A) : Matrix ι κ A :=
  fun i j => D (M i j)

theorem matrixDerivation_zero (D : Derivation F A A) :
    matrixDerivation D (0 : Matrix ι κ A) = 0 := by
  ext i j
  simp [matrixDerivation]

theorem matrixDerivation_add (D : Derivation F A A) (M N : Matrix ι κ A) :
    matrixDerivation D (M + N) = matrixDerivation D M + matrixDerivation D N := by
  ext i j
  simp [matrixDerivation]

theorem matrixDerivation_constant (D : Derivation F A A) (M : Matrix ι κ F) :
    matrixDerivation D (M.map (algebraMap F A)) = 0 := by
  ext i j
  exact D.map_algebraMap (M i j)

theorem matrixDerivation_one [DecidableEq ι] (D : Derivation F A A) :
    matrixDerivation D (1 : Matrix ι ι A) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [matrixDerivation, Matrix.one_apply, h]

theorem matrixDerivation_mul [Fintype κ] (D : Derivation F A A)
    (M : Matrix ι κ A) (N : Matrix κ μ A) :
    matrixDerivation D (M * N) =
      matrixDerivation D M * N + M * matrixDerivation D N := by
  ext i j
  simp [matrixDerivation, Matrix.mul_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, mul_comm, add_comm]

theorem matrixDerivation_inverse [Fintype ι] [DecidableEq ι]
    (D : Derivation F A A) (U Uinv : Matrix ι ι A)
    (hU : U * Uinv = 1) (hinv : Uinv * U = 1) :
    matrixDerivation D Uinv = -(Uinv * matrixDerivation D U * Uinv) := by
  have hd : matrixDerivation D U * Uinv + U * matrixDerivation D Uinv = 0 := by
    rw [← matrixDerivation_mul, hU, matrixDerivation_one]
  have hleft := congrArg (fun M : Matrix ι ι A => Uinv * M) hd
  simp only [mul_add, mul_zero, ← mul_assoc, hinv, one_mul] at hleft
  apply eq_neg_iff_add_eq_zero.mpr
  simpa [add_comm] using hleft

/-- Two-factor logarithmic derivative identity, with inverse variables explicit. -/
theorem logarithmic_product_rule [Fintype ι] [DecidableEq ι]
    (D : Derivation F A A) (U V Uinv Vinv : Matrix ι ι A)
    (hV : V * Vinv = 1) :
    matrixDerivation D (U * V) * (Vinv * Uinv) =
      matrixDerivation D U * Uinv +
        U * (matrixDerivation D V * Vinv) * Uinv := by
  rw [matrixDerivation_mul]
  calc
    (matrixDerivation D U * V + U * matrixDerivation D V) * (Vinv * Uinv) =
        matrixDerivation D U * (V * Vinv) * Uinv +
          U * (matrixDerivation D V * Vinv) * Uinv := by noncomm_ring
    _ = _ := by rw [hV]; simp

end CriticalDepth
end Merged_MatrixDerivation

/- ===== Source block: AlgebraicFrame; SHA-256 37fb04eec13069e9226575e12cb8d3a3910fc8555f84dec7ac3267476dee2a19 ===== -/
section Merged_AlgebraicFrame
/-!
# Algebraic frame transfer and finite gate insertions

Inverse matrices are explicit variables. The frame identities themselves do
not require the encoding matrices to be constant under a derivation; the
subsequent circuit application may impose that additional property.

The insertion theorem uses an actual finite sum over the list's gate indices.
The list product is taken in its written matrix order; physical execution
order is obtained by supplying the corresponding reversed gate list.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker BigOperators

variable {F K Phys Code Log Gauge : Type*}
variable [Field F] [Field K] [Algebra F K]
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Code] [DecidableEq Code]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem algebraic_forward_of_backward_frame
    (E : Matrix Code Phys K) (V : Matrix Phys Code K)
    (U Ui H : Matrix Phys Phys K) (T Ti : Matrix Code Code K)
    (hUUi : U * Ui = 1) (_hUiU : Ui * U = 1)
    (hTTi : T * Ti = 1) (_hTiT : Ti * T = 1)
    (hencoded : U * V = V * T) (hdual : E * U = T * E) :
    E * H * V = T * (E * Ui * H * U * V) * Ti := by
  have hleft : T * E * Ui = E := by
    calc
      T * E * Ui = (E * U) * Ui := by rw [← hdual]
      _ = E := by rw [Matrix.mul_assoc, hUUi, Matrix.mul_one]
  have hright : U * V * Ti = V := by
    rw [hencoded, Matrix.mul_assoc, hTTi, Matrix.mul_one]
  calc
    E * H * V = (T * E * Ui) * H * (U * V * Ti) := by rw [hleft, hright]
    _ = T * (E * Ui * H * U * V) * Ti := by simp only [Matrix.mul_assoc]

theorem algebraic_gauge_kronecker_conjugation
    (W Wi : Matrix Log Log K) (Z Zi N : Matrix Gauge Gauge K)
    (hWWi : W * Wi = 1) :
    (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) =
      (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by
  calc
    (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) =
        ((W * 1) ⊗ₖ (Z * N)) * (Wi ⊗ₖ Zi) := by
          rw [← Matrix.mul_kronecker_mul W (1 : Matrix Log Log K) Z N]
    _ = ((W * 1) * Wi) ⊗ₖ ((Z * N) * Zi) :=
      (Matrix.mul_kronecker_mul (W * 1) Wi (Z * N) Zi).symm
    _ = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by rw [mul_one, hWWi]

theorem algebraic_gauge_frame_transfer
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui H : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi N : Matrix Gauge Gauge K)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hbackward : E * Ui * H * U * V = (1 : Matrix Log Log K) ⊗ₖ N) :
    E * H * V = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) := by
  have hTTi : (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) = 1 := by
    rw [← Matrix.mul_kronecker_mul W Wi Z Zi, hWWi, hZZi,
      Matrix.one_kronecker_one]
  have hTiT : (Wi ⊗ₖ Zi) * (W ⊗ₖ Z) = 1 := by
    rw [← Matrix.mul_kronecker_mul Wi W Zi Z, hWiW, hZiZ,
      Matrix.one_kronecker_one]
  calc
    E * H * V = (W ⊗ₖ Z) * (E * Ui * H * U * V) * (Wi ⊗ₖ Zi) :=
      algebraic_forward_of_backward_frame E V U Ui H (W ⊗ₖ Z) (Wi ⊗ₖ Zi)
        hUUi hUiU hTTi hTiT hencoded hdual
    _ = (W ⊗ₖ Z) * ((1 : Matrix Log Log K) ⊗ₖ N) * (Wi ⊗ₖ Zi) := by
      rw [hbackward]
    _ = (1 : Matrix Log Log K) ⊗ₖ (Z * N * Zi) :=
      algebraic_gauge_kronecker_conjugation W Wi Z Zi N hWWi

section GateInsertions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev GateWithInverse (ι : Type*) (K : Type*) :=
  Matrix ι ι K × Matrix ι ι K

def gatePairProduct (gates : List (GateWithInverse ι K)) : Matrix ι ι K :=
  (gates.map Prod.fst).prod

def gatePairInverseProduct (gates : List (GateWithInverse ι K)) : Matrix ι ι K :=
  (gates.reverse.map Prod.snd).prod

@[simp] theorem gatePairProduct_nil : gatePairProduct ([] : List (GateWithInverse ι K)) = 1 := by
  simp [gatePairProduct]

@[simp] theorem gatePairInverseProduct_nil :
    gatePairInverseProduct ([] : List (GateWithInverse ι K)) = 1 := by
  simp [gatePairInverseProduct]

@[simp] theorem gatePairProduct_cons
    (p : GateWithInverse ι K) (gates : List (GateWithInverse ι K)) :
    gatePairProduct (p :: gates) = p.1 * gatePairProduct gates := by
  simp [gatePairProduct]

@[simp] theorem gatePairInverseProduct_cons
    (p : GateWithInverse ι K) (gates : List (GateWithInverse ι K)) :
    gatePairInverseProduct (p :: gates) = gatePairInverseProduct gates * p.2 := by
  simp [gatePairInverseProduct, List.reverse_cons, List.map_append, List.prod_append]

theorem gatePairProduct_mutual_inverse
    (gates : List (GateWithInverse ι K))
    (hgate : ∀ p ∈ gates, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1) :
    gatePairProduct gates * gatePairInverseProduct gates = 1 ∧
      gatePairInverseProduct gates * gatePairProduct gates = 1 := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      simp
  | cons p gates ih =>
      intro hgate
      have hp := hgate p (by simp)
      have hg : ∀ q ∈ gates, q.1 * q.2 = 1 ∧ q.2 * q.1 = 1 := by
        intro q hq
        exact hgate q (by simp [hq])
      obtain ⟨hprod, hinv⟩ := ih hg
      simp only [gatePairProduct_cons, gatePairInverseProduct_cons]
      constructor
      · calc
          (p.1 * gatePairProduct gates) * (gatePairInverseProduct gates * p.2) =
              p.1 * (gatePairProduct gates * gatePairInverseProduct gates) * p.2 := by
                simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hprod, mul_one, hp.1]
      · calc
          (gatePairInverseProduct gates * p.2) * (p.1 * gatePairProduct gates) =
              gatePairInverseProduct gates * (p.2 * p.1) * gatePairProduct gates := by
                simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hp.2, mul_one, hinv]

/-- A particular actual conjugated insertion, indexed by the finite gate list. -/
def gateInsertionAt (D : Derivation F K K) :
    (gates : List (GateWithInverse ι K)) → Fin gates.length → Matrix ι ι K
  | [], i => Fin.elim0 i
  | p :: gates, i =>
    Fin.cases (matrixDerivation D p.1 * p.2)
      (fun j => p.1 * gateInsertionAt D gates j * p.2) i

theorem gateInsertion_sum_cons
    (D : Derivation F K K) (p : GateWithInverse ι K)
    (gates : List (GateWithInverse ι K)) :
    (∑ i : Fin (p :: gates).length, gateInsertionAt D (p :: gates) i) =
      matrixDerivation D p.1 * p.2 +
        p.1 * (∑ i : Fin gates.length, gateInsertionAt D gates i) * p.2 := by
  change (∑ i : Fin (gates.length + 1), gateInsertionAt D (p :: gates) i) = _
  rw [Fin.sum_univ_succ]
  simp only [gateInsertionAt, Fin.cases_zero, Fin.cases_succ,
    Finset.mul_sum, Finset.sum_mul]

/-- The genuine finite gate-insertion expansion, with no assumed generator identity. -/
theorem logarithmic_gateProduct_insertion_sum
    (D : Derivation F K K) (gates : List (GateWithInverse ι K))
    (hgate : ∀ p ∈ gates, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1) :
    matrixDerivation D (gatePairProduct gates) * gatePairInverseProduct gates =
      ∑ i : Fin gates.length, gateInsertionAt D gates i := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      simp [matrixDerivation_one]
  | cons p gates ih =>
      intro hgate
      have hg : ∀ q ∈ gates, q.1 * q.2 = 1 ∧ q.2 * q.1 = 1 := by
        intro q hq
        exact hgate q (by simp [hq])
      have hprod := (gatePairProduct_mutual_inverse gates hg).1
      rw [gatePairProduct_cons, gatePairInverseProduct_cons,
        logarithmic_product_rule D p.1 (gatePairProduct gates) p.2
          (gatePairInverseProduct gates) hprod,
        gateInsertion_sum_cons]
      rw [ih hg]

end GateInsertions
end CriticalDepth
end Merged_AlgebraicFrame

/- ===== Source block: AlgebraicRigidity; SHA-256 f9affd32baf73d575ffdaaf15dfab4ea4a4a31e1dcd960cfbbb92bd4b8ebbb2b ===== -/
section Merged_AlgebraicRigidity
/-!
# Algebraic infinitesimal rigidity of an encoded factorization

All matrices in this module have entries in the extension field `K`.
Inverse matrices and the encoding dual are explicit algebraic variables;
there is no conjugation operation on `K` and no implicit Hermitian premise.
The circuit-support and distance argument producing gauge-only compression
is a separate obligation.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker

variable {F K Phys Log Gauge : Type*}
variable [Field F] [Field K] [Algebra F K]
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem matrixDerivation_kronecker (D : Derivation F K K)
    (A : Matrix Log Log K) (B : Matrix Gauge Gauge K) :
    matrixDerivation D (A ⊗ₖ B) =
      matrixDerivation D A ⊗ₖ B + A ⊗ₖ matrixDerivation D B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [matrixDerivation, Matrix.kronecker_apply, Derivation.leibniz,
    smul_eq_mul, mul_comm, add_comm]

/-- One gauge diagonal block forces the logical generator to be scalar. -/
theorem scalarity_of_tensor_generator_overField [Nonempty Gauge]
    (A : Matrix Log Log K) (B M : Matrix Gauge Gauge K)
    (h : A ⊗ₖ (1 : Matrix Gauge Gauge K) + (1 : Matrix Log Log K) ⊗ₖ B =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∃ scalar : K, A = scalar • (1 : Matrix Log Log K) := by
  classical
  let j : Gauge := Classical.choice inferInstance
  refine ⟨M j j - B j j, ?_⟩
  ext i k
  have hh := congrArg (fun X : Matrix (Log × Gauge) (Log × Gauge) K => X (i, j) (k, j)) h
  by_cases hik : i = k
  · subst k
    simp [Matrix.kronecker_apply] at hh ⊢
    linear_combination hh
  · simpa [Matrix.kronecker_apply, Matrix.one_apply, hik] using hh

/-- The encoded logarithmic derivative splits into logical and gauge terms. -/
theorem encoded_logarithmic_generator
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (_hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (_hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (_hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (_hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (_hdual : E * U = (W ⊗ₖ Z) * E) :
    E * (matrixDerivation D U * Ui) * V =
      (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
        (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) := by
  have hTTi : (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) = 1 := by
    rw [← Matrix.mul_kronecker_mul W Wi Z Zi, hWWi, hZZi,
      Matrix.one_kronecker_one]
  have hUiV : Ui * V = V * (Wi ⊗ₖ Zi) := by
    calc
      Ui * V = (Ui * V) * ((W ⊗ₖ Z) * (Wi ⊗ₖ Zi)) := by rw [hTTi]; simp
      _ = Ui * (V * (W ⊗ₖ Z)) * (Wi ⊗ₖ Zi) := by simp only [Matrix.mul_assoc]
      _ = Ui * (U * V) * (Wi ⊗ₖ Zi) := by rw [← hencoded]
      _ = V * (Wi ⊗ₖ Zi) := by simp only [← Matrix.mul_assoc, hUiU, Matrix.one_mul]
  have hdUV : matrixDerivation D U * V = V * matrixDerivation D (W ⊗ₖ Z) := by
    have hh := congrArg (matrixDerivation D) hencoded
    simpa only [matrixDerivation_mul, hV, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add] using hh
  calc
    E * (matrixDerivation D U * Ui) * V = E * (matrixDerivation D U * (Ui * V)) := by
      simp only [Matrix.mul_assoc]
    _ = E * (matrixDerivation D U * (V * (Wi ⊗ₖ Zi))) := by rw [hUiV]
    _ = E * (matrixDerivation D U * V) * (Wi ⊗ₖ Zi) := by
      simp only [Matrix.mul_assoc]
    _ = E * (V * matrixDerivation D (W ⊗ₖ Z)) * (Wi ⊗ₖ Zi) := by rw [hdUV]
    _ = matrixDerivation D (W ⊗ₖ Z) * (Wi ⊗ₖ Zi) := by
      simp only [← Matrix.mul_assoc, hEV, one_mul]
    _ = (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
        (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) := by
      rw [matrixDerivation_kronecker, add_mul,
        ← Matrix.mul_kronecker_mul (matrixDerivation D W) Wi Z Zi,
        ← Matrix.mul_kronecker_mul W Wi (matrixDerivation D Z) Zi,
        hWWi, hZZi]

theorem matrixDerivation_of_scalar_logarithmic_derivative
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hWiW : Wi * W = 1)
    (hscalar : matrixDerivation D W * Wi = scalar • (1 : Matrix Log Log K)) :
    matrixDerivation D W = scalar • W := by
  calc
    matrixDerivation D W = (matrixDerivation D W * Wi) * W := by
      simp only [Matrix.mul_assoc, hWiW, mul_one]
    _ = (scalar • (1 : Matrix Log Log K)) * W := by rw [hscalar]
    _ = scalar • W := by simp [smul_mul_assoc]

theorem matrixDerivation_inverse_of_scalar_derivative
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hscalar : matrixDerivation D W = scalar • W) :
    matrixDerivation D Wi = -(scalar • Wi) := by
  rw [matrixDerivation_inverse D W Wi hWWi hWiW, hscalar]
  simp only [mul_smul_comm, smul_mul_assoc, ← Matrix.mul_assoc, hWiW, one_mul]

theorem projective_coordinates_derivation_zero_of_scalar_derivatives
    (D : Derivation F K K) (W Wi : Matrix Log Log K) (scalar : K)
    (hW : matrixDerivation D W = scalar • W)
    (hWi : matrixDerivation D Wi = -(scalar • Wi)) :
    ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  intro a b c d
  have hw := congrArg (fun A : Matrix Log Log K => A a b) hW
  have hwi := congrArg (fun A : Matrix Log Log K => A c d) hWi
  change D (W a b) = scalar * W a b at hw
  change D (Wi c d) = -(scalar * Wi c d) at hwi
  rw [D.leibniz, hw, hwi]
  simp only [smul_eq_mul]
  ring

/--
Gauge-only compression kills every coordinate of the logical conjugation
action. The compression premise must still be established from the concrete
circuit and code-distance hypotheses.
-/
theorem encoded_logarithmic_rigidity [Nonempty Gauge]
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi M : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hcompression : E * (matrixDerivation D U * Ui) * V =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∃ scalar : K,
      matrixDerivation D W * Wi = scalar • (1 : Matrix Log Log K) ∧
      matrixDerivation D W = scalar • W ∧
      matrixDerivation D Wi = -(scalar • Wi) ∧
      ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  have hgenerator := encoded_logarithmic_generator D E V U Ui W Wi Z Zi
    hEV hE hV hUUi hUiU hWWi hWiW hZZi hZiZ hencoded hdual
  have htensor : (matrixDerivation D W * Wi) ⊗ₖ (1 : Matrix Gauge Gauge K) +
      (1 : Matrix Log Log K) ⊗ₖ (matrixDerivation D Z * Zi) =
        (1 : Matrix Log Log K) ⊗ₖ M := hgenerator.symm.trans hcompression
  obtain ⟨scalar, hscalar⟩ := scalarity_of_tensor_generator_overField
    (matrixDerivation D W * Wi) (matrixDerivation D Z * Zi) M htensor
  have hdW := matrixDerivation_of_scalar_logarithmic_derivative D W Wi scalar hWiW hscalar
  have hdWi := matrixDerivation_inverse_of_scalar_derivative D W Wi scalar hWWi hWiW hdW
  exact ⟨scalar, hscalar, hdW, hdWi,
    projective_coordinates_derivation_zero_of_scalar_derivatives D W Wi scalar hdW hdWi⟩

theorem encoded_projective_coordinates_derivation_zero [Nonempty Gauge]
    (D : Derivation F K K)
    (E : Matrix (Log × Gauge) Phys K) (V : Matrix Phys (Log × Gauge) K)
    (U Ui : Matrix Phys Phys K) (W Wi : Matrix Log Log K)
    (Z Zi M : Matrix Gauge Gauge K)
    (hEV : E * V = 1)
    (hE : matrixDerivation D E = 0) (hV : matrixDerivation D V = 0)
    (hUUi : U * Ui = 1) (hUiU : Ui * U = 1)
    (hWWi : W * Wi = 1) (hWiW : Wi * W = 1)
    (hZZi : Z * Zi = 1) (hZiZ : Zi * Z = 1)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hdual : E * U = (W ⊗ₖ Z) * E)
    (hcompression : E * (matrixDerivation D U * Ui) * V =
      (1 : Matrix Log Log K) ⊗ₖ M) :
    ∀ a b c d : Log, D (W a b * Wi c d) = 0 := by
  obtain ⟨scalar, hscalar, hdW, hdWi, hcoords⟩ :=
    encoded_logarithmic_rigidity D E V U Ui W Wi Z Zi M
      hEV hE hV hUUi hUiU hWWi hWiW hZZi hZiZ hencoded hdual hcompression
  exact hcoords

end CriticalDepth
end Merged_AlgebraicRigidity

/- ===== Source block: ArithmeticExamples; SHA-256 9036c8ed051c88bcd71dafd1b7c086d2070e839800a070b9c06ff5e3988cc9bc ===== -/
section Merged_ArithmeticExamples
/-! Real calls of arithmetic dependencies, not examples of quantum codes. -/

namespace CriticalDepth.ArithmeticExamples

open CriticalDepth.Arithmetic

theorem binary_distance_eight_depth_four : 4 < criticalDepth 2 8 := by
  apply (below_threshold_iff 2 8 4 (by decide)).mpr
  decide

theorem binary_distance_eight_depth_five : ¬ 5 < criticalDepth 2 8 := by
  intro h
  have hp := (below_threshold_iff 2 8 5 (by decide)).mp h
  have hn : ¬ 2 ^ ceilHalf 5 < 8 := by decide
  exact hn hp

theorem ternary_distance_eight_compression : compressedWeight 3 8 1 = 3 := by
  decide

theorem binary_distance_eight_compression_bound :
    compressedWeight 2 8 (Nat.clog 2 8 - 1) ≤ 2 := by
  exact compressedWeight_at_clog_pred_le 2 8 (by decide) (by decide)

theorem middle_layer_call : min 3 (4 - 3 + 1) ≤ ceilHalf 4 := by
  exact layer_min_le_ceilHalf 4 3 (by decide) (by decide)

theorem synthesis_call :
    (Nat.clog 3 8 - 1) + 1 + (Nat.clog 3 8 - 1) = criticalDepth 3 8 := by
  exact synthesis_depth_at_clog 3 8 (by decide) (by decide)

theorem logarithm_bridge_call :
    Nat.clog 3 8 = ⌈Real.log (8 : ℝ) / Real.log (3 : ℝ)⌉₊ := by
  exact clog_eq_natCeil_log 3 8

theorem unary_at_depth_one_thousand : (1 : ℕ) ^ ceilHalf 1000 < 2 := by
  exact unary_cone_bound 2 1000 (by decide)

theorem arity_at_least_distance_call : Nat.clog 8 8 = 1 := by
  exact clog_eq_one_of_distance_le_arity 8 8 (by decide) (by decide) (by decide)

#print CriticalDepth.Arithmetic.below_threshold_iff
#print CriticalDepth.Arithmetic.compressedWeight_at_clog_pred_le
#print CriticalDepth.Arithmetic.ceilDiv_le_iff
#print axioms CriticalDepth.Arithmetic.below_threshold_iff
#print axioms CriticalDepth.Arithmetic.clog_eq_natCeil_log
#print axioms CriticalDepth.Arithmetic.below_threshold_log_iff
#print axioms CriticalDepth.Arithmetic.layer_min_le_ceilHalf
#print axioms CriticalDepth.Arithmetic.unary_cone_bound
#print axioms CriticalDepth.Arithmetic.ceilDiv_comp
#print axioms CriticalDepth.Arithmetic.ceilDiv_le_iff
#print axioms CriticalDepth.Arithmetic.compressedWeight_eq_ceilDiv_pow
#print axioms CriticalDepth.Arithmetic.compressedWeight_at_clog_pred_le
#print axioms CriticalDepth.Arithmetic.clog_eq_one_of_distance_le_arity
#print axioms CriticalDepth.Arithmetic.synthesis_depth_at_clog
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_depth_four
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_depth_five
#print axioms CriticalDepth.ArithmeticExamples.binary_distance_eight_compression_bound
#print axioms CriticalDepth.ArithmeticExamples.middle_layer_call
#print axioms CriticalDepth.ArithmeticExamples.synthesis_call
#print axioms CriticalDepth.ArithmeticExamples.logarithm_bridge_call
#print axioms CriticalDepth.ArithmeticExamples.unary_at_depth_one_thousand
#print axioms CriticalDepth.ArithmeticExamples.arity_at_least_distance_call

end CriticalDepth.ArithmeticExamples
end Merged_ArithmeticExamples

/- ===== Source block: Compression; SHA-256 433e1c3d42d5d16c3e065657f137929f6b307dba343f4c4aa67a42245a6fddff ===== -/
section Merged_Compression
/-!
The two-sided frame-transfer step and logical scalarity.

Rectangular encoding matrices use `conjTranspose` explicitly. No isometry
hypothesis is needed for the frame identity itself. The later specialization
uses unitary logical and gauge factors to undo the change of frame.
-/

namespace CriticalDepth

open Matrix
open scoped Kronecker

variable {Phys Code Log Gauge : Type*}
variable [Fintype Phys] [DecidableEq Phys]
variable [Fintype Code] [DecidableEq Code]
variable [Fintype Log] [DecidableEq Log]
variable [Fintype Gauge] [DecidableEq Gauge]

theorem encoded_adjoint
    (U : Operator Phys) (V : Matrix Phys Code ℂ) (T : Operator Code)
    (hencoded : U * V = V * T) :
    V.conjTranspose * U.conjTranspose = T.conjTranspose * V.conjTranspose := by
  have h := congrArg Matrix.conjTranspose hencoded
  simpa only [Matrix.conjTranspose_mul] using h

/-- Compression in the backward frame is conjugation of forward compression. -/
theorem compressed_backward_frame
    (U H : Operator Phys) (V : Matrix Phys Code ℂ) (T : Operator Code)
    (hencoded : U * V = V * T) :
    V.conjTranspose * U.conjTranspose * H * U * V =
      T.conjTranspose * (V.conjTranspose * H * V) * T := by
  calc
    V.conjTranspose * U.conjTranspose * H * U * V =
        (V.conjTranspose * U.conjTranspose) * H * (U * V) := by
          simp only [Matrix.mul_assoc]
    _ = (T.conjTranspose * V.conjTranspose) * H * (V * T) := by
      rw [encoded_adjoint U V T hencoded, hencoded]
    _ = T.conjTranspose * (V.conjTranspose * H * V) * T := by
      simp only [Matrix.mul_assoc]

theorem compressed_forward_of_backward
    (U H : Operator Phys) (V : Matrix Phys Code ℂ) (T B : Operator Code)
    (hencoded : U * V = V * T)
    (hT : T * T.conjTranspose = 1)
    (hbackward : V.conjTranspose * U.conjTranspose * H * U * V = B) :
    V.conjTranspose * H * V = T * B * T.conjTranspose := by
  have hb : T.conjTranspose * (V.conjTranspose * H * V) * T = B := by
    rw [← compressed_backward_frame U H V T hencoded]
    exact hbackward
  calc
    V.conjTranspose * H * V =
        (T * T.conjTranspose) * (V.conjTranspose * H * V) *
          (T * T.conjTranspose) := by rw [hT]; simp
    _ = T * (T.conjTranspose * (V.conjTranspose * H * V) * T) * T.conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = T * B * T.conjTranspose := by rw [hb]

theorem conjTranspose_kronecker_operators
    (W : Operator Log) (Z : Operator Gauge) :
    (W ⊗ₖ Z).conjTranspose = W.conjTranspose ⊗ₖ Z.conjTranspose := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.conjTranspose_apply, Matrix.kronecker_apply, map_mul, mul_comm]

theorem kronecker_right_unitary
    (W : Operator Log) (Z : Operator Gauge)
    (hW : W * W.conjTranspose = 1) (hZ : Z * Z.conjTranspose = 1) :
    (W ⊗ₖ Z) * (W ⊗ₖ Z).conjTranspose = 1 := by
  calc
    (W ⊗ₖ Z) * (W ⊗ₖ Z).conjTranspose =
        (W ⊗ₖ Z) * (W.conjTranspose ⊗ₖ Z.conjTranspose) := by
          rw [conjTranspose_kronecker_operators]
    _ = (W * W.conjTranspose) ⊗ₖ (Z * Z.conjTranspose) :=
      (Matrix.mul_kronecker_mul W W.conjTranspose Z Z.conjTranspose).symm
    _ = 1 := by rw [hW, hZ, Matrix.one_kronecker_one]

theorem gauge_kronecker_conjugation
    (W : Operator Log) (Z N : Operator Gauge)
    (hW : W * W.conjTranspose = 1) :
    (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose =
      (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
  calc
    (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose =
        ((W * 1) ⊗ₖ (Z * N)) * (W.conjTranspose ⊗ₖ Z.conjTranspose) := by
          rw [← Matrix.mul_kronecker_mul W (1 : Operator Log) Z N,
            conjTranspose_kronecker_operators]
    _ = ((W * 1) * W.conjTranspose) ⊗ₖ ((Z * N) * Z.conjTranspose) :=
      (Matrix.mul_kronecker_mul (W * 1) W.conjTranspose (Z * N) Z.conjTranspose).symm
    _ = (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
      rw [mul_one, hW]

/--
The manuscript's backward-detectable insertion has gauge-only compression in
the forward frame. The physical-unitary hypothesis is retained explicitly;
the matrix identity in fact needs only the encoded equation and unitarity of
the two encoded factors.
-/
theorem gauge_frame_transfer
    (U H : Operator Phys) (V : Matrix Phys (Log × Gauge) ℂ)
    (W : Operator Log) (Z N : Operator Gauge)
    (_hU : IsUnitary U) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : U * V = V * (W ⊗ₖ Z))
    (hbackward : V.conjTranspose * U.conjTranspose * H * U * V =
      (1 : Operator Log) ⊗ₖ N) :
    V.conjTranspose * H * V =
      (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) := by
  have hWright : W * W.conjTranspose = 1 := hW.2
  have hZright : Z * Z.conjTranspose = 1 := hZ.2
  calc
    V.conjTranspose * H * V =
        (W ⊗ₖ Z) * ((1 : Operator Log) ⊗ₖ N) * (W ⊗ₖ Z).conjTranspose := by
          exact compressed_forward_of_backward U H V (W ⊗ₖ Z) ((1 : Operator Log) ⊗ₖ N)
            hencoded (kronecker_right_unitary W Z hWright hZright) hbackward
    _ = (1 : Operator Log) ⊗ₖ (Z * N * Z.conjTranspose) :=
      gauge_kronecker_conjugation W Z N hWright

/--
An individual gauge diagonal block already forces logical scalarity.
Consequently this statement needs no partial-trace normalization or division.
-/
theorem scalarity_of_tensor_generator
    [Nonempty Gauge] (A : Operator Log) (B M : Operator Gauge)
    (h : A ⊗ₖ (1 : Operator Gauge) + (1 : Operator Log) ⊗ₖ B =
      (1 : Operator Log) ⊗ₖ M) : IsScalar A := by
  classical
  let j : Gauge := Classical.choice inferInstance
  refine ⟨M j j - B j j, ?_⟩
  ext i k
  have hh := congrArg (fun X : Operator (Log × Gauge) => X (i, j) (k, j)) h
  by_cases hik : i = k
  · subst k
    simp [Matrix.kronecker_apply] at hh ⊢
    linear_combination hh
  · simpa [Matrix.kronecker_apply, Matrix.one_apply, hik] using hh

end CriticalDepth
end Merged_Compression

/- ===== Source block: FieldConstants; SHA-256 0ca698d92f3ee902c1727df10365e6e6d2258540356acd4b644c0817ef8f2b61 ===== -/
section Merged_FieldConstants
/-!
# Differential constants in characteristic-zero field extensions

The principal statement says that an element annihilated by every base-linear
derivation of a characteristic-zero field extension is algebraic over the
base field. The argument includes a purported transcendental element in a
transcendence basis and extends its polynomial partial derivation through
localization and the separable algebraic extension. The extension mechanism
is developed in `CriticalDepth.DerivationExtension`.

The preceding differential-structure lemmas also record finite-dimensional
extension and uniqueness. No finite-generation hypothesis on the ambient
field is used in the principal statement. In particular,
`Algebra.FiniteType` on the final field is not used as a substitute for
finite generation as a field extension.
-/

namespace CriticalDepth

universe u v w

/-- The differential structure whose derivation is identically zero. -/
def zeroDifferential (R : Type u) [CommRing R] : Differential R :=
  ⟨0⟩

/-- Compatibility of a differential structure with a constant base field. -/
def CompatibleWithZero
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (d : Differential K) : Prop :=
  letI : Differential F := zeroDifferential F
  letI : Differential K := d
  DifferentialAlgebra F K

/-- An element is constant for every derivation extending the zero
derivation of the base field. -/
def IsDifferentialConstant
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (x : K) : Prop :=
  ∀ d : Differential K,
    CompatibleWithZero F K d → @Differential.deriv K _ d x = 0

theorem zeroDifferential_compatible
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K] :
    CompatibleWithZero F K (zeroDifferential K) := by
  letI : Differential F := zeroDifferential F
  letI : Differential K := zeroDifferential K
  change DifferentialAlgebra F K
  refine ⟨?_⟩
  intro a
  change (0 : K) = algebraMap F K (0 : F)
  exact (map_zero (algebraMap F K)).symm

/-- Every scalar from the base field is a differential constant. -/
theorem isDifferentialConstant_algebraMap
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    (a : F) :
    IsDifferentialConstant F K (algebraMap F K a) := by
  intro d h
  letI : Differential F := zeroDifferential F
  letI : Differential K := d
  letI : DifferentialAlgebra F K := h
  change Differential.deriv (algebraMap F K a) = 0
  rw [DifferentialAlgebra.deriv_algebraMap]
  change algebraMap F K (0 : F) = 0
  exact map_zero (algebraMap F K)

/-- A differential structure extends across a finite-dimensional extension of
characteristic-zero fields. This is the actual existence statement used by
the proposed differential-constants argument. -/
theorem exists_compatible_differential
    (F : Type u) (K : Type v)
    [Field F] [Differential F] [CharZero F]
    [Field K] [Algebra F K] [FiniteDimensional F K] :
    ∃ d : Differential K, letI := d; DifferentialAlgebra F K := by
  refine ⟨Differential.differentialFiniteDimensional F K, ?_⟩
  exact Differential.differentialAlgebraFiniteDimensional (F := F) (K := K)

/-- Finite-dimensional extensions of a constant characteristic-zero field
have no nonzero compatible derivation. This is the algebraic direction of
the intended differential-constants criterion. -/
theorem isDifferentialConstant_of_finiteDimensional
    (F : Type u) (K : Type v)
    [Field F] [CharZero F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (x : K) :
    IsDifferentialConstant F K x := by
  intro d h
  letI : Differential F := zeroDifferential F
  letI : Unique {e : Differential K // CompatibleWithZero F K e} :=
    Differential.uniqueDifferentialAlgebraFiniteDimensional (F := F) (K := K)
  have heq :
      (⟨d, h⟩ : {e : Differential K // CompatibleWithZero F K e}) =
        ⟨zeroDifferential K, zeroDifferential_compatible F K⟩ :=
    Subsingleton.elim _ _
  have hd : d = zeroDifferential K := congrArg Subtype.val heq
  rw [hd]
  rfl

section DerivationConstants

open scoped IntermediateField.algebraAdjoinAdjoin

variable (F : Type u) (K : Type v)
variable [Field F] [Field K] [CharZero K] [Algebra F K]

/-- A transcendence-basis polynomial algebra maps formally etale to the
ambient characteristic-zero field: first localize to its field of
fractions, then use the separable algebraic extension. -/
theorem formallyEtale_adjoin_of_transcendenceBasis
    {ι : Type w} (b : ι → K) (hb : IsTranscendenceBasis F b) :
    Algebra.FormallyEtale (Algebra.adjoin F (Set.range b)) K := by
  let S := Algebra.adjoin F (Set.range b)
  let L := IntermediateField.adjoin F (Set.range b)
  letI : Algebra S L := by
    change Algebra (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b))
    infer_instance
  letI : IsScalarTower S L K := by
    change IsScalarTower (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b)) K
    infer_instance
  letI : IsFractionRing S L := by
    change IsFractionRing (Algebra.adjoin F (Set.range b))
      (IntermediateField.adjoin F (Set.range b))
    infer_instance
  letI : Algebra.IsAlgebraic L K := hb.isAlgebraic_field
  letI : Algebra.IsSeparable L K := inferInstance
  letI : Algebra.FormallyEtale L K :=
    Algebra.FormallyEtale.of_isSeparable L K
  letI : Algebra.FormallyEtale S L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  exact Algebra.FormallyEtale.comp S L K

/-- In characteristic zero, an element annihilated by every base-linear
derivation is algebraic over the base field. No finite-generation
hypothesis on the ambient field is required. -/
theorem isAlgebraic_of_forall_derivation_eq_zero
    (a : K) (h : ∀ d : Derivation F K K, d a = 0) :
    IsAlgebraic F a := by
  classical
  by_contra ha
  have htrans : Transcendental F a := ha
  have hsingle : AlgebraicIndepOn F id ({a} : Set K) := by
    letI : Subsingleton ({a} : Set K) := ⟨by
      intro x y
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp x.property).trans
        (Set.mem_singleton_iff.mp y.property).symm⟩
    change AlgebraicIndependent F (Subtype.val : ({a} : Set K) → K)
    exact (algebraicIndependent_singleton_iff
      (R := F) (x := (Subtype.val : ({a} : Set K) → K))
      (⟨a, by simp⟩ : ({a} : Set K))).2 htrans
  obtain ⟨t, hst, hb⟩ := exists_isTranscendenceBasis_superset hsingle
  let i : t := ⟨a, hst (by simp)⟩
  let b : t → K := Subtype.val
  let S := Algebra.adjoin F (Set.range b)
  let e : MvPolynomial t F ≃ₐ[F] S := hb.1.aevalEquiv
  letI : Algebra.FormallyEtale S K :=
    formallyEtale_adjoin_of_transcendenceBasis F K b hb
  let d : Derivation F K K :=
    polynomialCoordinateDerivationViaEquiv F S K t e i
  have hcoord : algebraMap S K (e (MvPolynomial.X i)) = a := by
    change algebraMap S K (hb.1.aevalEquiv (MvPolynomial.X i)) = a
    rw [hb.1.algebraMap_aevalEquiv]
    simp [i]
  have hdi : d (algebraMap S K (e (MvPolynomial.X i))) = 1 :=
    polynomialCoordinateDerivationViaEquiv_X F S K t e i
  rw [hcoord] at hdi
  exact one_ne_zero (hdi.symm.trans (h d))

end DerivationConstants

end CriticalDepth
end Merged_FieldConstants

/- ===== Source block: ManuscriptStatements; SHA-256 a83fefc1928efbc9adf5e348aa37dfae403c5313c5de326b1486e5dbd626666a ===== -/
section Merged_ManuscriptStatements
/-!
# Concrete manuscript objects and original proof obligations

Source SHA-256: ec18f629bd6bfc770f470d71ed995de2743d1bf1368dfee7a4366edb43ac3138.
The definitions `theoremOne` and `theoremTwo` below RECORD propositions. They
are not proof declarations, axioms, or accepted proofs of the manuscript.
Their status remains open until separately named theorems establish them.

All matrix scalars are complex. The physical tensor basis retains every site.
Logical equivalence removes one global unit-modulus scalar. Correctability
quantifies over every supported operator, not just Pauli operators.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker BigOperators

abbrev PhysicalBasis (n : ℕ) (dim : Fin n → ℕ) := (i : Fin n) → Fin (dim i)

abbrev LocalBasis {n : ℕ} (dim : Fin n → ℕ) (S : Finset (Fin n)) :=
  (i : S) → Fin (dim i.1)

/-- Exact tensor-local embedding, with the identity on every complementary site. -/
def localEmbed {n : ℕ} {dim : Fin n → ℕ} (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) : Operator (PhysicalBasis n dim) := by
  classical
  exact fun x y =>
    if ∀ i, i ∉ S → x i = y i then
      A (fun i => x i.1) (fun i => y i.1)
    else 0

def SupportedOn {n : ℕ} {dim : Fin n → ℕ}
    (O : Operator (PhysicalBasis n dim)) (S : Finset (Fin n)) : Prop :=
  ∃ A : Operator (LocalBasis dim S), O = localEmbed S A

/-- The logical index precedes the gauge index, as in V : H_L ⊗ H_G → H. -/
structure Code (n : ℕ) (dim : Fin n → ℕ) (K g : ℕ) where
  encoding : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ
  isometry : encoding.conjTranspose * encoding = 1

def GaugeOnly {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (O : Operator (PhysicalBasis n dim)) : Prop :=
  ∃ M : Operator (Fin g),
    C.encoding.conjTranspose * O * C.encoding = (1 : Operator (Fin K)) ⊗ₖ M

def DetectsBelow {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card < d →
    ∀ O : Operator (PhysicalBasis n dim), SupportedOn O S → GaugeOnly C O

/-- Actual distance includes an undetectable operator of precisely this weight. -/
def HasActualDistance {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (d : ℕ) : Prop :=
  DetectsBelow C d ∧ ∃ S : Finset (Fin n), S.card = d ∧
    ∃ O : Operator (PhysicalBasis n dim), SupportedOn O S ∧ ¬ GaugeOnly C O

def Implements {n K g : ℕ} {dim : Fin n → ℕ} (C : Code n dim K g)
    (U : Operator (PhysicalBasis n dim)) (W : Operator (Fin K)) : Prop :=
  IsUnitary W ∧ ∃ Z : Operator (Fin g), IsUnitary Z ∧
    U * C.encoding = C.encoding * (W ⊗ₖ Z)

/-- At most n nonempty, disjoint gates, padded by supported identity gates.
The equivalence to arbitrary finite gate lists is an explicit open bridge. -/
structure Layer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  support : Fin n → Finset (Fin n)
  gate : Fin n → Operator (PhysicalBasis n dim)
  disjoint : ∀ i j, i ≠ j → Disjoint (support i) (support j)
  arity : ∀ i, (support i).card ≤ q
  locality : ∀ i, SupportedOn (gate i) (support i)
  unitary : ∀ i, IsUnitary (gate i)

def Layer.eval {n q : ℕ} {dim : Fin n → ℕ} (L : Layer n dim q) :
    Operator (PhysicalBasis n dim) := (List.ofFn L.gate).reverse.prod

abbrev Circuit (n : ℕ) (dim : Fin n → ℕ) (q h : ℕ) := Fin h → Layer n dim q

def circuitEval {n q h : ℕ} {dim : Fin n → ℕ} (c : Circuit n dim q h) :
    Operator (PhysicalBasis n dim) := (List.ofFn fun i => (c i).eval).reverse.prod

def logicalImage {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (q h : ℕ) : Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ c : Circuit n dim q h, ∃ W : Operator (Fin K),
    Implements C (circuitEval c) W ∧ projectiveClass W = a}

/-- Source Theorem 1, lines 253–265: primary finiteness claim, including q=1.
The finite-list/padded-layer bridge and non-density corollary remain obligations. -/
def theoremOne : Prop :=
  ∀ (n K g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ K → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim K g, DetectsBelow C d →
      ∀ q h : ℕ,
        ((2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) →
        (logicalImage C q h).Finite

def hInfinity {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, r = (h : ℕ∞) ∧ (logicalImage C q h).Infinite}

abbrev QubitBasis (n : ℕ) := PhysicalBasis n (fun _ => 2)

inductive SinglePauli where
  | I | X | Y | Z
  deriving DecidableEq

instance : Fintype SinglePauli where
  elems := {.I, .X, .Y, .Z}
  complete p := by cases p <;> simp

def SinglePauli.matrix : SinglePauli → Operator (Fin 2)
  | .I => 1
  | .X => !![0, 1; 1, 0]
  | .Y => !![0, -Complex.I; Complex.I, 0]
  | .Z => !![1, 0; 0, -1]

def pauliMatrix {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    Operator (QubitBasis n) :=
  fun x y => Complex.I ^ phase.val * ∏ i, (p i).matrix (x i) (y i)

def IsPauli {n : ℕ} (U : Operator (QubitBasis n)) : Prop :=
  ∃ phase : Fin 4, ∃ p : Fin n → SinglePauli, U = pauliMatrix phase p

/-- Stabilizer subspace as the simultaneous +1 eigenspace of a Pauli subgroup. -/
def IsStabilizer {n k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1) : Prop :=
  ∃ S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ),
    (∀ U ∈ S, IsPauli (U : Operator (QubitBasis n))) ∧
    Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v}

def HasContinuousLogicalSubgroup {n K : ℕ} (C : Code n (fun _ => 2) K 1)
    (q h : ℕ) : Prop :=
  ∃ W : ℝ → Operator (Fin K), Continuous W ∧
    (∀ t, IsUnitary (W t)) ∧ W 0 = 1 ∧
    (∀ s t, W (s + t) = W s * W t) ∧
    (∃ t, ¬ ProjectivelyEquivalent (W t) 1) ∧
    (∀ t, projectiveClass (W t) ∈ logicalImage C q h)

/-- Source Theorem 2, lines 403–412. This is an OPEN proposition, not a proof. -/
def theoremTwo : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinity C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
        HasContinuousLogicalSubgroup C q (Arithmetic.criticalDepth q d)

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_ManuscriptStatements

/- ===== Source block: ProjectiveFaithfulness; SHA-256 e6ebf2136ba72d2d1cff1763cf4b39fbe1a11bb4e2fcca5d3e9d6413d6d3abb9 ===== -/
section Merged_ProjectiveFaithfulness
/-!
# Faithfulness of conjugation modulo one global phase

The quantified conjugation test uses every complex matrix. Its equivalent
coordinate matrix is an explicit finite array, so finiteness of this array's
image transfers to the manuscript's actual global-phase quotient.
-/

noncomputable section

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixUnit (j k : ι) : Operator ι :=
  fun a b => if a = j ∧ b = k then 1 else 0

theorem scalar_of_commutes_matrixUnits [Nonempty ι]
    (T : Operator ι)
    (hcomm : ∀ j k : ι, T * matrixUnit j k = matrixUnit j k * T) : IsScalar T := by
  classical
  let k : ι := Classical.choice inferInstance
  refine ⟨T k k, ?_⟩
  ext i j
  have hh := congrArg (fun A : Operator ι => A i k) (hcomm j k)
  by_cases hij : i = j
  · subst j
    simpa [matrixUnit, Matrix.mul_apply, Matrix.one_apply, mul_ite, ite_mul] using hh
  · simpa [matrixUnit, Matrix.mul_apply, Matrix.one_apply, hij, mul_ite, ite_mul] using hh

theorem scalar_of_commutes_all [Nonempty ι]
    (T : Operator ι) (hcomm : ∀ M : Operator ι, T * M = M * T) : IsScalar T := by
  apply scalar_of_commutes_matrixUnits T
  intro j k
  exact hcomm (matrixUnit j k)

theorem unitary_smul_phase [Nonempty ι]
    {U V : Operator ι} {z : ℂ} (hU : IsUnitary U) (hV : IsUnitary V)
    (hUV : U = z • V) : star z * z = 1 := by
  classical
  have hu := hU.1
  rw [hUV] at hu
  have hnorm : (star z * z) • (1 : Operator ι) = 1 := by
    simpa [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hV.1, mul_comm] using hu
  let i : ι := Classical.choice inferInstance
  have hdiag := congrArg (fun A : Operator ι => A i i) hnorm
  simpa using hdiag

def conjugation (U M : Operator ι) : Operator ι := U * M * star U

theorem projectivelyEquivalent_conjugation_eq
    {U V : Operator ι} (h : ProjectivelyEquivalent U V) (M : Operator ι) :
    conjugation U M = conjugation V M := by
  obtain ⟨z, hz, rfl⟩ := h
  simp only [conjugation, star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  change (star z * z) • (V * M * star V) = V * M * star V
  rw [hz, one_smul]

theorem unitary_conjugation_eq_iff_projectivelyEquivalent [Nonempty ι]
    (U V : Operator ι) (hU : IsUnitary U) (hV : IsUnitary V) :
    (∀ M : Operator ι, conjugation U M = conjugation V M) ↔
      ProjectivelyEquivalent U V := by
  constructor
  · intro hconj
    let T : Operator ι := star V * U
    have hcomm : ∀ M : Operator ι, T * M = M * T := by
      intro M
      calc
        T * M = star V * (U * M * star U) * U := by
          simp only [T, Matrix.mul_assoc, hU.1, mul_one]
        _ = star V * (V * M * star V) * U := by
          rw [show U * M * star U = V * M * star V from hconj M]
        _ = M * T := by
          simp only [T, ← Matrix.mul_assoc, hV.1, one_mul]
    obtain ⟨z, hT⟩ := scalar_of_commutes_all T hcomm
    have hUV : U = z • V := by
      calc
        U = (V * star V) * U := by rw [hV.2]; simp
        _ = V * (star V * U) := by rw [Matrix.mul_assoc]
        _ = V * T := rfl
        _ = V * (z • (1 : Operator ι)) := by rw [hT]
        _ = z • V := by simp [mul_smul_comm]
    exact ⟨z, unitary_smul_phase hU hV hUV, hUV⟩
  · intro h M
    exact projectivelyEquivalent_conjugation_eq h M

/-- The matrix of conjugation on matrix units, with output and input index pairs. -/
def conjugationCoordinates (U : Operator ι) : Operator (ι × ι) :=
  fun p r => U p.1 r.1 * (star U) r.2 p.2

theorem conjugationCoordinates_eq_iff
    (U V : Operator ι) : conjugationCoordinates U = conjugationCoordinates V ↔
      ∀ M : Operator ι, conjugation U M = conjugation V M := by
  classical
  constructor
  · intro hc M
    ext i k
    simp only [conjugation, Matrix.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro j hj
    have hh := congrArg (fun A : Operator (ι × ι) => A (i, k) (j, l)) hc
    change U i j * (star U) l k = V i j * (star V) l k at hh
    calc
      U i j * M j l * (star U) l k = M j l * (U i j * (star U) l k) := by ring
      _ = M j l * (V i j * (star V) l k) := by rw [hh]
      _ = V i j * M j l * (star V) l k := by ring
  · intro h
    ext ⟨i, k⟩ ⟨j, l⟩
    have hh := congrArg (fun A : Operator ι => A i k) (h (matrixUnit j l))
    simpa [conjugationCoordinates, conjugation, matrixUnit, Matrix.mul_apply,
      ite_and, mul_ite, ite_mul] using hh

theorem unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent [Nonempty ι]
    (U V : Operator ι) (hU : IsUnitary U) (hV : IsUnitary V) :
    conjugationCoordinates U = conjugationCoordinates V ↔ ProjectivelyEquivalent U V := by
  exact (conjugationCoordinates_eq_iff U V).trans
    (unitary_conjugation_eq_iff_projectivelyEquivalent U V hU hV)

/-- Finite coordinate images give finite images in the exact global-phase quotient. -/
theorem finite_projectiveImage_of_finite_conjugationCoordinates [Nonempty ι]
    (S : Set (Operator ι)) (hunit : ∀ U ∈ S, IsUnitary U)
    (hfinite : (conjugationCoordinates '' S).Finite) :
    (projectiveClass '' S).Finite := by
  classical
  let chooseClass : Operator (ι × ι) → ProjectiveOperator ι := fun A =>
    if h : ∃ U : Operator ι, U ∈ S ∧ conjugationCoordinates U = A then
      projectiveClass (Classical.choose h)
    else projectiveClass (1 : Operator ι)
  have hchoose (U : Operator ι) (hUS : U ∈ S) :
      chooseClass (conjugationCoordinates U) = projectiveClass U := by
    dsimp only [chooseClass]
    split_ifs with h
    · have hv := Classical.choose_spec h
      have hp : ProjectivelyEquivalent (Classical.choose h) U :=
        (unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent
          (Classical.choose h) U (hunit _ hv.1) (hunit U hUS)).mp hv.2
      exact Quotient.sound hp
    · exact False.elim (h ⟨U, hUS, rfl⟩)
  refine (hfinite.image chooseClass).subset ?_
  rintro a ⟨U, hUS, rfl⟩
  exact ⟨conjugationCoordinates U, ⟨U, hUS, rfl⟩, hchoose U hUS⟩

end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_ProjectiveFaithfulness

/- ===== Source block: Rotations; SHA-256 1ee6539e9955a4f3ed391d25c32894fdeacedb0324b4ea470215ad9bb71d1079 ===== -/
section Merged_Rotations
/-!
Rotation lemmas for a concrete Hermitian involution. These are dependencies of
the manuscript's upper construction, not a formalization of its circuit or
stabilizer-code hypotheses.
-/

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rotation (P : Operator ι) (t : ℝ) : Operator ι :=
  affine P (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ))

theorem imag_mul_imag (a b : ℂ) :
    (Complex.I * a) * (Complex.I * b) = -(a * b) := by
  calc
    (Complex.I * a) * (Complex.I * b) = (Complex.I * Complex.I) * (a * b) := by ring
    _ = -(a * b) := by rw [Complex.I_mul_I]; ring

@[simp] theorem rotation_zero (P : Operator ι) : rotation P 0 = 1 := by
  simp [rotation, affine]

theorem rotation_add {P : Operator ι} (hP : P * P = 1) (s t : ℝ) :
    rotation P (s + t) = rotation P s * rotation P t := by
  rw [rotation, rotation, rotation, affine_mul hP]
  have hc : (Real.cos (s + t) : ℂ) =
      (Real.cos s : ℂ) * (Real.cos t : ℂ) +
        (Complex.I * (Real.sin s : ℂ)) * (Complex.I * (Real.sin t : ℂ)) := by
    rw [imag_mul_imag, Real.cos_add]
    push_cast
    ring
  have hs : Complex.I * (Real.sin (s + t) : ℂ) =
      (Real.cos s : ℂ) * (Complex.I * (Real.sin t : ℂ)) +
        (Complex.I * (Real.sin s : ℂ)) * (Real.cos t : ℂ) := by
    rw [Real.sin_add]
    push_cast
    ring
  rw [hc, hs]

theorem star_rotation {P : Operator ι} (hP : star P = P) (t : ℝ) :
    star (rotation P t) = rotation P (-t) := by
  have hc : star (Real.cos t : ℂ) = (Real.cos t : ℂ) :=
    Complex.conj_ofReal (Real.cos t)
  have hs : star (Real.sin t : ℂ) = (Real.sin t : ℂ) :=
    Complex.conj_ofReal (Real.sin t)
  have hI : star Complex.I = -Complex.I := by simp
  have hb : star (Complex.I * (Real.sin t : ℂ)) =
      Complex.I * (Real.sin (-t) : ℂ) := by
    rw [star_mul, hs, hI, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    ring
  rw [rotation, star_affine hP, rotation, hc, hb, Real.cos_neg]

theorem rotation_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) (t : ℝ) : IsUnitary (rotation P t) := by
  constructor
  · rw [star_rotation hself, ← rotation_add hsq, neg_add_cancel, rotation_zero]
  · rw [star_rotation hself, ← rotation_add hsq, add_neg_cancel, rotation_zero]

theorem continuous_rotation (P : Operator ι) : Continuous (rotation P) := by
  unfold rotation affine
  fun_prop

@[simp] theorem rotation_pi_div_two (P : Operator ι) :
    rotation P (Real.pi / 2) = Complex.I • P := by
  simp [rotation, affine]

theorem rotation_pi_div_two_not_isScalar {P : Operator ι} (hP : ¬ IsScalar P) :
    ¬ IsScalar (rotation P (Real.pi / 2)) := by
  rw [rotation_pi_div_two]
  intro h
  exact hP (isScalar_of_smul Complex.I_ne_zero h)

theorem rotation_pi_div_two_not_projectivelyEquivalent_one
    {P : Operator ι} (hP : ¬ IsScalar P) :
    ¬ ProjectivelyEquivalent (rotation P (Real.pi / 2)) 1 := by
  intro h
  exact rotation_pi_div_two_not_isScalar hP (projectivelyEquivalent_one_isScalar h)

/-- A concrete nontrivial continuous one-parameter unitary family. -/
theorem rotation_one_parameter_family {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hP : ¬ IsScalar P) :
    Continuous (rotation P) ∧
      rotation P 0 = 1 ∧
      (∀ s t : ℝ, rotation P (s + t) = rotation P s * rotation P t) ∧
      (∀ t : ℝ, IsUnitary (rotation P t)) ∧
      ¬ ProjectivelyEquivalent (rotation P (Real.pi / 2)) 1 := by
  exact ⟨continuous_rotation P, rotation_zero P, rotation_add hsq,
    rotation_isUnitary hself hsq, rotation_pi_div_two_not_projectivelyEquivalent_one hP⟩

theorem affine_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) {a b : ℂ}
    (hnorm : star a * a + star b * b = 1)
    (hcross : star a * b + star b * a = 0) : IsUnitary (affine P a b) := by
  constructor
  · rw [star_affine hself, affine_mul hsq, hnorm, hcross]
    simp [affine]
  · rw [star_affine hself, affine_mul hsq]
    have hn : a * star a + b * star b = 1 := by simpa [mul_comm] using hnorm
    have hc : a * star b + b * star a = 0 := by simpa [mul_comm, add_comm] using hcross
    rw [hn, hc]
    simp [affine]

noncomputable def rationalScale (r : ℕ) : ℂ :=
  ((Real.sqrt (1 + (r : ℝ) ^ 2) : ℝ) : ℂ)⁻¹

theorem rationalScale_ne_zero (r : ℕ) : rationalScale r ≠ 0 := by
  apply inv_ne_zero
  have hpos : 0 < Real.sqrt (1 + (r : ℝ) ^ 2) := by positivity
  exact_mod_cast ne_of_gt hpos

theorem star_rationalScale (r : ℕ) : star (rationalScale r) = rationalScale r := by
  simp [rationalScale]

theorem rationalScale_sq_mul (r : ℕ) :
    rationalScale r ^ 2 * (1 + (r : ℂ) ^ 2) = 1 := by
  let s : ℂ := (Real.sqrt (1 + (r : ℝ) ^ 2) : ℝ)
  have hsne : s ≠ 0 := by
    dsimp [s]
    have hpos : 0 < Real.sqrt (1 + (r : ℝ) ^ 2) := by positivity
    exact_mod_cast ne_of_gt hpos
  have hs : s ^ 2 = 1 + (r : ℂ) ^ 2 := by
    dsimp [s]
    have hh := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + (r : ℝ) ^ 2 by positivity)
    exact_mod_cast hh
  change (s⁻¹) ^ 2 * (1 + (r : ℂ) ^ 2) = 1
  rw [← hs, ← mul_pow]
  simp [hsne]

/-- A countable family of genuine unitaries, with no matrix-exponential premise. -/
noncomputable def rationalRotation (P : Operator ι) (r : ℕ) : Operator ι :=
  affine P (rationalScale r) (rationalScale r * Complex.I * (r : ℂ))

theorem rationalRotation_isUnitary {P : Operator ι} (hself : star P = P)
    (hsq : P * P = 1) (r : ℕ) : IsUnitary (rationalRotation P r) := by
  let a : ℂ := rationalScale r
  let b : ℂ := a * Complex.I * (r : ℂ)
  have hsa : star a = a := star_rationalScale r
  have hsb : star b = -b := by
    simp [b, a, rationalScale, mul_comm, mul_left_comm, mul_assoc]
  have hbb : b * b = -(a * a * (r : ℂ) ^ 2) := by
    calc
      b * b = (Complex.I * Complex.I) * (a * a * (r : ℂ) ^ 2) := by dsimp [b]; ring
      _ = -(a * a * (r : ℂ) ^ 2) := by rw [Complex.I_mul_I]; ring
  apply affine_isUnitary hself hsq
  · change star a * a + star b * b = 1
    rw [hsa, hsb]
    calc
      a * a + -b * b = a ^ 2 * (1 + (r : ℂ) ^ 2) := by rw [neg_mul, hbb]; ring
      _ = 1 := rationalScale_sq_mul r
  · change star a * b + star b * a = 0
    rw [hsa, hsb]
    ring

theorem rationalRotation_projectivelyEquivalent_injective
    {P : Operator ι} (hP : ¬ IsScalar P) {r s : ℕ}
    (h : ProjectivelyEquivalent (rationalRotation P r) (rationalRotation P s)) : r = s := by
  obtain ⟨z, _, h⟩ := h
  have he : affine P (rationalScale r) (rationalScale r * Complex.I * (r : ℂ)) =
      affine P (z * rationalScale s) (z * (rationalScale s * Complex.I * (s : ℂ))) := by
    simpa [rationalRotation, affine, smul_add, smul_smul] using h
  obtain ⟨h0, h1⟩ := affine_coefficients_unique hP he
  have hprod : (rationalScale r * Complex.I) * (r : ℂ) =
      (rationalScale r * Complex.I) * (s : ℂ) := by
    calc
      (rationalScale r * Complex.I) * (r : ℂ) =
          z * (rationalScale s * Complex.I * (s : ℂ)) := h1
      _ = (z * rationalScale s) * Complex.I * (s : ℂ) := by ring
      _ = (rationalScale r * Complex.I) * (s : ℂ) := by rw [← h0]
  have hc : rationalScale r * Complex.I ≠ 0 :=
    mul_ne_zero (rationalScale_ne_zero r) Complex.I_ne_zero
  have hcast : (r : ℂ) = (s : ℂ) := mul_left_cancel₀ hc hprod
  exact_mod_cast hcast

theorem rationalRotation_classes_injective {P : Operator ι} (hP : ¬ IsScalar P) :
    Function.Injective (fun r : ℕ => projectiveClass (rationalRotation P r)) := by
  intro r s h
  exact rationalRotation_projectivelyEquivalent_injective hP (Quotient.exact h)

theorem rationalRotation_classes_infinite {P : Operator ι} (hP : ¬ IsScalar P) :
    Set.Infinite (Set.range (fun r : ℕ => projectiveClass (rationalRotation P r))) := by
  exact Set.infinite_range_of_injective (rationalRotation_classes_injective hP)

end CriticalDepth
end Merged_Rotations

/- ===== Source block: DepthZero; SHA-256 0579b3b022f22a7689d5a984e6c4dd28e0f297f5fca9a56e9a188d920f4ea162 ===== -/
section Merged_DepthZero
/-!
# The depth-zero specialization of the manuscript's first theorem

This module proves a special case of the original concrete logical-image
definition. It does not assume finite image, finite cells, infinitesimal
rigidity, or a circuit-synthesis principle. At depth zero, the physical
circuit evaluates to the identity. The encoding isometry then forces the
logical factor to be a scalar unitary.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped Kronecker

theorem projectivelyEquivalent_one_of_unitary_scalar
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {W : Operator ι} (hW : IsUnitary W) (hscalar : IsScalar W) :
    ProjectivelyEquivalent W 1 := by
  classical
  obtain ⟨z, hz⟩ := hscalar
  refine ⟨z, ?_, hz⟩
  have hunit := hW.1
  rw [hz] at hunit
  have hnorm : (star z * z) • (1 : Operator ι) = 1 := by
    simpa [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm] using hunit
  let i : ι := Classical.choice inferInstance
  have hdiag := congrArg (fun A : Operator ι => A i i) hnorm
  simpa using hdiag

namespace Manuscript

@[simp] theorem circuitEval_depth_zero
    {n q : ℕ} {dim : Fin n → ℕ} (c : Circuit n dim q 0) :
    circuitEval c = 1 := by
  simp [circuitEval]

theorem identity_implements_projective_identity
    {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (W : Operator (Fin K)) (himpl : Implements C 1 W) :
    ProjectivelyEquivalent W 1 := by
  classical
  letI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin g) := ⟨⟨0, by omega⟩⟩
  obtain ⟨hW, Z, hZ, hencoded⟩ := himpl
  have hencoded' : C.encoding = C.encoding * (W ⊗ₖ Z) := by
    simpa only [Matrix.one_mul] using hencoded
  have hT : W ⊗ₖ Z = 1 := by
    calc
      W ⊗ₖ Z = (C.encoding.conjTranspose * C.encoding) * (W ⊗ₖ Z) := by
        rw [C.isometry]
        simp
      _ = C.encoding.conjTranspose * (C.encoding * (W ⊗ₖ Z)) := by
        rw [Matrix.mul_assoc]
      _ = C.encoding.conjTranspose * C.encoding := by rw [← hencoded']
      _ = 1 := C.isometry
  have hZright : Z * Z.conjTranspose = 1 := hZ.2
  have hTensor : W ⊗ₖ (1 : Operator (Fin g)) =
      (1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose := by
    calc
      W ⊗ₖ (1 : Operator (Fin g)) =
          (W * (1 : Operator (Fin K))) ⊗ₖ (Z * Z.conjTranspose) := by
            rw [mul_one, hZright]
      _ = (W ⊗ₖ Z) * ((1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose) :=
        Matrix.mul_kronecker_mul W (1 : Operator (Fin K)) Z Z.conjTranspose
      _ = (1 : Operator (Fin K)) ⊗ₖ Z.conjTranspose := by rw [hT, one_mul]
  have hzero : (1 : Operator (Fin K)) ⊗ₖ (0 : Operator (Fin g)) = 0 := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.kronecker_apply]
  have hscalar : IsScalar W := by
    apply scalarity_of_tensor_generator W (0 : Operator (Fin g)) Z.conjTranspose
    rw [hzero, add_zero]
    exact hTensor
  exact projectivelyEquivalent_one_of_unitary_scalar hW hscalar

/--
Depth zero is an actual proved specialization of Theorem 1's logical-image
claim. No distance assumption is needed for this specialization.
-/
theorem depth_zero_logicalImage_finite
    {n K g : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) (q : ℕ) :
    (logicalImage C q 0).Finite := by
  classical
  refine (Set.finite_singleton (projectiveClass (1 : Operator (Fin K)))).subset ?_
  intro a ha
  obtain ⟨c, W, himpl, hclass⟩ := ha
  have himpl0 : Implements C 1 W := by
    simpa only [circuitEval_depth_zero] using himpl
  have hp : ProjectivelyEquivalent W 1 :=
    identity_implements_projective_identity C hK hg W himpl0
  have hq : projectiveClass W = projectiveClass (1 : Operator (Fin K)) :=
    Quotient.sound hp
  exact Set.mem_singleton_iff.mpr (hclass.symm.trans hq)

/-- A real call at the manuscript's original distance-assumption scope. -/
example (n K g d q : ℕ) (dim : Fin n → ℕ)
    (_hn : 1 ≤ n) (hK : 2 ≤ K) (hg : 1 ≤ g) (_hd : 2 ≤ d)
    (C : Code n dim K g) (_hdetect : DetectsBelow C d) :
    (logicalImage C q 0).Finite := by
  exact depth_zero_logicalImage_finite C hK hg q

#print axioms CriticalDepth.projectivelyEquivalent_one_of_unitary_scalar
#print axioms CriticalDepth.Manuscript.identity_implements_projective_identity
#print axioms CriticalDepth.Manuscript.depth_zero_logicalImage_finite

end Manuscript
end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_DepthZero

/- ===== Source block: PauliTensor; SHA-256 b24c215d2d7974fde674ab951544d0297b7a9773f6b3f71789dd9ab3cf19816f ===== -/
section Merged_PauliTensor
/-!
# Concrete tensor matrices and Pauli strings

The tensor-entry definition uses the manuscript's full computational basis.
No qubit disappears when a factor is an identity. Hermitian and involution
claims below are restricted to unphased strings; arbitrary Pauli phases are
handled separately for unitarity and commutation.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped BigOperators

def tensorEntries {I : Type*} [Fintype I] {R : Type*} [CommMonoid R]
    {α β : I → Type*} (A : ∀ i, Matrix (α i) (β i) R) :
    Matrix ((i : I) → α i) ((i : I) → β i) R :=
  fun x y => ∏ i, A i (x i) (y i)

theorem tensorEntries_mul
    {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommSemiring R]
    {α β γ : I → Type*} [∀ i, Fintype (β i)]
    (A : ∀ i, Matrix (α i) (β i) R) (B : ∀ i, Matrix (β i) (γ i) R) :
    tensorEntries (fun i => A i * B i) = tensorEntries A * tensorEntries B := by
  classical
  ext x z
  simp only [tensorEntries, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

theorem tensorEntries_one
    {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommSemiring R]
    {α : I → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] :
    tensorEntries (fun i => (1 : Matrix (α i) (α i) R)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [tensorEntries]
  · have hex : ∃ i, x i ≠ y i := by
      by_contra hn
      apply hxy
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hzero : (∏ j, (1 : Matrix (α j) (α j) R) (x j) (y j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Matrix.one_apply, hi]
    simpa [tensorEntries, Matrix.one_apply, hxy] using hzero

theorem tensorEntries_smul
    {I : Type*} [Fintype I] {R : Type*} [CommSemiring R]
    {α β : I → Type*} (z : I → R) (A : ∀ i, Matrix (α i) (β i) R) :
    tensorEntries (fun i => z i • A i) = (∏ i, z i) • tensorEntries A := by
  ext x y
  simp [tensorEntries, Finset.prod_mul_distrib, smul_eq_mul]

theorem tensorEntries_conjTranspose
    {I : Type*} [Fintype I] {α β : I → Type*}
    (A : ∀ i, Matrix (α i) (β i) ℂ) :
    tensorEntries (fun i => (A i).conjTranspose) = (tensorEntries A).conjTranspose := by
  ext x y
  simp [tensorEntries, Matrix.conjTranspose_apply]

theorem unitary_smul_of_phase
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ℂ) (U : Operator ι) (hz : star z * z = 1) (hU : IsUnitary U) :
    IsUnitary (z • U) := by
  have hz' : z * star z = 1 := by simpa [mul_comm] using hz
  constructor
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.1]
    change (z * star z) • (1 : Operator ι) = 1
    rw [hz', one_smul]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.2]
    change (star z * z) • (1 : Operator ι) = 1
    rw [hz, one_smul]

theorem i_pow_unit_modulus (r : ℕ) :
    star (Complex.I ^ r) * Complex.I ^ r = 1 := by
  rw [star_pow, ← mul_pow]
  simp

theorem prod_signs_eq_one_or_neg_one
    {I : Type*} [Fintype I] (s : I → ℂ) (h : ∀ i, s i = 1 ∨ s i = -1) :
    (∏ i, s i) = 1 ∨ (∏ i, s i) = -1 := by
  classical
  have haux : ∀ t : Finset I,
      (∀ i ∈ t, s i = 1 ∨ s i = -1) → t.prod s = 1 ∨ t.prod s = -1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih =>
        intro ht
        have hsign := ht a (by simp)
        have htail := ih (fun i hi => ht i (by simp [hi]))
        simp only [Finset.prod_insert ha]
        rcases hsign with hs | hs <;> rcases htail with hh | hh <;> simp [hs, hh]
  exact haux Finset.univ (fun i _ => h i)

namespace Manuscript

theorem singlePauli_selfAdjoint (p : SinglePauli) : p.matrix.conjTranspose = p.matrix := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [SinglePauli.matrix, Matrix.conjTranspose_apply]

theorem singlePauli_sq (p : SinglePauli) : p.matrix * p.matrix = 1 := by
  cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem singlePauli_isUnitary (p : SinglePauli) : IsUnitary p.matrix := by
  constructor
  · change p.matrix.conjTranspose * p.matrix = 1
    rw [singlePauli_selfAdjoint, singlePauli_sq]
  · change p.matrix * p.matrix.conjTranspose = 1
    rw [singlePauli_selfAdjoint, singlePauli_sq]

def SinglePauli.commutationSign (p q : SinglePauli) : ℂ :=
  if p = .I ∨ q = .I ∨ p = q then 1 else -1

theorem singlePauli_commutationSign_eq_one_or_neg_one (p q : SinglePauli) :
    p.commutationSign q = 1 ∨ p.commutationSign q = -1 := by
  unfold SinglePauli.commutationSign
  split_ifs <;> simp

theorem singlePauli_commutation (p q : SinglePauli) :
    p.matrix * q.matrix = p.commutationSign q • (q.matrix * p.matrix) := by
  cases p <;> cases q <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [SinglePauli.matrix, SinglePauli.commutationSign, Matrix.mul_apply,
      Fin.sum_univ_two, Complex.I_mul_I]

theorem pauliMatrix_zero_eq_tensorEntries {n : ℕ} (p : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p = tensorEntries (fun i => (p i).matrix) := by
  ext x y
  simp [pauliMatrix, tensorEntries]

theorem unphased_pauliMatrix_selfAdjoint {n : ℕ} (p : Fin n → SinglePauli) :
    (pauliMatrix (0 : Fin 4) p).conjTranspose = pauliMatrix (0 : Fin 4) p := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_conjTranspose]
  simp only [singlePauli_selfAdjoint]

theorem unphased_pauliMatrix_sq {n : ℕ} (p : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) p = 1 := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_mul]
  simp only [singlePauli_sq, tensorEntries_one]

theorem unphased_pauliMatrix_isUnitary {n : ℕ} (p : Fin n → SinglePauli) :
    IsUnitary (pauliMatrix (0 : Fin 4) p) := by
  constructor
  · change (pauliMatrix (0 : Fin 4) p).conjTranspose * pauliMatrix (0 : Fin 4) p = 1
    rw [unphased_pauliMatrix_selfAdjoint, unphased_pauliMatrix_sq]
  · change pauliMatrix (0 : Fin 4) p * (pauliMatrix (0 : Fin 4) p).conjTranspose = 1
    rw [unphased_pauliMatrix_selfAdjoint, unphased_pauliMatrix_sq]

theorem pauliMatrix_eq_phase_smul {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    pauliMatrix phase p = (Complex.I ^ phase.val) • pauliMatrix (0 : Fin 4) p := by
  ext x y
  simp [pauliMatrix, smul_eq_mul]

theorem pauliMatrix_isUnitary {n : ℕ} (phase : Fin 4) (p : Fin n → SinglePauli) :
    IsUnitary (pauliMatrix phase p) := by
  rw [pauliMatrix_eq_phase_smul phase p]
  exact unitary_smul_of_phase (Complex.I ^ phase.val) (pauliMatrix (0 : Fin 4) p)
    (i_pow_unit_modulus phase.val) (unphased_pauliMatrix_isUnitary p)

theorem unphased_pauliMatrix_commutation {n : ℕ} (p q : Fin n → SinglePauli) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) q =
      (∏ i, (p i).commutationSign (q i)) •
        (pauliMatrix (0 : Fin 4) q * pauliMatrix (0 : Fin 4) p) := by
  simp only [pauliMatrix_zero_eq_tensorEntries]
  calc
    tensorEntries (fun i => (p i).matrix) * tensorEntries (fun i => (q i).matrix) =
        tensorEntries (fun i => (p i).matrix * (q i).matrix) :=
      (tensorEntries_mul (fun i => (p i).matrix) (fun i => (q i).matrix)).symm
    _ = tensorEntries (fun i => (p i).commutationSign (q i) •
        ((q i).matrix * (p i).matrix)) := by
      congr 1
      funext i
      exact singlePauli_commutation (p i) (q i)
    _ = (∏ i, (p i).commutationSign (q i)) •
        tensorEntries (fun i => (q i).matrix * (p i).matrix) :=
      tensorEntries_smul (fun i => (p i).commutationSign (q i))
        (fun i => (q i).matrix * (p i).matrix)
    _ = (∏ i, (p i).commutationSign (q i)) •
        (tensorEntries (fun i => (q i).matrix) * tensorEntries (fun i => (p i).matrix)) := by
      rw [tensorEntries_mul]

theorem pauliMatrix_commutation {n : ℕ} (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q =
      (∏ i, (p i).commutationSign (q i)) • (pauliMatrix b q * pauliMatrix a p) := by
  calc
    pauliMatrix a p * pauliMatrix b q =
        ((Complex.I ^ a.val) * (Complex.I ^ b.val)) •
          (pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) q) := by
      rw [pauliMatrix_eq_phase_smul a p, pauliMatrix_eq_phase_smul b q]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [mul_comm (Complex.I ^ b.val) (Complex.I ^ a.val)]
    _ = (((Complex.I ^ a.val) * (Complex.I ^ b.val)) *
        (∏ i, (p i).commutationSign (q i))) •
          (pauliMatrix (0 : Fin 4) q * pauliMatrix (0 : Fin 4) p) := by
      rw [unphased_pauliMatrix_commutation p q, smul_smul]
    _ = (∏ i, (p i).commutationSign (q i)) • (pauliMatrix b q * pauliMatrix a p) := by
      rw [pauliMatrix_eq_phase_smul b q, pauliMatrix_eq_phase_smul a p]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      ring

theorem pauliMatrix_commute_or_anticommute {n : ℕ}
    (a b : Fin 4) (p q : Fin n → SinglePauli) :
    pauliMatrix a p * pauliMatrix b q = pauliMatrix b q * pauliMatrix a p ∨
      pauliMatrix a p * pauliMatrix b q = -(pauliMatrix b q * pauliMatrix a p) := by
  have hs := prod_signs_eq_one_or_neg_one
    (fun i => (p i).commutationSign (q i))
    (fun i => singlePauli_commutationSign_eq_one_or_neg_one (p i) (q i))
  rcases hs with hs | hs
  · left
    simpa only [hs, one_smul] using pauliMatrix_commutation a b p q
  · right
    simpa only [hs, neg_one_smul] using pauliMatrix_commutation a b p q

end Manuscript
end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliTensor

/- ===== Source block: ProjectiveTopology; SHA-256 82c75f1ee54111cb2970997d42c46ec47dc1f555cd15a060a45118d6728b05f5 ===== -/
section Merged_ProjectiveTopology
/-!
# The actual projective unitary space and non-density

The carrier is the quotient of genuine unitary matrices by one global phase,
with the standard quotient topology inherited from the matrix topology.
Closed fibers of the continuous conjugation-coordinate map prove the T1
property. Infinitude is witnessed by genuine unitary rational rotations.
No nonunitary matrix or zero matrix is used to establish non-density.
-/

noncomputable section

namespace CriticalDepth

open Matrix

universe u

abbrev UnitaryOperator (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  {U : Operator ι // IsUnitary U}

def unitaryPhaseSetoid (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Setoid (UnitaryOperator ι) where
  r U V := ProjectivelyEquivalent U.val V.val
  iseqv := ⟨fun U => projectivelyEquivalent_refl U.val,
    fun h => projectivelyEquivalent_symm h,
    fun h₁ h₂ => projectivelyEquivalent_trans h₁ h₂⟩

/-- Genuine projective unitaries, equipped with the usual quotient topology. -/
abbrev ProjectiveUnitary (ι : Type u) [Fintype ι] [DecidableEq ι] :=
  Quotient (unitaryPhaseSetoid ι)

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

def unitaryProjectiveClass (U : UnitaryOperator ι) : ProjectiveUnitary ι :=
  Quotient.mk (unitaryPhaseSetoid ι) U

/-- Forget unitarity while retaining exactly the same global-phase class. -/
def projectiveUnitaryToOperator (ι : Type u) [Fintype ι] [DecidableEq ι] :
    ProjectiveUnitary ι → ProjectiveOperator ι :=
  Quotient.lift (fun U : UnitaryOperator ι => projectiveClass U.val)
    (fun _ _ h => Quotient.sound h)

@[simp] theorem projectiveUnitaryToOperator_mk (U : UnitaryOperator ι) :
    projectiveUnitaryToOperator ι (unitaryProjectiveClass U) = projectiveClass U.val := rfl

theorem projectiveUnitaryToOperator_injective :
    Function.Injective (projectiveUnitaryToOperator ι) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro U V h
  change projectiveClass U.val = projectiveClass V.val at h
  have hphase :=
    @Quotient.exact (Operator ι) (projectiveSetoid ι) U.val V.val h
  exact @Quotient.sound (UnitaryOperator ι) (unitaryPhaseSetoid ι) U V hphase

theorem continuous_conjugationCoordinates :
    Continuous (conjugationCoordinates : Operator ι → Operator (ι × ι)) := by
  unfold conjugationCoordinates
  fun_prop

theorem continuous_unitaryConjugationCoordinates :
    Continuous (fun U : UnitaryOperator ι => conjugationCoordinates U.val) :=
  continuous_conjugationCoordinates.comp continuous_subtype_val

theorem isClosed_unitary_phase_fiber [Nonempty ι] (U : UnitaryOperator ι) :
    IsClosed {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} := by
  have heq : {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} =
      (fun V : UnitaryOperator ι => conjugationCoordinates V.val) ⁻¹'
        {conjugationCoordinates U.val} := by
    ext V
    change ProjectivelyEquivalent V.val U.val ↔
      conjugationCoordinates V.val = conjugationCoordinates U.val
    exact (unitary_conjugationCoordinates_eq_iff_projectivelyEquivalent
      V.val U.val V.property U.property).symm
  rw [heq]
  exact isClosed_singleton.preimage continuous_unitaryConjugationCoordinates

theorem unitaryProjectiveClass_singleton_preimage (U : UnitaryOperator ι) :
    unitaryProjectiveClass ⁻¹' {unitaryProjectiveClass U} =
      {V : UnitaryOperator ι | ProjectivelyEquivalent V.val U.val} := by
  ext V
  change unitaryProjectiveClass V = unitaryProjectiveClass U ↔
    ProjectivelyEquivalent V.val U.val
  constructor
  · intro h
    exact @Quotient.exact (UnitaryOperator ι) (unitaryPhaseSetoid ι) V U h
  · intro h
    exact @Quotient.sound (UnitaryOperator ι) (unitaryPhaseSetoid ι) V U h

/-- Projective unitary singletons are closed because their quotient
preimages are closed conjugation-coordinate fibers. -/
instance projectiveUnitaryT1Space [Nonempty ι] : T1Space (ProjectiveUnitary ι) where
  t1 q := by
    refine Quotient.inductionOn q ?_
    intro U
    letI : Setoid (UnitaryOperator ι) := unitaryPhaseSetoid ι
    have hquot : Topology.IsQuotientMap
        (Quotient.mk' : UnitaryOperator ι → ProjectiveUnitary ι) :=
      isQuotientMap_quotient_mk'
    apply ((Topology.isQuotientMap_iff_isClosed.mp hquot).2
      ({unitaryProjectiveClass U} : Set (ProjectiveUnitary ι))).mpr
    change IsClosed (unitaryProjectiveClass ⁻¹' {unitaryProjectiveClass U})
    rw [unitaryProjectiveClass_singleton_preimage]
    exact isClosed_unitary_phase_fiber U

def signInvolution (K : ℕ) : Operator (Fin K) :=
  fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

theorem signInvolution_selfAdjoint (K : ℕ) : star (signInvolution K) = signInvolution K := by
  classical
  ext i j
  change star (signInvolution K j i) = signInvolution K i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 <;> simp [signInvolution, hi]
  · simp [signInvolution, hij, Ne.symm hij]

theorem signInvolution_sq (K : ℕ) : signInvolution K * signInvolution K = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val = 0 <;>
      simp [signInvolution, Matrix.mul_apply, Matrix.one_apply, hi]
  · simp [signInvolution, Matrix.mul_apply, Matrix.one_apply, hij]

theorem signInvolution_not_isScalar (K : ℕ) (hK : 2 ≤ K) : ¬ IsScalar (signInvolution K) := by
  intro h
  obtain ⟨z, hz⟩ := h
  let i₀ : Fin K := ⟨0, by omega⟩
  let i₁ : Fin K := ⟨1, by omega⟩
  have h₀ : (1 : ℂ) = z := by
    have heq := congrArg (fun A : Operator (Fin K) => A i₀ i₀) hz
    simpa [signInvolution, i₀] using heq
  have h₁ : (-1 : ℂ) = z := by
    have heq := congrArg (fun A : Operator (Fin K) => A i₁ i₁) hz
    simpa [signInvolution, i₁] using heq
  have hbad : (1 : ℂ) = -1 := h₀.trans h₁.symm
  norm_num at hbad

def rationalRotationUnitary (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) (r : ℕ) : UnitaryOperator ι :=
  ⟨rationalRotation P r, rationalRotation_isUnitary hself hsq r⟩

theorem rationalRotation_projectiveUnitary_injective
    (P : Operator ι) (hself : star P = P) (hsq : P * P = 1) (hP : ¬ IsScalar P) :
    Function.Injective (fun r : ℕ =>
      unitaryProjectiveClass (rationalRotationUnitary P hself hsq r)) := by
  intro r s hrs
  have heq := congrArg (projectiveUnitaryToOperator ι) hrs
  change projectiveClass (rationalRotation P r) =
    projectiveClass (rationalRotation P s) at heq
  exact rationalRotation_classes_injective hP heq

/-- Infinitude is witnessed inside the unitary carrier itself. -/
theorem projectiveUnitary_infinite (K : ℕ) (hK : 2 ≤ K) :
    Infinite (ProjectiveUnitary (Fin K)) := by
  exact Infinite.of_injective _
    (rationalRotation_projectiveUnitary_injective (signInvolution K)
      (signInvolution_selfAdjoint K) (signInvolution_sq K)
      (signInvolution_not_isScalar K hK))

theorem finite_projectiveUnitary_preimage
    (S : Set (ProjectiveOperator ι)) (hS : S.Finite) :
    (projectiveUnitaryToOperator ι ⁻¹' S).Finite :=
  Set.Finite.preimage (projectiveUnitaryToOperator_injective (ι := ι)).injOn hS

/-- A finite projective image is not dense in the actual projective unitary
space in dimension at least two. -/
theorem finite_projectiveImage_not_dense_in_projectiveUnitary
    (K : ℕ) (hK : 2 ≤ K) (S : Set (ProjectiveOperator (Fin K))) (hS : S.Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin K) ⁻¹' S) := by
  letI : Nonempty (Fin K) := ⟨⟨0, by omega⟩⟩
  letI : Infinite (ProjectiveUnitary (Fin K)) := projectiveUnitary_infinite K hK
  have hfinite := finite_projectiveUnitary_preimage S hS
  intro hdense
  have heq : projectiveUnitaryToOperator (Fin K) ⁻¹' S = Set.univ :=
    hfinite.isClosed.closure_eq.symm.trans hdense.closure_eq
  have huniv : (Set.univ : Set (ProjectiveUnitary (Fin K))).Finite := by
    rw [← heq]
    exact hfinite
  exact Set.infinite_univ huniv

namespace Manuscript

/-- Every logical action in the manuscript's image has a genuinely unitary
representative, hence belongs to the image of the projective unitary carrier. -/
theorem logicalImage_subset_projectiveUnitary_range
    {n ℓ g q h : ℕ} {dim : Fin n → ℕ} (C : Code n dim ℓ g) :
    logicalImage C q h ⊆ Set.range (projectiveUnitaryToOperator (Fin ℓ)) := by
  rintro a ⟨c, W, hW, rfl⟩
  exact ⟨unitaryProjectiveClass ⟨W, hW.1⟩, rfl⟩

/-- The non-density corollary of Theorem 1, expressed in the quotient of
unitaries rather than in the quotient of all matrices. -/
theorem logicalImage_not_dense_in_projectiveUnitary
    {n ℓ g q h : ℕ} {dim : Fin n → ℕ}
    (C : Code n dim ℓ g) (hℓ : 2 ≤ ℓ) (hfinite : (logicalImage C q h).Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' logicalImage C q h) :=
  finite_projectiveImage_not_dense_in_projectiveUnitary ℓ hℓ _ hfinite

end Manuscript

end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_ProjectiveTopology

/- ===== Source block: RotationExamples; SHA-256 dbc72423f12d70f8939cb6afc463311487adc0d5fb597ab0a86641a8d7de18a5 ===== -/
section Merged_RotationExamples
namespace CriticalDepth.Examples

def pauliZ : Operator (Fin 2) := !![1, 0; 0, -1]

theorem pauliZ_selfAdjoint : star pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ]

theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem pauliZ_not_isScalar : ¬ IsScalar pauliZ := by
  rintro ⟨z, hz⟩
  have h0 := congrArg (fun A : Operator (Fin 2) => A 0 0) hz
  have h1 := congrArg (fun A : Operator (Fin 2) => A 1 1) hz
  simp [pauliZ] at h0 h1
  have : (1 : ℂ) = -1 := h0.trans h1.symm
  norm_num at this

/-- A real call supplying all hypotheses to the general family theorem. -/
example : Continuous (rotation pauliZ) ∧
    rotation pauliZ 0 = 1 ∧
    (∀ s t : ℝ, rotation pauliZ (s + t) = rotation pauliZ s * rotation pauliZ t) ∧
    (∀ t : ℝ, IsUnitary (rotation pauliZ t)) ∧
    ¬ ProjectivelyEquivalent (rotation pauliZ (Real.pi / 2)) 1 := by
  exact rotation_one_parameter_family pauliZ_selfAdjoint pauliZ_sq pauliZ_not_isScalar

example : IsUnitary (rotation pauliZ (3 / 7)) := by
  exact rotation_isUnitary pauliZ_selfAdjoint pauliZ_sq (3 / 7)

example (r : ℕ) : IsUnitary (rationalRotation pauliZ r) := by
  exact rationalRotation_isUnitary pauliZ_selfAdjoint pauliZ_sq r

example : Set.Infinite
    (Set.range (fun r : ℕ => projectiveClass (rationalRotation pauliZ r))) := by
  exact rationalRotation_classes_infinite pauliZ_not_isScalar

#print axioms CriticalDepth.affine_coefficients_unique
#print axioms CriticalDepth.rotation_one_parameter_family
#print axioms CriticalDepth.rationalRotation_isUnitary
#print axioms CriticalDepth.rationalRotation_classes_infinite
#print axioms CriticalDepth.Examples.pauliZ_not_isScalar

end CriticalDepth.Examples
end Merged_RotationExamples

/- ===== Source block: ScalarConstants; SHA-256 c82166415ae0609b27a763821920190ea37c4da943f9f765f23ed70df048c2df ===== -/
section Merged_ScalarConstants
/-!
# Scalar values of derivation constants

An algebraic element of a field extension of an algebraically closed field
comes from the base field. Combined with the differential-constants
criterion, this identifies the scalar value of a coordinate annihilated
by every base-linear derivation.
-/

namespace CriticalDepth

open Polynomial

universe u v w

variable (F : Type u) (K : Type v)
variable [Field F] [IsAlgClosed F] [Field K] [Algebra F K]

/-- An individual algebraic element over an algebraically closed field
is the image of a scalar from that field. No algebraicity assumption on
the whole ambient extension is imposed. -/
theorem exists_algebraMap_eq_of_isAlgebraic
    (a : K) (ha : IsAlgebraic F a) :
    ∃ c : F, algebraMap F K c = a := by
  have hi : IsIntegral F a := ha.isIntegral
  refine ⟨-(minpoly F a).coeff 0, ?_⟩
  have hq : (minpoly F a).leadingCoeff = 1 := minpoly.monic hi
  have hdeg : (minpoly F a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hi)
  have hroot : aeval a (minpoly F a) = 0 := minpoly.aeval F a
  rw [eq_X_add_C_of_degree_eq_one hdeg, hq, C_1, one_mul,
    aeval_add, aeval_X, aeval_C, add_eq_zero_iff_eq_neg] at hroot
  simpa only [map_neg] using hroot.symm

/-- In a characteristic-zero extension of an algebraically closed field,
an element annihilated by every base-linear derivation is a base scalar. -/
theorem exists_algebraMap_eq_of_forall_derivation_eq_zero
    [CharZero K] (a : K)
    (h : ∀ d : Derivation F K K, d a = 0) :
    ∃ c : F, algebraMap F K c = a :=
  exists_algebraMap_eq_of_isAlgebraic F K a
    (isAlgebraic_of_forall_derivation_eq_zero F K a h)

/-- A scalar value after an algebra homomorphism gives a scalar congruence
modulo its kernel. This applies in particular to the map from a coordinate
algebra to the fraction field of a prime quotient. -/
theorem exists_scalar_mod_kernel_of_forall_derivation_eq_zero
    [CharZero K] (R : Type w) [CommRing R] [Algebra F R]
    (φ : R →ₐ[F] K) (r : R)
    (h : ∀ d : Derivation F K K, d (φ r) = 0) :
    ∃ c : F, r - algebraMap F R c ∈ RingHom.ker φ.toRingHom := by
  obtain ⟨c, hc⟩ :=
    exists_algebraMap_eq_of_forall_derivation_eq_zero F K (φ r) h
  refine ⟨c, ?_⟩
  change φ (r - algebraMap F R c) = 0
  rw [map_sub, φ.commutes, hc, sub_self]

end CriticalDepth
end Merged_ScalarConstants

/- ===== Source block: Support; SHA-256 a431f17d7481655ab24241d15b7850d2fa45a65fa7b3fc33e135d4206ce08ecd ===== -/
section Merged_Support
/-!
# Tensor-local support on the full physical register

These lemmas use the manuscript's concrete matrix embedding. No support-growth
law is assumed. In particular, local operators retain the identity on every
site outside the declared support.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {n : ℕ} {dim : Fin n → ℕ}

@[simp] theorem localEmbed_zero (S : Finset (Fin n)) :
    localEmbed S (0 : Operator (LocalBasis dim S)) = 0 := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i <;> simp [localEmbed, h]

theorem localEmbed_add (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A + B) = localEmbed S A + localEmbed S B := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i
  · simp only [localEmbed, if_pos h, Matrix.add_apply]
  · simp only [localEmbed, if_neg h, Matrix.add_apply, zero_add]

theorem localEmbed_smul (S : Finset (Fin n)) (z : ℂ)
    (A : Operator (LocalBasis dim S)) :
    localEmbed S (z • A) = z • localEmbed S A := by
  classical
  ext x y
  by_cases h : ∀ i, i ∉ S → x i = y i <;> simp [localEmbed, h]

theorem localEmbed_neg (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    localEmbed S (-A) = -localEmbed S A := by
  simpa only [neg_one_smul] using localEmbed_smul S (-1 : ℂ) A

theorem localEmbed_sub (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A - B) = localEmbed S A - localEmbed S B := by
  rw [sub_eq_add_neg, localEmbed_add, localEmbed_neg, sub_eq_add_neg]

def localEmbedLinearMap (S : Finset (Fin n)) :
    Operator (LocalBasis dim S) →ₗ[ℂ] Operator (PhysicalBasis n dim) where
  toFun := localEmbed S
  map_add' := localEmbed_add S
  map_smul' := localEmbed_smul S

@[simp] theorem localEmbed_one (S : Finset (Fin n)) :
    localEmbed S (1 : Operator (LocalBasis dim S)) = 1 := by
  classical
  ext x y
  by_cases hout : ∀ i, i ∉ S → x i = y i
  · by_cases hin : (fun i : S => x i.1) = (fun i : S => y i.1)
    · have hxy : x = y := by
        funext i
        by_cases hi : i ∈ S
        · exact congrFun hin ⟨i, hi⟩
        · exact hout i hi
      subst y
      simp [localEmbed]
    · have hxy : x ≠ y := by
        intro hxy
        apply hin
        rw [hxy]
      simp [localEmbed, hout, Matrix.one_apply, hin, hxy]
  · have hxy : x ≠ y := by
      intro hxy
      apply hout
      intro i hi
      rw [hxy]
    simp [localEmbed, hout, Matrix.one_apply, hxy]

theorem localEmbed_conjTranspose (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) :
    localEmbed S A.conjTranspose = (localEmbed S A).conjTranspose := by
  classical
  ext x y
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · have hyx : ∀ i, i ∉ S → y i = x i := fun i hi => (hxy i hi).symm
    simp only [Matrix.conjTranspose_apply, localEmbed, if_pos hxy, if_pos hyx]
  · have hyx : ¬ ∀ i, i ∉ S → y i = x i := by
      intro h
      apply hxy
      exact fun i hi => (h i hi).symm
    simp only [Matrix.conjTranspose_apply, localEmbed, if_neg hxy, if_neg hyx, star_zero]

theorem supportedOn_zero (S : Finset (Fin n)) :
    SupportedOn (0 : Operator (PhysicalBasis n dim)) S := by
  exact ⟨0, (localEmbed_zero S).symm⟩

theorem supportedOn_one (S : Finset (Fin n)) :
    SupportedOn (1 : Operator (PhysicalBasis n dim)) S := by
  exact ⟨1, (localEmbed_one S).symm⟩

theorem SupportedOn.add {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O + P) S := by
  obtain ⟨A, rfl⟩ := hO
  obtain ⟨B, rfl⟩ := hP
  exact ⟨A + B, (localEmbed_add S A B).symm⟩

theorem SupportedOn.smul {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (z : ℂ) :
    SupportedOn (z • O) S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨z • A, (localEmbed_smul S z A).symm⟩

theorem SupportedOn.neg {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) : SupportedOn (-O) S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨-A, (localEmbed_neg S A).symm⟩

theorem SupportedOn.sub {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O - P) S := by
  rw [sub_eq_add_neg]
  exact hO.add hP.neg

theorem SupportedOn.conjTranspose {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) :
    SupportedOn O.conjTranspose S := by
  obtain ⟨A, rfl⟩ := hO
  exact ⟨A.conjTranspose, (localEmbed_conjTranspose S A).symm⟩

theorem SupportedOn.affine {O : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (a b : ℂ) :
    SupportedOn (CriticalDepth.affine O a b) S := by
  exact ((supportedOn_one S).smul a).add (hO.smul b)

theorem supportedOn_univ (O : Operator (PhysicalBasis n dim)) :
    SupportedOn O Finset.univ := by
  classical
  refine ⟨fun x y => O (fun i => x ⟨i, Finset.mem_univ i⟩)
    (fun i => y ⟨i, Finset.mem_univ i⟩), ?_⟩
  ext x y
  simp [localEmbed]

/-- Extend a local matrix to a larger local register by complementary identity. -/
def localInflate (S T : Finset (Fin n)) (hST : S ⊆ T)
    (A : Operator (LocalBasis dim S)) : Operator (LocalBasis dim T) := by
  classical
  exact fun x y =>
    if ∀ i : T, i.1 ∉ S → x i = y i then
      A (fun i => x ⟨i.1, hST i.2⟩) (fun i => y ⟨i.1, hST i.2⟩)
    else 0

theorem localEmbed_localInflate (S T : Finset (Fin n)) (hST : S ⊆ T)
    (A : Operator (LocalBasis dim S)) :
    localEmbed T (localInflate S T hST A) = localEmbed S A := by
  classical
  ext x y
  by_cases hS : ∀ i, i ∉ S → x i = y i
  · have hT : ∀ i, i ∉ T → x i = y i := by
      intro i hi
      apply hS i
      exact fun hiS => hi (hST hiS)
    have hin : ∀ i : T, i.1 ∉ S → x i.1 = y i.1 := by
      intro i hi
      exact hS i.1 hi
    unfold localEmbed localInflate
    rw [if_pos hT, if_pos hin, if_pos hS]
  · by_cases hT : ∀ i, i ∉ T → x i = y i
    · have hin : ¬ ∀ i : T, i.1 ∉ S → x i.1 = y i.1 := by
        intro h
        apply hS
        intro i hiS
        by_cases hiT : i ∈ T
        · exact h ⟨i, hiT⟩ hiS
        · exact hT i hiT
      unfold localEmbed localInflate
      rw [if_pos hT, if_neg hin, if_neg hS]
    · unfold localEmbed
      rw [if_neg hT, if_neg hS]

theorem SupportedOn.mono {O : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hST : S ⊆ T) :
    SupportedOn O T := by
  obtain ⟨A, hA⟩ := hO
  exact ⟨localInflate S T hST A, hA.trans (localEmbed_localInflate S T hST A).symm⟩

/-- Split the unchanged physical tensor basis into supported and complementary sites. -/
def basisSplit (S : Finset (Fin n)) :
    PhysicalBasis n dim ≃ LocalBasis dim S × LocalBasis dim Sᶜ := by
  classical
  exact
    { toFun := fun x => (fun i => x i.1, fun i => x i.1)
      invFun := fun p i => if hi : i ∈ S then p.1 ⟨i, hi⟩
        else p.2 ⟨i, Finset.mem_compl.mpr hi⟩
      left_inv := by
        intro x
        funext i
        by_cases hi : i ∈ S <;> simp [hi]
      right_inv := by
        intro p
        apply Prod.ext
        · funext i
          simp [i.2]
        · funext i
          have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
          simp [hi] }

/-- The explicit embedding is exactly `A ⊗ I` under the physical-basis split. -/
theorem reindex_localEmbed (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) =
      A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ)) := by
  classical
  ext p r
  change localEmbed S A ((basisSplit S).symm p) ((basisSplit S).symm r) =
    A p.1 r.1 * (1 : Operator (LocalBasis dim Sᶜ)) p.2 r.2
  have hp : (fun i : S => ((basisSplit S).symm p) i.1) = p.1 := by
    funext i
    simp [basisSplit, i.2]
  have hr : (fun i : S => ((basisSplit S).symm r) i.1) = r.1 := by
    funext i
    simp [basisSplit, i.2]
  have hout : (∀ i, i ∉ S → (basisSplit S).symm p i = (basisSplit S).symm r i) ↔
      p.2 = r.2 := by
    constructor
    · intro h
      funext i
      have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
      simpa [basisSplit, hi] using h i.1 hi
    · intro h i hi
      have he := congrFun h ⟨i, Finset.mem_compl.mpr hi⟩
      simpa [basisSplit, hi] using he
  by_cases hpr : p.2 = r.2 <;>
    simp [localEmbed, hout, hp, hr, Matrix.one_apply, hpr]

theorem localEmbed_mul (S : Finset (Fin n)) (A B : Operator (LocalBasis dim S)) :
    localEmbed S (A * B) = localEmbed S A * localEmbed S B := by
  classical
  apply (Matrix.reindexRingEquiv ℂ (basisSplit S)).injective
  rw [(Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul]
  change Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S (A * B)) =
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S B)
  rw [reindex_localEmbed, reindex_localEmbed, reindex_localEmbed]
  simpa only [one_mul] using
    (Matrix.mul_kronecker_mul A B (1 : Operator (LocalBasis dim Sᶜ))
      (1 : Operator (LocalBasis dim Sᶜ)))

theorem reindex_localEmbed_compl (S : Finset (Fin n))
    (B : Operator (LocalBasis dim Sᶜ)) :
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) =
      (1 : Operator (LocalBasis dim S)) ⊗ₖ B := by
  classical
  ext p r
  change localEmbed Sᶜ B ((basisSplit S).symm p) ((basisSplit S).symm r) =
    (1 : Operator (LocalBasis dim S)) p.1 r.1 * B p.2 r.2
  have hp : (fun i : ↥(Sᶜ) => ((basisSplit S).symm p) i.1) = p.2 := by
    funext i
    have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
    simp [basisSplit, hi]
  have hr : (fun i : ↥(Sᶜ) => ((basisSplit S).symm r) i.1) = r.2 := by
    funext i
    have hi : i.1 ∉ S := Finset.mem_compl.mp i.2
    simp [basisSplit, hi]
  have hout : (∀ i, i ∉ Sᶜ → (basisSplit S).symm p i = (basisSplit S).symm r i) ↔
      p.1 = r.1 := by
    constructor
    · intro h
      funext i
      have hi : i.1 ∉ Sᶜ := by simpa using i.2
      simpa [basisSplit, i.2] using h i.1 hi
    · intro h i hi
      have hiS : i ∈ S := by simpa using hi
      have he := congrFun h ⟨i, hiS⟩
      simpa [basisSplit, hiS] using he
  unfold localEmbed
  by_cases hpr : p.1 = r.1
  · have hcond := hout.mpr hpr
    rw [if_pos hcond, hp, hr]
    simp [Matrix.one_apply, hpr]
  · have hcond : ¬ ∀ i, i ∉ Sᶜ →
        (basisSplit S).symm p i = (basisSplit S).symm r i := by
      intro h
      exact hpr (hout.mp h)
    rw [if_neg hcond]
    simp [Matrix.one_apply, hpr]

theorem localEmbed_commute_compl (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) (B : Operator (LocalBasis dim Sᶜ)) :
    Commute (localEmbed S A) (localEmbed Sᶜ B) := by
  classical
  change localEmbed S A * localEmbed Sᶜ B = localEmbed Sᶜ B * localEmbed S A
  apply (Matrix.reindexRingEquiv ℂ (basisSplit S)).injective
  rw [(Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul,
    (Matrix.reindexRingEquiv ℂ (basisSplit S)).map_mul]
  change Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) =
    Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed Sᶜ B) *
      Matrix.reindex (basisSplit S) (basisSplit S) (localEmbed S A)
  simp only [reindex_localEmbed, reindex_localEmbed_compl]
  calc
    (A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ))) *
        ((1 : Operator (LocalBasis dim S)) ⊗ₖ B) =
        (A * 1) ⊗ₖ ((1 : Operator (LocalBasis dim Sᶜ)) * B) :=
      (Matrix.mul_kronecker_mul A 1 1 B).symm
    _ = ((1 : Operator (LocalBasis dim S)) * A) ⊗ₖ (B * 1) := by simp
    _ = ((1 : Operator (LocalBasis dim S)) ⊗ₖ B) *
        (A ⊗ₖ (1 : Operator (LocalBasis dim Sᶜ))) :=
      Matrix.mul_kronecker_mul 1 A B 1

theorem SupportedOn.mul_same {O P : Operator (PhysicalBasis n dim)}
    {S : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P S) :
    SupportedOn (O * P) S := by
  obtain ⟨A, rfl⟩ := hO
  obtain ⟨B, rfl⟩ := hP
  exact ⟨A * B, (localEmbed_mul S A B).symm⟩

/-- Products are supported on the union of their concrete tensor supports. -/
theorem SupportedOn.mul {O P : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P T) :
    SupportedOn (O * P) (S ∪ T) := by
  exact (hO.mono Finset.subset_union_left).mul_same
    (hP.mono Finset.subset_union_right)

theorem SupportedOn.conjugate {O U : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hU : SupportedOn U T) :
    SupportedOn (U * O * U.conjTranspose) (S ∪ T) := by
  have hO' : SupportedOn O (S ∪ T) := hO.mono Finset.subset_union_left
  have hU' : SupportedOn U (S ∪ T) := hU.mono Finset.subset_union_right
  exact (hU'.mul_same hO').mul_same hU'.conjTranspose

/-- Tensor-local operators on disjoint site sets commute. -/
theorem SupportedOn.commute {O P : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hP : SupportedOn P T)
    (hST : Disjoint S T) : Commute O P := by
  classical
  have hTS : T ⊆ Sᶜ := by
    intro i hiT
    apply Finset.mem_compl.mpr
    intro hiS
    exact Finset.disjoint_left.mp hST hiS hiT
  obtain ⟨A, hA⟩ := hO
  obtain ⟨B, hB⟩ := hP.mono hTS
  rw [hA, hB]
  exact localEmbed_commute_compl S A B

theorem SupportedOn.conjugate_disjoint {O U : Operator (PhysicalBasis n dim)}
    {S T : Finset (Fin n)} (hO : SupportedOn O S) (hU : SupportedOn U T)
    (hST : Disjoint S T) (hunit : IsUnitary U) :
    U * O * U.conjTranspose = O := by
  have hc : O * U = U * O := hO.commute hU hST
  have hUU : U * U.conjTranspose = 1 := hunit.2
  rw [← hc, mul_assoc, hUU, mul_one]

theorem supportedOn_list_prod (gates : List (Operator (PhysicalBasis n dim)))
    (S : Finset (Fin n)) (h : ∀ A ∈ gates, SupportedOn A S) :
    SupportedOn gates.prod S := by
  revert h
  induction gates with
  | nil =>
      intro h
      simpa using supportedOn_one (dim := dim) S
  | cons A gates ih =>
      intro h
      have hA : SupportedOn A S := h A (by simp)
      have hg : ∀ B ∈ gates, SupportedOn B S := by
        intro B hB
        exact h B (by simp [hB])
      simpa using hA.mul_same (ih hg)

def Layer.supportUnion {q : ℕ} (L : Layer n dim q) : Finset (Fin n) :=
  Finset.univ.biUnion L.support

theorem Layer.eval_supportedOn {q : ℕ} (L : Layer n dim q) :
    SupportedOn L.eval L.supportUnion := by
  classical
  apply supportedOn_list_prod
  intro A hA
  have hA' : ∃ i, L.gate i = A := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hA
  obtain ⟨i, rfl⟩ := hA'
  apply (L.locality i).mono
  intro j hj
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hj⟩

def Layer.activeIndices {q : ℕ} (L : Layer n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ¬ Disjoint (L.support i) S

/-- Sites already in the support, together with precisely the intersecting gates. -/
def Layer.lightCone {q : ℕ} (L : Layer n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := S ∪ (L.activeIndices S).biUnion L.support

theorem Layer.support_subset_lightCone_or_disjoint {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) (i : Fin n) :
    L.support i ⊆ L.lightCone S ∨ Disjoint (L.support i) (L.lightCone S) := by
  classical
  by_cases hi : Disjoint (L.support i) S
  · right
    apply Finset.disjoint_left.mpr
    intro x hxi hx
    rcases Finset.mem_union.mp hx with hxS | hxA
    · exact Finset.disjoint_left.mp hi hxi hxS
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hxA
      have hjact : ¬ Disjoint (L.support j) S := (Finset.mem_filter.mp hj).2
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hjact hi
      exact Finset.disjoint_left.mp (L.disjoint i j hij) hxi hxj
  · left
    intro x hx
    apply Finset.mem_union.mpr
    right
    apply Finset.mem_biUnion.mpr
    exact ⟨i, by simp [Layer.activeIndices, hi], hx⟩

private theorem supportedOn_conjugate_prod
    (gates : List (Operator (PhysicalBasis n dim))) (S : Finset (Fin n))
    (hstep : ∀ U ∈ gates, ∀ P : Operator (PhysicalBasis n dim), SupportedOn P S →
      SupportedOn (U * P * U.conjTranspose) S)
    (O : Operator (PhysicalBasis n dim)) (hO : SupportedOn O S) :
    SupportedOn (gates.prod * O * gates.prod.conjTranspose) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep
      simpa using hO
  | cons U gates ih =>
      intro hstep
      have hg : ∀ V ∈ gates, ∀ P : Operator (PhysicalBasis n dim), SupportedOn P S →
          SupportedOn (V * P * V.conjTranspose) S := by
        intro V hV P hP
        exact hstep V (by simp [hV]) P hP
      have hinner := ih hg
      have houter := hstep U (by simp) _ hinner
      simpa only [List.prod_cons, Matrix.conjTranspose_mul, mul_assoc] using houter

/-- The exact matrix light-cone law, proved by tensor commutation and cancellation. -/
theorem Layer.conjugate_supportedOn {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) {O : Operator (PhysicalBasis n dim)} (hO : SupportedOn O S) :
    SupportedOn (L.eval * O * L.eval.conjTranspose) (L.lightCone S) := by
  classical
  change SupportedOn (((List.ofFn L.gate).reverse).prod * O *
    (((List.ofFn L.gate).reverse).prod).conjTranspose) (L.lightCone S)
  apply supportedOn_conjugate_prod ((List.ofFn L.gate).reverse) (L.lightCone S)
    ?_ O (hO.mono Finset.subset_union_left)
  intro U hU P hP
  have hU' : ∃ i, L.gate i = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  rcases L.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hi : SupportedOn (L.gate i) (L.lightCone S) := (L.locality i).mono hsub
    exact (hi.mul_same hP).mul_same hi.conjTranspose
  · rw [hP.conjugate_disjoint (L.locality i) hdis.symm (L.unitary i)]
    exact hP

/-- The unique gate block containing a site, or that idle site's singleton. -/
def Layer.blockAt {q : ℕ} (L : Layer n dim q) (x : Fin n) : Finset (Fin n) := by
  classical
  exact if h : ∃ i, x ∈ L.support i then L.support (Classical.choose h) else {x}

theorem Layer.mem_blockAt {q : ℕ} (L : Layer n dim q) (x : Fin n) :
    x ∈ L.blockAt x := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · exact Classical.choose_spec h
  · simp

theorem Layer.blockAt_card_le {q : ℕ} (L : Layer n dim q) (x : Fin n) (hq : 1 ≤ q) :
    (L.blockAt x).card ≤ q := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · exact L.arity (Classical.choose h)
  · simpa using hq

theorem Layer.blockAt_eq_of_mem {q : ℕ} (L : Layer n dim q) (i : Fin n)
    (x : Fin n) (hx : x ∈ L.support i) : L.blockAt x = L.support i := by
  classical
  unfold Layer.blockAt
  split_ifs with h
  · have hci : Classical.choose h = i := by
      by_contra hne
      exact Finset.disjoint_left.mp (L.disjoint _ _ hne) (Classical.choose_spec h) hx
    rw [hci]
  · exact False.elim (h ⟨i, hx⟩)

theorem Layer.lightCone_subset_blocks {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) : L.lightCone S ⊆ S.biUnion L.blockAt := by
  classical
  intro y hy
  rcases Finset.mem_union.mp hy with hyS | hyA
  · exact Finset.mem_biUnion.mpr ⟨y, hyS, L.mem_blockAt y⟩
  · obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hyA
    have hact : ¬ Disjoint (L.support i) S := (Finset.mem_filter.mp hi).2
    have hex : ∃ x, x ∈ L.support i ∧ x ∈ S := by
      by_contra hn
      apply hact
      apply Finset.disjoint_left.mpr
      intro x hxi hxS
      exact hn ⟨x, hxi, hxS⟩
    obtain ⟨x, hxi, hxS⟩ := hex
    apply Finset.mem_biUnion.mpr
    refine ⟨x, hxS, ?_⟩
    rw [L.blockAt_eq_of_mem i x hxi]
    exact hyi

/-- Disjoint q-ary gates increase the number of supported sites by at most q. -/
theorem Layer.lightCone_card_le {q : ℕ} (L : Layer n dim q)
    (S : Finset (Fin n)) (hq : 1 ≤ q) : (L.lightCone S).card ≤ q * S.card := by
  classical
  calc
    (L.lightCone S).card ≤ (S.biUnion L.blockAt).card :=
      Finset.card_le_card (L.lightCone_subset_blocks S)
    _ ≤ ∑ x ∈ S, (L.blockAt x).card := by apply Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, q := Finset.sum_le_sum fun x _ => L.blockAt_card_le x hq
    _ = q * S.card := by simp [Nat.mul_comm]

/-- Evaluation in physical execution order: the first listed layer acts first. -/
def layerSequenceEval {q : ℕ} : List (Layer n dim q) → Operator (PhysicalBasis n dim)
  | [] => 1
  | L :: layers => layerSequenceEval layers * L.eval

def layerSequenceCone {q : ℕ} : List (Layer n dim q) → Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => layerSequenceCone layers (L.lightCone S)

theorem layerSequenceEval_eq_reverse_prod {q : ℕ} (layers : List (Layer n dim q)) :
    layerSequenceEval layers = (layers.map Layer.eval).reverse.prod := by
  induction layers with
  | nil => simp [layerSequenceEval]
  | cons L layers ih =>
      simp [layerSequenceEval, ih, List.reverse_cons, List.prod_append]

theorem layerSequence_conjugate_supportedOn {q : ℕ} (layers : List (Layer n dim q))
    (S : Finset (Fin n)) {O : Operator (PhysicalBasis n dim)} (hO : SupportedOn O S) :
    SupportedOn (layerSequenceEval layers * O * (layerSequenceEval layers).conjTranspose)
      (layerSequenceCone layers S) := by
  induction layers generalizing S O with
  | nil => simpa [layerSequenceEval, layerSequenceCone] using hO
  | cons L layers ih =>
      have hinner := L.conjugate_supportedOn S hO
      have houter := ih (L.lightCone S) hinner
      simpa only [layerSequenceEval, layerSequenceCone, Matrix.conjTranspose_mul,
        mul_assoc] using houter

theorem layerSequenceCone_card_le {q : ℕ} (layers : List (Layer n dim q))
    (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (layerSequenceCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [layerSequenceCone]
  | cons L layers ih =>
      calc
        (layerSequenceCone (L :: layers) S).card =
            (layerSequenceCone layers (L.lightCone S)).card := rfl
        _ ≤ q ^ layers.length * (L.lightCone S).card := ih (L.lightCone S)
        _ ≤ q ^ layers.length * (q * S.card) :=
          Nat.mul_le_mul_left _ (L.lightCone_card_le S hq)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_Support

/- ===== Source block: AlgebraicFiniteImage; SHA-256 39ab40ee8ae2b5463543f378d74b1fac179485e0bc31318f37c05e727ba62811 ===== -/
section Merged_AlgebraicFiniteImage
/-!
# A derivational criterion for finite algebraic evaluation images

This module combines the scalar-constants criterion, the minimal-prime
integrality argument, and finiteness of evaluations of integral
coordinates. Its derivative-vanishing premise is a substantive hypothesis
to be established from the actual circuit and code equations.
-/

namespace CriticalDepth

universe u v w

variable (F : Type u) (R : Type v)
variable [Field F] [CommRing R] [Algebra F R]

/-- The canonical algebra homomorphism into the fraction ring of an ideal
quotient. A prime ideal will later make the codomain a field. -/
noncomputable def quotientFractionMap (p : Ideal R) :
    R →ₐ[F] FractionRing (R ⧸ p) :=
  (IsScalarTower.toAlgHom F (R ⧸ p) (FractionRing (R ⧸ p))).comp
    (Ideal.Quotient.mkₐ F p)

/-- For a prime ideal, passing from its quotient domain to its fraction
field introduces no further kernel. -/
theorem quotientFractionMap_ker (p : Ideal R) [p.IsPrime] :
    RingHom.ker (quotientFractionMap F R p).toRingHom = p := by
  ext r
  change algebraMap (R ⧸ p) (FractionRing (R ⧸ p))
      (Ideal.Quotient.mk p r) = 0 ↔ r ∈ p
  constructor
  · intro hr
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ p) (FractionRing (R ⧸ p))
    simpa only [map_zero] using hr
  · intro hr
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

section PrimeDerivationCriterion

variable [IsAlgClosed F] [CharZero F] [IsNoetherianRing R]

/-- Vanishing of all base-linear derivatives in the minimal-prime fraction
fields forces an element of a Noetherian algebra to be integral. -/
theorem isIntegral_of_minimalPrime_derivations
    (r : R)
    (h : ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ d : Derivation F (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        d (quotientFractionMap F R p r) = 0) :
    IsIntegral F r := by
  apply isIntegral_of_scalar_mod_minimalPrimes F R r
  intro p hp
  letI : p.IsPrime := hp.isPrime
  let K := FractionRing (R ⧸ p)
  letI : CharZero K := ⟨by
    intro m n hmn
    have hF : (m : F) = (n : F) :=
      (algebraMap F K).injective (by simpa only [map_natCast] using hmn)
    exact Nat.cast_injective hF⟩
  obtain ⟨c, hc⟩ :=
    exists_scalar_mod_kernel_of_forall_derivation_eq_zero F K R
      (quotientFractionMap F R p) r (h p hp)
  refine ⟨c, ?_⟩
  change r - algebraMap F R c ∈
    RingHom.ker (quotientFractionMap F R p).toRingHom at hc
  rw [quotientFractionMap_ker F R p] at hc
  exact hc

/-- A finite collection of coordinates has a finite evaluation image if
all their relative derivatives vanish in every minimal-prime fraction
field. This statement includes nonreduced coordinate algebras. -/
theorem evaluation_image_finite_of_minimalPrime_derivations
    {ι : Type w} [Fintype ι] (r : ι → R)
    (h : ∀ i, ∀ p ∈ (⊥ : Ideal R).minimalPrimes,
      ∀ d : Derivation F (FractionRing (R ⧸ p)) (FractionRing (R ⧸ p)),
        d (quotientFractionMap F R p (r i)) = 0) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  apply integral_coordinate_evaluation_image_finite r
  intro i
  exact isIntegral_of_minimalPrime_derivations F R (r i) (h i)

/-- A field-valued formulation of the criterion. This lets an application
prove its derivative identity for arbitrary field-valued solutions of the
coordinate equations and then specialize to the prime fraction fields. -/
theorem evaluation_image_finite_of_all_field_derivations
    {ι : Type w} [Fintype ι] (r : ι → R)
    (h : ∀ (K : Type v) [Field K] [Algebra F K]
      (φ : R →ₐ[F] K) (i : ι) (d : Derivation F K K),
        d (φ (r i)) = 0) :
    (Set.range fun f : R →ₐ[F] F => fun i => f (r i)).Finite := by
  apply evaluation_image_finite_of_minimalPrime_derivations F R r
  intro i p hp d
  letI : p.IsPrime := hp.isPrime
  exact h (FractionRing (R ⧸ p)) (quotientFractionMap F R p) i d

end PrimeDerivationCriterion

end CriticalDepth
end Merged_AlgebraicFiniteImage

/- ===== Source block: CircuitParameters; SHA-256 5de081dad176ba0ccd52cac651b6e076a37cf320c69393928ebc826c381e1eaf ===== -/
section Merged_CircuitParameters
/-!
# A polynomial presentation containing every circuit on one support arrangement

Forward gates and inverse gates have independent local matrix variables.
Logical and gauge factors also have independent inverse variables. The
relations impose two-sided inverses and both encoded intertwining equations.
These are definitions of the proposed algebraic presentation. The actual
unitary-evaluation correspondence and its derivation-vanishing theorem are
separate open proof obligations, not assumptions of a claimed main proof.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

abbrev GateIndex (n h : ℕ) := Fin h × Fin n

abbrev CircuitVariable {n : ℕ} (dim : Fin n → ℕ) (K g h : ℕ)
    (support : GateIndex n h → Finset (Fin n)) :=
  (Σ p : GateIndex n h,
    Bool × LocalBasis dim (support p) × LocalBasis dim (support p)) ⊕
  (Bool × Fin K × Fin K) ⊕ (Bool × Fin g × Fin g)

/-- Coefficient-wise extension of an actual local complex-matrix basis. -/
def coefficientEmbed {n : ℕ} {dim : Fin n → ℕ} {R : Type*}
    [CommRing R] [Algebra ℂ R] (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) R) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) R :=
  ∑ a, ∑ b, A a b •
    (localEmbed S (Matrix.single a b (1 : ℂ))).map (algebraMap ℂ R)

section Presentation

variable {n K g h : ℕ} {dim : Fin n → ℕ}
variable (support : GateIndex n h → Finset (Fin n))

abbrev CircuitPolynomial := MvPolynomial (CircuitVariable dim K g h support) ℂ

def localGatePolynomial (p : GateIndex n h) (inverse : Bool) :
    Matrix (LocalBasis dim (support p)) (LocalBasis dim (support p))
      (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inl ⟨p, inverse, a, b⟩)

def physicalGatePolynomial (p : GateIndex n h) (inverse : Bool) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  coefficientEmbed (support p) (localGatePolynomial support p inverse)

def logicalPolynomial (inverse : Bool) :
    Matrix (Fin K) (Fin K) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inr (.inl (inverse, a, b)))

def gaugePolynomial (inverse : Bool) :
    Matrix (Fin g) (Fin g) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  fun a b => MvPolynomial.X (.inr (.inr (inverse, a, b)))

def executionGateIndices : List (GateIndex n h) :=
  (List.ofFn fun layer : Fin h => List.ofFn fun slot : Fin n => (layer, slot)).flatten

def totalPolynomial :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  ((executionGateIndices (n := n) (h := h)).map
    (fun p => physicalGatePolynomial support p false)).reverse.prod

def inverseTotalPolynomial :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  ((executionGateIndices (n := n) (h := h)).map
    (fun p => physicalGatePolynomial support p true)).prod

def matrixRelationEntries {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (dim := dim) (K := K) (g := g) support)) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  Set.range fun p : ι × κ => A p.1 p.2 - B p.1 p.2

def inverseRelationEntries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (dim := dim) (K := K) (g := g) support)) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  matrixRelationEntries support (A * B) 1 ∪
    matrixRelationEntries support (B * A) 1

def circuitRelations (C : Code n dim K g) : Set (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  (⋃ p : GateIndex n h,
    inverseRelationEntries support (physicalGatePolynomial support p false)
      (physicalGatePolynomial support p true)) ∪
  inverseRelationEntries support (logicalPolynomial support false) (logicalPolynomial support true) ∪
  inverseRelationEntries support (gaugePolynomial support false) (gaugePolynomial support true) ∪
  matrixRelationEntries support
    (totalPolynomial support * C.encoding.map MvPolynomial.C)
    (C.encoding.map MvPolynomial.C *
      (logicalPolynomial support false ⊗ₖ gaugePolynomial support false)) ∪
  matrixRelationEntries support
    (C.encoding.conjTranspose.map MvPolynomial.C * totalPolynomial support)
    ((logicalPolynomial support false ⊗ₖ gaugePolynomial support false) *
      C.encoding.conjTranspose.map MvPolynomial.C)

def circuitIdeal (C : Code n dim K g) : Ideal (CircuitPolynomial (dim := dim) (K := K) (g := g) support) :=
  Ideal.span (circuitRelations support C)

abbrev CircuitCoordinateRing (C : Code n dim K g) :=
  CircuitPolynomial (dim := dim) (K := K) (g := g) support ⧸ circuitIdeal support C

end Presentation

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_CircuitParameters

/- ===== Source block: LayerOperations; SHA-256 6351e0efea697f274db1dbd32e5147e524dbdb9cc44b605d5f9d50154e78933f ===== -/
section Merged_LayerOperations
/-!
# Operations on actual full-register layers

Layer inversion reverses the gate slots before taking adjoints. It therefore
does not assume an unproved permutation law for the layer product. The
single-gate constructor keeps the same physical register and uses identity
gates on empty supports in every other slot.
-/

noncomputable section

namespace CriticalDepth

open Matrix

theorem isUnitary_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    IsUnitary (1 : Operator ι) := by
  constructor <;> simp

theorem isUnitary_star {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Operator ι} (hU : IsUnitary U) : IsUnitary (star U) := by
  constructor
  · simpa only [star_star] using hU.2
  · simpa only [star_star] using hU.1

theorem isUnitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Operator ι} (hU : IsUnitary U) (hV : IsUnitary V) : IsUnitary (U * V) := by
  constructor
  · calc
      star (U * V) * (U * V) = star V * (star U * U) * V := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · calc
      (U * V) * star (U * V) = U * (V * star V) * star U := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hV.2, mul_one, hU.2]

theorem matrixList_prod_isUnitary
    {ι : Type*} [Fintype ι] [DecidableEq ι] (gates : List (Operator ι))
    (hgate : ∀ U ∈ gates, IsUnitary U) : IsUnitary gates.prod := by
  revert hgate
  induction gates with
  | nil =>
      intro hgate
      exact isUnitary_one
  | cons U gates ih =>
      intro hgate
      have hU := hgate U (by simp)
      have hg : ∀ V ∈ gates, IsUnitary V := by
        intro V hV
        exact hgate V (by simp [hV])
      exact isUnitary_mul hU (ih hg)

theorem star_matrixList_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (gates : List (Operator ι)) :
    star gates.prod = (gates.reverse.map star).prod := by
  induction gates with
  | nil => simp
  | cons U gates ih =>
      simp [List.prod_cons, star_mul, ih, List.reverse_cons, List.map_append, List.prod_append]

private theorem reverse_ofFn_slots {α : Type*} {m : ℕ} (f : Fin m → α) :
    (List.ofFn f).reverse = List.ofFn (fun i => f i.rev) := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_reverse, List.length_ofFn, List.getElem_ofFn]
  apply congrArg f
  apply Fin.ext
  simp [Fin.rev] <;> omega

namespace Manuscript

variable {n q : ℕ} {dim : Fin n → ℕ}

def Layer.adjoint (L : Layer n dim q) : Layer n dim q where
  support i := L.support i.rev
  gate i := star (L.gate i.rev)
  disjoint := by
    intro i j hij
    apply L.disjoint
    intro h
    apply hij
    have hh := congrArg Fin.rev h
    simpa only [Fin.rev_rev] using hh
  arity i := L.arity i.rev
  locality i := by
    change SupportedOn (L.gate i.rev).conjTranspose (L.support i.rev)
    exact (L.locality i.rev).conjTranspose
  unitary i := isUnitary_star (L.unitary i.rev)

theorem Layer.evalIsUnitary (L : Layer n dim q) : IsUnitary L.eval := by
  apply matrixList_prod_isUnitary
  intro U hU
  have hU' : ∃ i, L.gate i = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  exact L.unitary i

theorem Layer.eval_adjoint (L : Layer n dim q) : L.adjoint.eval = star L.eval := by
  simp [Layer.eval, Layer.adjoint, reverse_ofFn_slots, List.map_ofFn,
    star_matrixList_prod, Fin.rev_rev, Function.comp_def]

theorem layerSequenceEval_isUnitary (layers : List (Layer n dim q)) :
    IsUnitary (layerSequenceEval layers) := by
  induction layers with
  | nil => exact isUnitary_one
  | cons L layers ih =>
      exact isUnitary_mul ih L.evalIsUnitary

theorem layerSequenceEval_append (first second : List (Layer n dim q)) :
    layerSequenceEval (first ++ second) =
      layerSequenceEval second * layerSequenceEval first := by
  induction first with
  | nil => simp [layerSequenceEval]
  | cons L first ih => simp [layerSequenceEval, ih, mul_assoc]

theorem layerSequenceEval_reverse_adjoint (layers : List (Layer n dim q)) :
    layerSequenceEval (layers.reverse.map Layer.adjoint) = star (layerSequenceEval layers) := by
  induction layers with
  | nil => simp [layerSequenceEval]
  | cons L layers ih =>
      have ih' : layerSequenceEval (layers.map Layer.adjoint).reverse =
          star (layerSequenceEval layers) := by
        simpa only [List.map_reverse] using ih
      simp [List.reverse_cons, List.map_append, layerSequenceEval_append,
        layerSequenceEval, Layer.eval_adjoint, ih', star_mul]

def singleGateLayer (hn : 0 < n) (S : Finset (Fin n))
    (U : Operator (PhysicalBasis n dim)) (hS : S.card ≤ q)
    (hsupported : SupportedOn U S) (hunitary : IsUnitary U) : Layer n dim q where
  support i := if i.val = 0 then S else ∅
  gate i := if i.val = 0 then U else 1
  disjoint := by
    intro i j hij
    by_cases hi : i.val = 0
    · by_cases hj : j.val = 0
      · exact False.elim (hij (Fin.ext (hi.trans hj.symm)))
      · simp [hi, hj]
    · simp [hi]
  arity i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hS
    · simp [hi]
  locality i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hsupported
    · simpa [hi] using supportedOn_one (dim := dim) (∅ : Finset (Fin n))
  unitary i := by
    by_cases hi : i.val = 0
    · simpa [hi] using hunitary
    · simpa [hi] using (isUnitary_one (ι := PhysicalBasis n dim))

theorem singleGateLayer_eval (hn : 0 < n) (S : Finset (Fin n))
    (U : Operator (PhysicalBasis n dim)) (hS : S.card ≤ q)
    (hsupported : SupportedOn U S) (hunitary : IsUnitary U) :
    (singleGateLayer hn S U hS hsupported hunitary).eval = U := by
  cases n with
  | zero => omega
  | succ m =>
      simp [Layer.eval, singleGateLayer, List.ofFn_succ, List.reverse_cons, List.prod_append]

end Manuscript
end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_LayerOperations

/- ===== Source block: PauliSpan; SHA-256 686238212d7f49ccae85eb5a5baf7cb9af67acf91e589f0c01f88ce72bcf3eb5 ===== -/
section Merged_PauliSpan
/-!
# Pauli strings span every finite-qubit operator space

This is an explicit matrix expansion over complex scalars. It uses all
operators, including non-Hermitian operators, and all physical basis entries.
The code-distance argument can therefore apply it to an arbitrary supported
undetectable operator without adding a Pauli-witness hypothesis.
-/

noncomputable section

namespace CriticalDepth

open Matrix
open scoped BigOperators

theorem matrix_eq_sum_matrixUnits
    {α : Type*} [Fintype α] [DecidableEq α] (A : Operator α) :
    A = ∑ i : α, ∑ j : α, A i j • matrixUnit i j := by
  classical
  funext x y
  simp only [Matrix.sum_apply]
  change A x y = ∑ i : α, ∑ j : α, A i j * (if x = i ∧ y = j then 1 else 0)
  simp [ite_and, mul_ite]

theorem tensorEntries_sum
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] {α β : I → Type*}
    (A : ∀ i, J → Matrix (α i) (β i) ℂ) :
    tensorEntries (fun i => ∑ j : J, A i j) =
      ∑ p : I → J, tensorEntries (fun i => A i (p i)) := by
  classical
  ext x y
  simp only [tensorEntries, Matrix.sum_apply]
  exact Fintype.prod_sum (fun i j => A i j (x i) (y i))

namespace Manuscript

def singlePauliCoefficient (A : Operator (Fin 2)) : SinglePauli → ℂ
  | .I => (A 0 0 + A 1 1) / 2
  | .X => (A 0 1 + A 1 0) / 2
  | .Y => Complex.I * (A 0 1 - A 1 0) / 2
  | .Z => (A 0 0 - A 1 1) / 2

theorem singlePauli_expansion (A : Operator (Fin 2)) :
    A = ∑ p : SinglePauli, singlePauliCoefficient A p • p.matrix := by
  classical
  have hu : (Finset.univ : Finset SinglePauli) = {.I, .X, .Y, .Z} := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hu, singlePauliCoefficient, SinglePauli.matrix] <;>
    ring_nf <;> simp only [pow_two, Complex.I_mul_I] <;> ring

def tensorPauli {I : Type*} [Fintype I] (p : I → SinglePauli) :
    Operator (I → Fin 2) :=
  tensorEntries (fun i => (p i).matrix)

def pauliTensorSpan (I : Type*) [Fintype I] : Submodule ℂ (Operator (I → Fin 2)) :=
  Submodule.span ℂ (Set.range (tensorPauli (I := I)))

theorem matrixUnit_eq_tensorEntries
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I → Fin 2) :
    matrixUnit x y = tensorEntries (fun i => matrixUnit (x i) (y i)) := by
  classical
  ext a b
  by_cases h : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h
    simp [matrixUnit, tensorEntries]
  · have hex : ∃ i, a i ≠ x i ∨ b i ≠ y i := by
      by_contra hn
      apply h
      constructor
      · funext i
        by_contra hi
        exact hn ⟨i, Or.inl hi⟩
      · funext i
        by_contra hi
        exact hn ⟨i, Or.inr hi⟩
    obtain ⟨i, hi⟩ := hex
    have hzero : (∏ j, matrixUnit (x j) (y j) (a j) (b j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rcases hi with hi | hi <;> simp [matrixUnit, hi]
    simpa [tensorEntries, matrixUnit, h] using hzero.symm

theorem matrixUnit_mem_pauliTensorSpan
    {I : Type*} [Fintype I] [DecidableEq I] (x y : I → Fin 2) :
    matrixUnit x y ∈ pauliTensorSpan I := by
  classical
  rw [matrixUnit_eq_tensorEntries]
  have hlocal : (fun i => matrixUnit (x i) (y i)) =
      (fun i => ∑ p : SinglePauli,
        singlePauliCoefficient (matrixUnit (x i) (y i)) p • p.matrix) := by
    funext i
    exact singlePauli_expansion (matrixUnit (x i) (y i))
  rw [hlocal, tensorEntries_sum]
  apply Submodule.sum_mem
  intro p hp
  rw [tensorEntries_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨p, rfl⟩

theorem tensorPauli_span_eq_top
    {I : Type*} [Fintype I] [DecidableEq I] : pauliTensorSpan I = ⊤ := by
  classical
  apply top_unique
  intro A hA
  rw [matrix_eq_sum_matrixUnits A]
  apply Submodule.sum_mem
  intro x hx
  apply Submodule.sum_mem
  intro y hy
  exact Submodule.smul_mem _ _ (matrixUnit_mem_pauliTensorSpan x y)

theorem unphased_pauliMatrix_span_eq_top (n : ℕ) :
    Submodule.span ℂ (Set.range (fun p : Fin n → SinglePauli => pauliMatrix (0 : Fin 4) p)) =
      (⊤ : Submodule ℂ (Operator (QubitBasis n))) := by
  simp_rw [pauliMatrix_zero_eq_tensorEntries]
  change pauliTensorSpan (Fin n) = ⊤
  exact tensorPauli_span_eq_top

theorem local_pauliTensor_span_eq_top {n : ℕ} (S : Finset (Fin n)) :
    Submodule.span ℂ (Set.range (fun p : S → SinglePauli => tensorEntries (fun i => (p i).matrix))) =
      (⊤ : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S))) := by
  change pauliTensorSpan S = ⊤
  exact tensorPauli_span_eq_top

theorem pauliMatrix_eq_localEmbed_of_outside_identity
    {n : ℕ} (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) :
    pauliMatrix (0 : Fin 4) p =
      localEmbed S (tensorPauli (fun i : S => p i.1)) := by
  classical
  ext x y
  let f : Fin n → ℂ := fun i => (p i).matrix (x i) (y i)
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · have hprod : (∏ i ∈ S, f i) = ∏ i, f i := by
      apply Finset.prod_subset (Finset.subset_univ S)
      intro i hi hiS
      dsimp [f]
      rw [hout i hiS]
      change (1 : Operator (Fin 2)) (x i) (y i) = 1
      rw [hxy i hiS]
      simp [Matrix.one_apply]
    have hlocal : (∏ i : S, f i.1) = ∏ i ∈ S, f i := Finset.prod_coe_sort S f
    change (Complex.I ^ 0) * (∏ i, f i) =
      if ∀ i, i ∉ S → x i = y i then ∏ i : S, f i.1 else 0
    rw [if_pos hxy, pow_zero, one_mul]
    exact hprod.symm.trans hlocal.symm
  · have hex : ∃ i, i ∉ S ∧ x i ≠ y i := by
      by_contra hn
      apply hxy
      intro i hiS
      by_contra hi
      exact hn ⟨i, hiS, hi⟩
    obtain ⟨i, hiS, hi⟩ := hex
    have hzero : (∏ j, f j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      dsimp [f]
      rw [hout i hiS]
      simp [SinglePauli.matrix, Matrix.one_apply, hi]
    change (Complex.I ^ 0) * (∏ j, f j) =
      if ∀ i, i ∉ S → x i = y i then ∏ i : S, f i.1 else 0
    rw [if_neg hxy, pow_zero, one_mul]
    exact hzero

theorem pauliMatrix_supportedOn_of_outside_identity
    {n : ℕ} (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) :
    SupportedOn (pauliMatrix (0 : Fin 4) p) S := by
  exact ⟨tensorPauli (fun i : S => p i.1),
    pauliMatrix_eq_localEmbed_of_outside_identity S p hout⟩

def extendLocalPauli {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    Fin n → SinglePauli :=
  fun i => if hi : i ∈ S then p ⟨i, hi⟩ else .I

theorem pauliMatrix_extendLocalPauli_eq_localEmbed
    {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    pauliMatrix (0 : Fin 4) (extendLocalPauli S p) = localEmbed S (tensorPauli p) := by
  classical
  have hout : ∀ i, i ∉ S → extendLocalPauli S p i = .I := by
    intro i hi
    simp [extendLocalPauli, hi]
  have hrestrict : (fun i : S => extendLocalPauli S p i.1) = p := by
    funext i
    simp [extendLocalPauli, i.2]
  have h := pauliMatrix_eq_localEmbed_of_outside_identity S (extendLocalPauli S p) hout
  simpa only [hrestrict] using h

theorem pauliMatrix_extendLocalPauli_supportedOn
    {n : ℕ} (S : Finset (Fin n)) (p : S → SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) S := by
  exact ⟨tensorPauli p, pauliMatrix_extendLocalPauli_eq_localEmbed S p⟩

end Manuscript
end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliSpan

/- ===== Source block: ScalarExtension; SHA-256 a4320bd7e559673e9fcb6dadc4c1127f9aabce73284b86ee4def6eb0cdb10539 ===== -/
section Merged_ScalarExtension
/-!
# Scalar extension of concrete tensor support and distance detection

The supported submodule is generated by actual complex supported matrices.
No support or distance law over the extension field is assumed as an axiom.
Relative derivations may differentiate extension-field coefficients while
annihilating the complex matrix generators.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {K : Type*} [Field K] [Algebra ℂ K]

theorem constantMatrix_zero {ι κ : Type*} :
    (0 : Matrix ι κ ℂ).map (algebraMap ℂ K) = 0 := by
  ext i j
  exact map_zero (algebraMap ℂ K)

theorem constantMatrix_one {ι : Type*} [DecidableEq ι] :
    (1 : Matrix ι ι ℂ).map (algebraMap ℂ K) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, h]

theorem constantMatrix_add {ι κ : Type*} (A B : Matrix ι κ ℂ) :
    (A + B).map (algebraMap ℂ K) =
      A.map (algebraMap ℂ K) + B.map (algebraMap ℂ K) := by
  ext i j
  exact map_add (algebraMap ℂ K) (A i j) (B i j)

theorem constantMatrix_mul {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) :
    (A * B).map (algebraMap ℂ K) =
      A.map (algebraMap ℂ K) * B.map (algebraMap ℂ K) := by
  ext i j
  change algebraMap ℂ K (∑ k, A i k * B k j) =
    ∑ k, algebraMap ℂ K (A i k) * algebraMap ℂ K (B k j)
  simp only [map_sum, map_mul]

theorem constantMatrix_kronecker {ι κ μ ν : Type*}
    (A : Matrix ι κ ℂ) (B : Matrix μ ν ℂ) :
    (A ⊗ₖ B).map (algebraMap ℂ K) =
      A.map (algebraMap ℂ K) ⊗ₖ B.map (algebraMap ℂ K) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact map_mul (algebraMap ℂ K) (A i j) (B a b)

/-- Entrywise extension of scalar constants, as an actual matrix ring map. -/
def constantMatrixHom (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →+* Matrix ι ι K where
  toFun := fun A => A.map (algebraMap ℂ K)
  map_one' := constantMatrix_one
  map_mul' := constantMatrix_mul
  map_zero' := constantMatrix_zero
  map_add' := constantMatrix_add

@[simp] theorem constantMatrixHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    constantMatrixHom (K := K) ι A = A.map (algebraMap ℂ K) := rfl

variable {n : ℕ} {dim : Fin n → ℕ}

/-- The extension-field span of mapped, genuinely tensor-local complex matrices. -/
def supportedSpan (S : Finset (Fin n)) :
    Submodule K (Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K) :=
  Submodule.span K
    ((constantMatrixHom (K := K) (PhysicalBasis n dim)) ''
      {O : Operator (PhysicalBasis n dim) | SupportedOn O S})

theorem constant_mem_supportedSpan {S : Finset (Fin n)}
    {O : Operator (PhysicalBasis n dim)} (hO : SupportedOn O S) :
    O.map (algebraMap ℂ K) ∈ supportedSpan (K := K) S := by
  apply Submodule.subset_span
  exact ⟨O, hO, rfl⟩

theorem supportedSpan_mono {S T : Finset (Fin n)} (hST : S ⊆ T) :
    supportedSpan (K := K) (dim := dim) S ≤ supportedSpan (K := K) T := by
  apply Submodule.span_le.mpr
  rintro _ ⟨O, hO, rfl⟩
  exact constant_mem_supportedSpan (hO.mono hST)

theorem matrixDerivation_smul {ι κ : Type*} (D : Derivation ℂ K K)
    (z : K) (A : Matrix ι κ K) :
    matrixDerivation D (z • A) =
      D z • A + z • matrixDerivation D A := by
  ext i j
  simp [matrixDerivation, Derivation.leibniz, smul_eq_mul, mul_comm, add_comm]

theorem one_mem_supportedSpan (S : Finset (Fin n)) :
    (1 : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K) ∈
      supportedSpan (K := K) S := by
  simpa only [constantMatrix_one] using
    (constant_mem_supportedSpan (K := K) (supportedOn_one (dim := dim) S))

/-- Product support is inherited from the actual complex tensor generators. -/
theorem supportedSpan_mul {S T : Finset (Fin n)}
    {A B : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hA : A ∈ supportedSpan (K := K) S) (hB : B ∈ supportedSpan (K := K) T) :
    A * B ∈ supportedSpan (K := K) (S ∪ T) := by
  induction hA using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨O, hO, rfl⟩ := hX
      induction hB using Submodule.span_induction with
      | mem Y hY =>
          obtain ⟨P, hP, rfl⟩ := hY
          simpa only [constantMatrix_mul, constantMatrixHom_apply] using
            (constant_mem_supportedSpan (K := K) (hO.mul hP))
      | zero => simp
      | add X Y _hX _hY ihX ihY =>
          rw [mul_add]
          exact (supportedSpan (K := K) (S ∪ T)).add_mem ihX ihY
      | smul a X _hX ih =>
          rw [mul_smul_comm]
          exact (supportedSpan (K := K) (S ∪ T)).smul_mem a ih
  | zero => simp
  | add X Y _hX _hY ihX ihY =>
      rw [add_mul]
      exact (supportedSpan (K := K) (S ∪ T)).add_mem ihX ihY
  | smul a X _hX ih =>
      rw [smul_mul_assoc]
      exact (supportedSpan (K := K) (S ∪ T)).smul_mem a ih

/-- Disjoint-support commutation extends bilinearly from concrete complex matrices. -/
theorem supportedSpan_commute {S T : Finset (Fin n)}
    {A B : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hA : A ∈ supportedSpan (K := K) S) (hB : B ∈ supportedSpan (K := K) T)
    (hST : Disjoint S T) : Commute A B := by
  change A * B = B * A
  induction hA using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨O, hO, rfl⟩ := hX
      induction hB using Submodule.span_induction with
      | mem Y hY =>
          obtain ⟨P, hP, rfl⟩ := hY
          have hc : O * P = P * O := hO.commute hP hST
          have hm := congrArg (constantMatrixHom (K := K) (PhysicalBasis n dim)) hc
          simpa only [map_mul] using hm
      | zero => simp
      | add X Y _hX _hY ihX ihY => rw [mul_add, add_mul, ihX, ihY]
      | smul a X _hX ih => rw [mul_smul_comm, smul_mul_assoc, ih]
  | zero => simp
  | add X Y _hX _hY ihX ihY => rw [add_mul, mul_add, ihX, ihY]
  | smul a X _hX ih => rw [smul_mul_assoc, mul_smul_comm, ih]

/-- Relative derivations preserve support because all complex generators are constant. -/
theorem matrixDerivation_mem_supportedSpan (D : Derivation ℂ K K)
    {S : Finset (Fin n)} {A : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hA : A ∈ supportedSpan (K := K) S) :
    matrixDerivation D A ∈ supportedSpan (K := K) S := by
  induction hA using Submodule.span_induction with
  | mem X hX =>
      obtain ⟨O, _hO, rfl⟩ := hX
      change matrixDerivation D (O.map (algebraMap ℂ K)) ∈ supportedSpan (K := K) S
      rw [matrixDerivation_constant]
      exact (supportedSpan (K := K) S).zero_mem
  | zero =>
      rw [matrixDerivation_zero]
      exact (supportedSpan (K := K) S).zero_mem
  | add X Y _hX _hY ihX ihY =>
      rw [matrixDerivation_add]
      exact (supportedSpan (K := K) S).add_mem ihX ihY
  | smul a X hX ih =>
      rw [matrixDerivation_smul]
      exact (supportedSpan (K := K) S).add_mem
        ((supportedSpan (K := K) S).smul_mem (D a) hX)
        ((supportedSpan (K := K) S).smul_mem a ih)

private theorem sandwich_add {ι α : Type*} [Fintype α]
    (E : Matrix ι α K) (V : Matrix α ι K) (A B : Matrix α α K) :
    E * (A + B) * V = E * A * V + E * B * V := by
  simp only [Matrix.mul_add, Matrix.add_mul]

private theorem sandwich_smul {ι α : Type*} [Fintype α]
    (E : Matrix ι α K) (V : Matrix α ι K) (z : K) (A : Matrix α α K) :
    E * (z • A) * V = z • (E * A * V) := by
  ext i j
  simp [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm]

/-- Gauge-only compression is a genuine extension-field linear subspace. -/
def gaugeOnlySubmodule {ℓ g : ℕ} (C : Code n dim ℓ g) :
    Submodule K (Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K) where
  carrier := {O | ∃ M : Matrix (Fin g) (Fin g) K,
    C.encoding.conjTranspose.map (algebraMap ℂ K) * O *
      C.encoding.map (algebraMap ℂ K) = (1 : Matrix (Fin ℓ) (Fin ℓ) K) ⊗ₖ M}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    rintro A B ⟨MA, hA⟩ ⟨MB, hB⟩
    refine ⟨MA + MB, ?_⟩
    rw [sandwich_add, hA, hB, Matrix.kronecker_add]
  smul_mem' := by
    rintro z A ⟨M, hM⟩
    refine ⟨z • M, ?_⟩
    rw [sandwich_smul, hM, Matrix.kronecker_smul]

theorem constant_gaugeOnly {ℓ g : ℕ} (C : Code n dim ℓ g)
    {O : Operator (PhysicalBasis n dim)} (hO : GaugeOnly C O) :
    O.map (algebraMap ℂ K) ∈ gaugeOnlySubmodule (K := K) C := by
  obtain ⟨M, hM⟩ := hO
  refine ⟨M.map (algebraMap ℂ K), ?_⟩
  have hm := congrArg (fun A : Matrix (Fin ℓ × Fin g) (Fin ℓ × Fin g) ℂ =>
    A.map (algebraMap ℂ K)) hM
  rw [constantMatrix_mul, constantMatrix_mul, constantMatrix_kronecker,
    constantMatrix_one] at hm
  exact hm

/-- The original complex distance law implies its scalar extension by linear span. -/
theorem supportedSpan_le_gaugeOnlySubmodule {ℓ g d : ℕ} (C : Code n dim ℓ g)
    (hDetect : DetectsBelow C d) (S : Finset (Fin n)) (hS : S.card < d) :
    supportedSpan (K := K) S ≤ gaugeOnlySubmodule (K := K) C := by
  apply Submodule.span_le.mpr
  rintro _ ⟨O, hO, rfl⟩
  exact constant_gaugeOnly C (hDetect S hS O hO)

theorem detectsBelow_scalarExtension {ℓ g d : ℕ} (C : Code n dim ℓ g)
    (hDetect : DetectsBelow C d) (S : Finset (Fin n)) (hS : S.card < d)
    (O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K)
    (hO : O ∈ supportedSpan (K := K) S) :
    ∃ M : Matrix (Fin g) (Fin g) K,
      C.encoding.conjTranspose.map (algebraMap ℂ K) * O *
        C.encoding.map (algebraMap ℂ K) = (1 : Matrix (Fin ℓ) (Fin ℓ) K) ⊗ₖ M := by
  exact supportedSpan_le_gaugeOnlySubmodule C hDetect S hS hO

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_ScalarExtension

/- ===== Source block: CircuitNormalization; SHA-256 c5524e20fd9a162c72fd6b2c5280c1fb3962a0eb984628e0e6ae1dbc173d214e ===== -/
section Merged_CircuitNormalization
/-!
# Arbitrary finite gate lists and the bounded slot model

The input layers have arbitrary finite lengths. Empty-support gates are
removed with their unit-modulus scalar recorded. The retained list keeps its
order and is padded with identity gates on empty supports. No physical site
or ancillary tensor factor is added, including when the register has no sites.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Classical Kronecker

variable {n q : ℕ} {dim : Fin n → ℕ}

structure ListGate (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  support : Finset (Fin n)
  gate : Operator (PhysicalBasis n dim)
  arity : support.card ≤ q
  locality : SupportedOn gate support
  unitary : IsUnitary gate

structure ArbitraryLayer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  gates : List (ListGate n dim q)
  disjoint : gates.Pairwise (fun G H => Disjoint G.support H.support)

def identityListGate : ListGate n dim q where
  support := ∅
  gate := 1
  arity := by simp
  locality := supportedOn_one ∅
  unitary := isUnitary_one

def listGateEval (gates : List (ListGate n dim q)) : Operator (PhysicalBasis n dim) :=
  (gates.map ListGate.gate).reverse.prod

@[simp] theorem listGateEval_nil : listGateEval ([] : List (ListGate n dim q)) = 1 := by
  simp [listGateEval]

@[simp] theorem listGateEval_cons (G : ListGate n dim q) (gates : List (ListGate n dim q)) :
    listGateEval (G :: gates) = listGateEval gates * G.gate := by
  simp [listGateEval, List.reverse_cons, List.prod_append]

def ArbitraryLayer.eval (L : ArbitraryLayer n dim q) : Operator (PhysicalBasis n dim) :=
  listGateEval L.gates

/-- This recursive filter retains the original gate order. -/
def filterNonemptyGates : List (ListGate n dim q) → List (ListGate n dim q)
  | [] => []
  | G :: gates =>
      if G.support = ∅ then filterNonemptyGates gates
      else G :: filterNonemptyGates gates

theorem mem_filterNonemptyGates (G : ListGate n dim q) (gates : List (ListGate n dim q)) :
    G ∈ filterNonemptyGates gates ↔ G ∈ gates ∧ G.support ≠ ∅ := by
  induction gates with
  | nil => simp [filterNonemptyGates]
  | cons H gates ih =>
      by_cases hH : H.support = ∅
      · simp only [filterNonemptyGates, if_pos hH, ih, List.mem_cons]
        constructor
        · intro h
          exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨h | h, hne⟩
          · subst G
            exact False.elim (hne hH)
          · exact ⟨h, hne⟩
      · simp only [filterNonemptyGates, if_neg hH, List.mem_cons, ih]
        constructor
        · rintro (rfl | h)
          · exact ⟨Or.inl rfl, hH⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨h | h, hne⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, hne⟩

theorem filterNonemptyGates_pairwise (gates : List (ListGate n dim q))
    (h : gates.Pairwise (fun G H => Disjoint G.support H.support)) :
    (filterNonemptyGates gates).Pairwise (fun G H => Disjoint G.support H.support) := by
  revert h
  induction gates with
  | nil =>
      intro h
      simp [filterNonemptyGates]
  | cons G gates ih =>
      intro h
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      by_cases hG : G.support = ∅
      · simpa only [filterNonemptyGates, if_pos hG] using ih htail
      · rw [filterNonemptyGates, if_neg hG, List.pairwise_cons]
        refine ⟨?_, ih htail⟩
        intro H hH
        exact hhead H ((mem_filterNonemptyGates H gates).mp hH).1

def listGateSupportUnion : List (ListGate n dim q) → Finset (Fin n)
  | [] => ∅
  | G :: gates => G.support ∪ listGateSupportUnion gates

theorem mem_listGateSupportUnion (x : Fin n) (gates : List (ListGate n dim q)) :
    x ∈ listGateSupportUnion gates ↔ ∃ G ∈ gates, x ∈ G.support := by
  induction gates with
  | nil => simp [listGateSupportUnion]
  | cons G gates ih =>
      simp only [listGateSupportUnion, Finset.mem_union, ih, List.mem_cons]
      aesop

theorem nonemptyGateList_length_le_union_card (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support))
    (hne : ∀ G ∈ gates, G.support ≠ ∅) :
    gates.length ≤ (listGateSupportUnion gates).card := by
  revert hpair hne
  induction gates with
  | nil =>
      intro hpair hne
      simp [listGateSupportUnion]
  | cons G gates ih =>
      intro hpair hne
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      have hG : G.support ≠ ∅ := hne G (by simp)
      have htailne : ∀ H ∈ gates, H.support ≠ ∅ := by
        intro H hH
        exact hne H (by simp [hH])
      have hbound := ih htail htailne
      have hdis : Disjoint G.support (listGateSupportUnion gates) := by
        apply Finset.disjoint_left.mpr
        intro x hx hxu
        obtain ⟨H, hH, hxH⟩ := (mem_listGateSupportUnion x gates).mp hxu
        exact Finset.disjoint_left.mp (hhead H hH) hx hxH
      have hpos : 0 < G.support.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hG)
      simp only [List.length_cons, listGateSupportUnion, Finset.card_union_of_disjoint hdis]
      omega

theorem filterNonemptyGates_length_le (L : ArbitraryLayer n dim q) :
    (filterNonemptyGates L.gates).length ≤ n := by
  calc
    (filterNonemptyGates L.gates).length ≤
        (listGateSupportUnion (filterNonemptyGates L.gates)).card :=
      nonemptyGateList_length_le_union_card _ (filterNonemptyGates_pairwise _ L.disjoint)
        (fun G hG => ((mem_filterNonemptyGates G L.gates).mp hG).2)
    _ ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp

private theorem pairwise_append_identityGates (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) (k : ℕ) :
    (gates ++ List.replicate k (identityListGate : ListGate n dim q)).Pairwise
      (fun (G H : ListGate n dim q) => Disjoint G.support H.support) := by
  revert hpair
  induction gates with
  | nil =>
      intro hpair
      induction k with
      | zero => simp
      | succ k ih =>
          simp only [List.nil_append, List.replicate_succ, List.pairwise_cons] at *
          exact ⟨fun H _ => by simp [identityListGate], ih⟩
  | cons G gates ih =>
      intro hpair
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpair
      rw [List.cons_append, List.pairwise_cons]
      refine ⟨?_, ih htail⟩
      intro H hH
      rcases List.mem_append.mp hH with hH | hH
      · exact hhead H hH
      · have heq : H = (identityListGate : ListGate n dim q) := by
          simp only [List.mem_replicate] at hH
          aesop
        subst H
        simp [identityListGate]

private theorem gateList_get_disjoint (gates : List (ListGate n dim q))
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support))
    (i j : ℕ) (hi : i < gates.length) (hj : j < gates.length) (hij : i ≠ j) :
    Disjoint (gates[i]'hi).support (gates[j]'hj).support := by
  have hget := List.pairwise_iff_getElem.mp hpair
  by_cases hlt : i < j
  · exact hget i j hi hj hlt
  · have hgt : j < i := by omega
    exact (hget j i hj hi hgt).symm

def layerOfGateList (gates : List (ListGate n dim q)) (hlen : gates.length = n)
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) : Layer n dim q where
  support i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).support
  gate i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).gate
  disjoint := by
    intro i j hij
    apply gateList_get_disjoint gates hpair i.val j.val
      (by simpa only [hlen] using i.isLt) (by simpa only [hlen] using j.isLt)
    intro heq
    apply hij
    exact Fin.ext heq
  arity i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).arity
  locality i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).locality
  unitary i := (gates[i.val]'(by simpa only [hlen] using i.isLt)).unitary

theorem layerOfGateList_eval (gates : List (ListGate n dim q)) (hlen : gates.length = n)
    (hpair : gates.Pairwise (fun G H => Disjoint G.support H.support)) :
    (layerOfGateList gates hlen hpair).eval = listGateEval gates := by
  have hlist : List.ofFn (layerOfGateList gates hlen hpair).gate = gates.map ListGate.gate := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, layerOfGateList]
  unfold Layer.eval listGateEval
  rw [hlist]

def ArbitraryLayer.normalized (L : ArbitraryLayer n dim q) : Layer n dim q :=
  layerOfGateList
    (filterNonemptyGates L.gates ++
      List.replicate (n - (filterNonemptyGates L.gates).length) identityListGate)
    (by
      simp only [List.length_append, List.length_replicate]
      have h := filterNonemptyGates_length_le L
      omega)
    (pairwise_append_identityGates _ (filterNonemptyGates_pairwise _ L.disjoint) _)

theorem ArbitraryLayer.normalized_eval (L : ArbitraryLayer n dim q) :
    L.normalized.eval = listGateEval (filterNonemptyGates L.gates) := by
  rw [ArbitraryLayer.normalized, layerOfGateList_eval]
  simp [listGateEval, List.map_append, List.reverse_append, List.prod_append, identityListGate]

theorem scalar_of_supportedOn_empty {U : Operator (PhysicalBasis n dim)}
    (hsupported : SupportedOn U ∅) : IsScalar U := by
  obtain ⟨A, rfl⟩ := hsupported
  have no_mem (j : Fin n) : j ∉ (∅ : Finset (Fin n)) := by simp
  let e : LocalBasis dim (∅ : Finset (Fin n)) :=
    fun i => False.elim (no_mem i.1 i.2)
  have hA : A = A e e • (1 : Operator (LocalBasis dim (∅ : Finset (Fin n)))) := by
    ext x y
    have hx : x = e := by
      funext i
      exact False.elim (no_mem i.1 i.2)
    have hy : y = e := by
      funext i
      exact False.elim (no_mem i.1 i.2)
    subst x
    subst y
    simp
  refine ⟨A e e, ?_⟩
  calc
    localEmbed ∅ A = localEmbed ∅ (A e e • (1 : Operator (LocalBasis dim ∅))) :=
      congrArg (localEmbed ∅) hA
    _ = A e e • (1 : Operator (PhysicalBasis n dim)) := by
      rw [localEmbed_smul, localEmbed_one]

private theorem normalization_phase_mul {a b : ℂ}
    (ha : star a * a = 1) (hb : star b * b = 1) : star (a * b) * (a * b) = 1 := by
  calc
    star (a * b) * (a * b) = (star a * a) * (star b * b) := by rw [star_mul]; ring
    _ = 1 := by rw [ha, hb, mul_one]

theorem listGateEval_filter_phase [Nonempty (PhysicalBasis n dim)]
    (gates : List (ListGate n dim q)) :
    ProjectivelyEquivalent (listGateEval gates) (listGateEval (filterNonemptyGates gates)) := by
  induction gates with
  | nil => exact projectivelyEquivalent_refl 1
  | cons G gates ih =>
      obtain ⟨z, hz, heval⟩ := ih
      by_cases hG : G.support = ∅
      · have hscalar : IsScalar G.gate := scalar_of_supportedOn_empty (by simpa [hG] using G.locality)
        obtain ⟨c, hc, hgate⟩ := projectivelyEquivalent_one_of_unitary_scalar G.unitary hscalar
        refine ⟨c * z, normalization_phase_mul hc hz, ?_⟩
        simp only [listGateEval_cons, filterNonemptyGates, if_pos hG, heval, hgate,
          smul_mul_assoc, mul_smul_comm, smul_smul, mul_one]
      · refine ⟨z, hz, ?_⟩
        simp only [listGateEval_cons, filterNonemptyGates, if_neg hG, heval, smul_mul_assoc]

theorem ArbitraryLayer.normalization_phase [Nonempty (PhysicalBasis n dim)]
    (L : ArbitraryLayer n dim q) : ProjectivelyEquivalent L.eval L.normalized.eval := by
  rw [L.normalized_eval]
  exact listGateEval_filter_phase L.gates

theorem code_physicalBasis_nonempty {K g : ℕ} (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) : Nonempty (PhysicalBasis n dim) := by
  by_contra h
  letI : IsEmpty (PhysicalBasis n dim) := ⟨fun x => h ⟨x⟩⟩
  let j : Fin K × Fin g := (⟨0, by omega⟩, ⟨0, by omega⟩)
  have hdiag := congrArg (fun A : Operator (Fin K × Fin g) => A j j) C.isometry
  simp [Matrix.mul_apply] at hdiag

abbrev ArbitraryCircuit (n : ℕ) (dim : Fin n → ℕ) (q h : ℕ) :=
  Fin h → ArbitraryLayer n dim q

def arbitraryCircuitEval {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    Operator (PhysicalBasis n dim) := (List.ofFn fun i => (c i).eval).reverse.prod

def ArbitraryCircuit.normalized {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    Circuit n dim q h := fun i => (c i).normalized

private theorem normalization_projective_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A A' B B' : Operator ι}
    (hA : ProjectivelyEquivalent A A') (hB : ProjectivelyEquivalent B B') :
    ProjectivelyEquivalent (A * B) (A' * B') := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  refine ⟨b * a, normalization_phase_mul hb ha, ?_⟩
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]

private theorem normalization_projective_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι] (pairs : List (Operator ι × Operator ι))
    (h : ∀ p ∈ pairs, ProjectivelyEquivalent p.1 p.2) :
    ProjectivelyEquivalent (pairs.map Prod.fst).prod (pairs.map Prod.snd).prod := by
  revert h
  induction pairs with
  | nil =>
      intro h
      exact projectivelyEquivalent_refl 1
  | cons p pairs ih =>
      intro h
      have hp := h p (by simp)
      have htail : ∀ r ∈ pairs, ProjectivelyEquivalent r.1 r.2 := by
        intro r hr
        exact h r (by simp [hr])
      simpa only [List.map_cons, List.prod_cons] using normalization_projective_mul hp (ih htail)

theorem arbitraryCircuit_normalization_phase [Nonempty (PhysicalBasis n dim)]
    {h : ℕ} (c : ArbitraryCircuit n dim q h) :
    ProjectivelyEquivalent (arbitraryCircuitEval c) (circuitEval c.normalized) := by
  let pairs := (List.ofFn fun i => ((c i).eval, (c i).normalized.eval)).reverse
  have hp : ∀ p ∈ pairs, ProjectivelyEquivalent p.1 p.2 := by
    intro p hp
    have hp' : ∃ i, ((c i).eval, (c i).normalized.eval) = p := by
      simpa only [pairs, List.mem_reverse, List.mem_ofFn] using hp
    obtain ⟨i, rfl⟩ := hp'
    exact (c i).normalization_phase
  have hh := normalization_projective_prod pairs hp
  simpa [pairs, arbitraryCircuitEval, circuitEval, ArbitraryCircuit.normalized,
    List.map_reverse, List.map_ofFn, Function.comp_def] using hh

private theorem normalization_rect_smul_mul {α β γ : Type*} [Fintype β]
    (a : ℂ) (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    (a • A) * B = a • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

private theorem normalization_rect_mul_smul {α β γ : Type*} [Fintype β]
    (a : ℂ) (A : Matrix α β ℂ) (B : Matrix β γ ℂ) :
    A * (a • B) = a • (A * B) := by
  ext i j
  simp [Matrix.mul_apply, Finset.mul_sum, mul_left_comm, mul_assoc]

private theorem normalization_unitary_smul
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℂ) {U : Operator ι}
    (ha : star a * a = 1) (hU : IsUnitary U) : IsUnitary (a • U) := by
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  constructor
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.1]
    change (a * star a) • (1 : Operator ι) = 1
    rw [ha', one_smul]
  · simp only [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul, hU.2]
    change (star a * a) • (1 : Operator ι) = 1
    rw [ha, one_smul]

theorem implements_of_projectivelyEquivalent_physical {K g : ℕ}
    (C : Code n dim K g) {U V : Operator (PhysicalBasis n dim)} {W : Operator (Fin K)}
    (hphase : ProjectivelyEquivalent U V) (himpl : Implements C U W) : Implements C V W := by
  obtain ⟨a, ha, hUV⟩ := hphase
  obtain ⟨hW, Z, hZ, hencoded⟩ := himpl
  have ha' : a * star a = 1 := by simpa only [mul_comm] using ha
  have hstar : star (star a) * star a = 1 := by simpa only [star_star] using ha'
  refine ⟨hW, star a • Z, normalization_unitary_smul _ hstar hZ, ?_⟩
  have hk : W ⊗ₖ (star a • Z) = star a • (W ⊗ₖ Z) := by
    ext ⟨i, s⟩ ⟨j, t⟩
    simp [Matrix.kronecker_apply, smul_eq_mul, mul_left_comm]
  calc
    V * C.encoding = (star a * a) • (V * C.encoding) := by rw [ha, one_smul]
    _ = star a • (U * C.encoding) := by
      rw [hUV, normalization_rect_smul_mul, smul_smul]
    _ = star a • (C.encoding * (W ⊗ₖ Z)) := by rw [hencoded]
    _ = C.encoding * (W ⊗ₖ (star a • Z)) := by
      rw [hk, normalization_rect_mul_smul]

def arbitraryLogicalImage {K g : ℕ} (C : Code n dim K g) (q h : ℕ) :
    Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ c : ArbitraryCircuit n dim q h, ∃ W : Operator (Fin K),
    Implements C (arbitraryCircuitEval c) W ∧ projectiveClass W = a}

theorem arbitraryLogicalImage_subset_logicalImage {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) :
    arbitraryLogicalImage C q h ⊆ logicalImage C q h := by
  letI : Nonempty (PhysicalBasis n dim) := code_physicalBasis_nonempty C hK hg
  rintro a ⟨c, W, himpl, hclass⟩
  exact ⟨c.normalized, W,
    implements_of_projectivelyEquivalent_physical C (arbitraryCircuit_normalization_phase c) himpl,
    hclass⟩

def Layer.toArbitrary (L : Layer n dim q) : ArbitraryLayer n dim q where
  gates := List.ofFn fun i =>
    { support := L.support i, gate := L.gate i, arity := L.arity i,
      locality := L.locality i, unitary := L.unitary i }
  disjoint := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    simp only [List.length_ofFn] at hi hj
    simp only [List.getElem_ofFn]
    apply L.disjoint ⟨i, hi⟩ ⟨j, hj⟩
    intro heq
    have hv : i = j := congrArg Fin.val heq
    omega

@[simp] theorem Layer.toArbitrary_eval (L : Layer n dim q) : L.toArbitrary.eval = L.eval := by
  simp [ArbitraryLayer.eval, Layer.toArbitrary, listGateEval, Layer.eval, List.map_ofFn,
    Function.comp_def]

theorem logicalImage_subset_arbitraryLogicalImage {K g h : ℕ} (C : Code n dim K g) :
    logicalImage C q h ⊆ arbitraryLogicalImage C q h := by
  rintro a ⟨c, W, himpl, hclass⟩
  refine ⟨fun i => (c i).toArbitrary, W, ?_, hclass⟩
  simpa only [arbitraryCircuitEval, circuitEval, Layer.toArbitrary_eval] using himpl

/-- The finite-list and bounded-slot models have exactly the same logical image. -/
theorem arbitraryLogicalImage_eq_logicalImage {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g) :
    arbitraryLogicalImage C q h = logicalImage C q h := by
  exact Set.Subset.antisymm (arbitraryLogicalImage_subset_logicalImage C hK hg)
    (logicalImage_subset_arbitraryLogicalImage C)

theorem arbitraryLogicalImage_finite_of_logicalImage_finite {K g h : ℕ}
    (C : Code n dim K g) (hK : 2 ≤ K) (hg : 1 ≤ g)
    (hfinite : (logicalImage C q h).Finite) : (arbitraryLogicalImage C q h).Finite := by
  rw [arbitraryLogicalImage_eq_logicalImage C hK hg]
  exact hfinite

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_CircuitNormalization

/- ===== Source block: FieldLightCone; SHA-256 b58fa61f017768c4216d5a59399d571635461da9cfc63d933f6f044c2a4976ff ===== -/
section Merged_FieldLightCone
/-!
# Actual inverse-pair light cones over extension fields

The complex layer supplies only the finite site layout, disjointness, and arity.
The field-valued gates and inverse gates have concrete supported-span proofs.
There is no conjugation or Hermitian operation on the extension field.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {K : Type*} [Field K] [Algebra ℂ K]
variable {n q : ℕ} {dim : Fin n → ℕ}

theorem supportedSpan_mul_same {S : Finset (Fin n)}
    {A B : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hA : A ∈ supportedSpan (K := K) S) (hB : B ∈ supportedSpan (K := K) S) :
    A * B ∈ supportedSpan (K := K) S := by
  simpa only [Finset.union_self] using supportedSpan_mul hA hB

theorem supportedSpan_pair_conjugate_disjoint {S T : Finset (Fin n)}
    {O U Ui : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) (hU : U ∈ supportedSpan (K := K) T)
    (hST : Disjoint S T) (hUUi : U * Ui = 1) : U * O * Ui = O := by
  have hc : O * U = U * O := supportedSpan_commute hO hU hST
  rw [← hc, mul_assoc, hUUi, mul_one]

/-- Field-valued gates on a genuine disjoint complex support layout. -/
structure FieldLayer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) where
  layout : Layer n dim q
  gate : Fin n → GateWithInverse (PhysicalBasis n dim) K
  gate_locality : ∀ i, (gate i).1 ∈ supportedSpan (K := K) (layout.support i)
  inverse_locality : ∀ i, (gate i).2 ∈ supportedSpan (K := K) (layout.support i)
  inverse_identities : ∀ i, (gate i).1 * (gate i).2 = 1 ∧
    (gate i).2 * (gate i).1 = 1

def FieldLayer.eval (L : FieldLayer (K := K) n dim q) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K :=
  gatePairProduct (List.ofFn L.gate).reverse

def FieldLayer.evalInv (L : FieldLayer (K := K) n dim q) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K :=
  gatePairInverseProduct (List.ofFn L.gate).reverse

def FieldLayer.lightCone (L : FieldLayer (K := K) n dim q) (S : Finset (Fin n)) :
    Finset (Fin n) := L.layout.lightCone S

theorem FieldLayer.mutual_inverse (L : FieldLayer (K := K) n dim q) :
    L.eval * L.evalInv = 1 ∧ L.evalInv * L.eval = 1 := by
  apply gatePairProduct_mutual_inverse
  intro p hp
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  exact L.inverse_identities i

theorem FieldLayer.logarithmic_gate_mem (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) (i : Fin n) :
    matrixDerivation D (L.gate i).1 * (L.gate i).2 ∈
      supportedSpan (K := K) (L.layout.support i) := by
  exact supportedSpan_mul_same
    (matrixDerivation_mem_supportedSpan D (L.gate_locality i)) (L.inverse_locality i)

theorem FieldLayer.backward_logarithmic_gate_mem (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) (i : Fin n) :
    (L.gate i).2 * matrixDerivation D (L.gate i).1 ∈
      supportedSpan (K := K) (L.layout.support i) := by
  exact supportedSpan_mul_same (L.inverse_locality i)
    (matrixDerivation_mem_supportedSpan D (L.gate_locality i))

private theorem supportedSpan_conjugate_pairProduct
    (gates : List (GateWithInverse (PhysicalBasis n dim) K)) (S : Finset (Fin n))
    (hstep : ∀ p ∈ gates, ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S → p.1 * O * p.2 ∈ supportedSpan (K := K) S) :
    ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S →
      gatePairProduct gates * O * gatePairInverseProduct gates ∈
        supportedSpan (K := K) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep O hO
      simpa using hO
  | cons p gates ih =>
      intro hstep O hO
      have hg : ∀ r ∈ gates,
          ∀ P : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
          P ∈ supportedSpan (K := K) S →
          r.1 * P * r.2 ∈ supportedSpan (K := K) S := by
        intro r hr P hP
        exact hstep r (by simp [hr]) P hP
      have hinner := ih hg O hO
      have houter := hstep p (by simp) _ hinner
      simpa only [gatePairProduct_cons, gatePairInverseProduct_cons, mul_assoc]
        using houter

private theorem supportedSpan_inverse_conjugate_pairProduct
    (gates : List (GateWithInverse (PhysicalBasis n dim) K)) (S : Finset (Fin n))
    (hstep : ∀ p ∈ gates, ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S → p.2 * O * p.1 ∈ supportedSpan (K := K) S) :
    ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
      O ∈ supportedSpan (K := K) S →
      gatePairInverseProduct gates * O * gatePairProduct gates ∈
        supportedSpan (K := K) S := by
  revert hstep
  induction gates with
  | nil =>
      intro hstep O hO
      simpa using hO
  | cons p gates ih =>
      intro hstep O hO
      have hg : ∀ r ∈ gates,
          ∀ P : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K,
          P ∈ supportedSpan (K := K) S →
          r.2 * P * r.1 ∈ supportedSpan (K := K) S := by
        intro r hr P hP
        exact hstep r (by simp [hr]) P hP
      have hinner := hstep p (by simp) O hO
      have houter := ih hg _ hinner
      simpa only [gatePairProduct_cons, gatePairInverseProduct_cons, mul_assoc]
        using houter

/-- Forward conjugation has the same selective cone as the actual physical layout. -/
theorem FieldLayer.conjugate_mem_supportedSpan (L : FieldLayer (K := K) n dim q)
    (S : Finset (Fin n)) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    L.eval * O * L.evalInv ∈ supportedSpan (K := K) (L.lightCone S) := by
  classical
  apply supportedSpan_conjugate_pairProduct (List.ofFn L.gate).reverse (L.lightCone S)
    ?_ O (supportedSpan_mono Finset.subset_union_left hO)
  intro p hp P hP
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  rcases L.layout.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hu := supportedSpan_mono hsub (L.gate_locality i)
    have hui := supportedSpan_mono hsub (L.inverse_locality i)
    exact supportedSpan_mul_same (supportedSpan_mul_same hu hP) hui
  · rw [supportedSpan_pair_conjugate_disjoint hP (L.gate_locality i)
      hdis.symm (L.inverse_identities i).1]
    exact hP

/-- Backward conjugation uses the actual inverse product, with no reordered premise. -/
theorem FieldLayer.inverse_conjugate_mem_supportedSpan
    (L : FieldLayer (K := K) n dim q) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    L.evalInv * O * L.eval ∈ supportedSpan (K := K) (L.lightCone S) := by
  classical
  apply supportedSpan_inverse_conjugate_pairProduct (List.ofFn L.gate).reverse
    (L.lightCone S) ?_ O (supportedSpan_mono Finset.subset_union_left hO)
  intro p hp P hP
  have hp' : ∃ i, L.gate i = p := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hp
  obtain ⟨i, rfl⟩ := hp'
  rcases L.layout.support_subset_lightCone_or_disjoint S i with hsub | hdis
  · have hu := supportedSpan_mono hsub (L.gate_locality i)
    have hui := supportedSpan_mono hsub (L.inverse_locality i)
    exact supportedSpan_mul_same (supportedSpan_mul_same hui hP) hu
  · rw [supportedSpan_pair_conjugate_disjoint hP (L.inverse_locality i)
      hdis.symm (L.inverse_identities i).2]
    exact hP

theorem FieldLayer.lightCone_card_le (L : FieldLayer (K := K) n dim q)
    (S : Finset (Fin n)) (hq : 1 ≤ q) : (L.lightCone S).card ≤ q * S.card :=
  L.layout.lightCone_card_le S hq

def fieldLayerSequenceEval : List (FieldLayer (K := K) n dim q) →
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [] => 1
  | L :: layers => fieldLayerSequenceEval layers * L.eval

def fieldLayerSequenceInv : List (FieldLayer (K := K) n dim q) →
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [] => 1
  | L :: layers => L.evalInv * fieldLayerSequenceInv layers

def fieldLayerSequenceCone : List (FieldLayer (K := K) n dim q) →
    Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => fieldLayerSequenceCone layers (L.lightCone S)

def fieldLayerSequenceBackwardCone : List (FieldLayer (K := K) n dim q) →
    Finset (Fin n) → Finset (Fin n)
  | [], S => S
  | L :: layers, S => L.lightCone (fieldLayerSequenceBackwardCone layers S)

theorem fieldLayerSequence_mutual_inverse (layers : List (FieldLayer (K := K) n dim q)) :
    fieldLayerSequenceEval layers * fieldLayerSequenceInv layers = 1 ∧
      fieldLayerSequenceInv layers * fieldLayerSequenceEval layers = 1 := by
  induction layers with
  | nil => simp [fieldLayerSequenceEval, fieldLayerSequenceInv]
  | cons L layers ih =>
      obtain ⟨hL, hLi⟩ := L.mutual_inverse
      obtain ⟨hR, hRi⟩ := ih
      constructor
      · calc
          fieldLayerSequenceEval (L :: layers) * fieldLayerSequenceInv (L :: layers) =
              fieldLayerSequenceEval layers * (L.eval * L.evalInv) *
                fieldLayerSequenceInv layers := by
            simp only [fieldLayerSequenceEval, fieldLayerSequenceInv, mul_assoc]
          _ = 1 := by rw [hL, mul_one, hR]
      · calc
          fieldLayerSequenceInv (L :: layers) * fieldLayerSequenceEval (L :: layers) =
              L.evalInv * (fieldLayerSequenceInv layers * fieldLayerSequenceEval layers) *
                L.eval := by
            simp only [fieldLayerSequenceEval, fieldLayerSequenceInv, mul_assoc]
          _ = 1 := by rw [hRi, mul_one, hLi]

theorem fieldLayerSequence_conjugate_mem
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    fieldLayerSequenceEval layers * O * fieldLayerSequenceInv layers ∈
      supportedSpan (K := K) (fieldLayerSequenceCone layers S) := by
  induction layers generalizing S O with
  | nil => simpa [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceCone] using hO
  | cons L layers ih =>
      have hinner := L.conjugate_mem_supportedSpan S hO
      have houter := ih (L.lightCone S) hinner
      simpa only [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceCone,
        mul_assoc] using houter

theorem fieldLayerSequence_inverse_conjugate_mem
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n))
    {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) S) :
    fieldLayerSequenceInv layers * O * fieldLayerSequenceEval layers ∈
      supportedSpan (K := K) (fieldLayerSequenceBackwardCone layers S) := by
  induction layers generalizing S O with
  | nil =>
      simpa [fieldLayerSequenceEval, fieldLayerSequenceInv, fieldLayerSequenceBackwardCone] using hO
  | cons L layers ih =>
      have hinner := ih S hO
      have houter := L.inverse_conjugate_mem_supportedSpan
        (fieldLayerSequenceBackwardCone layers S) hinner
      simpa only [fieldLayerSequenceEval, fieldLayerSequenceInv,
        fieldLayerSequenceBackwardCone, mul_assoc] using houter

theorem fieldLayerSequenceCone_card_le (layers : List (FieldLayer (K := K) n dim q))
    (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (fieldLayerSequenceCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [fieldLayerSequenceCone]
  | cons L layers ih =>
      calc
        (fieldLayerSequenceCone (L :: layers) S).card =
            (fieldLayerSequenceCone layers (L.lightCone S)).card := rfl
        _ ≤ q ^ layers.length * (L.lightCone S).card := ih (L.lightCone S)
        _ ≤ q ^ layers.length * (q * S.card) :=
          Nat.mul_le_mul_left _ (L.lightCone_card_le S hq)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

theorem fieldLayerSequenceBackwardCone_card_le
    (layers : List (FieldLayer (K := K) n dim q)) (S : Finset (Fin n)) (hq : 1 ≤ q) :
    (fieldLayerSequenceBackwardCone layers S).card ≤ q ^ layers.length * S.card := by
  induction layers generalizing S with
  | nil => simp [fieldLayerSequenceBackwardCone]
  | cons L layers ih =>
      calc
        (fieldLayerSequenceBackwardCone (L :: layers) S).card =
            (L.lightCone (fieldLayerSequenceBackwardCone layers S)).card := rfl
        _ ≤ q * (fieldLayerSequenceBackwardCone layers S).card :=
          L.lightCone_card_le _ hq
        _ ≤ q * (q ^ layers.length * S.card) := Nat.mul_le_mul_left q (ih S)
        _ = q ^ (L :: layers).length * S.card := by
          simp only [List.length_cons, pow_succ]
          ring

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_FieldLightCone

/- ===== Source block: LocalScalarCoordinates; SHA-256 4607791218fe73b6bf7267c394c591645ef346a914936f2da7b3baa2b1b5d43c ===== -/
section Merged_LocalScalarCoordinates
/-!
# Actual local matrix coordinates and scalar-extension support

The polynomial presentation uses coefficients of the standard local matrix
basis. This module binds that formula to the original complex tensor embedding
and to the supported span after any algebraic evaluation into an extension field.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {n : ℕ} {dim : Fin n → ℕ}

theorem matrix_map_self {ι κ : Type*} (A : Matrix ι κ ℂ) :
    A.map (algebraMap ℂ ℂ) = A := by
  ext i j
  simp

theorem matrix_eq_sum_smul_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) :
    A = ∑ a, ∑ b, A a b • Matrix.single a b (1 : ℂ) := by
  classical
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (Matrix.matrix_eq_sum_single A)

private theorem localEmbedLinearMap_apply (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) :
    (localEmbedLinearMap S) A = localEmbed S A := rfl

/-- At complex points the coefficient formula is precisely the original embedding. -/
theorem coefficientEmbed_complex (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) : coefficientEmbed S A = localEmbed S A := by
  classical
  have hmap := congrArg (localEmbedLinearMap (dim := dim) S)
    (matrix_eq_sum_smul_single A)
  have hmap' : localEmbed S A =
      ∑ a, ∑ b, A a b • localEmbed S (Matrix.single a b (1 : ℂ)) := by
    simpa only [map_sum, map_smul, localEmbedLinearMap_apply] using hmap
  calc
    coefficientEmbed S A =
        ∑ a, ∑ b, A a b • localEmbed S (Matrix.single a b (1 : ℂ)) := by
      simp only [coefficientEmbed, matrix_map_self]
    _ = localEmbed S A := hmap'.symm

theorem coefficientEmbed_naturality {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (S : Finset (Fin n))
    (M : Matrix (LocalBasis dim S) (LocalBasis dim S) A) (φ : A →ₐ[ℂ] B) :
    (coefficientEmbed S M).map φ = coefficientEmbed S (M.map φ) := by
  classical
  ext x y
  simp only [coefficientEmbed, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, φ.commutes]

variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]

/-- Every arbitrary local extension-field matrix has genuine supported-span membership. -/
theorem coefficientEmbed_mem_supportedSpan (S : Finset (Fin n))
    (A : Matrix (LocalBasis dim S) (LocalBasis dim S) 𝕂) :
    coefficientEmbed S A ∈ supportedSpan (K := 𝕂) S := by
  classical
  unfold coefficientEmbed
  apply (supportedSpan (K := 𝕂) S).sum_mem
  intro a _ha
  apply (supportedSpan (K := 𝕂) S).sum_mem
  intro b _hb
  apply (supportedSpan (K := 𝕂) S).smul_mem
  exact constant_mem_supportedSpan (K := 𝕂) ⟨Matrix.single a b (1 : ℂ), rfl⟩

/-- Polynomial gate evaluation lands in the concrete supported span at every field point. -/
theorem physicalGatePolynomial_map_mem_supportedSpan {ℓ g h : ℕ}
    (support : GateIndex n h → Finset (Fin n)) (p : GateIndex n h) (inverse : Bool)
    (φ : CircuitPolynomial (K := ℓ) (g := g) (dim := dim) support →ₐ[ℂ] 𝕂) :
    (physicalGatePolynomial (K := ℓ) (g := g) (dim := dim) support p inverse).map φ ∈
      supportedSpan (K := 𝕂) (support p) := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality]
  exact coefficientEmbed_mem_supportedSpan _ _

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_LocalScalarCoordinates

/- ===== Source block: PauliConjugation; SHA-256 e34ff5da491aec96c9feb8c19cdc8f80e9ecc5493590bfb1a29dc734401415b0 ===== -/
section Merged_PauliConjugation
/-!
# A concrete one-block Pauli compression gate

A normalized sum of anticommuting Hermitian involutions conjugates one into
the other. Applying this once, or twice inside the same local matrix, gives a
single allowed gate on any nonempty Pauli block. No qubit or auxiliary register
is removed, and no internal factor is counted as an additional circuit layer.
-/

noncomputable section

namespace CriticalDepth

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def involutionBisector (P Q : Operator ι) : Operator ι :=
  rationalScale 1 • (P + Q)

theorem involutionBisector_selfAdjoint {P Q : Operator ι}
    (hP : star P = P) (hQ : star Q = Q) :
    star (involutionBisector P Q) = involutionBisector P Q := by
  simp [involutionBisector, star_smul, hP, hQ, star_rationalScale]

theorem involutionBisector_sq {P Q : Operator ι}
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    involutionBisector P Q * involutionBisector P Q = 1 := by
  have ha : (rationalScale 1 * rationalScale 1) * (2 : ℂ) = 1 := by
    have h := rationalScale_sq_mul 1
    norm_num [pow_two] at h
    exact h
  have hsum : (P + Q) * (P + Q) = (2 : ℂ) • (1 : Operator ι) := by
    calc
      (P + Q) * (P + Q) = P * P + (P * Q + Q * P) + Q * Q := by noncomm_ring
      _ = 1 + 0 + 1 := by rw [hP, hQ, hanti, neg_add_cancel]
      _ = (2 : ℂ) • (1 : Operator ι) := by simp [two_smul]
  calc
    involutionBisector P Q * involutionBisector P Q =
        (rationalScale 1 * rationalScale 1) • ((P + Q) * (P + Q)) := by
      simp only [involutionBisector, smul_mul_assoc, mul_smul_comm, smul_smul]
    _ = (rationalScale 1 * rationalScale 1) • ((2 : ℂ) • (1 : Operator ι)) := by rw [hsum]
    _ = 1 := by rw [smul_smul, ha, one_smul]

theorem involutionBisector_isUnitary {P Q : Operator ι}
    (hPself : star P = P) (hQself : star Q = Q)
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    IsUnitary (involutionBisector P Q) := by
  constructor
  · rw [involutionBisector_selfAdjoint hPself hQself,
      involutionBisector_sq hP hQ hanti]
  · rw [involutionBisector_selfAdjoint hPself hQself,
      involutionBisector_sq hP hQ hanti]

theorem involutionBisector_conjugates {P Q : Operator ι}
    (hP : P * P = 1) (hQ : Q * Q = 1) (hanti : P * Q = -(Q * P)) :
    involutionBisector P Q * P * involutionBisector P Q = Q := by
  have hraw : (P + Q) * P = Q * (P + Q) := by
    rw [add_mul, mul_add, hP, hQ]
    exact add_comm _ _
  have hinter : involutionBisector P Q * P = Q * involutionBisector P Q := by
    dsimp [involutionBisector]
    rw [smul_mul_assoc, mul_smul_comm, hraw]
  calc
    involutionBisector P Q * P * involutionBisector P Q =
        Q * (involutionBisector P Q * involutionBisector P Q) := by
      rw [hinter, mul_assoc]
    _ = Q := by rw [involutionBisector_sq hP hQ hanti, mul_one]

theorem unitary_mul {U V : Operator ι} (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (U * V) := by
  constructor
  · rw [star_mul]
    calc
      star V * star U * (U * V) = star V * (star U * U) * V := by
        simp only [mul_assoc]
      _ = 1 := by rw [hU.1, mul_one, hV.1]
  · rw [star_mul]
    calc
      U * V * (star V * star U) = U * (V * star V) * star U := by
        simp only [mul_assoc]
      _ = 1 := by rw [hV.2, mul_one, hU.2]

namespace Manuscript

variable {n : ℕ}

def singleSitePauli (j : Fin n) (a : SinglePauli) : Fin n → SinglePauli :=
  fun i => if i = j then a else .I

theorem singleSitePauli_supportedOn (G : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ G) (a : SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) (singleSitePauli j a)) G := by
  classical
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  have hij : i ≠ j := by
    intro hij
    subst i
    exact hi hj
  simp [singleSitePauli, hij]

theorem unphased_pauliMatrix_anticommute_single
    (p : Fin n → SinglePauli) (j : Fin n) (a : SinglePauli)
    (hp : p j ≠ .I) (ha : a ≠ .I) (hne : p j ≠ a) :
    pauliMatrix (0 : Fin 4) p * pauliMatrix (0 : Fin 4) (singleSitePauli j a) =
      -(pauliMatrix (0 : Fin 4) (singleSitePauli j a) * pauliMatrix (0 : Fin 4) p) := by
  classical
  have hs : (∏ i, (p i).commutationSign (singleSitePauli j a i)) = -1 := by
    calc
      (∏ i, (p i).commutationSign (singleSitePauli j a i)) =
          (p j).commutationSign a := by
        rw [Finset.prod_eq_single j]
        · simp [singleSitePauli]
        · intro i _hi hij
          simp [singleSitePauli, hij, SinglePauli.commutationSign]
        · simp
      _ = -1 := by simp [SinglePauli.commutationSign, hp, ha, hne]
  simpa only [hs, neg_one_smul] using
    unphased_pauliMatrix_commutation p (singleSitePauli j a)

theorem SupportedOn.involutionBisector {dim : Fin n → ℕ}
    {P Q : Operator (PhysicalBasis n dim)} {G : Finset (Fin n)}
    (hP : SupportedOn P G) (hQ : SupportedOn Q G) :
    SupportedOn (involutionBisector P Q) G := by
  exact (hP.add hQ).smul (rationalScale 1)

/-- A single matrix supported on G compresses its nontrivial Pauli to one Z. -/
theorem pauli_group_to_single_site
    (G : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ G → p i = .I) (j : Fin n) (hj : j ∈ G) (hpj : p j ≠ .I) :
    ∃ U : Operator (QubitBasis n), IsUnitary U ∧ SupportedOn U G ∧
      U * pauliMatrix (0 : Fin 4) p * U.conjTranspose =
        pauliMatrix (0 : Fin 4) (singleSitePauli j .Z) := by
  classical
  let P : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) p
  let Z : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) (singleSitePauli j .Z)
  have hPself : star P = P := unphased_pauliMatrix_selfAdjoint p
  have hZself : star Z = Z := unphased_pauliMatrix_selfAdjoint (singleSitePauli j .Z)
  have hPsq : P * P = 1 := unphased_pauliMatrix_sq p
  have hZsq : Z * Z = 1 := unphased_pauliMatrix_sq (singleSitePauli j .Z)
  have hPsupport : SupportedOn P G := pauliMatrix_supportedOn_of_outside_identity G p hout
  have hZsupport : SupportedOn Z G := singleSitePauli_supportedOn G j hj .Z
  by_cases hpZ : p j = .Z
  · let Q : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) (singleSitePauli j .X)
    have hQself : star Q = Q := unphased_pauliMatrix_selfAdjoint (singleSitePauli j .X)
    have hQsq : Q * Q = 1 := unphased_pauliMatrix_sq (singleSitePauli j .X)
    have hQsupport : SupportedOn Q G := singleSitePauli_supportedOn G j hj .X
    have hPQ : P * Q = -(Q * P) := by
      apply unphased_pauliMatrix_anticommute_single p j .X hpj (by decide)
      simp [hpZ]
    have hQZ : Q * Z = -(Z * Q) := by
      apply unphased_pauliMatrix_anticommute_single (singleSitePauli j .X) j .Z
      · simp [singleSitePauli]
      · decide
      · simp [singleSitePauli]
    let H1 := involutionBisector P Q
    let H2 := involutionBisector Q Z
    have hH1self : star H1 = H1 := involutionBisector_selfAdjoint hPself hQself
    have hH2self : star H2 = H2 := involutionBisector_selfAdjoint hQself hZself
    have hH1 : IsUnitary H1 := involutionBisector_isUnitary hPself hQself hPsq hQsq hPQ
    have hH2 : IsUnitary H2 := involutionBisector_isUnitary hQself hZself hQsq hZsq hQZ
    have h1 : H1 * P * H1 = Q := involutionBisector_conjugates hPsq hQsq hPQ
    have h2 : H2 * Q * H2 = Z := involutionBisector_conjugates hQsq hZsq hQZ
    refine ⟨H2 * H1, unitary_mul hH2 hH1,
      (hQsupport.involutionBisector hZsupport).mul_same
        (hPsupport.involutionBisector hQsupport), ?_⟩
    change (H2 * H1) * P * star (H2 * H1) = Z
    rw [star_mul, hH1self, hH2self]
    calc
      (H2 * H1) * P * (H1 * H2) = H2 * (H1 * P * H1) * H2 := by
        simp only [mul_assoc]
      _ = Z := by rw [h1, h2]
  · have hPZ : P * Z = -(Z * P) :=
      unphased_pauliMatrix_anticommute_single p j .Z hpj (by decide) hpZ
    let H := involutionBisector P Z
    have hHself : star H = H := involutionBisector_selfAdjoint hPself hZself
    refine ⟨H, involutionBisector_isUnitary hPself hZself hPsq hZsq hPZ,
      hPsupport.involutionBisector hZsupport, ?_⟩
    change H * P * star H = Z
    rw [hHself]
    exact involutionBisector_conjugates hPsq hZsq hPZ

end Manuscript
end CriticalDepth
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliConjugation

/- ===== Source block: StabilizerWitness; SHA-256 aaa0a58eeb6c7e78ae350ab7e6a8e0b18db3f2d7cca7a2447c41c4894d0f3d53 ===== -/
section Merged_StabilizerWitness
/-!
# A minimum-weight logical Pauli from the original stabilizer-code hypotheses

The Pauli witness is derived from an arbitrary undetectable supported operator
using the concrete Pauli span. It is not an additional premise. The stabilizer
fixed-space equality is then used to obtain actual code preservation.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker BigOperators

variable {n K g d : ℕ} {dim : Fin n → ℕ}

def gaugeOnlyComplexSubmodule (C : Code n dim K g) :
    Submodule ℂ (Operator (PhysicalBasis n dim)) where
  carrier := {O | GaugeOnly C O}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    rintro A B ⟨MA, hA⟩ ⟨MB, hB⟩
    refine ⟨MA + MB, ?_⟩
    rw [Matrix.mul_add, Matrix.add_mul, hA, hB, Matrix.kronecker_add]
  smul_mem' := by
    rintro z A ⟨M, hM⟩
    refine ⟨z • M, ?_⟩
    rw [Matrix.mul_smul, Matrix.smul_mul, hM, Matrix.kronecker_smul]

def pauliSupport (p : Fin n → SinglePauli) : Finset (Fin n) :=
  Finset.univ.filter fun i => p i ≠ .I

theorem pauliSupport_subset_of_outside_identity
    (S : Finset (Fin n)) (p : Fin n → SinglePauli)
    (hout : ∀ i, i ∉ S → p i = .I) : pauliSupport p ⊆ S := by
  intro i hi
  by_contra hiS
  exact (Finset.mem_filter.mp hi).2 (hout i hiS)

theorem pauliMatrix_supportedOn_pauliSupport (p : Fin n → SinglePauli) :
    SupportedOn (pauliMatrix (0 : Fin 4) p) (pauliSupport p) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  by_contra hp
  exact hi (by simp [pauliSupport, hp])

theorem actualDistance_exists_nongauge_unphasedPauli
    (C : Code n (fun _ => 2) K g) (hdistance : HasActualDistance C d) :
    ∃ p : Fin n → SinglePauli, (pauliSupport p).card = d ∧
      ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) p) := by
  classical
  obtain ⟨hdetect, S, hS, O, hOsupported, hOnongauge⟩ := hdistance
  obtain ⟨A, hAencoding⟩ := hOsupported
  have hex : ∃ p : S → SinglePauli,
      ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) := by
    by_contra hn
    have hall : ∀ p : S → SinglePauli,
        GaugeOnly C (pauliMatrix (0 : Fin 4) (extendLocalPauli S p)) := by
      intro p
      by_contra hp
      exact hn ⟨p, hp⟩
    let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin n => 2) S)) :=
      (gaugeOnlyComplexSubmodule C).comap (localEmbedLinearMap S)
    have hspan : pauliTensorSpan S ≤ B := by
      apply Submodule.span_le.mpr
      rintro _ ⟨p, rfl⟩
      change GaugeOnly C (localEmbed S (tensorPauli p))
      rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
      exact hall p
    rw [tensorPauli_span_eq_top] at hspan
    have hA : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
    change GaugeOnly C (localEmbed S A) at hA
    apply hOnongauge
    simpa only [hAencoding] using hA
  obtain ⟨p, hp⟩ := hex
  let pfull : Fin n → SinglePauli := extendLocalPauli S p
  have hout : ∀ i, i ∉ S → pfull i = .I := by
    intro i hi
    simp [pfull, extendLocalPauli, hi]
  have hsubset : pauliSupport pfull ⊆ S :=
    pauliSupport_subset_of_outside_identity S pfull hout
  have hle : (pauliSupport pfull).card ≤ d := by
    simpa only [hS] using Finset.card_le_card hsubset
  have hge : d ≤ (pauliSupport pfull).card := by
    by_contra hn
    have hlt : (pauliSupport pfull).card < d := by omega
    apply hp
    exact hdetect (pauliSupport pfull) hlt (pauliMatrix (0 : Fin 4) pfull)
      (pauliMatrix_supportedOn_pauliSupport pfull)
  exact ⟨pfull, Nat.le_antisymm hle hge, hp⟩

/-- Every encoding column belongs to the encoded range, with an explicit coordinate vector. -/
theorem encoding_column_mem_range (C : Code n dim K g) (j : Fin K × Fin g) :
    (fun x => C.encoding x j) ∈ Set.range (fun v => C.encoding.mulVec v) := by
  classical
  refine ⟨fun i => if i = j then 1 else 0, ?_⟩
  funext x
  simp [Matrix.mulVec, dotProduct, mul_ite]

theorem encoding_fixed_of_fixedSpace
    (C : Code n dim K g)
    (S : Subgroup (Matrix.unitaryGroup (PhysicalBasis n dim) ℂ))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v})
    (U : Matrix.unitaryGroup (PhysicalBasis n dim) ℂ) (hUS : U ∈ S) :
    (U : Operator (PhysicalBasis n dim)) * C.encoding = C.encoding := by
  ext x j
  have hcol := encoding_column_mem_range C j
  rw [hspace] at hcol
  have hh := congrFun (hcol U hUS) x
  change ((U : Operator (PhysicalBasis n dim)) * C.encoding) x j = C.encoding x j at hh
  exact hh

theorem encoding_adjoint_fixed_of_fixed
    (C : Code n dim K g) (U : Operator (PhysicalBasis n dim))
    (hU : IsUnitary U) (hfix : U * C.encoding = C.encoding) :
    C.encoding.conjTranspose * U = C.encoding.conjTranspose := by
  have hh := congrArg Matrix.conjTranspose hfix
  have hstar : C.encoding.conjTranspose * U.conjTranspose = C.encoding.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul] using hh
  have hUleft : U.conjTranspose * U = 1 := hU.1
  calc
    C.encoding.conjTranspose * U = (C.encoding.conjTranspose * U.conjTranspose) * U := by
      rw [hstar]
    _ = C.encoding.conjTranspose := by rw [Matrix.mul_assoc, hUleft, Matrix.mul_one]

theorem gaugeOnly_of_compression_zero
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hzero : C.encoding.conjTranspose * P * C.encoding = 0) : GaugeOnly C P := by
  refine ⟨0, ?_⟩
  rw [hzero]
  simp

theorem anticommuting_fixed_operator_gaugeOnly
    (C : Code n dim K g) (P U : Operator (PhysicalBasis n dim))
    (hU : IsUnitary U) (hfix : U * C.encoding = C.encoding)
    (hanti : U * P = -(P * U)) : GaugeOnly C P := by
  have hEfix := encoding_adjoint_fixed_of_fixed C U hU hfix
  have hneg : C.encoding.conjTranspose * P * C.encoding =
      -(C.encoding.conjTranspose * P * C.encoding) := by
    calc
      C.encoding.conjTranspose * P * C.encoding =
          (C.encoding.conjTranspose * U) * P * C.encoding := by rw [hEfix]
      _ = C.encoding.conjTranspose * (U * P) * C.encoding := by
        simp only [Matrix.mul_assoc]
      _ = -(C.encoding.conjTranspose * (P * U) * C.encoding) := by
        rw [hanti]
        simp only [Matrix.mul_neg, Matrix.neg_mul]
      _ = -(C.encoding.conjTranspose * P * C.encoding) := by
        simp only [Matrix.mul_assoc, hfix]
  apply gaugeOnly_of_compression_zero C P
  ext i j
  change (C.encoding.conjTranspose * P * C.encoding) i j = 0
  have hh := congrArg (fun A : Operator (Fin K × Fin g) => A i j) hneg
  change (C.encoding.conjTranspose * P * C.encoding) i j =
    -((C.encoding.conjTranspose * P * C.encoding) i j) at hh
  linear_combination (1 / 2 : ℂ) * hh

theorem pauli_commutes_stabilizer_of_nongauge
    {k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (S : Subgroup (Matrix.unitaryGroup (QubitBasis n) ℂ))
    (hpauli : ∀ U ∈ S, IsPauli (U : Operator (QubitBasis n)))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (QubitBasis n)).mulVec v = v})
    (p : Fin n → SinglePauli) (hnongauge : ¬ GaugeOnly C (pauliMatrix (0 : Fin 4) p)) :
    ∀ U ∈ S, (U : Operator (QubitBasis n)) * pauliMatrix (0 : Fin 4) p =
      pauliMatrix (0 : Fin 4) p * (U : Operator (QubitBasis n)) := by
  intro U hUS
  obtain ⟨a, q, hU⟩ := hpauli U hUS
  have hcases := pauliMatrix_commute_or_anticommute a (0 : Fin 4) q p
  rw [← hU] at hcases
  rcases hcases with hcomm | hanti
  · exact hcomm
  · exact False.elim (hnongauge (anticommuting_fixed_operator_gaugeOnly C
      (pauliMatrix (0 : Fin 4) p) (U : Operator (QubitBasis n))
      ⟨U.2.1, U.2.2⟩ (encoding_fixed_of_fixedSpace C S hspace U hUS) hanti))

theorem code_preservation_of_stabilizer_commutation
    (C : Code n dim K g)
    (S : Subgroup (Matrix.unitaryGroup (PhysicalBasis n dim) ℂ))
    (hspace : Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v})
    (P : Operator (PhysicalBasis n dim))
    (hcomm : ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)) * P =
      P * (U : Operator (PhysicalBasis n dim))) :
    P * C.encoding = C.encoding * (C.encoding.conjTranspose * P * C.encoding) := by
  classical
  have hcolrange : ∀ j : Fin K × Fin g,
      ∃ v : (Fin K × Fin g) → ℂ, C.encoding.mulVec v = fun x => (P * C.encoding) x j := by
    intro j
    have hfixed : (fun x => (P * C.encoding) x j) ∈
        {v | ∀ U ∈ S, (U : Operator (PhysicalBasis n dim)).mulVec v = v} := by
      intro U hUS
      have hfix := encoding_fixed_of_fixedSpace C S hspace U hUS
      have hm : (U : Operator (PhysicalBasis n dim)) * (P * C.encoding) = P * C.encoding := by
        calc
          (U : Operator (PhysicalBasis n dim)) * (P * C.encoding) =
              ((U : Operator (PhysicalBasis n dim)) * P) * C.encoding := by rw [Matrix.mul_assoc]
          _ = (P * (U : Operator (PhysicalBasis n dim))) * C.encoding := by rw [hcomm U hUS]
          _ = P * C.encoding := by rw [Matrix.mul_assoc, hfix]
      funext x
      change ((U : Operator (PhysicalBasis n dim)) * (P * C.encoding)) x j =
        (P * C.encoding) x j
      rw [hm]
    rw [← hspace] at hfixed
    exact hfixed
  let Y : Operator (Fin K × Fin g) := fun i j => Classical.choose (hcolrange j) i
  have hPY : P * C.encoding = C.encoding * Y := by
    ext x j
    have hh := congrFun (Classical.choose_spec (hcolrange j)) x
    change (C.encoding * Y) x j = (P * C.encoding) x j at hh
    exact hh.symm
  have hY : Y = C.encoding.conjTranspose * P * C.encoding := by
    calc
      Y = (C.encoding.conjTranspose * C.encoding) * Y := by rw [C.isometry]; simp
      _ = C.encoding.conjTranspose * (C.encoding * Y) := by rw [Matrix.mul_assoc]
      _ = C.encoding.conjTranspose * (P * C.encoding) := by rw [← hPY]
      _ = C.encoding.conjTranspose * P * C.encoding := by rw [Matrix.mul_assoc]
  rw [hPY, hY]

def subspaceLogicalMatrix (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim)) :
    Operator (Fin K) :=
  fun i j => (C.encoding.conjTranspose * P * C.encoding) (i, 0) (j, 0)

theorem subspaceCompression_eq_kronecker
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim)) :
    C.encoding.conjTranspose * P * C.encoding =
      subspaceLogicalMatrix C P ⊗ₖ (1 : Operator (Fin 1)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = 0 := Subsingleton.elim _ _
  subst a
  subst b
  simp [subspaceLogicalMatrix, Matrix.kronecker_apply]

theorem codeCompression_selfAdjoint
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hself : P.conjTranspose = P) :
    (C.encoding.conjTranspose * P * C.encoding).conjTranspose =
      C.encoding.conjTranspose * P * C.encoding := by
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hself, Matrix.mul_assoc]

theorem codeCompression_sq_of_preserving
    (C : Code n dim K g) (P : Operator (PhysicalBasis n dim))
    (hsq : P * P = 1)
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    (C.encoding.conjTranspose * P * C.encoding) *
      (C.encoding.conjTranspose * P * C.encoding) = 1 := by
  let Q : Operator (Fin K × Fin g) := C.encoding.conjTranspose * P * C.encoding
  have hp : P * C.encoding = C.encoding * Q := hpreserve
  change Q * Q = 1
  calc
    Q * Q = (C.encoding.conjTranspose * P) * (C.encoding * Q) := by
      dsimp [Q]
      simp only [Matrix.mul_assoc]
    _ = (C.encoding.conjTranspose * P) * (P * C.encoding) := by rw [← hp]
    _ = C.encoding.conjTranspose * (P * P) * C.encoding := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hsq, Matrix.mul_one, C.isometry]

theorem subspaceLogicalMatrix_selfAdjoint
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hself : P.conjTranspose = P) :
    (subspaceLogicalMatrix C P).conjTranspose = subspaceLogicalMatrix C P := by
  ext i j
  have hh := congrArg (fun A : Operator (Fin K × Fin 1) => A (i, 0) (j, 0))
    (codeCompression_selfAdjoint C P hself)
  simpa only [subspaceLogicalMatrix, Matrix.conjTranspose_apply] using hh

theorem subspaceLogicalMatrix_sq_of_preserving
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hsq : P * P = 1)
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    subspaceLogicalMatrix C P * subspaceLogicalMatrix C P = 1 := by
  have hc := codeCompression_sq_of_preserving C P hsq hpreserve
  simp only [subspaceCompression_eq_kronecker C P] at hc
  rw [← Matrix.mul_kronecker_mul (subspaceLogicalMatrix C P) (subspaceLogicalMatrix C P)
    (1 : Operator (Fin 1)) (1 : Operator (Fin 1))] at hc
  simp only [one_mul] at hc
  ext i j
  have hh := congrArg (fun A : Operator (Fin K × Fin 1) => A (i, 0) (j, 0)) hc
  simpa [Matrix.kronecker_apply, Matrix.one_apply] using hh

theorem subspaceLogicalMatrix_nonscalar_of_nongauge
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hnongauge : ¬ GaugeOnly C P) : ¬ IsScalar (subspaceLogicalMatrix C P) := by
  rintro ⟨z, hz⟩
  apply hnongauge
  refine ⟨z • (1 : Operator (Fin 1)), ?_⟩
  calc
    C.encoding.conjTranspose * P * C.encoding =
        subspaceLogicalMatrix C P ⊗ₖ (1 : Operator (Fin 1)) :=
      subspaceCompression_eq_kronecker C P
    _ = (z • (1 : Operator (Fin K))) ⊗ₖ (1 : Operator (Fin 1)) := by rw [hz]
    _ = (1 : Operator (Fin K)) ⊗ₖ (z • (1 : Operator (Fin 1))) := by
      ext ⟨i, a⟩ ⟨j, b⟩
      change (z * (1 : Operator (Fin K)) i j) * (1 : Operator (Fin 1)) a b =
        (1 : Operator (Fin K)) i j * (z * (1 : Operator (Fin 1)) a b)
      ring

theorem subspaceLogicalMatrix_implements_of_preserving
    (C : Code n dim K 1) (P : Operator (PhysicalBasis n dim))
    (hunitary : IsUnitary (subspaceLogicalMatrix C P))
    (hpreserve : P * C.encoding =
      C.encoding * (C.encoding.conjTranspose * P * C.encoding)) :
    Implements C P (subspaceLogicalMatrix C P) := by
  refine ⟨hunitary, 1, ?_, ?_⟩
  · constructor <;> simp
  · exact hpreserve.trans
      (congrArg (fun A : Operator (Fin K × Fin 1) => C.encoding * A)
        (subspaceCompression_eq_kronecker C P))

/--
The minimum-weight nonscalar logical Pauli follows from the original actual
distance and stabilizer fixed-space hypotheses. No Pauli witness, preservation
predicate, or desired logical action is supplied as an extra hypothesis.
-/
theorem stabilizer_actualDistance_logicalPauli
    {k : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (pauliSupport p).card = d ∧
      Implements C (pauliMatrix (0 : Fin 4) p) W ∧
      IsUnitary W ∧ W.conjTranspose = W ∧ W * W = 1 ∧ ¬ IsScalar W := by
  classical
  obtain ⟨p, hcard, hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  obtain ⟨S, hpauli, hspace⟩ := hstabilizer
  let P : Operator (QubitBasis n) := pauliMatrix (0 : Fin 4) p
  have hcomm := pauli_commutes_stabilizer_of_nongauge C S hpauli hspace p hnongauge
  have hpreserve := code_preservation_of_stabilizer_commutation C S hspace P hcomm
  have hself : (subspaceLogicalMatrix C P).conjTranspose = subspaceLogicalMatrix C P :=
    subspaceLogicalMatrix_selfAdjoint C P (unphased_pauliMatrix_selfAdjoint p)
  have hsq : subspaceLogicalMatrix C P * subspaceLogicalMatrix C P = 1 :=
    subspaceLogicalMatrix_sq_of_preserving C P (unphased_pauliMatrix_sq p) hpreserve
  have hunitary : IsUnitary (subspaceLogicalMatrix C P) := by
    constructor
    · change (subspaceLogicalMatrix C P).conjTranspose * subspaceLogicalMatrix C P = 1
      rw [hself, hsq]
    · change subspaceLogicalMatrix C P * (subspaceLogicalMatrix C P).conjTranspose = 1
      rw [hself, hsq]
  have hnonscalar := subspaceLogicalMatrix_nonscalar_of_nongauge C P hnongauge
  exact ⟨p, subspaceLogicalMatrix C P, hcard,
    subspaceLogicalMatrix_implements_of_preserving C P hunitary hpreserve,
    hunitary, hself, hsq, hnonscalar⟩

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_StabilizerWitness

/- ===== Source block: CircuitSolutions; SHA-256 1cfbf7b5a621ab50e2a6c946cdf572e868f1b35b708ab45f06da051f8166f7cb ===== -/
section Merged_CircuitSolutions
/-!
# Field-valued solutions of the actual circuit presentation

Every relation below is obtained by evaluating a generator of the defining
ideal. Physical inverse pairs, the two encoded intertwining equations, and
concrete tensor-support membership are proved from that presentation.
No inverse equation for the unembedded local matrices is asserted.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

section MatrixEvaluation

variable {A B : Type*} [CommRing A] [CommRing B]
variable [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)

theorem solutionMap_mul {ι κ μ : Type*} [Fintype κ]
    (M : Matrix ι κ A) (N : Matrix κ μ A) :
    (M * N).map φ = M.map φ * N.map φ := by
  ext i j
  change φ (∑ k, M i k * N k j) = ∑ k, φ (M i k) * φ (N k j)
  simp only [map_sum, map_mul]

theorem solutionMap_one {ι : Type*} [DecidableEq ι] :
    (1 : Matrix ι ι A).map φ = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, hij]

theorem solutionMap_kronecker {ι κ μ ν : Type*}
    (M : Matrix ι κ A) (N : Matrix μ ν A) :
    (M ⊗ₖ N).map φ = M.map φ ⊗ₖ N.map φ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  exact map_mul φ (M i j) (N a b)

theorem solutionMap_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Matrix ι ι A)) :
    matrices.prod.map φ = (matrices.map fun M => M.map φ).prod := by
  induction matrices with
  | nil => simpa only [List.prod_nil, List.map_nil] using solutionMap_one φ
  | cons M matrices ih =>
      simpa only [List.prod_cons, List.map_cons, solutionMap_mul, ih]

end MatrixEvaluation

section Solutions

variable {n ℓ g h : ℕ} {dim : Fin n → ℕ}
variable (C : Code n dim ℓ g)
variable (support : GateIndex n h → Finset (Fin n))
variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
variable (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂)

/-- The presentation has finitely many matrix-entry variables. -/
instance circuitCoordinateRing_isNoetherianRing :
    IsNoetherianRing (CircuitCoordinateRing (C := C) (support := support)) := by
  classical
  unfold CircuitCoordinateRing
  infer_instance

/-- Pull a coordinate-ring point back to the polynomial presentation. -/
def circuitPointMap :
    CircuitPolynomial (dim := dim) (K := ℓ) (g := g) support →ₐ[ℂ] 𝕂 :=
  ψ.comp (Ideal.Quotient.mkₐ ℂ (circuitIdeal support C))

theorem circuitPointMap_relation
    (f : CircuitPolynomial (K := ℓ) (g := g) support)
    (hf : f ∈ circuitRelations support C) : circuitPointMap C support ψ f = 0 := by
  have hi : f ∈ circuitIdeal support C := Ideal.subset_span hf
  change ψ (Ideal.Quotient.mk (circuitIdeal support C) f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]

theorem circuitPointMap_matrixRelation {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (K := ℓ) (g := g) support))
    (hAB : matrixRelationEntries support A B ⊆ circuitRelations support C) :
    A.map (circuitPointMap C support ψ) = B.map (circuitPointMap C support ψ) := by
  ext i j
  change circuitPointMap C support ψ (A i j) = circuitPointMap C support ψ (B i j)
  have hf := circuitPointMap_relation C support ψ (A i j - B i j)
    (hAB ⟨(i, j), rfl⟩)
  exact sub_eq_zero.mp (by simpa only [map_sub] using hf)

theorem circuitPointMap_inverseRelations {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (K := ℓ) (g := g) support))
    (hAB : inverseRelationEntries support A B ⊆ circuitRelations support C) :
    A.map (circuitPointMap C support ψ) * B.map (circuitPointMap C support ψ) = 1 ∧
      B.map (circuitPointMap C support ψ) * A.map (circuitPointMap C support ψ) = 1 := by
  constructor
  · have heq := circuitPointMap_matrixRelation C support ψ (A * B) 1
      (fun f hf => hAB (Set.mem_union_left _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using heq
  · have heq := circuitPointMap_matrixRelation C support ψ (B * A) 1
      (fun f hf => hAB (Set.mem_union_right _ hf))
    simpa only [solutionMap_mul, solutionMap_one] using heq

private theorem physicalInverseRelations_subset (p : GateIndex n h) :
    inverseRelationEntries support (physicalGatePolynomial support p false)
      (physicalGatePolynomial support p true) ⊆ circuitRelations support C := by
  intro f hf
  have hf0 : f ∈ (⋃ p : GateIndex n h,
      inverseRelationEntries support (physicalGatePolynomial support p false)
        (physicalGatePolynomial support p true)) := Set.mem_iUnion.mpr ⟨p, hf⟩
  simp only [circuitRelations, Set.mem_union]
  tauto

private theorem logicalInverseRelations_subset :
    inverseRelationEntries support (logicalPolynomial support false)
      (logicalPolynomial support true) ⊆ circuitRelations support C := by
  intro f hf
  simp only [circuitRelations, Set.mem_union]
  tauto

private theorem gaugeInverseRelations_subset :
    inverseRelationEntries support (gaugePolynomial support false)
      (gaugePolynomial support true) ⊆ circuitRelations support C := by
  intro f hf
  simp only [circuitRelations, Set.mem_union]
  tauto

def solutionGate (p : GateIndex n h) (inverse : Bool) :
    Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (physicalGatePolynomial support p inverse).map (circuitPointMap C support ψ)

def solutionLogical (inverse : Bool) : Matrix (Fin ℓ) (Fin ℓ) 𝕂 :=
  (logicalPolynomial support inverse).map (circuitPointMap C support ψ)

def solutionGauge (inverse : Bool) : Matrix (Fin g) (Fin g) 𝕂 :=
  (gaugePolynomial support inverse).map (circuitPointMap C support ψ)

def solutionTotal : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (totalPolynomial support).map (circuitPointMap C support ψ)

def solutionInverseTotal : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) 𝕂 :=
  (inverseTotalPolynomial support).map (circuitPointMap C support ψ)

theorem solutionGate_inverse (p : GateIndex n h) :
    solutionGate C support ψ p false * solutionGate C support ψ p true = 1 ∧
      solutionGate C support ψ p true * solutionGate C support ψ p false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (physicalInverseRelations_subset C support p)

theorem solutionLogical_inverse :
    solutionLogical C support ψ false * solutionLogical C support ψ true = 1 ∧
      solutionLogical C support ψ true * solutionLogical C support ψ false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (logicalInverseRelations_subset C support)

theorem solutionGauge_inverse :
    solutionGauge C support ψ false * solutionGauge C support ψ true = 1 ∧
      solutionGauge C support ψ true * solutionGauge C support ψ false = 1 := by
  exact circuitPointMap_inverseRelations C support ψ _ _
    (gaugeInverseRelations_subset C support)

theorem solutionGate_mem_supportedSpan (p : GateIndex n h) (inverse : Bool) :
    solutionGate C support ψ p inverse ∈ supportedSpan (K := 𝕂) (support p) :=
  physicalGatePolynomial_map_mem_supportedSpan support p inverse (circuitPointMap C support ψ)

theorem circuitPointMap_constant {ι κ : Type*} (A : Matrix ι κ ℂ) :
    (A.map MvPolynomial.C).map (circuitPointMap C support ψ) =
      A.map (algebraMap ℂ 𝕂) := by
  ext i j
  exact (circuitPointMap C support ψ).commutes (A i j)

theorem solution_encoding :
    solutionTotal C support ψ * C.encoding.map (algebraMap ℂ 𝕂) =
      C.encoding.map (algebraMap ℂ 𝕂) *
        (solutionLogical C support ψ false ⊗ₖ solutionGauge C support ψ false) := by
  have hsub : matrixRelationEntries support
      (totalPolynomial support * C.encoding.map MvPolynomial.C)
      (C.encoding.map MvPolynomial.C *
        (logicalPolynomial support false ⊗ₖ gaugePolynomial support false)) ⊆
      circuitRelations support C := by
    intro f hf
    simp only [circuitRelations, Set.mem_union]
    tauto
  have heq := circuitPointMap_matrixRelation C support ψ _ _ hsub
  simpa only [solutionMap_mul, solutionMap_kronecker, circuitPointMap_constant,
    solutionTotal, solutionLogical, solutionGauge] using heq

theorem solution_encoding_dual :
    C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) * solutionTotal C support ψ =
      (solutionLogical C support ψ false ⊗ₖ solutionGauge C support ψ false) *
        C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) := by
  have hsub : matrixRelationEntries support
      (C.encoding.conjTranspose.map MvPolynomial.C * totalPolynomial support)
      ((logicalPolynomial support false ⊗ₖ gaugePolynomial support false) *
        C.encoding.conjTranspose.map MvPolynomial.C) ⊆ circuitRelations support C := by
    intro f hf
    simp only [circuitRelations, Set.mem_union]
    tauto
  have heq := circuitPointMap_matrixRelation C support ψ _ _ hsub
  simpa only [solutionMap_mul, solutionMap_kronecker, circuitPointMap_constant,
    solutionTotal, solutionLogical, solutionGauge] using heq

theorem solution_encoding_isometry :
    C.encoding.conjTranspose.map (algebraMap ℂ 𝕂) *
      C.encoding.map (algebraMap ℂ 𝕂) = 1 := by
  have heq := congrArg (fun A : Matrix (Fin ℓ × Fin g) (Fin ℓ × Fin g) ℂ =>
    A.map (algebraMap ℂ 𝕂)) C.isometry
  simpa only [constantMatrix_mul, constantMatrix_one] using heq

def solutionGateList : List (GateWithInverse (PhysicalBasis n dim) 𝕂) :=
  (executionGateIndices (n := n) (h := h)).map fun p =>
    (solutionGate C support ψ p false, solutionGate C support ψ p true)

theorem solutionTotal_eq_gatePairProduct :
    solutionTotal C support ψ = gatePairProduct (solutionGateList C support ψ).reverse := by
  unfold solutionTotal totalPolynomial gatePairProduct solutionGateList
  rw [solutionMap_list_prod]
  simp [solutionGate, List.map_reverse, List.map_map, Function.comp_def]

theorem solutionInverseTotal_eq_gatePairInverseProduct :
    solutionInverseTotal C support ψ =
      gatePairInverseProduct (solutionGateList C support ψ).reverse := by
  unfold solutionInverseTotal inverseTotalPolynomial gatePairInverseProduct solutionGateList
  rw [solutionMap_list_prod]
  simp [solutionGate, List.map_map, Function.comp_def]

theorem solutionTotal_inverse :
    solutionTotal C support ψ * solutionInverseTotal C support ψ = 1 ∧
      solutionInverseTotal C support ψ * solutionTotal C support ψ = 1 := by
  rw [solutionTotal_eq_gatePairProduct, solutionInverseTotal_eq_gatePairInverseProduct]
  apply gatePairProduct_mutual_inverse
  intro pair hp
  have hp' : ∃ p, (solutionGate C support ψ p false,
      solutionGate C support ψ p true) = pair := by
    obtain ⟨p, _hp, heq⟩ := List.mem_map.mp
      (show pair ∈ solutionGateList C support ψ from List.mem_reverse.mp hp)
    exact ⟨p, heq⟩
  obtain ⟨p, rfl⟩ := hp'
  exact solutionGate_inverse C support ψ p

end Solutions

section LayoutSolutions

variable {n ℓ g h q : ℕ} {dim : Fin n → ℕ}
variable (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
variable {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]

def layoutSupport : GateIndex n h → Finset (Fin n) := fun p => (L p.1).support p.2

/-- A field-valued layer with precisely the supplied physical support layout. -/
def solutionFieldLayer
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) : FieldLayer (K := 𝕂) n dim q where
  layout := L layer
  gate := fun i => (solutionGate C (layoutSupport L) ψ (layer, i) false,
    solutionGate C (layoutSupport L) ψ (layer, i) true)
  gate_locality := fun i => solutionGate_mem_supportedSpan C (layoutSupport L) ψ (layer, i) false
  inverse_locality := fun i => solutionGate_mem_supportedSpan C (layoutSupport L) ψ (layer, i) true
  inverse_identities := fun i => solutionGate_inverse C (layoutSupport L) ψ (layer, i)

theorem solutionFieldLayer_eval
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) :
    (solutionFieldLayer C L ψ layer).eval =
      (List.ofFn fun i => solutionGate C (layoutSupport L) ψ (layer, i) false).reverse.prod := by
  simp [FieldLayer.eval, gatePairProduct, solutionFieldLayer, List.map_reverse,
    Function.comp_def]

theorem solutionFieldLayer_evalInv
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (layer : Fin h) :
    (solutionFieldLayer C L ψ layer).evalInv =
      (List.ofFn fun i => solutionGate C (layoutSupport L) ψ (layer, i) true).prod := by
  simp [FieldLayer.evalInv, gatePairInverseProduct, solutionFieldLayer, Function.comp_def]

private theorem map_executionGateIndices {α : Type*} (f : GateIndex n h → α) :
    (executionGateIndices (n := n) (h := h)).map f =
      (List.ofFn fun layer : Fin h => List.ofFn fun i : Fin n => f (layer, i)).flatten := by
  simp [executionGateIndices, List.map_flatten, List.map_ofFn, Function.comp_def]

private theorem list_reverse_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.reverse.prod = (lists.map fun xs => xs.reverse.prod).reverse.prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.reverse_append, List.prod_append, ih]

private theorem list_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.prod = (lists.map List.prod).prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.prod_append, ih]

private theorem solution_fieldSequenceEval_eq_reverse_prod
    (layers : List (FieldLayer (K := 𝕂) n dim q)) :
    fieldLayerSequenceEval layers = (layers.map FieldLayer.eval).reverse.prod := by
  induction layers with
  | nil => simp [fieldLayerSequenceEval]
  | cons layer layers ih =>
      simp [fieldLayerSequenceEval, ih, List.reverse_cons, List.prod_append]

private theorem solution_fieldSequenceInv_eq_prod
    (layers : List (FieldLayer (K := 𝕂) n dim q)) :
    fieldLayerSequenceInv layers = (layers.map FieldLayer.evalInv).prod := by
  induction layers with
  | nil => simp [fieldLayerSequenceInv]
  | cons layer layers ih => simp [fieldLayerSequenceInv, ih]

/-- The polynomial total uses exactly the same layer and slot order as the
actual field-valued layer sequence. -/
theorem solutionTotal_eq_fieldLayerSequence
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂) :
    solutionTotal C (layoutSupport L) ψ =
      fieldLayerSequenceEval (List.ofFn (solutionFieldLayer C L ψ)) := by
  rw [solution_fieldSequenceEval_eq_reverse_prod]
  unfold solutionTotal totalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_reverse, List.map_map]
  change ((executionGateIndices (n := n) (h := h)).map
    (fun p => solutionGate C (layoutSupport L) ψ p false)).reverse.prod = _
  rw [map_executionGateIndices, list_reverse_prod_flatten]
  simp only [List.map_ofFn, solutionFieldLayer_eval, Function.comp_def]

/-- The inverse polynomial total has the corresponding unreversed inverse
execution order. -/
theorem solutionInverseTotal_eq_fieldLayerSequence
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂) :
    solutionInverseTotal C (layoutSupport L) ψ =
      fieldLayerSequenceInv (List.ofFn (solutionFieldLayer C L ψ)) := by
  rw [solution_fieldSequenceInv_eq_prod]
  unfold solutionInverseTotal inverseTotalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_map]
  change ((executionGateIndices (n := n) (h := h)).map
    (fun p => solutionGate C (layoutSupport L) ψ p true)).prod = _
  rw [map_executionGateIndices, list_prod_flatten]
  simp only [List.map_ofFn, solutionFieldLayer_evalInv, Function.comp_def]

end LayoutSolutions

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_CircuitSolutions

/- ===== Source block: FieldLayerDerivative; SHA-256 86396a45830fe5dd3a15c326d5102590167677526ac432da5ae0e3ab7d5fdf57 ===== -/
section Merged_FieldLayerDerivative
/-!
# Concrete layer derivatives and the two-sided same-layer support endpoint

Disjoint gates in one layer do not enlarge one another's logarithmic insertions.
The derivative identities below use the actual gate/inverse lists and their
explicit physical execution order.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {K : Type*} [Field K] [Algebra ℂ K]
variable {n q : ℕ} {dim : Fin n → ℕ}

/-- A layer's own gate support is unchanged by its selective light cone. -/
theorem Layer.lightCone_support (L : Layer n dim q) (j : Fin n) :
    L.lightCone (L.support j) = L.support j := by
  classical
  apply le_antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hxj | hxA
    · exact hxj
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxA
      have hact : ¬ Disjoint (L.support i) (L.support j) :=
        (Finset.mem_filter.mp hi).2
      by_cases hij : i = j
      · simpa only [hij] using hxi
      · exact False.elim (hact (L.disjoint i j hij))
  · exact Finset.subset_union_left

theorem FieldLayer.conjugate_gateSupport_mem (L : FieldLayer (K := K) n dim q)
    (j : Fin n) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) (L.layout.support j)) :
    L.eval * O * L.evalInv ∈ supportedSpan (K := K) (L.layout.support j) := by
  simpa only [FieldLayer.lightCone, Layer.lightCone_support] using
    L.conjugate_mem_supportedSpan (L.layout.support j) hO

theorem FieldLayer.inverse_conjugate_gateSupport_mem (L : FieldLayer (K := K) n dim q)
    (j : Fin n) {O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K}
    (hO : O ∈ supportedSpan (K := K) (L.layout.support j)) :
    L.evalInv * O * L.eval ∈ supportedSpan (K := K) (L.layout.support j) := by
  simpa only [FieldLayer.lightCone, Layer.lightCone_support] using
    L.inverse_conjugate_mem_supportedSpan (L.layout.support j) hO

theorem FieldLayer.backward_conjugated_logarithmic_gate_mem
    (L : FieldLayer (K := K) n dim q) (D : Derivation ℂ K K) (j : Fin n) :
    L.evalInv * (matrixDerivation D (L.gate j).1 * (L.gate j).2) * L.eval ∈
      supportedSpan (K := K) (L.layout.support j) := by
  exact L.inverse_conjugate_gateSupport_mem j (L.logarithmic_gate_mem D j)

private theorem conjugate_list_sum
    (indices : List (Fin n))
    (H : Fin n → Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K)
    (U Ui : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K)
    (h : ∀ j ∈ indices, U * H j * Ui = H j) :
    U * (indices.map H).sum * Ui = (indices.map H).sum := by
  revert h
  induction indices with
  | nil =>
      intro h
      simp
  | cons j indices ih =>
      intro h
      have hj := h j (by simp)
      have hr : ∀ k ∈ indices, U * H k * Ui = H k := by
        intro k hk
        exact h k (by simp [hk])
      simp only [List.map_cons, List.sum_cons, mul_add, add_mul, hj, ih hr]

private theorem indexed_layer_logarithmic_derivative
    (L : FieldLayer (K := K) n dim q) (D : Derivation ℂ K K)
    (indices : List (Fin n)) (hn : indices.Nodup) :
    matrixDerivation D (gatePairProduct (indices.map L.gate)) *
        gatePairInverseProduct (indices.map L.gate) =
      (indices.map fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2).sum := by
  revert hn
  induction indices with
  | nil =>
      intro hn
      simp [matrixDerivation_one]
  | cons i indices ih =>
      intro hn
      have hi : i ∉ indices := (List.nodup_cons.mp hn).1
      have hr : indices.Nodup := (List.nodup_cons.mp hn).2
      have hg : ∀ p ∈ indices.map L.gate, p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 := by
        intro p hp
        obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp hp
        exact L.inverse_identities j
      have hprod := (gatePairProduct_mutual_inverse (indices.map L.gate) hg).1
      have hfixed : ∀ j ∈ indices,
          (L.gate i).1 * (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            (L.gate i).2 = matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
        intro j hj
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hi hj
        exact supportedSpan_pair_conjugate_disjoint (L.logarithmic_gate_mem D j)
          (L.gate_locality i) (L.layout.disjoint j i hji) (L.inverse_identities i).1
      simp only [List.map_cons, gatePairProduct_cons, gatePairInverseProduct_cons,
        List.sum_cons]
      rw [logarithmic_product_rule D (L.gate i).1 (gatePairProduct (indices.map L.gate))
        (L.gate i).2 (gatePairInverseProduct (indices.map L.gate)) hprod, ih hr]
      rw [conjugate_list_sum indices
        (fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2)
        (L.gate i).1 (L.gate i).2 hfixed]

private theorem sum_ofFn_eq_fintype_sum {M : Type*} [AddCommMonoid M]
    {m : ℕ} (f : Fin m → M) : (List.ofFn f).sum = ∑ i, f i := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.ofFn_succ, List.sum_cons, Fin.sum_univ_succ]
      exact congrArg (fun z => f 0 + z) (ih (fun i => f i.succ))

/-- The genuine layer derivative is the finite sum of local gate insertions. -/
theorem FieldLayer.logarithmic_derivative_eq_sum (L : FieldLayer (K := K) n dim q)
    (D : Derivation ℂ K K) :
    matrixDerivation D L.eval * L.evalInv =
      ∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
  classical
  let indices : List (Fin n) := (List.ofFn fun j : Fin n => j).reverse
  have hn' : (List.ofFn fun j : Fin n => j).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj hij
    have hij' := congrArg Fin.val hij
    simpa only [List.getElem_ofFn] using hij'
  have hn : indices.Nodup := by
    simpa only [indices, List.nodup_reverse] using hn'
  have hg : indices.map L.gate = (List.ofFn L.gate).reverse := by
    simp [indices, List.map_reverse, List.map_ofFn, Function.comp_def]
  have hs : (indices.map fun j => matrixDerivation D (L.gate j).1 * (L.gate j).2).sum =
      ∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2 := by
    simp only [indices, List.map_reverse, List.sum_reverse, List.map_ofFn,
      Function.comp_def]
    exact sum_ofFn_eq_fintype_sum _
  have hh := indexed_layer_logarithmic_derivative L D indices hn
  rw [hg, hs] at hh
  exact hh

/-- An actual gate insertion, conjugated by all physically later layers. -/
def layerGateInsertionAt (D : Derivation ℂ K K) :
    (layers : List (FieldLayer (K := K) n dim q)) → Fin layers.length → Fin n →
      Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) K
  | [], i => Fin.elim0 i
  | L :: layers, i =>
      Fin.cases
        (fun j => fieldLayerSequenceEval layers *
          (matrixDerivation D (L.gate j).1 * (L.gate j).2) * fieldLayerSequenceInv layers)
        (fun r => layerGateInsertionAt D layers r) i

theorem layerGateInsertion_sum_cons (D : Derivation ℂ K K)
    (L : FieldLayer (K := K) n dim q) (layers : List (FieldLayer (K := K) n dim q)) :
    (∑ r : Fin (L :: layers).length, ∑ j : Fin n, layerGateInsertionAt D (L :: layers) r j) =
      fieldLayerSequenceEval layers *
          (∑ j : Fin n, matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            fieldLayerSequenceInv layers +
        ∑ r : Fin layers.length, ∑ j : Fin n, layerGateInsertionAt D layers r j := by
  change (∑ r : Fin (layers.length + 1),
    ∑ j : Fin n, layerGateInsertionAt D (L :: layers) r j) = _
  rw [Fin.sum_univ_succ]
  simp only [layerGateInsertionAt, Fin.cases_zero, Fin.cases_succ,
    Finset.mul_sum, Finset.sum_mul]

/-- The total derivative expansion is derived from the actual field-valued layers. -/
theorem fieldLayerSequence_logarithmic_derivative_eq_sum
    (D : Derivation ℂ K K) (layers : List (FieldLayer (K := K) n dim q)) :
    matrixDerivation D (fieldLayerSequenceEval layers) * fieldLayerSequenceInv layers =
      ∑ r : Fin layers.length, ∑ j : Fin n, layerGateInsertionAt D layers r j := by
  induction layers with
  | nil =>
      simp [fieldLayerSequenceEval, fieldLayerSequenceInv, matrixDerivation_one]
  | cons L layers ih =>
      rw [fieldLayerSequenceEval, fieldLayerSequenceInv,
        logarithmic_product_rule D (fieldLayerSequenceEval layers) L.eval
          (fieldLayerSequenceInv layers) L.evalInv L.mutual_inverse.1,
        L.logarithmic_derivative_eq_sum D, ih, layerGateInsertion_sum_cons]
      exact add_comm _ _

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_FieldLayerDerivative

/- ===== Source block: FourQubitExample; SHA-256 c576f4cf2058e7330f3aeb5a7dba94c998cbe38438665a98e007c59ca66310d7 ===== -/
section Merged_FourQubitExample
/-!
# The concrete four-qubit distance-two subspace

The four columns are the normalized complementary pairs
0000/1111, 0011/1100, 0101/1010, and 0110/1001. All matrix entries
are explicit. Finite index calculations use kernel-reduced `decide` and
ordinary arithmetic tactics, never an external decision oracle.
-/

noncomputable section

namespace CriticalDepth.Manuscript.FourQubit

open Matrix
open scoped BigOperators Kronecker

def word : Fin 4 → QubitBasis 4 :=
  ![![0, 0, 0, 0], ![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]]

def complement (x : QubitBasis 4) : QubitBasis 4 := fun i => 1 - x i

@[simp] theorem word_eq_word (i j : Fin 4) : word i = word j ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem complement_word_eq_complement_word (i j : Fin 4) :
    complement (word i) = complement (word j) ↔ i = j := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem word_ne_complement_word (i j : Fin 4) :
    word i ≠ complement (word j) := by
  fin_cases i <;> fin_cases j <;> decide

@[simp] theorem complement_word_ne_word (i j : Fin 4) :
    complement (word i) ≠ word j := by
  fin_cases i <;> fin_cases j <;> decide

def dirac {α : Type*} [DecidableEq α] (a : α) (x : α) : ℂ := if x = a then 1 else 0

@[simp] theorem star_dirac {α : Type*} [DecidableEq α] (a x : α) :
    star (dirac a x) = dirac a x := by
  by_cases h : x = a <;> simp [dirac, h]

@[simp] theorem sum_dirac_mul {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℂ) : (∑ x, dirac a x * f x) = f a := by
  simp [dirac, ite_mul]

@[simp] theorem sum_mul_dirac {α : Type*} [Fintype α] [DecidableEq α]
    (a : α) (f : α → ℂ) : (∑ x, f x * dirac a x) = f a := by
  simp [dirac, mul_ite]

def scale : ℂ := (Real.sqrt (1 / 2 : ℝ) : ℂ)

theorem scale_norm : star scale * scale = (1 / 2 : ℂ) := by
  have hs : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = (1 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  change star (Real.sqrt (1 / 2 : ℝ) : ℂ) * (Real.sqrt (1 / 2 : ℝ) : ℂ) = _
  have hstar : star (Real.sqrt (1 / 2 : ℝ) : ℂ) = (Real.sqrt (1 / 2 : ℝ) : ℂ) :=
    Complex.conj_ofReal _
  rw [hstar]
  have hreal : Real.sqrt (1 / 2 : ℝ) * Real.sqrt (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
    simpa only [pow_two] using hs
  simpa using congrArg Complex.ofReal hreal

def encoding : Matrix (QubitBasis 4) (Fin 4 × Fin 1) ℂ :=
  fun x j => scale * (dirac (word j.1) x + dirac (complement (word j.1)) x)

theorem encoding_adjoint_mul_entry (O : Operator (QubitBasis 4))
    (j : Fin 4 × Fin 1) (y : QubitBasis 4) :
    (encoding.conjTranspose * O) j y =
      star scale * (O (word j.1) y + O (complement (word j.1)) y) := by
  classical
  change (∑ x, star (scale * (dirac (word j.1) x +
    dirac (complement (word j.1)) x)) * O x y) = _
  calc
    _ = star scale * (∑ x, dirac (word j.1) x * O x y) +
        star scale * (∑ x, dirac (complement (word j.1)) x * O x y) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      rw [star_mul, star_add, star_dirac, star_dirac]
      ring
    _ = _ := by rw [sum_dirac_mul, sum_dirac_mul, mul_add]

theorem encoding_compression_entry (O : Operator (QubitBasis 4))
    (j k : Fin 4 × Fin 1) :
    (encoding.conjTranspose * O * encoding) j k =
      (star scale * scale) *
        (O (word j.1) (word k.1) + O (word j.1) (complement (word k.1)) +
          O (complement (word j.1)) (word k.1) +
          O (complement (word j.1)) (complement (word k.1))) := by
  classical
  change (∑ x, (encoding.conjTranspose * O) j x * encoding x k) = _
  simp only [encoding_adjoint_mul_entry, encoding]
  calc
    _ = (star scale * scale) *
        ((∑ x, O (word j.1) x * dirac (word k.1) x) +
          (∑ x, O (word j.1) x * dirac (complement (word k.1)) x) +
          (∑ x, O (complement (word j.1)) x * dirac (word k.1) x) +
          (∑ x, O (complement (word j.1)) x * dirac (complement (word k.1)) x)) := by
      conv_rhs => simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by simp only [sum_mul_dirac]

theorem encoding_isometry : encoding.conjTranspose * encoding = 1 := by
  have hc := encoding_compression_entry (1 : Operator (QubitBasis 4))
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  change (encoding.conjTranspose * encoding) (i, 0) (j, 0) =
    (1 : Operator (Fin 4 × Fin 1)) (i, 0) (j, 0)
  have hh := hc (i, 0) (j, 0)
  simp only [Matrix.mul_one] at hh
  rw [hh, scale_norm]
  by_cases hij : i = j
  · subst j
    norm_num [Matrix.one_apply]
  · simp [Matrix.one_apply, hij]

def code : Code 4 (fun _ => 2) (2 ^ 2) 1 where
  encoding := encoding
  isometry := encoding_isometry

def sitePauli (site : Fin 4) (p : SinglePauli) : Fin 4 → SinglePauli :=
  fun i => if i = site then p else .I

def weightTwoPauli : Fin 4 → SinglePauli := fun i => if i = 0 ∨ i = 1 then .Z else .I

def logicalZ : Operator (Fin 4) :=
  fun i j => if i = j then if i.val < 2 then 1 else -1 else 0

theorem sitePauli_compression (site : Fin 4) (p : SinglePauli) :
    encoding.conjTranspose * pauliMatrix 0 (sitePauli site p) * encoding =
      if p = .I then 1 else 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  rw [encoding_compression_entry, scale_norm]
  fin_cases site <;> cases p <;> fin_cases i <;> fin_cases j <;>
    norm_num [sitePauli, pauliMatrix, word, complement, SinglePauli.matrix,
      Fin.prod_univ_succ, Matrix.one_apply]

theorem weightTwoPauli_compression :
    encoding.conjTranspose * pauliMatrix 0 weightTwoPauli * encoding =
      logicalZ ⊗ₖ (1 : Operator (Fin 1)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  rw [encoding_compression_entry, scale_norm]
  fin_cases i <;> fin_cases j <;>
    norm_num [weightTwoPauli, pauliMatrix, word, complement, SinglePauli.matrix,
      logicalZ, Matrix.kronecker_apply, Fin.prod_univ_succ]

theorem weightTwoPauli_supported :
    SupportedOn (pauliMatrix 0 weightTwoPauli) ({0, 1} : Finset (Fin 4)) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  simp [weightTwoPauli, hi.1, hi.2]

theorem weightTwoPauli_nongauge : ¬ GaugeOnly code (pauliMatrix 0 weightTwoPauli) := by
  rintro ⟨M, hM⟩
  change encoding.conjTranspose * pauliMatrix 0 weightTwoPauli * encoding = _ at hM
  rw [weightTwoPauli_compression] at hM
  have h0 := congrArg (fun A : Operator (Fin 4 × Fin 1) => A (0, 0) (0, 0)) hM
  have h2 := congrArg (fun A : Operator (Fin 4 × Fin 1) => A (2, 0) (2, 0)) hM
  have hp : (1 : ℂ) = M 0 0 := by simpa [logicalZ, Matrix.kronecker_apply] using h0
  have hn : (-1 : ℂ) = M 0 0 := by simpa [logicalZ, Matrix.kronecker_apply] using h2
  have hh : (1 : ℂ) = -1 := hp.trans hn.symm
  norm_num at hh

/-- An actual supported, undetectable weight-two operator for this encoding. -/
theorem explicit_distance_witness :
    ∃ S : Finset (Fin 4), S.card = 2 ∧ ∃ O : Operator (QubitBasis 4),
      SupportedOn O S ∧ ¬ GaugeOnly code O := by
  exact ⟨{0, 1}, by decide, pauliMatrix 0 weightTwoPauli,
    weightTwoPauli_supported, weightTwoPauli_nongauge⟩

theorem sitePauli_gaugeOnly (site : Fin 4) (p : SinglePauli) :
    GaugeOnly code (pauliMatrix 0 (sitePauli site p)) := by
  refine ⟨if p = .I then 1 else 0, ?_⟩
  change encoding.conjTranspose * pauliMatrix 0 (sitePauli site p) * encoding = _
  rw [sitePauli_compression]
  by_cases hp : p = .I
  · simp [hp, Matrix.one_kronecker_one]
  · simp [hp]

theorem allIdentity_pauliMatrix : pauliMatrix (0 : Fin 4) (fun _ : Fin 4 => SinglePauli.I) = 1 := by
  rw [pauliMatrix_zero_eq_tensorEntries]
  exact tensorEntries_one

theorem detectsBelow_two : DetectsBelow code 2 := by
  classical
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin 4 => 2) S)) :=
    (gaugeOnlyComplexSubmodule code).comap (localEmbedLinearMap S)
  have hPauli : ∀ p : S → SinglePauli,
      GaugeOnly code (pauliMatrix 0 (extendLocalPauli S p)) := by
    intro p
    by_cases hempty : S = ∅
    · have hp : extendLocalPauli S p = fun _ => SinglePauli.I := by
        funext i
        simp [extendLocalPauli, hempty]
      rw [hp, allIdentity_pauliMatrix]
      refine ⟨1, ?_⟩
      simp [code, encoding_isometry, Matrix.one_kronecker_one]
    · have hcard : S.card = 1 := by
        have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      obtain ⟨site, hsite⟩ := Finset.card_eq_one.mp hcard
      have hsite_mem : site ∈ S := by rw [hsite]; simp
      let psite : SinglePauli := p ⟨site, hsite_mem⟩
      have hp : extendLocalPauli S p = sitePauli site psite := by
        funext i
        by_cases hi : i = site
        · subst i
          simp [extendLocalPauli, sitePauli, psite, hsite_mem]
        · have hiS : i ∉ S := by rw [hsite]; simpa using hi
          simp [extendLocalPauli, sitePauli, hi, hiS]
      rw [hp]
      exact sitePauli_gaugeOnly site psite
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly code (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    exact hPauli p
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly code (localEmbed S A) at hAB
  simpa only [hA] using hAB

theorem hasActualDistance_two : HasActualDistance code 2 :=
  ⟨detectsBelow_two, explicit_distance_witness⟩

end CriticalDepth.Manuscript.FourQubit
end -- explicit closure of the original file-level noncomputable section
end Merged_FourQubitExample

/- ===== Source block: PauliCompression; SHA-256 dd52f1f0f883ac61a674d3a37e5e33ce7b47a5f9b43a9b20a829b9446ab670e8 ===== -/
section Merged_PauliCompression
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
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliCompression

/- ===== Source block: CircuitPoints; SHA-256 d5235a2d3de9bae4fde1fde8fdfe0d76a1056fc538eb67724f2b0835c70961ca ===== -/
section Merged_CircuitPoints
/-!
# Actual complex circuits give points of the coordinate algebra

Local witnesses come from the supplied layer locality proofs. Their adjoints
provide inverse coordinates; no unembedded local inverse equation is needed.
The two encoded relations follow from the original encoded unitary action.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

variable {n ℓ g h q : ℕ} {dim : Fin n → ℕ}

def pointLocalGate (L : Fin h → Layer n dim q) (p : GateIndex n h) :
    Operator (LocalBasis dim (layoutSupport L p)) :=
  Classical.choose ((L p.1).locality p.2)

theorem pointLocalGate_embed (L : Fin h → Layer n dim q) (p : GateIndex n h) :
    localEmbed (layoutSupport L p) (pointLocalGate L p) = (L p.1).gate p.2 :=
  (Classical.choose_spec ((L p.1).locality p.2)).symm

def actualCircuitAssignment (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    CircuitVariable dim ℓ g h (layoutSupport L) → ℂ
  | .inl ⟨p, false, a, b⟩ => pointLocalGate L p a b
  | .inl ⟨p, true, a, b⟩ => (pointLocalGate L p).conjTranspose a b
  | .inr (.inl (false, a, b)) => W a b
  | .inr (.inl (true, a, b)) => W.conjTranspose a b
  | .inr (.inr (false, a, b)) => Z a b
  | .inr (.inr (true, a, b)) => Z.conjTranspose a b

def actualPolynomialPoint (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    CircuitPolynomial (dim := dim) (K := ℓ) (g := g) (layoutSupport L) →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (actualCircuitAssignment L W Z)

theorem point_localPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (localGatePolynomial (layoutSupport L) p false).map (actualPolynomialPoint L W Z) =
      pointLocalGate L p := by
  ext a b
  simp [localGatePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_localPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (localGatePolynomial (layoutSupport L) p true).map (actualPolynomialPoint L W Z) =
      (pointLocalGate L p).conjTranspose := by
  ext a b
  simp [localGatePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_physicalPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (physicalGatePolynomial (layoutSupport L) p false).map (actualPolynomialPoint L W Z) =
      (L p.1).gate p.2 := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality,
    point_localPolynomial_forward, coefficientEmbed_complex, pointLocalGate_embed]

theorem point_physicalPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (p : GateIndex n h) :
    (physicalGatePolynomial (layoutSupport L) p true).map (actualPolynomialPoint L W Z) =
      ((L p.1).gate p.2).conjTranspose := by
  rw [physicalGatePolynomial, coefficientEmbed_naturality,
    point_localPolynomial_inverse, coefficientEmbed_complex,
    localEmbed_conjTranspose, pointLocalGate_embed]

theorem point_logicalPolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (logicalPolynomial (layoutSupport L) false).map (actualPolynomialPoint L W Z) = W := by
  ext a b
  simp [logicalPolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_logicalPolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (logicalPolynomial (layoutSupport L) true).map (actualPolynomialPoint L W Z) =
      W.conjTranspose := by
  ext a b
  simp [logicalPolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_gaugePolynomial_forward (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (gaugePolynomial (layoutSupport L) false).map (actualPolynomialPoint L W Z) = Z := by
  ext a b
  simp [gaugePolynomial, actualPolynomialPoint, actualCircuitAssignment]

theorem point_gaugePolynomial_inverse (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (gaugePolynomial (layoutSupport L) true).map (actualPolynomialPoint L W Z) =
      Z.conjTranspose := by
  ext a b
  simp [gaugePolynomial, actualPolynomialPoint, actualCircuitAssignment]

private theorem point_map_executionGateIndices {α : Type*} (f : GateIndex n h → α) :
    (executionGateIndices (n := n) (h := h)).map f =
      (List.ofFn fun layer : Fin h => List.ofFn fun slot : Fin n => f (layer, slot)).flatten := by
  simp [executionGateIndices, List.map_flatten, List.map_ofFn, Function.comp_def]

private theorem point_reverse_prod_flatten {M : Type*} [Monoid M] (lists : List (List M)) :
    lists.flatten.reverse.prod = (lists.map fun xs => xs.reverse.prod).reverse.prod := by
  induction lists with
  | nil => simp
  | cons xs lists ih => simp [List.reverse_append, List.prod_append, ih]

theorem point_circuitEval_execution (L : Fin h → Layer n dim q) :
    circuitEval L = ((executionGateIndices (n := n) (h := h)).map
      (fun p => (L p.1).gate p.2)).reverse.prod := by
  rw [point_map_executionGateIndices, point_reverse_prod_flatten]
  simp only [circuitEval, Layer.eval, List.map_ofFn, Function.comp_def]

theorem point_totalPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (totalPolynomial (layoutSupport L)).map (actualPolynomialPoint L W Z) = circuitEval L := by
  unfold totalPolynomial
  rw [solutionMap_list_prod]
  simp only [List.map_reverse, List.map_map, Function.comp_def,
    point_physicalPolynomial_forward]
  exact (point_circuitEval_execution L).symm

private theorem point_conjTranspose_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Operator ι)) :
    matrices.prod.conjTranspose = (matrices.reverse.map Matrix.conjTranspose).prod := by
  induction matrices with
  | nil => simp
  | cons A matrices ih =>
      simp [Matrix.conjTranspose_mul, ih, List.reverse_cons, List.map_append, List.prod_append]

theorem point_inverseTotalPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) :
    (inverseTotalPolynomial (layoutSupport L)).map (actualPolynomialPoint L W Z) =
      (circuitEval L).conjTranspose := by
  unfold inverseTotalPolynomial
  rw [solutionMap_list_prod, point_circuitEval_execution, point_conjTranspose_list_prod]
  simp only [List.reverse_reverse, List.map_map, Function.comp_def,
    point_physicalPolynomial_inverse]

private theorem point_isUnitary_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Operator ι) (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A * B) := by
  constructor
  · calc
      star (A * B) * (A * B) = star B * (star A * A) * B := by
        simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hA.1, mul_one, hB.1]
  · calc
      (A * B) * star (A * B) = A * (B * star B) * star A := by
        simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB.2, mul_one, hA.2]

private theorem point_isUnitary_list_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (matrices : List (Operator ι)) (hunit : ∀ A ∈ matrices, IsUnitary A) :
    IsUnitary matrices.prod := by
  revert hunit
  induction matrices with
  | nil => intro hunit; constructor <;> simp
  | cons A matrices ih =>
      intro hunit
      exact point_isUnitary_mul A matrices.prod (hunit A (by simp))
        (ih (fun B hB => hunit B (by simp [hB])))

theorem point_circuitEval_isUnitary (L : Fin h → Layer n dim q) : IsUnitary (circuitEval L) := by
  rw [point_circuitEval_execution]
  apply point_isUnitary_list_prod
  intro U hU
  obtain ⟨p, _hp, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hU)
  exact (L p.1).unitary p.2

private theorem point_star_kronecker {ι κ : Type*}
    (W : Operator ι) (Z : Operator κ) : star (W ⊗ₖ Z) = star W ⊗ₖ star Z := by
  ext ⟨i, a⟩ ⟨j, b⟩
  change star (W j i * Z b a) = star (W j i) * star (Z b a)
  rw [star_mul]
  ring

theorem point_kronecker_isUnitary {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Operator ι) (Z : Operator κ) (hW : IsUnitary W) (hZ : IsUnitary Z) :
    IsUnitary (W ⊗ₖ Z) := by
  constructor
  · rw [point_star_kronecker, ← Matrix.mul_kronecker_mul, hW.1, hZ.1,
      Matrix.one_kronecker_one]
  · rw [point_star_kronecker, ← Matrix.mul_kronecker_mul, hW.2, hZ.2,
      Matrix.one_kronecker_one]

theorem point_encoded_dual (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    C.encoding.conjTranspose * circuitEval L = (W ⊗ₖ Z) * C.encoding.conjTranspose := by
  let U := circuitEval L
  let T := W ⊗ₖ Z
  have hU : IsUnitary U := point_circuitEval_isUnitary L
  have hT : IsUnitary T := point_kronecker_isUnitary W Z hW hZ
  have hadj : C.encoding.conjTranspose * star U = star T * C.encoding.conjTranspose := by
    change C.encoding.conjTranspose * (circuitEval L).conjTranspose =
      (W ⊗ₖ Z).conjTranspose * C.encoding.conjTranspose
    have heq := congrArg Matrix.conjTranspose hencoded
    simpa only [Matrix.conjTranspose_mul] using heq
  change C.encoding.conjTranspose * U = T * C.encoding.conjTranspose
  calc
    C.encoding.conjTranspose * U =
        ((T * star T) * C.encoding.conjTranspose) * U := by rw [hT.2]; simp
    _ = T * (star T * C.encoding.conjTranspose) * U := by
      simp only [Matrix.mul_assoc]
    _ = T * (C.encoding.conjTranspose * star U) * U := by rw [← hadj]
    _ = T * C.encoding.conjTranspose := by
      simp only [Matrix.mul_assoc, hU.1, Matrix.mul_one]

private theorem point_constantPolynomial (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g))
    {ι κ : Type*} (A : Matrix ι κ ℂ) :
    (A.map MvPolynomial.C).map (actualPolynomialPoint L W Z) = A := by
  ext i j
  simpa using (actualPolynomialPoint L W Z).commutes (A i j)

private theorem point_matrixRelation_vanish (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) {ι κ : Type*}
    (A B : Matrix ι κ (CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)))
    (heq : A.map (actualPolynomialPoint L W Z) = B.map (actualPolynomialPoint L W Z)) :
    ∀ f ∈ matrixRelationEntries (layoutSupport L) A B, actualPolynomialPoint L W Z f = 0 := by
  rintro f ⟨⟨i, j⟩, rfl⟩
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun M => M i j) heq)

private theorem point_inverseRelation_vanish (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι (CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)))
    (hinv : A.map (actualPolynomialPoint L W Z) * B.map (actualPolynomialPoint L W Z) = 1 ∧
      B.map (actualPolynomialPoint L W Z) * A.map (actualPolynomialPoint L W Z) = 1) :
    ∀ f ∈ inverseRelationEntries (layoutSupport L) A B,
      actualPolynomialPoint L W Z f = 0 := by
  intro f hf
  rcases hf with hf | hf
  · apply point_matrixRelation_vanish L W Z (A * B) 1 ?_ f hf
    simpa only [solutionMap_mul, solutionMap_one] using hinv.1
  · apply point_matrixRelation_vanish L W Z (B * A) 1 ?_ f hf
    simpa only [solutionMap_mul, solutionMap_one] using hinv.2

/-- Every generator of the defining ideal vanishes at the actual circuit
assignment. The dual relation is derived from the original unitary action. -/
theorem actualPolynomialPoint_relations
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    ∀ f ∈ circuitRelations (layoutSupport L) C, actualPolynomialPoint L W Z f = 0 := by
  intro f hf
  simp only [circuitRelations, Set.mem_union, Set.mem_iUnion] at hf
  rcases hf with (((hphysical | hlogical) | hgauge) | hencoding) | hdual
  · obtain ⟨p, hp⟩ := hphysical
    apply point_inverseRelation_vanish L W Z _ _ ?_ f hp
    rw [point_physicalPolynomial_forward, point_physicalPolynomial_inverse]
    exact ⟨((L p.1).unitary p.2).2, ((L p.1).unitary p.2).1⟩
  · apply point_inverseRelation_vanish L W Z _ _ ?_ f hlogical
    rw [point_logicalPolynomial_forward, point_logicalPolynomial_inverse]
    exact ⟨hW.2, hW.1⟩
  · apply point_inverseRelation_vanish L W Z _ _ ?_ f hgauge
    rw [point_gaugePolynomial_forward, point_gaugePolynomial_inverse]
    exact ⟨hZ.2, hZ.1⟩
  · apply point_matrixRelation_vanish L W Z _ _ ?_ f hencoding
    simpa only [solutionMap_mul, point_constantPolynomial, point_totalPolynomial,
      solutionMap_kronecker, point_logicalPolynomial_forward,
      point_gaugePolynomial_forward] using hencoded
  · apply point_matrixRelation_vanish L W Z _ _ ?_ f hdual
    simpa only [solutionMap_mul, point_constantPolynomial, point_totalPolynomial,
      solutionMap_kronecker, point_logicalPolynomial_forward,
      point_gaugePolynomial_forward] using point_encoded_dual C L W Z hW hZ hencoded

theorem actualPolynomialPoint_ideal
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    ∀ f, f ∈ circuitIdeal (layoutSupport L) C → actualPolynomialPoint L W Z f = 0 := by
  have hker : circuitIdeal (layoutSupport L) C ≤
      RingHom.ker (actualPolynomialPoint L W Z).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    change actualPolynomialPoint L W Z f = 0
    exact actualPolynomialPoint_relations C L W Z hW hZ hencoded f hf
  intro f hf
  exact hker hf

/-- The actual complex circuit, logical unitary, and gauge unitary give an
algebra-homomorphism point of the coordinate algebra. -/
def actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (circuitIdeal (layoutSupport L) C) (actualPolynomialPoint L W Z)
    (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)

@[simp] theorem actualCircuitPoint_quotient
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z))
    (f : CircuitPolynomial (K := ℓ) (g := g) (layoutSupport L)) :
    actualCircuitPoint C L W Z hW hZ hencoded
      (Ideal.Quotient.mk (circuitIdeal (layoutSupport L) C) f) = actualPolynomialPoint L W Z f := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (circuitIdeal (layoutSupport L) C)
      (actualPolynomialPoint L W Z) (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)) f

theorem circuitPointMap_actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    circuitPointMap C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) =
      actualPolynomialPoint L W Z := by
  exact Ideal.Quotient.liftₐ_comp (circuitIdeal (layoutSupport L) C)
    (actualPolynomialPoint L W Z) (actualPolynomialPoint_ideal C L W Z hW hZ hencoded)

theorem actualCircuitPoint_logical
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionLogical C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) false = W ∧
      solutionLogical C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) true =
        W.conjTranspose := by
  constructor
  · unfold solutionLogical
    rw [circuitPointMap_actualCircuitPoint]
    exact point_logicalPolynomial_forward L W Z
  · unfold solutionLogical
    rw [circuitPointMap_actualCircuitPoint]
    exact point_logicalPolynomial_inverse L W Z

theorem actualCircuitPoint_gauge
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionGauge C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) false = Z ∧
      solutionGauge C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) true =
        Z.conjTranspose := by
  constructor
  · unfold solutionGauge
    rw [circuitPointMap_actualCircuitPoint]
    exact point_gaugePolynomial_forward L W Z
  · unfold solutionGauge
    rw [circuitPointMap_actualCircuitPoint]
    exact point_gaugePolynomial_inverse L W Z

theorem actualCircuitPoint_total
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    solutionTotal C (layoutSupport L) (actualCircuitPoint C L W Z hW hZ hencoded) = circuitEval L := by
  unfold solutionTotal
  rw [circuitPointMap_actualCircuitPoint]
  exact point_totalPolynomial L W Z

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_CircuitPoints

/- ===== Source block: FourQubitStabilizer; SHA-256 2a2d0ee94e4f1788e7ca58e44c0e35771cc4948ff45650d4765cf56c6b8b21b5 ===== -/
section Merged_FourQubitStabilizer
/-!
# The four-element stabilizer of the four-qubit example

The actual subgroup is generated by XXXX and ZZZZ. The range of the explicit
encoding is identified with its simultaneous fixed space through the exact
projector VV† = (I + XXXX + ZZZZ + YYYY)/4.
-/

noncomputable section

namespace CriticalDepth.Manuscript.FourQubit

open Matrix
open scoped BigOperators

private theorem inv_of_involution {G : Type*} [Group G] (x : G) (hx : x * x = 1) :
    x⁻¹ = x := by
  calc
    x⁻¹ = x⁻¹ * (x * x) := by rw [hx, mul_one]
    _ = x := by simp [← mul_assoc]

private def kleinFourSubgroup {G : Type*} [Group G] (x z : G)
    (hx : x * x = 1) (hz : z * z = 1) (hc : x * z = z * x) : Subgroup G := by
  have hxxz : x * (x * z) = z := by rw [← mul_assoc, hx, one_mul]
  have hxzz : (x * z) * z = x := by rw [mul_assoc, hz, mul_one]
  have hxzx : (x * z) * x = z := by
    rw [mul_assoc, ← hc, ← mul_assoc, hx, one_mul]
  have hzxz : z * (x * z) = x := by
    rw [← mul_assoc, ← hc, mul_assoc, hz, mul_one]
  have hxzxz : (x * z) * (x * z) = 1 := by
    rw [← mul_assoc, hxzx, hz]
  exact
    { carrier := {u | u = 1 ∨ u = x ∨ u = z ∨ u = x * z}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl | rfl | rfl <;>
          rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hx, hz, ← hc, hxxz, hxzz, hxzx, hzxz, hxzxz]
      inv_mem' := by
        have hix := inv_of_involution x hx
        have hiz := inv_of_involution z hz
        have hixz := inv_of_involution (x * z) hxzxz
        intro a ha
        rcases ha with rfl | rfl | rfl | rfl <;>
          simp [hix, hiz, hixz, ← hc] }

private theorem mem_kleinFourSubgroup {G : Type*} [Group G] (x z u : G)
    (hx : x * x = 1) (hz : z * z = 1) (hc : x * z = z * x) :
    u ∈ kleinFourSubgroup x z hx hz hc ↔ u = 1 ∨ u = x ∨ u = z ∨ u = x * z := Iff.rfl

def allX : Operator (QubitBasis 4) := pauliMatrix 0 (fun _ => SinglePauli.X)
def allY : Operator (QubitBasis 4) := pauliMatrix 0 (fun _ => SinglePauli.Y)
def allZ : Operator (QubitBasis 4) := pauliMatrix 0 (fun _ => SinglePauli.Z)

theorem allX_sq : allX * allX = 1 := unphased_pauliMatrix_sq _
theorem allZ_sq : allZ * allZ = 1 := unphased_pauliMatrix_sq _

theorem allX_allZ : allX * allZ = allY := by
  have hlocal : SinglePauli.X.matrix * SinglePauli.Z.matrix =
      (-Complex.I) • SinglePauli.Y.matrix := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [SinglePauli.matrix, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]
  unfold allX allZ allY
  simp only [pauliMatrix_zero_eq_tensorEntries]
  rw [← tensorEntries_mul]
  simp only [hlocal]
  rw [tensorEntries_smul]
  have hphase : (∏ _i : Fin 4, (-Complex.I)) = 1 := by
    norm_num [Fin.prod_univ_succ, Complex.I_mul_I]
  rw [hphase, one_smul]

theorem allZ_allX : allZ * allX = allX * allZ := by
  have hh := unphased_pauliMatrix_commutation
    (fun _ : Fin 4 => SinglePauli.Z) (fun _ => SinglePauli.X)
  have hs : (∏ _i : Fin 4, SinglePauli.Z.commutationSign SinglePauli.X) = (1 : ℂ) := by
    norm_num [SinglePauli.commutationSign, Fin.prod_univ_succ]
  simpa only [allX, allZ, hs, one_smul] using hh

theorem encoding_rangeProjector_entry (x y : QubitBasis 4) :
    (encoding * encoding.conjTranspose) x y =
      (scale * star scale) *
        ∑ j : Fin 4,
          (dirac (word j) x + dirac (complement (word j)) x) *
            (dirac (word j) y + dirac (complement (word j)) y) := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, encoding,
    Matrix.conjTranspose_apply, star_mul, star_add, star_dirac]
  ring

private theorem vector4_eq_iff (a b c d e f g h : Fin 2) :
    (![a, b, c, d] : QubitBasis 4) = ![e, f, g, h] ↔
      a = e ∧ b = f ∧ c = g ∧ d = h := by
  constructor
  · intro heq
    exact ⟨congrFun heq 0, congrFun heq 1, congrFun heq 2, congrFun heq 3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

private theorem complement_vector4 (a b c d : Fin 2) :
    complement (![a, b, c, d] : QubitBasis 4) = ![1 - a, 1 - b, 1 - c, 1 - d] := by
  funext i
  fin_cases i <;> rfl

theorem encoding_rangeProjector :
    encoding * encoding.conjTranspose = (1 / 4 : ℂ) • (1 + allX + allZ + allY) := by
  classical
  ext x y
  rw [encoding_rangeProjector_entry]
  have hs : scale * star scale = (1 / 2 : ℂ) := by simpa only [mul_comm] using scale_norm
  rw [hs]
  have hx : x = ![x 0, x 1, x 2, x 3] := by
    funext i
    fin_cases i <;> rfl
  have hy : y = ![y 0, y 1, y 2, y 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx, hy]
  generalize hx0 : x 0 = a0
  generalize hx1 : x 1 = a1
  generalize hx2 : x 2 = a2
  generalize hx3 : x 3 = a3
  generalize hy0 : y 0 = b0
  generalize hy1 : y 1 = b1
  generalize hy2 : y 2 = b2
  generalize hy3 : y 3 = b3
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    norm_num [dirac, word, complement_vector4, vector4_eq_iff, allX, allY, allZ, pauliMatrix,
      SinglePauli.matrix, Matrix.one_apply, Fin.sum_univ_succ, Fin.prod_univ_succ]

theorem allX_encoding : allX * encoding = encoding := by
  let P : Operator (QubitBasis 4) := encoding * encoding.conjTranspose
  have hPV : P * encoding = encoding := by
    dsimp [P]
    rw [Matrix.mul_assoc, encoding_isometry, Matrix.mul_one]
  have hXY : allX * allY = allZ := by rw [← allX_allZ, ← mul_assoc, allX_sq, one_mul]
  have hXP : allX * P = P := by
    dsimp [P]
    rw [encoding_rangeProjector, mul_smul_comm]
    congr 1
    simp only [mul_add, mul_one, allX_sq, allX_allZ, hXY]
    abel
  calc
    allX * encoding = allX * (P * encoding) := by rw [hPV]
    _ = (allX * P) * encoding := by simp only [Matrix.mul_assoc]
    _ = encoding := by rw [hXP, hPV]

theorem allZ_encoding : allZ * encoding = encoding := by
  let P : Operator (QubitBasis 4) := encoding * encoding.conjTranspose
  have hPV : P * encoding = encoding := by
    dsimp [P]
    rw [Matrix.mul_assoc, encoding_isometry, Matrix.mul_one]
  have hZY : allZ * allY = allX := by
    rw [← allX_allZ, ← mul_assoc, allZ_allX, mul_assoc, allZ_sq, mul_one]
  have hZP : allZ * P = P := by
    dsimp [P]
    rw [encoding_rangeProjector, mul_smul_comm]
    congr 1
    simp only [mul_add, mul_one, allZ_sq, allZ_allX, allX_allZ, hZY]
    abel
  calc
    allZ * encoding = allZ * (P * encoding) := by rw [hPV]
    _ = (allZ * P) * encoding := by simp only [Matrix.mul_assoc]
    _ = encoding := by rw [hZP, hPV]

def xUnitary : Matrix.unitaryGroup (QubitBasis 4) ℂ :=
  ⟨allX, unphased_pauliMatrix_isUnitary _⟩

def zUnitary : Matrix.unitaryGroup (QubitBasis 4) ℂ :=
  ⟨allZ, unphased_pauliMatrix_isUnitary _⟩

theorem xUnitary_sq : xUnitary * xUnitary = 1 := by
  apply Subtype.ext
  exact allX_sq

theorem zUnitary_sq : zUnitary * zUnitary = 1 := by
  apply Subtype.ext
  exact allZ_sq

theorem xUnitary_commutes_zUnitary : xUnitary * zUnitary = zUnitary * xUnitary := by
  apply Subtype.ext
  exact allZ_allX.symm

def stabilizer : Subgroup (Matrix.unitaryGroup (QubitBasis 4) ℂ) :=
  kleinFourSubgroup xUnitary zUnitary xUnitary_sq zUnitary_sq xUnitary_commutes_zUnitary

theorem mem_stabilizer (U : Matrix.unitaryGroup (QubitBasis 4) ℂ) :
    U ∈ stabilizer ↔ U = 1 ∨ U = xUnitary ∨ U = zUnitary ∨ U = xUnitary * zUnitary :=
  mem_kleinFourSubgroup _ _ _ _ _ _

theorem stabilizer_pauli (U : Matrix.unitaryGroup (QubitBasis 4) ℂ) (hU : U ∈ stabilizer) :
    IsPauli (U : Operator (QubitBasis 4)) := by
  rcases (mem_stabilizer U).mp hU with rfl | rfl | rfl | rfl
  · exact ⟨0, fun _ => .I, allIdentity_pauliMatrix.symm⟩
  · exact ⟨0, fun _ => .X, rfl⟩
  · exact ⟨0, fun _ => .Z, rfl⟩
  · exact ⟨0, fun _ => .Y, allX_allZ⟩

theorem stabilizer_encoding (U : Matrix.unitaryGroup (QubitBasis 4) ℂ) (hU : U ∈ stabilizer) :
    (U : Operator (QubitBasis 4)) * encoding = encoding := by
  rcases (mem_stabilizer U).mp hU with rfl | rfl | rfl | rfl
  · exact Matrix.one_mul encoding
  · exact allX_encoding
  · exact allZ_encoding
  · change (allX * allZ) * encoding = encoding
    rw [Matrix.mul_assoc, allZ_encoding, allX_encoding]

theorem stabilizer_fixedSpace :
    Set.range (fun v => encoding.mulVec v) =
      {v | ∀ U ∈ stabilizer, (U : Operator (QubitBasis 4)).mulVec v = v} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩ U hU
    have hh := congrArg (fun A : Matrix (QubitBasis 4) (Fin 4 × Fin 1) ℂ => A.mulVec w)
      (stabilizer_encoding U hU)
    simpa only [Matrix.mulVec_mulVec] using hh
  · intro hfixed
    have hx : allX.mulVec v = v := hfixed xUnitary (by rw [mem_stabilizer]; simp)
    have hz : allZ.mulVec v = v := hfixed zUnitary (by rw [mem_stabilizer]; simp)
    have hy : allY.mulVec v = v := by
      rw [← allX_allZ, ← Matrix.mulVec_mulVec, hz, hx]
    have hPv : (encoding * encoding.conjTranspose).mulVec v = v := by
      rw [encoding_rangeProjector]
      simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hx, hz, hy]
      funext i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    refine ⟨encoding.conjTranspose.mulVec v, ?_⟩
    change encoding.mulVec (encoding.conjTranspose.mulVec v) = v
    rw [Matrix.mulVec_mulVec]
    exact hPv

/-- A fully explicit stabilizer-code instance, with no supplied witness premise. -/
theorem isStabilizer : IsStabilizer code := by
  exact ⟨stabilizer, stabilizer_pauli, stabilizer_fixedSpace⟩

theorem original_stabilizer_distance_hypotheses : IsStabilizer code ∧ HasActualDistance code 2 :=
  ⟨isStabilizer, hasActualDistance_two⟩

end CriticalDepth.Manuscript.FourQubit
end -- explicit closure of the original file-level noncomputable section
end Merged_FourQubitStabilizer

/- ===== Source block: InsertionDetection; SHA-256 424bc26c5b5ec827132b772f3203aaffe7f6cf9a331df95a45f85f84b2e72df4 ===== -/
section Merged_InsertionDetection
/-!
# Distance detection of the actual two-sided circuit insertions

Every term is obtained from the finite derivative expansion of the real gate
products. The short-cone hypothesis is a numerical bound to be discharged by
the manuscript depth inequality, rather than an assumed generator identity.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {F : Type*} [Field F] [Algebra ℂ F]
variable {n q ℓ g d : ℕ} {dim : Fin n → ℕ}

theorem fieldLayerSequenceEval_append
    (before after : List (FieldLayer (K := F) n dim q)) :
    fieldLayerSequenceEval (before ++ after) =
      fieldLayerSequenceEval after * fieldLayerSequenceEval before := by
  induction before with
  | nil => simp [fieldLayerSequenceEval]
  | cons L before ih =>
      simp only [List.cons_append, fieldLayerSequenceEval, ih, Matrix.mul_assoc]

theorem fieldLayerSequenceInv_append
    (before after : List (FieldLayer (K := F) n dim q)) :
    fieldLayerSequenceInv (before ++ after) =
      fieldLayerSequenceInv before * fieldLayerSequenceInv after := by
  induction before with
  | nil => simp [fieldLayerSequenceInv]
  | cons L before ih =>
      simp only [List.cons_append, fieldLayerSequenceInv, ih, Matrix.mul_assoc]

theorem layerGateInsertionAt_exists_split (D : Derivation ℂ F F)
    (layers : List (FieldLayer (K := F) n dim q))
    (r : Fin layers.length) (j : Fin n) :
    ∃ (before : List (FieldLayer (K := F) n dim q))
      (L : FieldLayer (K := F) n dim q)
      (after : List (FieldLayer (K := F) n dim q)),
      layers = before ++ L :: after ∧
      layerGateInsertionAt D layers r j =
        fieldLayerSequenceEval after *
          (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
            fieldLayerSequenceInv after := by
  revert r
  induction layers with
  | nil => intro r; exact Fin.elim0 r
  | cons L layers ih =>
      intro r
      refine Fin.cases ?_ (fun t => ?_) r
      · exact ⟨[], L, layers, rfl, rfl⟩
      · obtain ⟨before, M, after, heq, hins⟩ := ih t
        refine ⟨L :: before, M, after, ?_, ?_⟩
        · simpa only [List.cons_append] using congrArg (List.cons L) heq
        · exact hins

theorem blockInsertion_mem_gaugeOnly
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hq : 1 ≤ q)
    (D : Derivation ℂ F F)
    (before : List (FieldLayer (K := F) n dim q))
    (L : FieldLayer (K := F) n dim q)
    (after : List (FieldLayer (K := F) n dim q)) (j : Fin n)
    (W Wi : Matrix (Fin ℓ) (Fin ℓ) F) (Z Zi : Matrix (Fin g) (Fin g) F)
    (hW : W * Wi = 1 ∧ Wi * W = 1) (hZ : Z * Zi = 1 ∧ Zi * Z = 1)
    (hencoded : fieldLayerSequenceEval (before ++ L :: after) *
      C.encoding.map (algebraMap ℂ F) =
      C.encoding.map (algebraMap ℂ F) * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose.map (algebraMap ℂ F) *
      fieldLayerSequenceEval (before ++ L :: after) =
      (W ⊗ₖ Z) * C.encoding.conjTranspose.map (algebraMap ℂ F))
    (hshort : q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d) :
    fieldLayerSequenceEval after *
      (matrixDerivation D (L.gate j).1 * (L.gate j).2) *
        fieldLayerSequenceInv after ∈ gaugeOnlySubmodule (K := F) C := by
  let S := L.layout.support j
  let O := matrixDerivation D (L.gate j).1 * (L.gate j).2
  let H := fieldLayerSequenceEval after * O * fieldLayerSequenceInv after
  change H ∈ gaugeOnlySubmodule (K := F) C
  rcases hshort with hforward | hbackward
  · have hcard : (fieldLayerSequenceCone after S).card < d := by
      calc
        (fieldLayerSequenceCone after S).card ≤ q ^ after.length * S.card :=
          fieldLayerSequenceCone_card_le after S hq
        _ ≤ q ^ after.length * q := Nat.mul_le_mul_left _ (L.layout.arity j)
        _ = q ^ (after.length + 1) := (pow_succ q after.length).symm
        _ < d := hforward
    exact supportedSpan_le_gaugeOnlySubmodule C hDetect _ hcard
      (fieldLayerSequence_conjugate_mem after S (L.logarithmic_gate_mem D j))
  · have hcard : (fieldLayerSequenceBackwardCone before S).card < d := by
      calc
        (fieldLayerSequenceBackwardCone before S).card ≤ q ^ before.length * S.card :=
          fieldLayerSequenceBackwardCone_card_le before S hq
        _ ≤ q ^ before.length * q := Nat.mul_le_mul_left _ (L.layout.arity j)
        _ = q ^ (before.length + 1) := (pow_succ q before.length).symm
        _ < d := hbackward
    have hlocal : L.evalInv * O * L.eval ∈ supportedSpan (K := F) S :=
      L.backward_conjugated_logarithmic_gate_mem D j
    have hb : fieldLayerSequenceInv before * (L.evalInv * O * L.eval) *
        fieldLayerSequenceEval before ∈ gaugeOnlySubmodule (K := F) C :=
      supportedSpan_le_gaugeOnlySubmodule C hDetect _ hcard
        (fieldLayerSequence_inverse_conjugate_mem before S hlocal)
    obtain ⟨N, hN⟩ := hb
    let E := C.encoding.conjTranspose.map (algebraMap ℂ F)
    let V := C.encoding.map (algebraMap ℂ F)
    let U := fieldLayerSequenceEval (before ++ L :: after)
    let Ui := fieldLayerSequenceInv (before ++ L :: after)
    have ha := fieldLayerSequence_mutual_inverse after
    have hu := fieldLayerSequence_mutual_inverse (before ++ L :: after)
    have hframe : E * Ui * H * U * V = (1 : Matrix (Fin ℓ) (Fin ℓ) F) ⊗ₖ N := by
      calc
        E * Ui * H * U * V =
            E * (fieldLayerSequenceInv before * L.evalInv *
              (fieldLayerSequenceInv after * fieldLayerSequenceEval after) * O *
              (fieldLayerSequenceInv after * fieldLayerSequenceEval after) *
              L.eval * fieldLayerSequenceEval before) * V := by
          simp only [U, Ui, H, fieldLayerSequenceEval_append, fieldLayerSequenceInv_append,
            fieldLayerSequenceEval, fieldLayerSequenceInv, Matrix.mul_assoc]
        _ = E * fieldLayerSequenceInv before * (L.evalInv * O * L.eval) *
            fieldLayerSequenceEval before * V := by
          rw [ha.2]
          simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        _ = (1 : Matrix (Fin ℓ) (Fin ℓ) F) ⊗ₖ N := by
          simpa only [E, V, Matrix.mul_assoc] using hN
    refine ⟨Z * N * Zi, ?_⟩
    exact algebraic_gauge_frame_transfer E V U Ui H W Wi Z Zi N
      hu.1 hu.2 hW.1 hW.2 hZ.1 hZ.2 hencoded hdual hframe

theorem fieldLayerSequence_derivative_mem_gaugeOnly
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hq : 1 ≤ q)
    (D : Derivation ℂ F F) (layers : List (FieldLayer (K := F) n dim q))
    (W Wi : Matrix (Fin ℓ) (Fin ℓ) F) (Z Zi : Matrix (Fin g) (Fin g) F)
    (hW : W * Wi = 1 ∧ Wi * W = 1) (hZ : Z * Zi = 1 ∧ Zi * Z = 1)
    (hencoded : fieldLayerSequenceEval layers * C.encoding.map (algebraMap ℂ F) =
      C.encoding.map (algebraMap ℂ F) * (W ⊗ₖ Z))
    (hdual : C.encoding.conjTranspose.map (algebraMap ℂ F) * fieldLayerSequenceEval layers =
      (W ⊗ₖ Z) * C.encoding.conjTranspose.map (algebraMap ℂ F))
    (hshort : ∀ before L after, layers = before ++ L :: after →
      q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d) :
    matrixDerivation D (fieldLayerSequenceEval layers) * fieldLayerSequenceInv layers ∈
      gaugeOnlySubmodule (K := F) C := by
  rw [fieldLayerSequence_logarithmic_derivative_eq_sum]
  apply (gaugeOnlySubmodule (K := F) C).sum_mem
  intro r _
  apply (gaugeOnlySubmodule (K := F) C).sum_mem
  intro j _
  obtain ⟨before, L, after, heq, hins⟩ := layerGateInsertionAt_exists_split D layers r j
  rw [hins]
  apply blockInsertion_mem_gaugeOnly C hDetect hq D before L after j W Wi Z Zi hW hZ
  · simpa only [heq] using hencoded
  · simpa only [heq] using hdual
  · exact hshort before L after heq

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_InsertionDetection

/- ===== Source block: PauliSynthesis; SHA-256 5675ebc520314bcd222be3b69cd1f1cdd88925f4595e988a38f5c8b057f4a32a ===== -/
section Merged_PauliSynthesis
/-!
# Iterated compression and actual critical-depth Pauli-rotation circuits

All layers act on the same n physical qubits. The synthesis consists of
compression, one supported middle gate, and the reverse adjoint compression
sequence. List-to-circuit packing preserves the actual evaluated matrix.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix

variable {n q : ℕ} {dim : Fin n → ℕ}

def circuitOfLayers (layers : List (Layer n dim q)) : Circuit n dim q layers.length :=
  fun i => layers[i.val]

theorem circuitOfLayers_list (layers : List (Layer n dim q)) :
    List.ofFn (circuitOfLayers layers) = layers := by
  exact List.ofFn_getElem

theorem circuitOfLayers_eval (layers : List (Layer n dim q)) :
    circuitEval (circuitOfLayers layers) = layerSequenceEval layers := by
  have hm' : List.ofFn (fun i => (circuitOfLayers layers i).eval) =
      layers.map Layer.eval := by
    exact List.ofFn_getElem_eq_map layers Layer.eval
  unfold circuitEval
  rw [hm']
  exact (layerSequenceEval_eq_reverse_prod layers).symm

theorem circuitEval_cast {h h' : ℕ} (e : h = h') (c : Circuit n dim q h) :
    circuitEval (e ▸ c : Circuit n dim q h') = circuitEval c := by
  cases e
  rfl

theorem compressedWeight_shift (q w r : ℕ) :
    Arithmetic.compressedWeight q (Arithmetic.ceilDiv w q) r =
      Arithmetic.compressedWeight q w (r + 1) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Arithmetic.compressedWeight, ih]

/-- Iteration realizes the exact arithmetic support recurrence on the original register. -/
theorem pauli_compression_sequence (q : ℕ) (hq : 1 ≤ q)
    (p : Fin n → SinglePauli) (r : ℕ) :
    ∃ layers : List (Layer n (fun _ => 2) q), ∃ p' : Fin n → SinglePauli,
      layers.length = r ∧
      layerSequenceEval layers * pauliMatrix (0 : Fin 4) p * star (layerSequenceEval layers) =
        pauliMatrix (0 : Fin 4) p' ∧
      (pauliSupport p').card = Arithmetic.compressedWeight q (pauliSupport p).card r := by
  classical
  induction r generalizing p with
  | zero =>
      refine ⟨[], p, rfl, ?_, rfl⟩
      simp [layerSequenceEval]
  | succ r ih =>
      obtain ⟨p₁, L, hL, hwL⟩ := pauli_compression_layer q hq p
      obtain ⟨layers, p', hlen, hconj, hweight⟩ := ih p₁
      refine ⟨L :: layers, p', by simp [hlen], ?_, ?_⟩
      · calc
          layerSequenceEval (L :: layers) * pauliMatrix (0 : Fin 4) p *
              star (layerSequenceEval (L :: layers)) =
            layerSequenceEval layers *
              (L.eval * pauliMatrix (0 : Fin 4) p * star L.eval) *
                star (layerSequenceEval layers) := by
              simp only [layerSequenceEval, star_mul, mul_assoc]
          _ = pauliMatrix (0 : Fin 4) p' := by rw [hL, hconj]
      · calc
          (pauliSupport p').card = Arithmetic.compressedWeight q (pauliSupport p₁).card r := hweight
          _ = Arithmetic.compressedWeight q (Arithmetic.ceilDiv (pauliSupport p).card q) r := by
            rw [hwL]
          _ = Arithmetic.compressedWeight q (pauliSupport p).card (r + 1) :=
            compressedWeight_shift q (pauliSupport p).card r

theorem pauli_compression_to_arity (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) :
    ∃ layers : List (Layer n (fun _ => 2) q), ∃ p' : Fin n → SinglePauli,
      layers.length = Nat.clog q (pauliSupport p).card - 1 ∧
      layerSequenceEval layers * pauliMatrix (0 : Fin 4) p * star (layerSequenceEval layers) =
        pauliMatrix (0 : Fin 4) p' ∧
      (pauliSupport p').card ≤ q := by
  obtain ⟨layers, p', hlen, hconj, hweight⟩ :=
    pauli_compression_sequence q (by omega) p (Nat.clog q (pauliSupport p).card - 1)
  refine ⟨layers, p', hlen, hconj, ?_⟩
  rw [hweight]
  exact Arithmetic.compressedWeight_at_clog_pred_le q (pauliSupport p).card hq hd

theorem affine_uncompress {α : Type*} [Fintype α] [DecidableEq α]
    (C P Q : Operator α) (hC : IsUnitary C) (hconj : C * P * star C = Q)
    (a b : ℂ) : star C * affine Q a b * C = affine P a b := by
  have hback : star C * Q * C = P := by
    calc
      star C * Q * C = star C * (C * P * star C) * C := by rw [hconj]
      _ = (star C * C) * P * (star C * C) := by simp only [mul_assoc]
      _ = P := by rw [hC.1, one_mul, mul_one]
  calc
    star C * affine Q a b * C =
        a • (star C * C) + b • (star C * Q * C) := by
      simp only [affine, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one]
    _ = affine P a b := by rw [hC.1, hback]; rfl

/-- A supported unitary middle factor gives one actual compress/rotate/uncompute sequence. -/
theorem affine_synthesis_from_compression
    (layers : List (Layer n (fun _ => 2) q)) (p p' : Fin n → SinglePauli)
    (hn : 0 < n)
    (hconj : layerSequenceEval layers * pauliMatrix (0 : Fin 4) p *
      star (layerSequenceEval layers) = pauliMatrix (0 : Fin 4) p')
    (hweight : (pauliSupport p').card ≤ q) (a b : ℂ)
    (hmid : IsUnitary (affine (pauliMatrix (0 : Fin 4) p') a b)) :
    ∃ output : List (Layer n (fun _ => 2) q),
      output.length = 2 * layers.length + 1 ∧
      layerSequenceEval output = affine (pauliMatrix (0 : Fin 4) p) a b := by
  classical
  let S := pauliSupport p'
  let M := affine (pauliMatrix (0 : Fin 4) p') a b
  have hsupported : SupportedOn M S :=
    (pauliMatrix_supportedOn_pauliSupport p').affine a b
  let middle := singleGateLayer hn S M hweight hsupported hmid
  let output := layers ++ [middle] ++ layers.reverse.map Layer.adjoint
  refine ⟨output, ?_, ?_⟩
  · simp only [output, List.length_append, List.length_singleton, List.length_map,
      List.length_reverse]
    omega
  · calc
      layerSequenceEval output = star (layerSequenceEval layers) * M * layerSequenceEval layers := by
        have huncompute : layerSequenceEval (layers.map Layer.adjoint).reverse =
            star (layerSequenceEval layers) := by
          simpa only [List.map_reverse] using layerSequenceEval_reverse_adjoint layers
        simp [output, middle, layerSequenceEval_append, huncompute,
          layerSequenceEval, singleGateLayer_eval, mul_assoc]
      _ = affine (pauliMatrix (0 : Fin 4) p) a b :=
        affine_uncompress _ _ _ (layerSequenceEval_isUnitary layers) hconj a b

private theorem positive_sites_of_pauli_distance (p : Fin n → SinglePauli)
    (hd : 2 ≤ (pauliSupport p).card) : 0 < n := by
  have hcard : (pauliSupport p).card ≤ n := by
    calc
      (pauliSupport p).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- One compression works for every admissible affine middle gate at the critical depth. -/
theorem pauli_affine_synthesis_data (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) :
    ∃ p' : Fin n → SinglePauli, (pauliSupport p').card ≤ q ∧
      ∀ a b : ℂ, IsUnitary (affine (pauliMatrix (0 : Fin 4) p') a b) →
        ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
          circuitEval c = affine (pauliMatrix (0 : Fin 4) p) a b := by
  classical
  obtain ⟨layers, p', hlen, hconj, hweight⟩ := pauli_compression_to_arity q hq p hd
  refine ⟨p', hweight, ?_⟩
  intro a b hmid
  obtain ⟨output, houtlen, heval⟩ := affine_synthesis_from_compression layers p p'
    (positive_sites_of_pauli_distance p hd) hconj hweight a b hmid
  have hm : 0 < Nat.clog q (pauliSupport p).card :=
    Arithmetic.clog_pos_of_two_le q (pauliSupport p).card hq hd
  have hcritical : output.length = Arithmetic.criticalDepth q (pauliSupport p).card := by
    rw [houtlen, hlen]
    unfold Arithmetic.criticalDepth
    omega
  refine ⟨hcritical ▸ circuitOfLayers output, ?_⟩
  rw [circuitEval_cast, circuitOfLayers_eval]
  exact heval

/-- Every continuous Pauli rotation is realized by an actual critical-depth circuit. -/
theorem pauli_rotation_synthesis (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) (t : ℝ) :
    ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
      circuitEval c = rotation (pauliMatrix (0 : Fin 4) p) t := by
  obtain ⟨p', _hweight, hsynth⟩ := pauli_affine_synthesis_data q hq p hd
  have hmid := rotation_isUnitary (unphased_pauliMatrix_selfAdjoint p')
    (unphased_pauliMatrix_sq p') t
  simpa only [rotation] using hsynth (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ)) hmid

/-- The explicit projectively injective rational family has the same exact depth. -/
theorem pauli_rationalRotation_synthesis (q : ℕ) (hq : 2 ≤ q)
    (p : Fin n → SinglePauli) (hd : 2 ≤ (pauliSupport p).card) (r : ℕ) :
    ∃ c : Circuit n (fun _ => 2) q (Arithmetic.criticalDepth q (pauliSupport p).card),
      circuitEval c = rationalRotation (pauliMatrix (0 : Fin 4) p) r := by
  obtain ⟨p', _hweight, hsynth⟩ := pauli_affine_synthesis_data q hq p hd
  have hmid := rationalRotation_isUnitary (unphased_pauliMatrix_selfAdjoint p')
    (unphased_pauliMatrix_sq p') r
  simpa only [rationalRotation] using
    hsynth (rationalScale r) (rationalScale r * Complex.I * (r : ℂ)) hmid

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliSynthesis

/- ===== Source block: PhysicalCompressionExample; SHA-256 1e800478d45eef678be822bf126e0a3f3878e1c616749ba6f29e3ea07bc0e8ae ===== -/
section Merged_PhysicalCompressionExample
/-!
# Five-qubit physical compression and depth-three synthesis

The unphased string is X ⊗ Y ⊗ Z ⊗ I ⊗ I on the complete five-qubit
register. Its weight is three. Binary compression therefore needs one
parallel layer, followed by one two-site middle gate and one inverse layer.
The calls below produce actual circuits on the 32-dimensional register.

This is a physical circuit example. It does not supply a code-distance or
stabilizer-code hypothesis. The support statements concern the evaluated
operators; they do not add a claim about every intermediate gate.
-/

noncomputable section

namespace CriticalDepth.Manuscript.PhysicalCompressionExample

open Matrix

def p : Fin 5 → SinglePauli := ![.X, .Y, .Z, .I, .I]

def activeSites : Finset (Fin 5) := {0, 1, 2}

def P : Operator (QubitBasis 5) := pauliMatrix (0 : Fin 4) p

theorem register_dimension : Fintype.card (QubitBasis 5) = 32 := by
  decide

theorem pauli_support : pauliSupport p = activeSites := by
  decide

theorem weight_three : (pauliSupport p).card = 3 := by
  rw [pauli_support]
  decide

theorem critical_depth_three :
    Arithmetic.criticalDepth 2 (pauliSupport p).card = 3 := by
  rw [weight_three]
  decide

theorem pauli_supported : SupportedOn P activeSites := by
  simpa only [P, pauli_support] using pauliMatrix_supportedOn_pauliSupport p

/-- The example is a genuine non-scalar physical Pauli operator. -/
theorem pauli_nonscalar : ¬ IsScalar P := by
  let x : QubitBasis 5 := ![0, 0, 0, 0, 0]
  let y : QubitBasis 5 := ![1, 1, 0, 0, 0]
  have hxy : x ≠ y := by decide
  have hentry : P x y = -Complex.I := by
    norm_num [P, p, x, y, pauliMatrix, SinglePauli.matrix, Fin.prod_univ_succ]
  rintro ⟨z, hz⟩
  have hh := congrArg (fun A : Operator (QubitBasis 5) => A x y) hz
  have hzero : (-Complex.I : ℂ) = 0 := by
    simpa only [hentry, Matrix.smul_apply, Matrix.one_apply, if_neg hxy, smul_zero]
      using hh
  exact Complex.I_ne_zero (neg_eq_zero.mp hzero)

/-- A real two-ary layer compresses the weight from three to two. -/
theorem one_round_compression :
    ∃ p' : Fin 5 → SinglePauli, ∃ L : Layer 5 (fun _ => 2) 2,
      L.eval * P * star L.eval = pauliMatrix (0 : Fin 4) p' ∧
        (pauliSupport p').card = 2 := by
  obtain ⟨p', L, hconj, hweight⟩ := pauli_compression_layer 2 (by decide) p
  refine ⟨p', L, ?_, ?_⟩
  · simpa only [P] using hconj
  · have hceil : Arithmetic.ceilDiv 3 2 = 2 := by decide
    simpa only [weight_three, hceil] using hweight

/-- Every real parameter has an actual depth-three two-ary circuit. -/
theorem rotation_depth_three (t : ℝ) :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rotation P t := by
  have hd : 2 ≤ (pauliSupport p).card := by rw [weight_three]; decide
  obtain ⟨c, hc⟩ := pauli_rotation_synthesis 2 (by decide) p hd t
  refine ⟨(critical_depth_three ▸ c : Circuit 5 (fun _ => 2) 2 3), ?_⟩
  exact (circuitEval_cast (n := 5) (dim := fun _ => 2) (q := 2)
    critical_depth_three c).trans hc

theorem rotation_supported (t : ℝ) : SupportedOn (rotation P t) activeSites := by
  unfold rotation
  exact pauli_supported.affine _ _

/-- The concrete rational parameter two is synthesized at the same exact depth. -/
theorem rational_rotation_two_depth_three :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rationalRotation P 2 := by
  have hd : 2 ≤ (pauliSupport p).card := by rw [weight_three]; decide
  obtain ⟨c, hc⟩ := pauli_rationalRotation_synthesis 2 (by decide) p hd 2
  refine ⟨(critical_depth_three ▸ c : Circuit 5 (fun _ => 2) 2 3), ?_⟩
  exact (circuitEval_cast (n := 5) (dim := fun _ => 2) (q := 2)
    critical_depth_three c).trans hc

/-- This formula follows the actual normalization used by rationalRotation. -/
theorem rational_rotation_two_formula :
    rationalRotation P 2 =
      affine P ((Real.sqrt (5 : ℝ) : ℂ)⁻¹)
        (((Real.sqrt (5 : ℝ) : ℂ)⁻¹) * Complex.I * 2) := by
  norm_num [rationalRotation, rationalScale]

theorem rational_rotation_two_isUnitary : IsUnitary (rationalRotation P 2) := by
  exact rationalRotation_isUnitary (unphased_pauliMatrix_selfAdjoint p)
    (unphased_pauliMatrix_sq p) 2

theorem rational_rotation_two_supported :
    SupportedOn (rationalRotation P 2) activeSites := by
  unfold rationalRotation
  exact pauli_supported.affine _ _

/-- A synthesized circuit has the stated output support on the full register. -/
theorem supported_rational_circuit :
    ∃ c : Circuit 5 (fun _ => 2) 2 3,
      circuitEval c = rationalRotation P 2 ∧ SupportedOn (circuitEval c) activeSites := by
  obtain ⟨c, hc⟩ := rational_rotation_two_depth_three
  refine ⟨c, hc, ?_⟩
  rw [hc]
  exact rational_rotation_two_supported

#print CriticalDepth.Manuscript.PhysicalCompressionExample.one_round_compression
#print CriticalDepth.Manuscript.PhysicalCompressionExample.rotation_depth_three
#print CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.pauli_nonscalar
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.one_round_compression
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rotation_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_depth_three
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.rational_rotation_two_formula
#print axioms CriticalDepth.Manuscript.PhysicalCompressionExample.supported_rational_circuit

end CriticalDepth.Manuscript.PhysicalCompressionExample
end -- explicit closure of the original file-level noncomputable section
end Merged_PhysicalCompressionExample

/- ===== Source block: TheoremOne; SHA-256 9834ba1acbf60e5784c0e797e85ba0fba82865e821d535df4b6cbe0cfee25d8c ===== -/
section Merged_TheoremOne
/-!
# Finiteness for the declared bounded-depth circuit model

The proof derives the algebraic derivative identities from actual tensor
support, distance detection, inverse pairs, and the encoded action. It then
uses the Noetherian coordinate algebra and the faithful projective-coordinate
map. Only the finite support arrangements are enumerated; circuit matrices
themselves remain arbitrary.

The final proposition is the existing `Manuscript.theoremOne`, whose layers
have `Fin n` slots. The separate normalization from arbitrary finite gate
lists to this declared circuit model is not supplied by this module.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped BigOperators Kronecker

private theorem theoremOne_pow_mono (q a b : ℕ) (hq : 1 ≤ q) (hab : a ≤ b) :
    q ^ a ≤ q ^ b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hk : 1 ≤ q ^ k := by
    have hpos : 0 < q ^ k := pow_pos (by omega : 0 < q) k
    omega
  simpa only [mul_one] using Nat.mul_le_mul_left (q ^ a) hk

private theorem theoremOne_split_short (q d h before after : ℕ)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (hcounts : before + 1 + after = h) :
    q ^ (after + 1) < d ∨ q ^ (before + 1) < d := by
  by_cases hb : before + 1 ≤ Arithmetic.ceilHalf h
  · exact Or.inr ((theoremOne_pow_mono q _ _ hq hb).trans_lt hcone)
  · have ha : after + 1 ≤ Arithmetic.ceilHalf h := by
      unfold Arithmetic.ceilHalf at *
      omega
    exact Or.inl ((theoremOne_pow_mono q _ _ hq ha).trans_lt hcone)

variable {n ℓ g d q h : ℕ} {dim : Fin n → ℕ}

/-- The derivative premise of the algebraic finite-image theorem is proved
from the actual code, distance, layout, and numerical cone bound. -/
theorem circuitPoint_projective_derivation_zero
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (L : Fin h → Layer n dim q)
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := layoutSupport L) →ₐ[ℂ] 𝕂)
    (D : Derivation ℂ 𝕂 𝕂) :
    ∀ a b c e : Fin ℓ,
      D (solutionLogical C (layoutSupport L) ψ false a b *
        solutionLogical C (layoutSupport L) ψ true c e) = 0 := by
  letI : Nonempty (Fin g) := ⟨⟨0, by omega⟩⟩
  let layers := List.ofFn (solutionFieldLayer C L ψ)
  let W := solutionLogical C (layoutSupport L) ψ false
  let Wi := solutionLogical C (layoutSupport L) ψ true
  let Z := solutionGauge C (layoutSupport L) ψ false
  let Zi := solutionGauge C (layoutSupport L) ψ true
  let E := C.encoding.conjTranspose.map (algebraMap ℂ 𝕂)
  let V := C.encoding.map (algebraMap ℂ 𝕂)
  have hW : W * Wi = 1 ∧ Wi * W = 1 := solutionLogical_inverse C (layoutSupport L) ψ
  have hZ : Z * Zi = 1 ∧ Zi * Z = 1 := solutionGauge_inverse C (layoutSupport L) ψ
  have hencoded : fieldLayerSequenceEval layers * V = V * (W ⊗ₖ Z) := by
    simpa only [layers, V, W, Z, solutionTotal_eq_fieldLayerSequence] using
      solution_encoding C (layoutSupport L) ψ
  have hdual : E * fieldLayerSequenceEval layers = (W ⊗ₖ Z) * E := by
    simpa only [layers, E, W, Z, solutionTotal_eq_fieldLayerSequence] using
      solution_encoding_dual C (layoutSupport L) ψ
  have hshort : ∀ before M after, layers = before ++ M :: after →
      q ^ (after.length + 1) < d ∨ q ^ (before.length + 1) < d := by
    intro before M after heq
    have hlen := congrArg List.length heq
    simp only [layers, List.length_ofFn, List.length_append, List.length_cons] at hlen
    apply theoremOne_split_short q d h before.length after.length hq hcone
    omega
  have hcompression := fieldLayerSequence_derivative_mem_gaugeOnly
    C hDetect hq D layers W Wi Z Zi hW hZ hencoded hdual hshort
  obtain ⟨M, hM⟩ := hcompression
  have hEV : E * V = 1 := solution_encoding_isometry (𝕂 := 𝕂) C
  have hE : matrixDerivation D E = 0 := matrixDerivation_constant D _
  have hV : matrixDerivation D V = 0 := matrixDerivation_constant D _
  have hU := fieldLayerSequence_mutual_inverse layers
  exact encoded_projective_coordinates_derivation_zero D E V
    (fieldLayerSequenceEval layers) (fieldLayerSequenceInv layers) W Wi Z Zi M
    hEV hE hV hU.1 hU.2 hW.1 hW.2 hZ.1 hZ.2 hencoded hdual hM

abbrev LogicalCoordinateIndex (ℓ : ℕ) := (Fin ℓ × Fin ℓ) × (Fin ℓ × Fin ℓ)

/-- These are precisely the entries of conjugation when the inverse
logical coordinates are evaluated at the adjoint. -/
def circuitLogicalCoordinate (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n)) (i : LogicalCoordinateIndex ℓ) :
    CircuitCoordinateRing (C := C) (support := support) :=
  Ideal.Quotient.mk (circuitIdeal support C)
    (logicalPolynomial support false i.1.1 i.2.1 *
      logicalPolynomial support true i.2.2 i.1.2)

def circuitConjugationCoordinates (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n))
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂) :
    Matrix (Fin ℓ × Fin ℓ) (Fin ℓ × Fin ℓ) 𝕂 :=
  fun p r => ψ (circuitLogicalCoordinate C support (p, r))

theorem circuitConjugationCoordinates_apply (C : Code n dim ℓ g)
    (support : GateIndex n h → Finset (Fin n))
    {𝕂 : Type*} [Field 𝕂] [Algebra ℂ 𝕂]
    (ψ : CircuitCoordinateRing (C := C) (support := support) →ₐ[ℂ] 𝕂)
    (p r : Fin ℓ × Fin ℓ) :
    circuitConjugationCoordinates C support ψ p r =
      solutionLogical C support ψ false p.1 r.1 *
        solutionLogical C support ψ true r.2 p.2 := by
  change circuitPointMap C support ψ
      (logicalPolynomial support false p.1 r.1 * logicalPolynomial support true r.2 p.2) = _
  rw [map_mul]
  rfl

theorem circuitConjugationCoordinates_range_finite
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (L : Fin h → Layer n dim q) :
    (Set.range (circuitConjugationCoordinates (𝕂 := ℂ) C (layoutSupport L))).Finite := by
  let R := CircuitCoordinateRing (C := C) (support := layoutSupport L)
  let coords : LogicalCoordinateIndex ℓ → R := circuitLogicalCoordinate C (layoutSupport L)
  have hflat : (Set.range fun ψ : R →ₐ[ℂ] ℂ => fun i => ψ (coords i)).Finite := by
    apply evaluation_image_finite_of_all_field_derivations ℂ R coords
    intro 𝕂 _ _ ψ i D
    rcases i with ⟨⟨a, e⟩, ⟨b, c⟩⟩
    change D (circuitPointMap C (layoutSupport L) ψ
      (logicalPolynomial (layoutSupport L) false a b *
        logicalPolynomial (layoutSupport L) true c e)) = 0
    rw [map_mul]
    exact circuitPoint_projective_derivation_zero C hDetect hg hq hcone L ψ D a b c e
  let unflatten : (LogicalCoordinateIndex ℓ → ℂ) → Operator (Fin ℓ × Fin ℓ) :=
    fun f p r => f (p, r)
  apply (hflat.image unflatten).subset
  rintro A ⟨ψ, rfl⟩
  exact ⟨(fun i => ψ (coords i)), ⟨ψ, rfl⟩, rfl⟩

theorem circuitConjugationCoordinates_actualCircuitPoint
    (C : Code n dim ℓ g) (L : Fin h → Layer n dim q)
    (W : Operator (Fin ℓ)) (Z : Operator (Fin g)) (hW : IsUnitary W) (hZ : IsUnitary Z)
    (hencoded : circuitEval L * C.encoding = C.encoding * (W ⊗ₖ Z)) :
    circuitConjugationCoordinates C (layoutSupport L)
      (actualCircuitPoint C L W Z hW hZ hencoded) = conjugationCoordinates W := by
  ext p r
  rw [circuitConjugationCoordinates_apply,
    (actualCircuitPoint_logical C L W Z hW hZ hencoded).1,
    (actualCircuitPoint_logical C L W Z hW hZ hencoded).2]
  rfl

/-- Logical matrices realized by any circuit with one specified support
arrangement. Gate values are unrestricted. -/
def supportLogicalMatrices (C : Code n dim ℓ g) (q : ℕ)
    (support : GateIndex n h → Finset (Fin n)) : Set (Operator (Fin ℓ)) :=
  {W | ∃ L : Circuit n dim q h,
    layoutSupport L = support ∧ Implements C (circuitEval L) W}

theorem supportLogicalMatrices_projective_finite
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d)
    (support : GateIndex n h → Finset (Fin n)) :
    (projectiveClass '' supportLogicalMatrices C q support).Finite := by
  classical
  letI : Nonempty (Fin ℓ) := ⟨⟨0, by omega⟩⟩
  apply finite_projectiveImage_of_finite_conjugationCoordinates
    (supportLogicalMatrices C q support)
  · rintro W ⟨L, _hSupport, hImpl⟩
    exact hImpl.1
  · by_cases hreal : ∃ L : Circuit n dim q h, layoutSupport L = support
    · obtain ⟨L₀, rfl⟩ := hreal
      apply (circuitConjugationCoordinates_range_finite C hDetect hg hq hcone L₀).subset
      rintro A ⟨W, hW, rfl⟩
      obtain ⟨L, hSupport, hImpl⟩ := hW
      obtain ⟨hWU, Z, hZU, hencoded⟩ := hImpl
      rw [← hSupport]
      exact ⟨actualCircuitPoint C L W Z hWU hZU hencoded,
        circuitConjugationCoordinates_actualCircuitPoint C L W Z hWU hZU hencoded⟩
    · apply (Set.finite_empty : (∅ : Set (Operator (Fin ℓ × Fin ℓ))).Finite).subset
      rintro A ⟨W, ⟨L, hSupport, _hImpl⟩, _hA⟩
      exact False.elim (hreal ⟨L, hSupport⟩)

/-- Finiteness for every support arrangement under the numerical cone
criterion, including arbitrary finite unary depth. -/
theorem logicalImage_finite_of_cone
    (C : Code n dim ℓ g) (hDetect : DetectsBelow C d) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g)
    (hq : 1 ≤ q) (hcone : q ^ Arithmetic.ceilHalf h < d) :
    (logicalImage C q h).Finite := by
  classical
  have hEach : ∀ support : GateIndex n h → Finset (Fin n),
      (projectiveClass '' supportLogicalMatrices C q support).Finite :=
    supportLogicalMatrices_projective_finite C hDetect hℓ hg hq hcone
  have hUnion :
      (⋃ support : GateIndex n h → Finset (Fin n),
        projectiveClass '' supportLogicalMatrices C q support).Finite :=
    Set.finite_iUnion hEach
  apply hUnion.subset
  rintro a ⟨L, W, hImpl, rfl⟩
  apply Set.mem_iUnion.mpr
  exact ⟨layoutSupport L, W, ⟨L, rfl, hImpl⟩, rfl⟩

/-- The full proposition recorded as `Manuscript.theoremOne`, with its
original dimension, distance, depth, and arity guards. -/
theorem theoremOne_proved : theoremOne := by
  intro n ℓ g d dim _hn hℓ hg hd C hDetect q h hdepth
  rcases hdepth with ⟨hq, hh⟩ | hq
  · exact logicalImage_finite_of_cone C hDetect hℓ hg (by omega)
      ((Arithmetic.below_threshold_iff q d h hq).mp hh)
  · subst q
    exact logicalImage_finite_of_cone C hDetect hℓ hg (by decide)
      (Arithmetic.unary_cone_bound d h hd)

/-- Non-density of the same logical image in the actual projective
unitary quotient, with exactly the declared Theorem 1 hypotheses. -/
theorem theoremOne_nondense
    (n ℓ g d : ℕ) (dim : Fin n → ℕ) (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ)
    (hg : 1 ≤ g) (hd : 2 ≤ d) (C : Code n dim ℓ g) (hDetect : DetectsBelow C d)
    (q h : ℕ) (hdepth : (2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' logicalImage C q h) :=
  logicalImage_not_dense_in_projectiveUnitary C hℓ
    (theoremOne_proved n ℓ g d dim hn hℓ hg hd C hDetect q h hdepth)

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_TheoremOne

/- ===== Source block: TheoremTwoReduction; SHA-256 dc8e711bfb8e7322809f20ea1562e3ac64e1d67eb0c70470ce59e7a0f5405516 ===== -/
section Merged_TheoremTwoReduction
/-!
# The stabilizer upper construction and the explicit reduction of Theorem 2

The continuous subgroup and infinite image are constructed from the original
stabilizer and actual-distance assumptions. The final equality is explicitly
conditional on `theoremOne`; this module does not present that premise as a
closed proof of the first manuscript theorem.
-/

noncomputable section

namespace CriticalDepth.Manuscript

open Matrix
open scoped Kronecker

variable {n ℓ g d k q : ℕ} {dim : Fin n → ℕ}

/-- The canonical subspace logical matrix has an exact identity gauge factor. -/
theorem stabilizer_exact_logicalPauli
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (p : Fin n → SinglePauli) (W : Operator (Fin (2 ^ k))),
      (pauliSupport p).card = d ∧
      pauliMatrix (0 : Fin 4) p * C.encoding =
        C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))) ∧
      star W = W ∧ W * W = 1 ∧ ¬ IsScalar W := by
  classical
  obtain ⟨p, hcard, hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  obtain ⟨S, hpauli, hspace⟩ := hstabilizer
  let P := pauliMatrix (0 : Fin 4) p
  have hcomm := pauli_commutes_stabilizer_of_nongauge C S hpauli hspace p hnongauge
  have hpreserve := code_preservation_of_stabilizer_commutation C S hspace P hcomm
  let W := subspaceLogicalMatrix C P
  have hself : star W = W :=
    subspaceLogicalMatrix_selfAdjoint C P (unphased_pauliMatrix_selfAdjoint p)
  have hsq : W * W = 1 :=
    subspaceLogicalMatrix_sq_of_preserving C P (unphased_pauliMatrix_sq p) hpreserve
  refine ⟨p, W, hcard, ?_, hself, hsq,
    subspaceLogicalMatrix_nonscalar_of_nongauge C P hnongauge⟩
  exact hpreserve.trans (congrArg (fun A => C.encoding * A)
    (subspaceCompression_eq_kronecker C P))

theorem affine_encoding_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (a b : ℂ) :
    affine P a b * C.encoding =
      C.encoding * (affine W a b ⊗ₖ (1 : Operator (Fin 1))) := by
  have htensor : affine W a b ⊗ₖ (1 : Operator (Fin 1)) =
      affine (W ⊗ₖ (1 : Operator (Fin 1))) a b := by
    simp only [affine, Matrix.add_kronecker, Matrix.smul_kronecker,
      Matrix.one_kronecker_one]
  calc
    affine P a b * C.encoding = a • C.encoding + b • (P * C.encoding) := by
      simp only [affine, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul]
    _ = C.encoding * affine (W ⊗ₖ (1 : Operator (Fin 1))) a b := by
      rw [hencoded]
      simp only [affine, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one]
    _ = C.encoding * (affine W a b ⊗ₖ (1 : Operator (Fin 1))) :=
      congrArg (fun A => C.encoding * A) htensor.symm

theorem implements_rotation_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (hself : star W = W) (hsq : W * W = 1) (t : ℝ) :
    Implements C (rotation P t) (rotation W t) := by
  refine ⟨rotation_isUnitary hself hsq t, 1, isUnitary_one, ?_⟩
  exact affine_encoding_subspace C P W hencoded (Real.cos t : ℂ)
    (Complex.I * (Real.sin t : ℂ))

theorem implements_rationalRotation_subspace (C : Code n dim ℓ 1)
    (P : Operator (PhysicalBasis n dim)) (W : Operator (Fin ℓ))
    (hencoded : P * C.encoding = C.encoding * (W ⊗ₖ (1 : Operator (Fin 1))))
    (hself : star W = W) (hsq : W * W = 1) (r : ℕ) :
    Implements C (rationalRotation P r) (rationalRotation W r) := by
  refine ⟨rationalRotation_isUnitary hself hsq r, 1, isUnitary_one, ?_⟩
  exact affine_encoding_subspace C P W hencoded (rationalScale r)
    (rationalScale r * Complex.I * (r : ℂ))

/-- Both upper-endpoint conclusions follow from the original stabilizer hypotheses. -/
theorem stabilizer_critical_logical_image (C : Code n (fun _ => 2) (2 ^ k) 1)
    (_hk : 1 ≤ k) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    (logicalImage C q (Arithmetic.criticalDepth q d)).Infinite ∧
      HasContinuousLogicalSubgroup C q (Arithmetic.criticalDepth q d) := by
  classical
  obtain ⟨p, W, hcard, hencoded, hself, hsq, hnonscalar⟩ :=
    stabilizer_exact_logicalPauli C hstabilizer hdistance
  have hpdist : 2 ≤ (pauliSupport p).card := by omega
  have hrational : ∀ r : ℕ,
      projectiveClass (rationalRotation W r) ∈
        logicalImage C q (Arithmetic.criticalDepth q d) := by
    intro r
    have hsynth := pauli_rationalRotation_synthesis q hq p hpdist r
    rw [hcard] at hsynth
    obtain ⟨c, hceval⟩ := hsynth
    refine ⟨c, rationalRotation W r, ?_, rfl⟩
    rw [hceval]
    exact implements_rationalRotation_subspace C _ W hencoded hself hsq r
  have hrotation : ∀ t : ℝ,
      projectiveClass (rotation W t) ∈ logicalImage C q (Arithmetic.criticalDepth q d) := by
    intro t
    have hsynth := pauli_rotation_synthesis q hq p hpdist t
    rw [hcard] at hsynth
    obtain ⟨c, hceval⟩ := hsynth
    refine ⟨c, rotation W t, ?_, rfl⟩
    rw [hceval]
    exact implements_rotation_subspace C _ W hencoded hself hsq t
  constructor
  · apply (rationalRotation_classes_infinite hnonscalar).mono
    rintro a ⟨r, rfl⟩
    exact hrational r
  · refine ⟨rotation W, continuous_rotation W, rotation_isUnitary hself hsq,
      rotation_zero W, rotation_add hsq, ?_, hrotation⟩
    exact ⟨Real.pi / 2, rotation_pi_div_two_not_projectivelyEquivalent_one hnonscalar⟩

theorem hInfinity_eq_of_finite_below_and_infinite_at
    (C : Code n dim ℓ g) (q H : ℕ)
    (hbelow : ∀ h : ℕ, h < H → (logicalImage C q h).Finite)
    (hat : (logicalImage C q H).Infinite) : hInfinity C q = (H : ℕ∞) := by
  unfold hInfinity
  apply le_antisymm
  · exact sInf_le ⟨H, rfl, hat⟩
  · apply le_sInf
    rintro r ⟨h, rfl, hinfinite⟩
    have hnat : H ≤ h := by
      by_contra hn
      have hlt : h < H := by omega
      exact hinfinite (hbelow h hlt)
    exact_mod_cast hnat

private theorem two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem sites_positive_of_actualDistance
    (C : Code n (fun _ => 2) (2 ^ k) 1) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨p, hcard, _hnongauge⟩ := actualDistance_exists_nongauge_unphasedPauli C hdistance
  have hsites : (pauliSupport p).card ≤ n := by
    calc
      (pauliSupport p).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Explicit conditional reduction: the sole remaining theorem premise is Theorem 1. -/
theorem theoremTwo_of_theoremOne (hT1 : theoremOne) : theoremTwo := by
  intro n k d q hk hd hq C hstabilizer hdistance
  obtain ⟨hinfinite, hcontinuous⟩ :=
    stabilizer_critical_logical_image C hk hd hq hstabilizer hdistance
  refine ⟨?_, hcontinuous⟩
  apply hInfinity_eq_of_finite_below_and_infinite_at C q (Arithmetic.criticalDepth q d) ?_ hinfinite
  intro h hh
  exact hT1 n (2 ^ k) 1 d (fun _ => 2)
    (sites_positive_of_actualDistance C hd hdistance) (two_le_two_pow k hk) (by decide) hd
    C hdistance.1 q h (Or.inl ⟨hq, hh⟩)

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_TheoremTwoReduction

/- ===== Source block: BudgetSemantics; SHA-256 bb5e3761dcbad8773a60b7801b249cb481c31bffbbeb3c8ec3886407d0990139 ===== -/
section Merged_BudgetSemantics
/-!
# The original common total-depth budget

The manuscript counts all circuits of depth at most h. The set below is the
finite union of the arbitrary-gate-list images at depths 0 through h. No
monotonicity of exact-depth images, identity-layer padding, or generated-group
closure is assumed.
-/

noncomputable section

namespace CriticalDepth.Manuscript

variable {n ℓ g d k q h : ℕ} {dim : Fin n → ℕ}

def arbitraryLogicalImageAtMost (C : Code n dim ℓ g) (q h : ℕ) :
    Set (ProjectiveOperator (Fin ℓ)) :=
  {a | ∃ r : ℕ, r ≤ h ∧ a ∈ arbitraryLogicalImage C q r}

theorem arbitraryLogicalImageAtMost_eq_iUnion (C : Code n dim ℓ g) (q h : ℕ) :
    arbitraryLogicalImageAtMost C q h =
      ⋃ r : Fin (h + 1), arbitraryLogicalImage C q r.val := by
  ext a
  constructor
  · rintro ⟨r, hr, ha⟩
    exact Set.mem_iUnion.mpr ⟨⟨r, Nat.lt_succ_of_le hr⟩, ha⟩
  · intro ha
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp ha
    exact ⟨r.val, Nat.le_of_lt_succ r.isLt, hr⟩

theorem arbitraryLogicalImage_subset_atMost (C : Code n dim ℓ g)
    (q r h : ℕ) (hr : r ≤ h) :
    arbitraryLogicalImage C q r ⊆ arbitraryLogicalImageAtMost C q h := by
  intro a ha
  exact ⟨r, hr, ha⟩

theorem logicalImage_subset_atMost (C : Code n dim ℓ g) (q r h : ℕ) (hr : r ≤ h) :
    logicalImage C q r ⊆ arbitraryLogicalImageAtMost C q h := by
  intro a ha
  exact ⟨r, hr, logicalImage_subset_arbitraryLogicalImage C ha⟩

theorem arbitraryLogicalImageAtMost_mono (C : Code n dim ℓ g) (q : ℕ)
    {h h' : ℕ} (hh : h ≤ h') :
    arbitraryLogicalImageAtMost C q h ⊆ arbitraryLogicalImageAtMost C q h' := by
  rintro a ⟨r, hr, ha⟩
  exact ⟨r, hr.trans hh, ha⟩

theorem arbitraryLogicalImageAtMost_finite_of_exact (C : Code n dim ℓ g) (q h : ℕ)
    (hexact : ∀ r : ℕ, r ≤ h → (arbitraryLogicalImage C q r).Finite) :
    (arbitraryLogicalImageAtMost C q h).Finite := by
  rw [arbitraryLogicalImageAtMost_eq_iUnion]
  apply Set.finite_iUnion
  intro r
  exact hexact r.val (Nat.le_of_lt_succ r.isLt)

/-- The finite common-budget image follows from actual exact-depth finiteness. -/
theorem arbitraryLogicalImageAtMost_finite_of_theoremOne (hT1 : theoremOne)
    (C : Code n dim ℓ g) (hn : 1 ≤ n) (hℓ : 2 ≤ ℓ) (hg : 1 ≤ g) (hd : 2 ≤ d)
    (hdetect : DetectsBelow C d) (q h : ℕ)
    (hbudget : (2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) :
    (arbitraryLogicalImageAtMost C q h).Finite := by
  apply arbitraryLogicalImageAtMost_finite_of_exact C q h
  intro r hr
  have hrbudget : (2 ≤ q ∧ r < Arithmetic.criticalDepth q d) ∨ q = 1 := by
    rcases hbudget with ⟨hq, hh⟩ | hq
    · exact Or.inl ⟨hq, hr.trans_lt hh⟩
    · exact Or.inr hq
  have hfinite := hT1 n ℓ g d dim hn hℓ hg hd C hdetect q r hrbudget
  exact arbitraryLogicalImage_finite_of_logicalImage_finite C hℓ hg hfinite

theorem arbitraryLogicalImageAtMost_not_dense (C : Code n dim ℓ g) (q h : ℕ)
    (hℓ : 2 ≤ ℓ) (hfinite : (arbitraryLogicalImageAtMost C q h).Finite) :
    ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' arbitraryLogicalImageAtMost C q h) :=
  finite_projectiveImage_not_dense_in_projectiveUnitary ℓ hℓ _ hfinite

/-- Source Theorem 1 with its original total-depth budget and non-density conclusion. -/
def theoremOneAtMost : Prop :=
  ∀ (n ℓ g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ ℓ → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim ℓ g, DetectsBelow C d → ∀ q h : ℕ,
      ((2 ≤ q ∧ h < Arithmetic.criticalDepth q d) ∨ q = 1) →
      (arbitraryLogicalImageAtMost C q h).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹' arbitraryLogicalImageAtMost C q h)

theorem theoremOneAtMost_of_theoremOne (hT1 : theoremOne) : theoremOneAtMost := by
  intro n ℓ g d dim hn hℓ hg hd C hdetect q h hbudget
  have hfinite := arbitraryLogicalImageAtMost_finite_of_theoremOne hT1 C
    hn hℓ hg hd hdetect q h hbudget
  exact ⟨hfinite, arbitraryLogicalImageAtMost_not_dense C q h hℓ hfinite⟩

def hInfinityAtMost (C : Code n dim ℓ g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, r = (h : ℕ∞) ∧ (arbitraryLogicalImageAtMost C q h).Infinite}

def HasContinuousLogicalSubgroupAtMost (C : Code n (fun _ => 2) ℓ 1) (q h : ℕ) : Prop :=
  ∃ W : ℝ → Operator (Fin ℓ), Continuous W ∧
    (∀ t, IsUnitary (W t)) ∧ W 0 = 1 ∧
    (∀ s t, W (s + t) = W s * W t) ∧
    (∃ t, ¬ ProjectivelyEquivalent (W t) 1) ∧
    (∀ t, projectiveClass (W t) ∈ arbitraryLogicalImageAtMost C q h)

theorem HasContinuousLogicalSubgroup.atMost (C : Code n (fun _ => 2) ℓ 1)
    (q h : ℕ) (hexact : HasContinuousLogicalSubgroup C q h) :
    HasContinuousLogicalSubgroupAtMost C q h := by
  obtain ⟨W, hcont, hunit, hzero, hadd, hnontriv, hmem⟩ := hexact
  refine ⟨W, hcont, hunit, hzero, hadd, hnontriv, ?_⟩
  intro t
  exact logicalImage_subset_atMost C q h h (le_refl _) (hmem t)

theorem hInfinityAtMost_eq_of_finite_below_and_infinite_at
    (C : Code n dim ℓ g) (q H : ℕ)
    (hbelow : ∀ h : ℕ, h < H → (arbitraryLogicalImageAtMost C q h).Finite)
    (hat : (arbitraryLogicalImageAtMost C q H).Infinite) :
    hInfinityAtMost C q = (H : ℕ∞) := by
  unfold hInfinityAtMost
  apply le_antisymm
  · exact sInf_le ⟨H, rfl, hat⟩
  · apply le_sInf
    rintro r ⟨h, rfl, hinfinite⟩
    have hnat : H ≤ h := by
      by_contra hn
      have hlt : h < H := by omega
      exact hinfinite (hbelow h hlt)
    exact_mod_cast hnat

private theorem budget_two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem budget_sites_positive (C : Code n dim ℓ g) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨S, hS, _O, _hO, _hnon⟩ := hdistance.2
  have hsites : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Source Theorem 2 with the original at-most-depth definition of the critical depth. -/
def theoremTwoAtMost : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityAtMost C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
        HasContinuousLogicalSubgroupAtMost C q (Arithmetic.criticalDepth q d)

/-- Explicit conditional reduction; root must supply an actual Theorem 1 proof. -/
theorem theoremTwoAtMost_of_theoremOne (hT1 : theoremOne) : theoremTwoAtMost := by
  intro n k d q hk hd hq C hstabilizer hdistance
  obtain ⟨hinfinite, hcontinuous⟩ :=
    stabilizer_critical_logical_image C hk hd hq hstabilizer hdistance
  have hatmost : (arbitraryLogicalImageAtMost C q (Arithmetic.criticalDepth q d)).Infinite :=
    hinfinite.mono (logicalImage_subset_atMost C q (Arithmetic.criticalDepth q d)
      (Arithmetic.criticalDepth q d) (le_refl _))
  refine ⟨?_, HasContinuousLogicalSubgroup.atMost C q _ hcontinuous⟩
  apply hInfinityAtMost_eq_of_finite_below_and_infinite_at C q
    (Arithmetic.criticalDepth q d) ?_ hatmost
  intro h hh
  exact arbitraryLogicalImageAtMost_finite_of_theoremOne hT1 C
    (budget_sites_positive C hd hdistance) (budget_two_le_two_pow k hk) (by decide) hd
    hdistance.1 q h (Or.inl ⟨hq, hh⟩)

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_BudgetSemantics

/- ===== Source block: MainResults; SHA-256 3201e51c5017435e3729ec240a3f824b84a8b1a59cee2dc6bd31e1c352968ea7 ===== -/
section Merged_MainResults
/-!
# Closed manuscript targets

These declarations discharge the named reductions with the actual Theorem 1
proof. The at-most-depth targets also include the arbitrary finite gate-list
normalization and the common total-depth budget used in the manuscript.

This source file is a candidate until its recorded Lean build and recursive
axiom audit succeed; the declaration names alone are not verification evidence.
-/

namespace CriticalDepth.Manuscript

theorem theoremTwo_proved : theoremTwo :=
  theoremTwo_of_theoremOne theoremOne_proved

theorem theoremOneAtMost_proved : theoremOneAtMost :=
  theoremOneAtMost_of_theoremOne theoremOne_proved

theorem theoremTwoAtMost_proved : theoremTwoAtMost :=
  theoremTwoAtMost_of_theoremOne theoremOne_proved

end CriticalDepth.Manuscript
end Merged_MainResults

/- ===== Source block: MainExamples; SHA-256 3ecf26531e4f80149b3ca9b0df4337132dc378c3cf29d554ae48b43142e53e37 ===== -/
section Merged_MainExamples
/-!
# Closed calls of the manuscript results for the explicit four-qubit code

Every code, stabilizer, and distance premise is supplied by the concrete
example. The only parameter below is the arbitrary finite unary depth budget.
These declarations are candidates until their recorded build and recursive
axiom audit succeed.
-/

namespace CriticalDepth.Manuscript.MainExamples

theorem fourQubit_binary_criticalDepth : Arithmetic.criticalDepth 2 2 = 1 := by
  have hm : Nat.clog 2 2 = 1 :=
    Arithmetic.clog_eq_one_of_distance_le_arity 2 2 (by decide) (by decide) (by decide)
  norm_num [Arithmetic.criticalDepth, hm]

/-- A direct call of the original at-most-depth finiteness and non-density result. -/
theorem fourQubit_binary_depthZero_finite_nondense :
    (arbitraryLogicalImageAtMost FourQubit.code 2 0).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 4) ⁻¹'
        arbitraryLogicalImageAtMost FourQubit.code 2 0) := by
  apply theoremOneAtMost_proved 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 2 0
  left
  constructor
  · decide
  · rw [fourQubit_binary_criticalDepth]
    decide

/-- Unary gates have a finite logical image at every finite total-depth budget. -/
theorem fourQubit_unary_budget_finite_nondense (h : ℕ) :
    (arbitraryLogicalImageAtMost FourQubit.code 1 h).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 4) ⁻¹'
        arbitraryLogicalImageAtMost FourQubit.code 1 h) := by
  exact theoremOneAtMost_proved 4 4 1 2 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.detectsBelow_two 1 h (Or.inr rfl)

/-- A direct call of Theorem 2 with its original common total-depth budget. -/
theorem fourQubit_binary_critical_subgroup :
    hInfinityAtMost FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 := by
  have hh := theoremTwoAtMost_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [fourQubit_binary_criticalDepth] using hh

/-- The corresponding exact-depth statement also calls the closed original target. -/
theorem fourQubit_binary_exactDepth_critical_subgroup :
    hInfinity FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroup FourQubit.code 2 1 := by
  have hh := theoremTwo_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [fourQubit_binary_criticalDepth] using hh

/-- The actual infinite image at budget one, obtained from the constructed family. -/
theorem fourQubit_binary_budgetOne_infinite :
    (arbitraryLogicalImageAtMost FourQubit.code 2 1).Infinite := by
  have hh := (stabilizer_critical_logical_image (k := 2) (d := 2) (q := 2) FourQubit.code
    (by decide) (by decide) (by decide)
    FourQubit.isStabilizer FourQubit.hasActualDistance_two).1
  rw [fourQubit_binary_criticalDepth] at hh
  exact hh.mono (logicalImage_subset_atMost FourQubit.code 2 1 1 (le_refl _))

end CriticalDepth.Manuscript.MainExamples
end Merged_MainExamples

/- ===== Source block: PositiveDepth; SHA-256 93d551ecaceae7ad662417d9f7a8f538e98907985cc00671e3d9763325a60bb6 ===== -/
section Merged_PositiveDepth
/-!
# Positive-depth critical onset for the current manuscript

The current manuscript minimizes over positive depth budgets. The stronger
nonnegative-budget results remain available in MainResults. Finiteness at
budget zero makes the two critical-depth definitions equal, including when
neither definition has a finite value.
-/

noncomputable section

namespace CriticalDepth.Manuscript

variable {n ℓ g d k q : ℕ} {dim : Fin n → ℕ}

/-- The current manuscript's minimum over integer depth budgets h ≥ 1. -/
def hInfinityPositiveAtMost (C : Code n dim ℓ g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, 1 ≤ h ∧ r = (h : ℕ∞) ∧
    (arbitraryLogicalImageAtMost C q h).Infinite}

/-- Excluding budget zero changes nothing when its logical image is finite. -/
theorem hInfinityPositiveAtMost_eq_hInfinityAtMost (C : Code n dim ℓ g) (q : ℕ)
    (hzero : (arbitraryLogicalImageAtMost C q 0).Finite) :
    hInfinityPositiveAtMost C q = hInfinityAtMost C q := by
  unfold hInfinityPositiveAtMost hInfinityAtMost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨h, _hpositive, hr, hinfinite⟩
    exact ⟨h, hr, hinfinite⟩
  · rintro ⟨h, hr, hinfinite⟩
    have hpositive : 1 ≤ h := by
      by_contra hn
      have hz : h = 0 := by omega
      subst h
      exact hinfinite hzero
    exact ⟨h, hpositive, hr, hinfinite⟩

/-- The current Theorem 1 restricts attention to h ≥ 1 and q ≥ 2. -/
def theoremOnePositive : Prop :=
  ∀ (n ℓ g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ ℓ → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim ℓ g, DetectsBelow C d → ∀ q h : ℕ,
      2 ≤ q → 1 ≤ h → h < Arithmetic.criticalDepth q d →
      (arbitraryLogicalImageAtMost C q h).Finite ∧
        ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹'
          arbitraryLogicalImageAtMost C q h)

/-- A direct restriction of the stronger closed common-budget theorem. -/
theorem theoremOnePositive_proved : theoremOnePositive := by
  intro n ℓ g d dim hn hℓ hg hd C hdetect q h hq _hpositive hbelow
  exact theoremOneAtMost_proved n ℓ g d dim hn hℓ hg hd C hdetect q h
    (Or.inl ⟨hq, hbelow⟩)

private theorem positiveDepth_sites_positive (C : Code n dim ℓ g) (hd : 2 ≤ d)
    (hdistance : HasActualDistance C d) : 1 ≤ n := by
  obtain ⟨S, hS, _O, _hO, _hnongauge⟩ := hdistance.2
  have hsites : S.card ≤ n := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

private theorem positiveDepth_two_le_two_pow (k : ℕ) (hk : 1 ≤ k) : 2 ≤ 2 ^ k := by
  cases k with
  | zero => omega
  | succ k =>
      have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) k
      rw [pow_succ]
      omega

private theorem positiveDepth_criticalDepth_positive (q d : ℕ)
    (hq : 2 ≤ q) (hd : 2 ≤ d) : 0 < Arithmetic.criticalDepth q d := by
  have hm : 0 < Nat.clog q d := Arithmetic.clog_pos_of_two_le q d hq hd
  unfold Arithmetic.criticalDepth
  omega

/-- Current Theorem 2 with its positive-depth definition of h∞. -/
def theoremTwoPositive : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityPositiveAtMost C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
          HasContinuousLogicalSubgroupAtMost C q (Arithmetic.criticalDepth q d)

/-- The updated critical-depth conclusion follows from the closed main results. -/
theorem theoremTwoPositive_proved : theoremTwoPositive := by
  intro n k d q hk hd hq C hstabilizer hdistance
  have hzero : (arbitraryLogicalImageAtMost C q 0).Finite :=
    (theoremOneAtMost_proved n (2 ^ k) 1 d (fun _ => 2)
      (positiveDepth_sites_positive C hd hdistance) (positiveDepth_two_le_two_pow k hk)
      (by decide) hd C hdistance.1 q 0
      (Or.inl ⟨hq, positiveDepth_criticalDepth_positive q d hq hd⟩)).1
  obtain ⟨hcritical, hcontinuous⟩ :=
    theoremTwoAtMost_proved n k d q hk hd hq C hstabilizer hdistance
  exact ⟨(hInfinityPositiveAtMost_eq_hInfinityAtMost C q hzero).trans hcritical,
    hcontinuous⟩

end CriticalDepth.Manuscript
end -- explicit closure of the original file-level noncomputable section
end Merged_PositiveDepth

/- ===== Source block: PositiveDepthExamples; SHA-256 747b764b835e1d9303ba1535b6159bfdfa5a21b9c8f27ad20411b6a600a96472 ===== -/
section Merged_PositiveDepthExamples
/-!
# Closed examples for the current manuscript's positive-depth minimum

The four-qubit declarations supply every code, stabilizer, and distance
premise from the concrete encoding. Their comparison of positive and
nonnegative minima uses its finite depth-zero budget image. The labeled
five-site application schema retains the code and detection hypotheses as
parameters.
-/

namespace CriticalDepth.Manuscript.PositiveDepthExamples

/-- A generic current-Theorem-1 application schema at a positive depth budget.
The encoding and its original distance-detection hypothesis are parameters;
this declaration does not construct a five-qubit code. -/
theorem fiveSite_distanceThree_positiveBudget_schema
    (C : Code 5 (fun _ => 2) 2 1) (hdetect : DetectsBelow C 3) :
    (arbitraryLogicalImageAtMost C 2 1).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 2) ⁻¹'
        arbitraryLogicalImageAtMost C 2 1) := by
  have hcritical : Arithmetic.criticalDepth 2 3 = 3 := by decide
  exact theoremOnePositive_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide) C hdetect 2 1
    (by decide) (by decide) (by rw [hcritical]; decide)

/-- A direct call of the current manuscript's positive-minimum Theorem 2. -/
theorem fourQubit_positive_critical_subgroup :
    hInfinityPositiveAtMost FourQubit.code 2 = 1 ∧
      HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 := by
  have hh := theoremTwoPositive_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two
  simpa [MainExamples.fourQubit_binary_criticalDepth] using hh

/-- The actual zero-budget image supplies the only premise of the minimum comparison. -/
theorem fourQubit_positive_eq_nonnegative :
    hInfinityPositiveAtMost FourQubit.code 2 = hInfinityAtMost FourQubit.code 2 := by
  exact hInfinityPositiveAtMost_eq_hInfinityAtMost FourQubit.code 2
    MainExamples.fourQubit_binary_depthZero_finite_nondense.1

theorem fourQubit_positive_minimum_one : hInfinityPositiveAtMost FourQubit.code 2 = 1 :=
  fourQubit_positive_critical_subgroup.1

theorem fourQubit_positive_continuous_subgroup :
    HasContinuousLogicalSubgroupAtMost FourQubit.code 2 1 :=
  fourQubit_positive_critical_subgroup.2

end CriticalDepth.Manuscript.PositiveDepthExamples
end Merged_PositiveDepthExamples

/- ===== Source block: IntegratedStatements; SHA-256 d5acc6db7bbc8602176a055979d77899dd558460273eb2bc6983864fff4b6b6b ===== -/
section Merged_IntegratedStatements
/-!
# Three-layer statement integration

Layer 1: the manuscript's finite-dimensional complex-coordinate objects.
Layer 2: explicit readable definitions and statements in this namespace.
Layer 3: proved bridges to the accepted project definitions and closing proofs.

This review wrapper imports the existing project development. Its body can also
be appended after those mathematical modules in a flattened single source file.
The wrapper alone does not flatten their auxiliary proofs or provide a generic
transport API from arbitrary Hilbert-space carriers. One global phase is used.
-/

noncomputable section

namespace CriticalDepth.ReviewIntegration

open Matrix
open scoped Kronecker

variable {n K g q h k : ℕ} {dim : Fin n → ℕ}

abbrev RegisterBasis (n : ℕ) (dim : Fin n → ℕ) := Manuscript.PhysicalBasis n dim
abbrev LocalBasis (dim : Fin n → ℕ) (S : Finset (Fin n)) := Manuscript.LocalBasis dim S
abbrev Code (n : ℕ) (dim : Fin n → ℕ) (K g : ℕ) := Manuscript.Code n dim K g

/-- The aliased Code contains an encoding matrix with exactly this isometry field. -/
theorem code_isometry (C : Code n dim K g) :
    C.encoding.conjTranspose * C.encoding = 1 := C.isometry

def localEmbed (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    Operator (RegisterBasis n dim) := by
  classical
  exact fun x y => if ∀ i, i ∉ S → x i = y i then
    A (fun i => x i.1) (fun i => y i.1) else 0

theorem localEmbed_eq (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    localEmbed S A = Manuscript.localEmbed S A := rfl

def SupportedOn (O : Operator (RegisterBasis n dim)) (S : Finset (Fin n)) : Prop :=
  ∃ A : Operator (LocalBasis dim S), O = localEmbed S A

theorem supportedOn_iff (O : Operator (RegisterBasis n dim)) (S : Finset (Fin n)) :
    SupportedOn O S ↔ Manuscript.SupportedOn O S := Iff.rfl

def GaugeOnly (C : Code n dim K g) (O : Operator (RegisterBasis n dim)) : Prop :=
  ∃ M : Operator (Fin g),
    C.encoding.conjTranspose * O * C.encoding = (1 : Operator (Fin K)) ⊗ₖ M

theorem gaugeOnly_iff (C : Code n dim K g) (O : Operator (RegisterBasis n dim)) :
    GaugeOnly C O ↔ Manuscript.GaugeOnly C O := Iff.rfl

/-- All supported operators are quantified over, without a Pauli or unitarity restriction. -/
def DetectsBelow (C : Code n dim K g) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card < d →
    ∀ O : Operator (RegisterBasis n dim), SupportedOn O S → GaugeOnly C O

theorem detectsBelow_iff (C : Code n dim K g) (d : ℕ) :
    DetectsBelow C d ↔ Manuscript.DetectsBelow C d := Iff.rfl

def HasActualDistance (C : Code n dim K g) (d : ℕ) : Prop :=
  DetectsBelow C d ∧ ∃ S : Finset (Fin n), S.card = d ∧
    ∃ O : Operator (RegisterBasis n dim), SupportedOn O S ∧ ¬ GaugeOnly C O

theorem hasActualDistance_iff (C : Code n dim K g) (d : ℕ) :
    HasActualDistance C d ↔ Manuscript.HasActualDistance C d := Iff.rfl

def Implements (C : Code n dim K g) (U : Operator (RegisterBasis n dim))
    (W : Operator (Fin K)) : Prop :=
  IsUnitary W ∧ ∃ Z : Operator (Fin g), IsUnitary Z ∧
    U * C.encoding = C.encoding * (W ⊗ₖ Z)

theorem implements_iff (C : Code n dim K g) (U : Operator (RegisterBasis n dim))
    (W : Operator (Fin K)) : Implements C U W ↔ Manuscript.Implements C U W := Iff.rfl

/-- A gate has support, matrix, arity, locality and unitarity fields. A layer
has an arbitrary finite gate list and its pairwise-disjointness field. -/
abbrev Gate (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) := Manuscript.ListGate n dim q
abbrev Layer (n : ℕ) (dim : Fin n → ℕ) (q : ℕ) := Manuscript.ArbitraryLayer n dim q
abbrev Circuit (n : ℕ) (dim : Fin n → ℕ) (q r : ℕ) := Fin r → Layer n dim q

theorem gate_conditions (G : Gate n dim q) :
    G.support.card ≤ q ∧ SupportedOn G.gate G.support ∧ IsUnitary G.gate :=
  ⟨G.arity, G.locality, G.unitary⟩

theorem layer_disjoint (L : Layer n dim q) :
    L.gates.Pairwise (fun G H => Disjoint G.support H.support) := L.disjoint

def layerEval (L : Layer n dim q) : Operator (RegisterBasis n dim) :=
  (L.gates.map Manuscript.ListGate.gate).reverse.prod

def circuitEval {r : ℕ} (c : Circuit n dim q r) : Operator (RegisterBasis n dim) :=
  (List.ofFn fun i => layerEval (c i)).reverse.prod

theorem circuitEval_eq {r : ℕ} (c : Circuit n dim q r) :
    circuitEval c = Manuscript.arbitraryCircuitEval c := rfl

def logicalImageExact (C : Code n dim K g) (q r : ℕ) : Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ c : Circuit n dim q r, ∃ W : Operator (Fin K),
    Implements C (circuitEval c) W ∧ projectiveClass W = a}

theorem logicalImageExact_eq (C : Code n dim K g) (q r : ℕ) :
    logicalImageExact C q r = Manuscript.arbitraryLogicalImage C q r := rfl

/-- One common budget, including exact depth zero. No generated-group closure is taken. -/
def logicalImageAtMost (C : Code n dim K g) (q h : ℕ) : Set (ProjectiveOperator (Fin K)) :=
  {a | ∃ r : ℕ, r ≤ h ∧ a ∈ logicalImageExact C q r}

theorem logicalImageAtMost_eq (C : Code n dim K g) (q h : ℕ) :
    logicalImageAtMost C q h = Manuscript.arbitraryLogicalImageAtMost C q h := rfl

/-- Actual PU(K), with its quotient topology, rather than an ambient matrix quotient. -/
abbrev PU (K : ℕ) := ProjectiveUnitary (Fin K)

def logicalImagePU (C : Code n dim K g) (q h : ℕ) : Set (PU K) :=
  projectiveUnitaryToOperator (Fin K) ⁻¹' logicalImageAtMost C q h

theorem logicalImageAtMost_subset_unitaryRange (C : Code n dim K g) (q h : ℕ) :
    logicalImageAtMost C q h ⊆ Set.range (projectiveUnitaryToOperator (Fin K)) := by
  rintro a ⟨r, _hr, c, W, hW, hclass⟩
  exact ⟨unitaryProjectiveClass ⟨W, hW.1⟩, hclass⟩

theorem logicalImagePU_image_eq (C : Code n dim K g) (q h : ℕ) :
    projectiveUnitaryToOperator (Fin K) '' logicalImagePU C q h =
      logicalImageAtMost C q h := by
  ext a
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · intro ha
    obtain ⟨u, hu⟩ := logicalImageAtMost_subset_unitaryRange C q h ha
    refine ⟨u, ?_, hu⟩
    change projectiveUnitaryToOperator (Fin K) u ∈ logicalImageAtMost C q h
    rw [hu]
    exact ha

theorem logicalImage_finite_iff (C : Code n dim K g) (q h : ℕ) :
    (logicalImagePU C q h).Finite ↔ (logicalImageAtMost C q h).Finite := by
  constructor
  · intro hf
    rw [← logicalImagePU_image_eq C q h]
    exact hf.image (projectiveUnitaryToOperator (Fin K))
  · intro hf
    exact finite_projectiveUnitary_preimage (logicalImageAtMost C q h) hf

theorem logicalImage_infinite_iff (C : Code n dim K g) (q h : ℕ) :
    (logicalImagePU C q h).Infinite ↔ (logicalImageAtMost C q h).Infinite :=
  not_congr (logicalImage_finite_iff C q h)

def hInfinityPositive (C : Code n dim K g) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, 1 ≤ h ∧ r = (h : ℕ∞) ∧ (logicalImagePU C q h).Infinite}

theorem hInfinityPositive_eq_original (C : Code n dim K g) (q : ℕ) :
    hInfinityPositive C q = Manuscript.hInfinityPositiveAtMost C q := by
  unfold hInfinityPositive Manuscript.hInfinityPositiveAtMost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨h, hp, hr, hi⟩
    exact ⟨h, hp, hr, (logicalImage_infinite_iff C q h).1 hi⟩
  · rintro ⟨h, hp, hr, hi⟩
    exact ⟨h, hp, hr, (logicalImage_infinite_iff C q h).2 hi⟩

def IsPauli (U : Operator (RegisterBasis n (fun _ => 2))) : Prop :=
  ∃ phase : Fin 4, ∃ p : Fin n → Manuscript.SinglePauli, U = Manuscript.pauliMatrix phase p

/-- The encoding range is the entire common +1 fixed space of the Pauli subgroup. -/
def IsStabilizer (C : Code n (fun _ => 2) (2 ^ k) 1) : Prop :=
  ∃ S : Subgroup (Matrix.unitaryGroup (RegisterBasis n (fun _ => 2)) ℂ),
    (∀ U ∈ S, IsPauli (U : Operator (RegisterBasis n (fun _ => 2)))) ∧
    Set.range (fun v => C.encoding.mulVec v) =
      {v | ∀ U ∈ S, (U : Operator (RegisterBasis n (fun _ => 2))).mulVec v = v}

theorem isStabilizer_iff (C : Code n (fun _ => 2) (2 ^ k) 1) :
    IsStabilizer C ↔ Manuscript.IsStabilizer C := Iff.rfl

/-- Continuous real-parameter unitary homomorphism, nontrivial modulo one phase,
with every value in the common-budget PU image. No U(1)-isomorphism is asserted. -/
def ContinuousLogicalSubgroup (C : Code n (fun _ => 2) K 1) (q h : ℕ) : Prop :=
  ∃ W : ℝ → Operator (Fin K), ∃ hW : ∀ t, IsUnitary (W t),
    Continuous W ∧ W 0 = 1 ∧ (∀ s t, W (s + t) = W s * W t) ∧
    (∃ t, ¬ ProjectivelyEquivalent (W t) 1) ∧
    (∀ t, unitaryProjectiveClass ⟨W t, hW t⟩ ∈ logicalImagePU C q h)

theorem continuousLogicalSubgroup_iff (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    ContinuousLogicalSubgroup C q h ↔ Manuscript.HasContinuousLogicalSubgroupAtMost C q h := by
  constructor
  · rintro ⟨W, hW, hc, hz, ha, hn, hm⟩
    exact ⟨W, hc, hW, hz, ha, hn, hm⟩
  · rintro ⟨W, hc, hW, hz, ha, hn, hm⟩
    exact ⟨W, hW, hc, hz, ha, hn, hm⟩

/-- Current manuscript Theorem 1, entirely in actual PU(K). -/
def TheoremOne : Prop :=
  ∀ (n K g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ K → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim K g, DetectsBelow C d → ∀ q h : ℕ,
      2 ≤ q → 1 ≤ h → h < Arithmetic.criticalDepth q d →
      (logicalImagePU C q h).Finite ∧ ¬ Dense (logicalImagePU C q h)

theorem theoremOne_iff_original : TheoremOne ↔ Manuscript.theoremOnePositive := by
  constructor
  · intro ht n K g d dim hn hK hg hd C hdetect q h hq hp hb
    obtain ⟨hf, hnd⟩ := ht n K g d dim hn hK hg hd C hdetect q h hq hp hb
    exact ⟨(logicalImage_finite_iff C q h).1 hf, hnd⟩
  · intro ht n K g d dim hn hK hg hd C hdetect q h hq hp hb
    obtain ⟨hf, hnd⟩ := ht n K g d dim hn hK hg hd C hdetect q h hq hp hb
    exact ⟨(logicalImage_finite_iff C q h).2 hf, hnd⟩

theorem theoremOne_proved : TheoremOne :=
  theoremOne_iff_original.mpr Manuscript.theoremOnePositive_proved

/-- Current manuscript Theorem 2: positive minimum and a continuous subgroup.
There is no assumed zero-budget finiteness or pointwise angle-minimality premise. -/
def TheoremTwo : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityPositive C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
          ContinuousLogicalSubgroup C q (Arithmetic.criticalDepth q d)

theorem theoremTwo_iff_original : TheoremTwo ↔ Manuscript.theoremTwoPositive := by
  constructor
  · intro ht n k d q hk hd hq C hs hdist
    obtain ⟨hm, hc⟩ := ht n k d q hk hd hq C hs hdist
    refine ⟨?_, (continuousLogicalSubgroup_iff C q _).1 hc⟩
    rw [← hInfinityPositive_eq_original C q]
    exact hm
  · intro ht n k d q hk hd hq C hs hdist
    obtain ⟨hm, hc⟩ := ht n k d q hk hd hq C hs hdist
    refine ⟨?_, (continuousLogicalSubgroup_iff C q _).2 hc⟩
    rw [hInfinityPositive_eq_original C q]
    exact hm

theorem theoremTwo_proved : TheoremTwo :=
  theoremTwo_iff_original.mpr Manuscript.theoremTwoPositive_proved

#print axioms CriticalDepth.ReviewIntegration.theoremOne_proved
#print axioms CriticalDepth.ReviewIntegration.theoremTwo_proved

end CriticalDepth.ReviewIntegration
end -- explicit closure of the original file-level noncomputable section
end Merged_IntegratedStatements

/- ===== Source block: LocalityBridges; SHA-256 a5a1f626e027b1e40619036a35664287fc43e84c1a909eee1e6c97170cce8150 ===== -/
section Merged_LocalityBridges
/-!
# Local unitary matrices and the full physical register

The existing support predicate embeds a local matrix with the identity on the
complement. A fixed complementary basis assignment shows that this embedding
is injective whenever the physical basis is nonempty. Consequently, requiring
the embedded matrix to be unitary is equivalent to requiring the local matrix
to be unitary. The code-based versions derive nonemptiness from the original
encoding assumptions rather than adding a hypothesis to either main theorem.
-/

noncomputable section

namespace CriticalDepth.Manuscript.ReviewBridges

open Matrix

variable {n K g q h : ℕ} {dim : Fin n → ℕ}

/-- Fill the complementary sites using one fixed physical basis assignment. -/
def fillLocalWith (S : Finset (Fin n)) (base : PhysicalBasis n dim)
    (x : LocalBasis dim S) : PhysicalBasis n dim := by
  classical
  exact fun i => if hi : i ∈ S then x ⟨i, hi⟩ else base i

theorem fillLocalWith_restrict (S : Finset (Fin n))
    (base : PhysicalBasis n dim) (x : LocalBasis dim S) :
    (fun i : S => fillLocalWith S base x i.val) = x := by
  classical
  funext i
  simp [fillLocalWith, i.property]

/-- Equal complementary assignments expose the original local matrix entry. -/
theorem localEmbed_apply_fill (S : Finset (Fin n))
    (base : PhysicalBasis n dim) (A : Operator (LocalBasis dim S))
    (x y : LocalBasis dim S) :
    localEmbed S A (fillLocalWith S base x) (fillLocalWith S base y) = A x y := by
  classical
  have houtside : ∀ i, i ∉ S →
      fillLocalWith S base x i = fillLocalWith S base y i := by
    intro i hi
    simp [fillLocalWith, hi]
  change (if ∀ i, i ∉ S → fillLocalWith S base x i = fillLocalWith S base y i then
      A (fun i : S => fillLocalWith S base x i.val)
        (fun i : S => fillLocalWith S base y i.val) else 0) = A x y
  rw [if_pos houtside, fillLocalWith_restrict, fillLocalWith_restrict]

theorem localEmbed_injective [Nonempty (PhysicalBasis n dim)]
    (S : Finset (Fin n)) :
    Function.Injective (localEmbed S :
      Operator (LocalBasis dim S) → Operator (PhysicalBasis n dim)) := by
  classical
  let base : PhysicalBasis n dim := Classical.choice inferInstance
  intro A B hAB
  ext x y
  have hentry := congrArg
    (fun M : Operator (PhysicalBasis n dim) =>
      M (fillLocalWith S base x) (fillLocalWith S base y)) hAB
  simpa only [localEmbed_apply_fill] using hentry

/-- Embedding a local unitary always gives a unitary on the full register. -/
theorem localEmbed_isUnitary (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) (hA : IsUnitary A) :
    IsUnitary (localEmbed S A) := by
  classical
  have hstar : localEmbed S (star A) = star (localEmbed S A) :=
    localEmbed_conjTranspose S A
  constructor
  · calc
      star (localEmbed S A) * localEmbed S A = localEmbed S (star A * A) := by
        rw [localEmbed_mul, hstar]
      _ = localEmbed S 1 := congrArg (localEmbed S) hA.1
      _ = 1 := localEmbed_one S
  · calc
      localEmbed S A * star (localEmbed S A) = localEmbed S (A * star A) := by
        rw [localEmbed_mul, hstar]
      _ = localEmbed S 1 := congrArg (localEmbed S) hA.2
      _ = 1 := localEmbed_one S

theorem localEmbed_isUnitary_iff [Nonempty (PhysicalBasis n dim)]
    (S : Finset (Fin n)) (A : Operator (LocalBasis dim S)) :
    IsUnitary (localEmbed S A) ↔ IsUnitary A := by
  classical
  constructor
  · intro hU
    have hstar : localEmbed S (star A) = star (localEmbed S A) :=
      localEmbed_conjTranspose S A
    constructor
    · apply localEmbed_injective S
      rw [localEmbed_mul, hstar, localEmbed_one]
      exact hU.1
    · apply localEmbed_injective S
      rw [localEmbed_mul, hstar, localEmbed_one]
      exact hU.2
  · exact localEmbed_isUnitary S A

theorem localEmbed_injective_of_code (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) (S : Finset (Fin n)) :
    Function.Injective (localEmbed S :
      Operator (LocalBasis dim S) → Operator (PhysicalBasis n dim)) := by
  letI : Nonempty (PhysicalBasis n dim) := code_physicalBasis_nonempty C hK hg
  exact localEmbed_injective S

theorem localEmbed_isUnitary_iff_of_code (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) (S : Finset (Fin n))
    (A : Operator (LocalBasis dim S)) :
    IsUnitary (localEmbed S A) ↔ IsUnitary A := by
  letI : Nonempty (PhysicalBasis n dim) := code_physicalBasis_nonempty C hK hg
  exact localEmbed_isUnitary_iff S A

/-- The supported-unitary gate representation has exactly the local-unitary witnesses. -/
theorem supportedUnitary_iff_localUnitary [Nonempty (PhysicalBasis n dim)]
    (S : Finset (Fin n)) (U : Operator (PhysicalBasis n dim)) :
    (SupportedOn U S ∧ IsUnitary U) ↔
      ∃ A : Operator (LocalBasis dim S), IsUnitary A ∧ U = localEmbed S A := by
  classical
  constructor
  · rintro ⟨⟨A, hA⟩, hU⟩
    refine ⟨A, ?_, hA⟩
    apply (localEmbed_isUnitary_iff S A).mp
    rw [← hA]
    exact hU
  · rintro ⟨A, hA, rfl⟩
    exact ⟨⟨A, rfl⟩, localEmbed_isUnitary S A hA⟩

theorem supportedUnitary_iff_localUnitary_of_code (C : Code n dim K g)
    (hK : 2 ≤ K) (hg : 1 ≤ g) (S : Finset (Fin n))
    (U : Operator (PhysicalBasis n dim)) :
    (SupportedOn U S ∧ IsUnitary U) ↔
      ∃ A : Operator (LocalBasis dim S), IsUnitary A ∧ U = localEmbed S A := by
  letI : Nonempty (PhysicalBasis n dim) := code_physicalBasis_nonempty C hK hg
  exact supportedUnitary_iff_localUnitary S U

theorem arbitraryLayerEval_isUnitary (L : ArbitraryLayer n dim q) :
    IsUnitary L.eval := by
  classical
  unfold ArbitraryLayer.eval listGateEval
  apply matrixList_prod_isUnitary
  intro U hU
  have hU' : U ∈ L.gates.map ListGate.gate := by
    simpa only [List.mem_reverse] using hU
  obtain ⟨G, _hG, rfl⟩ := List.mem_map.mp hU'
  exact G.unitary

/-- Arbitrary finite gate lists evaluate to genuine physical unitary matrices. -/
theorem arbitraryCircuitEval_isUnitary (c : ArbitraryCircuit n dim q h) :
    IsUnitary (arbitraryCircuitEval c) := by
  classical
  unfold arbitraryCircuitEval
  apply matrixList_prod_isUnitary
  intro U hU
  have hU' : ∃ i, (c i).eval = U := by
    simpa only [List.mem_reverse, List.mem_ofFn] using hU
  obtain ⟨i, rfl⟩ := hU'
  exact arbitraryLayerEval_isUnitary (c i)

end CriticalDepth.Manuscript.ReviewBridges

end
end Merged_LocalityBridges

/- ===== Source block: SemanticBridges; SHA-256 0442b23226c17cfb1c32454881e7958759d2f34eea8236eace367b6b29cee5b4 ===== -/
section Merged_SemanticBridges
/-!
# Notational bridges for the semantic review

These lemmas connect the closure formulation of nondensity and unitary-valued
one-parameter families with the integrated statements. They make no generic
Hilbert-space transport or U(1)-isomorphism claim.
-/

noncomputable section

namespace CriticalDepth.ReviewIntegration.SemanticBridges

variable {n K g : ℕ} {dim : Fin n → ℕ}

/-- Mathlib's `dense_iff_closure_eq` is in Topology/Closure.lean, at the pinned revision. -/
theorem not_dense_iff_closure_ne_univ {X : Type*} [TopologicalSpace X] (S : Set X) :
    (¬ Dense S) ↔ closure S ≠ Set.univ :=
  not_congr (dense_iff_closure_eq (s := S))

/-- The same continuous real-parameter family, with its codomain explicitly
restricted to genuine unitaries carrying the matrix subtype topology. -/
def UnitaryValuedContinuousLogicalSubgroup
    (C : Code n (fun _ => 2) K 1) (q h : ℕ) : Prop :=
  ∃ F : ℝ → UnitaryOperator (Fin K), Continuous F ∧
    (F 0).val = 1 ∧
    (∀ s t, (F (s + t)).val = (F s).val * (F t).val) ∧
    (∃ t, ¬ ProjectivelyEquivalent (F t).val 1) ∧
    (∀ t, unitaryProjectiveClass (F t) ∈ logicalImagePU C q h)

theorem continuousLogicalSubgroup_iff_unitaryValued
    (C : Code n (fun _ => 2) K 1) (q h : ℕ) :
    ContinuousLogicalSubgroup C q h ↔ UnitaryValuedContinuousLogicalSubgroup C q h := by
  constructor
  · rintro ⟨W, hW, hc, hz, ha, hn, hm⟩
    exact ⟨fun t => ⟨W t, hW t⟩, hc.subtype_mk hW, hz, ha, hn, hm⟩
  · rintro ⟨F, hF, hz, ha, hn, hm⟩
    refine ⟨fun t => (F t).val, fun t => (F t).property,
      continuous_subtype_val.comp hF, hz, ha, hn, ?_⟩
    intro t
    simpa using hm t

/-- An undetectable operator cannot be supported on any smaller set. Actual
distance supplies exactly this detection property and such a witness. -/
theorem undetectable_support_card_ge (C : Code n dim K g) (d : ℕ)
    (hdetect : DetectsBelow C d) (O : Operator (RegisterBasis n dim))
    (hbad : ¬ GaugeOnly C O) (T : Finset (Fin n)) (hT : SupportedOn O T) :
    d ≤ T.card := by
  by_contra hcard
  have hsmall : T.card < d := by omega
  exact hbad (hdetect T hsmall O hT)

end CriticalDepth.ReviewIntegration.SemanticBridges

end
end Merged_SemanticBridges

/- ===== Source block: IntegrationCalls; SHA-256 4380f0ce5b498b22722de82e3cc2c486aeba4f1edd1314508746edbb28cda36b ===== -/
section Merged_IntegrationCalls
/-!
# Calls of the integrated statements

The five-site call retains the encoding and detection hypotheses as parameters;
it does not construct a five-qubit code. The four-qubit call supplies every
code, stabilizer and actual-distance premise from the explicit [[4,2,2]] code.
-/

namespace CriticalDepth.ReviewIntegration.Examples

/-- Current Theorem 1 at positive budget one, with its code hypotheses supplied
as parameters. This is a general application schema, not a five-qubit construction. -/
theorem fiveSite_distanceThree_positiveBudget_schema
    (C : Code 5 (fun _ => 2) 2 1) (hdetect : DetectsBelow C 3) :
    (logicalImagePU C 2 1).Finite ∧ ¬ Dense (logicalImagePU C 2 1) := by
  have hcritical : Arithmetic.criticalDepth 2 3 = 3 := by decide
  exact CriticalDepth.ReviewIntegration.theoremOne_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide) C hdetect 2 1
    (by decide) (by decide) (by rw [hcritical]; decide)

/-- Closed call of current Theorem 2 on the explicit [[4,2,2]] stabilizer code. -/
theorem fourQubit_positive_critical_subgroup :
    hInfinityPositive Manuscript.FourQubit.code 2 = 1 ∧
      ContinuousLogicalSubgroup Manuscript.FourQubit.code 2 1 := by
  have hh := CriticalDepth.ReviewIntegration.theoremTwo_proved 4 2 2 2
    (by decide) (by decide) (by decide)
    Manuscript.FourQubit.code Manuscript.FourQubit.isStabilizer
    Manuscript.FourQubit.hasActualDistance_two
  simpa [Manuscript.MainExamples.fourQubit_binary_criticalDepth] using hh

#print axioms CriticalDepth.ReviewIntegration.Examples.fiveSite_distanceThree_positiveBudget_schema
#print axioms CriticalDepth.ReviewIntegration.Examples.fourQubit_positive_critical_subgroup

end CriticalDepth.ReviewIntegration.Examples
end Merged_IntegrationCalls

/- ===== Source block: MathlibProjectiveUnitary; SHA-256 45e82a3c960434815c04913dd7b08de99101ec77149573a06ae6919303ea9b6d ===== -/
section Merged_MathlibProjectiveUnitary
/-!
The foundational carriers and their algebraic/topological structures in this
file are Mathlib's matrix unitary group and quotient group.  The only newly
specified subgroup is the scalar-phase subgroup of that existing group.

The old phase quotient occurs solely as the codomain of a proved bridge, so
the previously accepted finiteness and circuit arguments can be transported.
No group or topology is installed on an ad hoc foundational carrier.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

universe u

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

/-- Mathlib's unitary functor applied to the scalar star-algebra map. -/
def scalarPhaseHom : unitary ℂ →* Matrix.unitaryGroup ι ℂ :=
  (Unitary.map (StarMonoidHom.ofClass
    (StarAlgHom.ofId ℂ (Matrix ι ι ℂ)))).toMonoidHom

@[simp] theorem scalarPhaseHom_val (z : unitary ℂ) :
    ((scalarPhaseHom ι z : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      (z : ℂ) • (1 : Matrix ι ι ℂ) := by
  change algebraMap ℂ (Matrix ι ι ℂ) (z : ℂ) = _
  simp only [Algebra.algebraMap_eq_smul_one]

/-- The subgroup of scalar unitary matrices, using Mathlib's range operation. -/
def scalarPhaseSubgroup : Subgroup (Matrix.unitaryGroup ι ℂ) :=
  (scalarPhaseHom ι).range

theorem mem_scalarPhaseSubgroup_iff (U : Matrix.unitaryGroup ι ℂ) :
    U ∈ scalarPhaseSubgroup ι ↔
      ProjectivelyEquivalent (U : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ) := by
  change (∃ z : unitary ℂ, scalarPhaseHom ι z = U) ↔ _
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z : ℂ), z.property.1, scalarPhaseHom_val ι z⟩
  · rintro ⟨z, hz, hU⟩
    let w : unitary ℂ := ⟨z, hz, by simpa only [mul_comm] using hz⟩
    refine ⟨w, Subtype.ext ?_⟩
    exact (scalarPhaseHom_val ι w).trans hU.symm

theorem scalarPhaseSubgroup_le_center :
    scalarPhaseSubgroup ι ≤ Subgroup.center (Matrix.unitaryGroup ι ℂ) := by
  intro U hU
  rcases (mem_scalarPhaseSubgroup_iff ι U).mp hU with ⟨z, _, hU⟩
  rw [Subgroup.mem_center_iff]
  intro V
  apply Subtype.ext
  change (V : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ) =
    (U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)
  rw [hU]
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

instance scalarPhaseSubgroup_normal : (scalarPhaseSubgroup ι).Normal :=
  Subgroup.normal_of_le_center (scalarPhaseSubgroup_le_center ι)

/-- The genuine Mathlib quotient group, with its native quotient topology. -/
abbrev PU := Matrix.unitaryGroup ι ℂ ⧸ scalarPhaseSubgroup ι

/-- Mathlib's canonical quotient-group homomorphism. -/
def projectiveMk : Matrix.unitaryGroup ι ℂ →* PU ι :=
  QuotientGroup.mk' (scalarPhaseSubgroup ι)

theorem continuous_projectiveMk :
    Continuous (projectiveMk (ι := ι) : Matrix.unitaryGroup ι ℂ → PU ι) :=
  QuotientGroup.continuous_mk

/-- The native matrix-unitary membership predicate is exactly the old
two-sided inverse predicate; this is a definitional bridge. -/
theorem isUnitary_iff_mem_unitaryGroup (U : Matrix ι ι ℂ) :
    IsUnitary U ↔ U ∈ Matrix.unitaryGroup ι ℂ := Iff.rfl

theorem leftRel_iff_phase (U V : Matrix.unitaryGroup ι ℂ) :
    QuotientGroup.leftRel (scalarPhaseSubgroup ι) U V ↔
      ProjectivelyEquivalent (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  rw [QuotientGroup.leftRel_apply, mem_scalarPhaseSubgroup_iff]
  change ProjectivelyEquivalent
    (star (U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) 1 ↔ _
  constructor
  · rintro ⟨z, hz, hUV⟩
    apply projectivelyEquivalent_symm
    refine ⟨z, hz, ?_⟩
    calc
      (V : Matrix ι ι ℂ) =
          (U : Matrix ι ι ℂ) * (star (U : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)) := by
        rw [← mul_assoc, U.property.2, one_mul]
      _ = (U : Matrix ι ι ℂ) * (z • (1 : Matrix ι ι ℂ)) := by rw [hUV]
      _ = z • (U : Matrix ι ι ℂ) := by rw [mul_smul_comm, mul_one]
  · rintro ⟨z, hz, hUV⟩
    refine ⟨star z, by simpa only [star_star, mul_comm] using hz, ?_⟩
    rw [hUV]
    simp only [star_smul, smul_mul_assoc, V.property.1]

theorem projectiveMk_eq_iff (U V : Matrix.unitaryGroup ι ℂ) :
    projectiveMk (ι := ι) U = projectiveMk (ι := ι) V ↔
      ProjectivelyEquivalent (U : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) := by
  change ((U : PU ι) = (V : PU ι)) ↔ _
  rw [QuotientGroup.eq]
  simpa only [QuotientGroup.leftRel_apply] using leftRel_iff_phase ι U V

/-- The quotient relations agree under the identity on the definitionally
equal native and old unitary subtypes.  Mathlib transports the topology. -/
def puHomeomorphOld : PU ι ≃ₜ CriticalDepth.ProjectiveUnitary ι :=
  Homeomorph.Quotient.congrRight (leftRel_iff_phase ι)

@[simp] theorem puHomeomorphOld_mk (U : Matrix.unitaryGroup ι ℂ) :
    puHomeomorphOld ι (projectiveMk (ι := ι) U) =
      CriticalDepth.unitaryProjectiveClass U := rfl

theorem isClosed_scalarPhaseSubgroup [Nonempty ι] :
    IsClosed (scalarPhaseSubgroup ι : Set (Matrix.unitaryGroup ι ℂ)) := by
  have hset : (scalarPhaseSubgroup ι : Set (Matrix.unitaryGroup ι ℂ)) =
      {U : CriticalDepth.UnitaryOperator ι |
        ProjectivelyEquivalent U.val (1 : Matrix ι ι ℂ)} := by
    ext U
    exact mem_scalarPhaseSubgroup_iff ι U
  rw [hset]
  exact CriticalDepth.isClosed_unitary_phase_fiber
    (⟨1, by constructor <;> simp⟩ : CriticalDepth.UnitaryOperator ι)

/-- Hausdorffness is supplied by the native topological-group quotient
instances after the scalar subgroup's closedness has been proved. -/
instance puT2Space [Nonempty ι] : T2Space (PU ι) := by
  letI : IsClosed (scalarPhaseSubgroup ι : Set (Matrix.unitaryGroup ι ℂ)) :=
    isClosed_scalarPhaseSubgroup ι
  infer_instance

/-- A compatibility map into the old matrix-phase quotient; the new main
statements can take their images directly in the native quotient group. -/
def puToProjectiveOperator : PU ι → CriticalDepth.ProjectiveOperator ι :=
  CriticalDepth.projectiveUnitaryToOperator ι ∘ puHomeomorphOld ι

@[simp] theorem puToProjectiveOperator_mk (U : Matrix.unitaryGroup ι ℂ) :
    puToProjectiveOperator ι (projectiveMk (ι := ι) U) =
      CriticalDepth.projectiveClass (U : Matrix ι ι ℂ) := rfl

theorem puToProjectiveOperator_injective :
    Function.Injective (puToProjectiveOperator ι) :=
  CriticalDepth.projectiveUnitaryToOperator_injective.comp (puHomeomorphOld ι).injective

end CriticalDepth.ReviewV2
end -- explicit closure of the original file-level noncomputable section
end Merged_MathlibProjectiveUnitary

/- ===== Source block: PauliRowAction; SHA-256 b7fb37f35ff2d950ccff567a76525b796765e661c4e6ad9677dcf6dc4b9538d5 ===== -/
section Merged_PauliRowAction
/-!
# Sparse row action of a tensor Pauli matrix

Each row has exactly one potentially nonzero entry. The theorem below reduces
left multiplication of an arbitrary rectangular complex matrix to evaluation
at the flipped physical basis word. All physical tensor factors are retained.
In particular, the row coefficients of `Y` are `-I` at zero and `I` at one,
matching the actual matrix convention in `SinglePauli.matrix`.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.PauliRowAction

open Matrix CriticalDepth.Manuscript
open scoped BigOperators

def singleFlip (p : SinglePauli) (x : Fin 2) : Fin 2 :=
  match p with
  | .I | .Z => x
  | .X | .Y => 1 - x

def singleCoefficient (p : SinglePauli) (x : Fin 2) : ℂ :=
  match p with
  | .I | .X => 1
  | .Y => if x = 0 then -Complex.I else Complex.I
  | .Z => if x = 0 then 1 else -1

def flipWord {n : ℕ} (p : Fin n → SinglePauli) (x : QubitBasis n) : QubitBasis n :=
  fun i => singleFlip (p i) (x i)

def rowCoefficient {n : ℕ} (p : Fin n → SinglePauli) (x : QubitBasis n) : ℂ :=
  ∏ i : Fin n, singleCoefficient (p i) (x i)

theorem singlePauli_row (p : SinglePauli) (x y : Fin 2) :
    p.matrix x y = if y = singleFlip p x then singleCoefficient p x else 0 := by
  cases p <;> fin_cases x <;> fin_cases y <;>
    norm_num [SinglePauli.matrix, singleFlip, singleCoefficient]

theorem pauliMatrix_row {n : ℕ} (p : Fin n → SinglePauli)
    (x y : QubitBasis n) :
    pauliMatrix 0 p x y = if y = flipWord p x then rowCoefficient p x else 0 := by
  classical
  unfold pauliMatrix
  simp only [Fin.val_zero, pow_zero, one_mul]
  by_cases h : y = flipWord p x
  · subst y
    simp [singlePauli_row, flipWord, rowCoefficient]
  · rw [if_neg h]
    have hex : ∃ i : Fin n, y i ≠ singleFlip (p i) (x i) := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [singlePauli_row, if_neg hi]

/-- A tensor Pauli acts on any rectangular matrix by a single row lookup.
No finite enumeration of physical matrix columns is needed by a caller. -/
theorem pauliMatrix_mul_apply {n : ℕ} {κ : Type*}
    (p : Fin n → SinglePauli) (F : Matrix (QubitBasis n) κ ℂ)
    (x : QubitBasis n) (j : κ) :
    (pauliMatrix 0 p * F) x j = rowCoefficient p x * F (flipWord p x) j := by
  classical
  simp only [Matrix.mul_apply, pauliMatrix_row, ite_mul, zero_mul]
  simp

#print axioms singlePauli_row
#print axioms pauliMatrix_row
#print axioms pauliMatrix_mul_apply

end CriticalDepth.ReviewV2.PauliRowAction
end -- explicit closure of the original file-level noncomputable section
end Merged_PauliRowAction

/- ===== Source block: RotationPeriods; SHA-256 ab9b527cbf1293d185b63200e7f9b3712ea5769db0c314106b898b970b268c27 ===== -/
section Merged_RotationPeriods
/-!
# Exponential and exact projective periods of an involution rotation

The exponential below is Mathlib's `NormedSpace.exp` on complex matrices.
The unitary-valued rotation uses Mathlib's `Matrix.unitaryGroup` directly.
The exact kernel statement is about equality modulo one scalar phase; it is
stronger than merely exhibiting a nonconstant continuous real-parameter map.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix
open scoped Nat

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem involution_pow_even {P : Operator ι} (hP : P * P = 1) (k : ℕ) :
    P ^ (2 * k) = 1 := by
  rw [pow_mul, pow_two, hP, one_pow]

theorem involution_pow_odd {P : Operator ι} (hP : P * P = 1) (k : ℕ) :
    P ^ (2 * k + 1) = P := by
  rw [pow_succ, involution_pow_even hP, one_mul]

theorem imaginary_scalar_pow_even (t : ℝ) (k : ℕ) :
    (Complex.I * (t : ℂ)) ^ (2 * k) = (-1 : ℂ) ^ k * (t : ℂ) ^ (2 * k) := by
  have hI : Complex.I ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul, pow_two, Complex.I_mul_I]
  rw [mul_pow, hI]

theorem imaginary_scalar_pow_odd (t : ℝ) (k : ℕ) :
    (Complex.I * (t : ℂ)) ^ (2 * k + 1) =
      ((-1 : ℂ) ^ k * (t : ℂ) ^ (2 * k + 1)) * Complex.I := by
  rw [pow_succ, imaginary_scalar_pow_even, pow_succ]
  ring

/-- The even and odd power series give the actual Mathlib matrix exponential. -/
theorem exp_involution_eq_rotation {P : Operator ι} (hP : P * P = 1) (t : ℝ) :
    NormedSpace.exp ((Complex.I * (t : ℂ)) • P) = rotation P t := by
  let Q : Operator ι := (Complex.I * (t : ℂ)) • P
  have hc : HasSum (fun k : ℕ =>
      ((-1 : ℂ) ^ k * (t : ℂ) ^ (2 * k) / ((2 * k)! : ℂ)))
      (Real.cos t : ℂ) := by
    simpa only [Complex.ofReal_cos] using Complex.hasSum_cos (t : ℂ)
  have hs : HasSum (fun k : ℕ =>
      ((-1 : ℂ) ^ k * (t : ℂ) ^ (2 * k + 1) / ((2 * k + 1)! : ℂ)))
      (Real.sin t : ℂ) := by
    simpa only [Complex.ofReal_sin] using Complex.hasSum_sin (t : ℂ)
  have heven : HasSum (fun k : ℕ => ((2 * k)! : ℂ)⁻¹ • Q ^ (2 * k))
      ((Real.cos t : ℂ) • (1 : Operator ι)) := by
    convert hc.smul_const (1 : Operator ι) using 1
    funext k
    dsimp only [Q]
    rw [smul_pow, involution_pow_even hP, imaginary_scalar_pow_even, smul_smul]
    congr 1
    ring
  have hodd : HasSum (fun k : ℕ => ((2 * k + 1)! : ℂ)⁻¹ • Q ^ (2 * k + 1))
      ((Real.sin t : ℂ) • (Complex.I • P)) := by
    convert hs.smul_const (Complex.I • P) using 1
    funext k
    dsimp only [Q]
    rw [smul_pow, involution_pow_odd hP, imaginary_scalar_pow_odd,
      smul_smul, smul_smul]
    congr 1
    ring
  have hsum : HasSum (fun k : ℕ => (k ! : ℂ)⁻¹ • Q ^ k)
      ((Real.cos t : ℂ) • (1 : Operator ι) +
        (Real.sin t : ℂ) • (Complex.I • P)) :=
    HasSum.even_add_odd heven hodd
  have hsum' : HasSum (fun k : ℕ => (k ! : ℂ)⁻¹ • Q ^ k) (rotation P t) := by
    simpa only [rotation, affine, smul_smul, mul_comm (Real.sin t : ℂ) Complex.I]
      using hsum
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact hsum'.tsum_eq

theorem rotation_eq_exp_involution {P : Operator ι} (hP : P * P = 1) (t : ℝ) :
    rotation P t = NormedSpace.exp ((Complex.I * (t : ℂ)) • P) :=
  (exp_involution_eq_rotation hP t).symm

theorem rotation_projectivelyEquivalent_one_iff_sin_eq_zero
    {P : Operator ι} (hP : ¬ IsScalar P) (t : ℝ) :
    ProjectivelyEquivalent (rotation P t) 1 ↔ Real.sin t = 0 := by
  constructor
  · rintro ⟨z, _hz, hrotation⟩
    have haffine : affine P (Real.cos t : ℂ) (Complex.I * (Real.sin t : ℂ)) =
        affine P z 0 := by
      simpa only [rotation, affine, zero_smul, add_zero] using hrotation
    have hcoefficient := (affine_coefficients_unique hP haffine).2
    have hsin : (Real.sin t : ℂ) = 0 :=
      (mul_eq_zero.mp hcoefficient).resolve_left Complex.I_ne_zero
    exact_mod_cast hsin
  · intro hsin
    rcases Real.sin_eq_zero_iff_cos_eq.mp hsin with hcos | hcos
    · refine ⟨1, by simp, ?_⟩
      simp [rotation, affine, hsin, hcos]
    · refine ⟨-1, by simp, ?_⟩
      simp [rotation, affine, hsin, hcos]

/-- The projective kernel is exactly the integer multiples of pi. -/
theorem rotation_projectivelyEquivalent_one_iff
    {P : Operator ι} (hP : ¬ IsScalar P) (t : ℝ) :
    ProjectivelyEquivalent (rotation P t) 1 ↔
      ∃ k : ℤ, t = (k : ℝ) * Real.pi := by
  rw [rotation_projectivelyEquivalent_one_iff_sin_eq_zero hP]
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact Real.sin_int_mul_pi k

/-- These and only these real numbers are projective periods. -/
theorem rotation_projective_period_iff
    {P : Operator ι} (hP : P * P = 1) (hnonscalar : ¬ IsScalar P) (p : ℝ) :
    Function.Periodic (fun t : ℝ => projectiveClass (rotation P t)) p ↔
      ∃ k : ℤ, p = (k : ℝ) * Real.pi := by
  constructor
  · intro hperiod
    have heq : projectiveClass (rotation P p) = projectiveClass (1 : Operator ι) := by
      simpa only [zero_add, rotation_zero] using hperiod 0
    exact (rotation_projectivelyEquivalent_one_iff hnonscalar p).mp (Quotient.exact heq)
  · intro hp
    obtain ⟨z, hz, hrotation⟩ :=
      (rotation_projectivelyEquivalent_one_iff hnonscalar p).mpr hp
    intro t
    apply Quotient.sound
    refine ⟨z, hz, ?_⟩
    rw [rotation_add hP, hrotation, Matrix.mul_smul, Matrix.mul_one]

theorem rotation_projective_period_pi
    {P : Operator ι} (hP : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    Function.Periodic (fun t : ℝ => projectiveClass (rotation P t)) Real.pi :=
  (rotation_projective_period_iff hP hnonscalar Real.pi).mpr ⟨1, by simp⟩

/-- Mathlib's unitary group packages the already proved rotation matrix. -/
def unitaryRotation (P : Operator ι) (hself : star P = P) (hsq : P * P = 1)
    (t : ℝ) : Matrix.unitaryGroup ι ℂ :=
  ⟨rotation P t, rotation_isUnitary hself hsq t⟩

theorem continuous_unitaryRotation (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) :
    Continuous (unitaryRotation P hself hsq) :=
  (continuous_rotation P).subtype_mk _

end CriticalDepth.ReviewV2

end
end Merged_RotationPeriods

/- ===== Source block: CircleRotations; SHA-256 b537878716afc094d290fb6f4728601c24ff20e73e4ce65838a4a25ecac1f016 ===== -/
section Merged_CircleRotations
/-!
# A closed circle subgroup in Mathlib's projective unitary group

The domain is Mathlib's `Circle`, the ambient group is its native quotient
group `PU`, and the image is a Mathlib `MonoidHom.range` subgroup. No group
structure is reconstructed on the old matrix-phase quotient.

The representative `(z+1)/2 * I + (z-1)/2 * P` avoids choosing an argument or
a square root of `z`. At `z = Circle.exp (2*t)` it differs from `rotation P t`
by the scalar phase `Circle.exp t`. Its projective image is therefore exactly
the original real-parameter rotation image, not merely a containing subgroup.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem circle_star_mul_self (z : Circle) : star (z : ℂ) * (z : ℂ) = 1 := by
  change (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1
  simpa only [Circle.normSq_coe, Complex.ofReal_one] using
    (Complex.normSq_eq_conj_mul_self (z := (z : ℂ))).symm

def circleRotationMatrix (P : Operator ι) (z : Circle) : Operator ι :=
  affine P (((z : ℂ) + 1) / 2) (((z : ℂ) - 1) / 2)

theorem circleRotationMatrix_isUnitary {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (z : Circle) :
    IsUnitary (circleRotationMatrix P z) := by
  have ha : star (((z : ℂ) + 1) / 2) = (star (z : ℂ) + 1) / 2 := by simp
  have hb : star (((z : ℂ) - 1) / 2) = (star (z : ℂ) - 1) / 2 := by simp
  apply affine_isUnitary hself hsq
  · rw [ha, hb]
    linear_combination (1 / 2 : ℂ) * circle_star_mul_self z
  · rw [ha, hb]
    linear_combination (1 / 2 : ℂ) * circle_star_mul_self z

/-- A homomorphism into Mathlib's actual matrix unitary group. -/
def circleUnitaryHom (P : Operator ι) (hself : star P = P) (hsq : P * P = 1) :
    Circle →* Matrix.unitaryGroup ι ℂ where
  toFun z := ⟨circleRotationMatrix P z, circleRotationMatrix_isUnitary hself hsq z⟩
  map_one' := by
    apply Subtype.ext
    simp [circleRotationMatrix, affine]
  map_mul' z w := by
    apply Subtype.ext
    change circleRotationMatrix P (z * w) = circleRotationMatrix P z * circleRotationMatrix P w
    unfold circleRotationMatrix
    rw [affine_mul hsq]
    simp only [Circle.coe_mul]
    congr 1 <;> ring

def circleProjectiveHom (P : Operator ι) (hself : star P = P) (hsq : P * P = 1) :
    Circle →* PU ι :=
  (projectiveMk (ι := ι)).comp (circleUnitaryHom P hself hsq)

theorem continuous_circleUnitaryHom (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) :
    Continuous (circleUnitaryHom P hself hsq : Circle → Matrix.unitaryGroup ι ℂ) := by
  apply Continuous.subtype_mk
  change Continuous (circleRotationMatrix P)
  unfold circleRotationMatrix affine
  fun_prop

theorem continuous_circleProjectiveHom (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) :
    Continuous (circleProjectiveHom P hself hsq : Circle → PU ι) :=
  (continuous_projectiveMk (ι := ι)).comp (continuous_circleUnitaryHom P hself hsq)

theorem circleProjectiveHom_injective {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    Function.Injective (circleProjectiveHom P hself hsq) := by
  intro z w hzw
  have hphase : ProjectivelyEquivalent (circleRotationMatrix P z) (circleRotationMatrix P w) :=
    (projectiveMk_eq_iff (ι := ι) _ _).mp hzw
  obtain ⟨c, _hc, hmatrix⟩ := hphase
  have haffine : affine P (((z : ℂ) + 1) / 2) (((z : ℂ) - 1) / 2) =
      affine P (c * (((w : ℂ) + 1) / 2)) (c * (((w : ℂ) - 1) / 2)) := by
    simpa only [circleRotationMatrix, affine, smul_add, smul_smul] using hmatrix
  obtain ⟨hzero, hone⟩ := affine_coefficients_unique hnonscalar haffine
  have hc : c = 1 := by
    linear_combination -hzero + hone
  rw [hc] at hzero
  apply Circle.ext
  linear_combination (2 : ℂ) * hzero

theorem nonempty_of_nonscalar {P : Operator ι} (hnonscalar : ¬ IsScalar P) : Nonempty ι := by
  classical
  by_contra hn
  letI : IsEmpty ι := ⟨fun i => hn ⟨i⟩⟩
  apply hnonscalar
  exact ⟨0, Subsingleton.elim _ _⟩

/-- The subgroup is Mathlib's native range subgroup. -/
def circleRotationSubgroup (P : Operator ι) (hself : star P = P) (hsq : P * P = 1) :
    Subgroup (PU ι) :=
  (circleProjectiveHom P hself hsq).range

theorem isClosed_circleRotationSubgroup {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    IsClosed (circleRotationSubgroup P hself hsq : Set (PU ι)) := by
  letI : Nonempty ι := nonempty_of_nonscalar hnonscalar
  change IsClosed (Set.range (circleProjectiveHom P hself hsq))
  exact ((continuous_circleProjectiveHom P hself hsq).isClosedEmbedding
    (circleProjectiveHom_injective hself hsq hnonscalar)).isClosed_range

/-- A genuine topological group isomorphism with the standard unit circle. -/
def circleRotationEquiv {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    Circle ≃ₜ* circleRotationSubgroup P hself hsq := by
  letI : Nonempty ι := nonempty_of_nonscalar hnonscalar
  let e : Circle ≃* circleRotationSubgroup P hself hsq :=
    MonoidHom.ofInjective (circleProjectiveHom_injective hself hsq hnonscalar)
  have he : Continuous (e : Circle → circleRotationSubgroup P hself hsq) :=
    (continuous_circleProjectiveHom P hself hsq).subtype_mk _
  let home := e.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap
  exact { e with continuous_toFun := he, continuous_invFun := home.continuous_symm }

theorem circleRotationSubgroup_ne_bot {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    circleRotationSubgroup P hself hsq ≠ ⊥ := by
  intro hbot
  have hmem : circleProjectiveHom P hself hsq (-1) ∈ circleRotationSubgroup P hself hsq :=
    ⟨-1, rfl⟩
  rw [hbot] at hmem
  have heq : circleProjectiveHom P hself hsq (-1) = circleProjectiveHom P hself hsq 1 := by
    simpa only [Subgroup.mem_bot, map_one] using hmem
  have hcircle := circleProjectiveHom_injective hself hsq hnonscalar heq
  have hcomplex := congrArg (fun z : Circle => (z : ℂ)) hcircle
  norm_num at hcomplex

def projectiveRotation (P : Operator ι) (hself : star P = P) (hsq : P * P = 1)
    (t : ℝ) : PU ι :=
  projectiveMk (ι := ι) (unitaryRotation P hself hsq t)

theorem projectiveRotation_eq_one_iff {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) (t : ℝ) :
    projectiveRotation P hself hsq t = 1 ↔ ∃ k : ℤ, t = (k : ℝ) * Real.pi := by
  unfold projectiveRotation
  have hone : projectiveMk (ι := ι) (1 : Matrix.unitaryGroup ι ℂ) = 1 := map_one _
  rw [← hone, projectiveMk_eq_iff]
  exact rotation_projectivelyEquivalent_one_iff hnonscalar t

theorem circleRotationMatrix_exp_two_mul (P : Operator ι) (t : ℝ) :
    circleRotationMatrix P (Circle.exp (2 * t)) = (Circle.exp t : ℂ) • rotation P t := by
  have hexp : (Circle.exp (2 * t) : ℂ) = (Circle.exp t : ℂ) ^ 2 := by
    rw [two_mul, Circle.exp_add, Circle.coe_mul, pow_two]
  have he : (Circle.exp t : ℂ) = (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]
    ring
  have htrig : (Real.cos t : ℂ) ^ 2 + (Real.sin t : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq t
  have hI : Complex.I ^ 2 = (-1 : ℂ) := Complex.I_sq
  have ha : (((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) ^ 2 + 1) / 2 =
      ((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) * (Real.cos t : ℂ) := by
    linear_combination -(1 / 2 : ℂ) * htrig + ((Real.sin t : ℂ) ^ 2 / 2) * hI
  have hb : (((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) ^ 2 - 1) / 2 =
      ((Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ)) *
        (Complex.I * (Real.sin t : ℂ)) := by
    linear_combination (1 / 2 : ℂ) * htrig - ((Real.sin t : ℂ) ^ 2 / 2) * hI
  unfold circleRotationMatrix
  rw [hexp, he, ha, hb]
  simp only [rotation, affine, smul_add, smul_smul]

theorem circleProjectiveHom_exp_two_mul (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) (t : ℝ) :
    circleProjectiveHom P hself hsq (Circle.exp (2 * t)) = projectiveRotation P hself hsq t := by
  apply (projectiveMk_eq_iff (ι := ι) _ _).mpr
  exact ⟨(Circle.exp t : ℂ), circle_star_mul_self _, circleRotationMatrix_exp_two_mul P t⟩

/-- The closed circle subgroup is exactly the original real-parameter image. -/
theorem mem_circleRotationSubgroup_iff (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) (x : PU ι) :
    x ∈ circleRotationSubgroup P hself hsq ↔
      ∃ t : ℝ, projectiveRotation P hself hsq t = x := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨a, rfl⟩ := Circle.exp_surjective z
    refine ⟨a / 2, ?_⟩
    have hangle : 2 * (a / 2) = a := by ring
    simpa only [hangle] using (circleProjectiveHom_exp_two_mul P hself hsq (a / 2)).symm
  · rintro ⟨t, rfl⟩
    exact ⟨Circle.exp (2 * t), circleProjectiveHom_exp_two_mul P hself hsq t⟩

theorem circleRotationSubgroup_subset_of_rotation_mem (P : Operator ι)
    (hself : star P = P) (hsq : P * P = 1) (S : Set (PU ι))
    (hmem : ∀ t : ℝ, projectiveRotation P hself hsq t ∈ S) :
    (circleRotationSubgroup P hself hsq : Set (PU ι)) ⊆ S := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_circleRotationSubgroup_iff P hself hsq x).mp hx
  exact hmem t

/-- An independent closed-circle target with its exact real-parameter image. -/
theorem exists_closed_circle_rotation_subgroup {P : Operator ι}
    (hself : star P = P) (hsq : P * P = 1) (hnonscalar : ¬ IsScalar P) :
    ∃ S : Subgroup (PU ι), IsClosed (S : Set (PU ι)) ∧ S ≠ ⊥ ∧
      Nonempty (Circle ≃ₜ* S) ∧
      ∀ x : PU ι, x ∈ S ↔ ∃ t : ℝ, projectiveRotation P hself hsq t = x := by
  exact ⟨circleRotationSubgroup P hself hsq,
    isClosed_circleRotationSubgroup hself hsq hnonscalar,
    circleRotationSubgroup_ne_bot hself hsq hnonscalar,
    ⟨circleRotationEquiv hself hsq hnonscalar⟩,
    mem_circleRotationSubgroup_iff P hself hsq⟩

end CriticalDepth.ReviewV2

end
end Merged_CircleRotations

/- ===== Source block: NativeCircuitModel; SHA-256 b3977c39a964bfa5c812b1ee22b28b64e98275064ae1b7a9da11a7b85190f4f2 ===== -/
section Merged_NativeCircuitModel
/-!
Native finite-list circuits and their logical image.  The data carriers are
products, finite sets, lists, functions, matrices and Mathlib unitary groups.
Locality, arity and disjointness are predicates on those data.  The public
logical image takes a raw encoding matrix, not a custom code structure.

The legacy structures occur only in the adapters and proved image equality.
Neither an extra site nor an extra layer is introduced by an adapter.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix
open Manuscript
open scoped Classical Kronecker

abbrev NativeGateData (n : ℕ) (dim : Fin n → ℕ) :=
  Finset (Fin n) × Matrix.unitaryGroup (PhysicalBasis n dim) ℂ

abbrev NativeLayer (n : ℕ) (dim : Fin n → ℕ) := List (NativeGateData n dim)

abbrev NativeCircuit (n : ℕ) (dim : Fin n → ℕ) (r : ℕ) :=
  Fin r → NativeLayer n dim

variable {n K g q r h : ℕ} {dim : Fin n → ℕ}

def NativeGateAllowed (q : ℕ) (G : NativeGateData n dim) : Prop :=
  G.1.card ≤ q ∧ SupportedOn (dim := dim) G.2.val G.1

def NativeLayerAllowed (q : ℕ) (L : NativeLayer n dim) : Prop :=
  (∀ G ∈ L, NativeGateAllowed q G) ∧
    L.Pairwise (fun G H => Disjoint G.1 H.1)

def NativeCircuitAllowed (q : ℕ) (c : NativeCircuit n dim r) : Prop :=
  ∀ i, NativeLayerAllowed q (c i)

def nativeLayerEval (L : NativeLayer n dim) :
    Matrix.unitaryGroup (PhysicalBasis n dim) ℂ :=
  (L.map Prod.snd).reverse.prod

def nativeCircuitEval (c : NativeCircuit n dim r) :
    Matrix.unitaryGroup (PhysicalBasis n dim) ℂ :=
  (List.ofFn fun i => nativeLayerEval (c i)).reverse.prod

private theorem unitary_list_prod_val {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.unitaryGroup ι ℂ)) :
    L.prod.val =
      (L.map fun U : Matrix.unitaryGroup ι ℂ => U.val).prod := by
  induction L with
  | nil => rfl
  | cons U L ih =>
      change U.val * L.prod.val =
        U.val * (L.map fun U : Matrix.unitaryGroup ι ℂ => U.val).prod
      exact congrArg (fun M : Matrix ι ι ℂ => U.val * M) ih

theorem nativeLayerEval_val (L : NativeLayer n dim) :
    (nativeLayerEval L).val =
      (L.map fun G : NativeGateData n dim => G.2.val).reverse.prod := by
  rw [nativeLayerEval, unitary_list_prod_val]
  simp only [List.map_reverse, List.map_map, Function.comp_def]

theorem nativeCircuitEval_val (c : NativeCircuit n dim r) :
    (nativeCircuitEval c).val =
      (List.ofFn fun i => (nativeLayerEval (c i)).val).reverse.prod := by
  rw [nativeCircuitEval, unitary_list_prod_val]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_def]

/-- The image is specified directly in the native projective unitary group. -/
def nativeLogicalImage
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q h : ℕ) :
    Set (PU (Fin K)) :=
  {a | ∃ r : ℕ, r ≤ h ∧ ∃ c : NativeCircuit n dim r,
    NativeCircuitAllowed q c ∧
    ∃ W : Matrix.unitaryGroup (Fin K) ℂ,
    ∃ Z : Matrix.unitaryGroup (Fin g) ℂ,
      (nativeCircuitEval c).val * V = V * (W.val ⊗ₖ Z.val) ∧
      projectiveMk (ι := Fin K) W = a}

def nativeToLegacyGate (G : NativeGateData n dim) (hG : NativeGateAllowed q G) :
    ListGate n dim q where
  support := G.1
  gate := G.2.val
  arity := hG.1
  locality := hG.2
  unitary := (isUnitary_iff_mem_unitaryGroup (PhysicalBasis n dim) G.2.val).mpr
    G.2.property

def nativeToLegacyGateList : (L : NativeLayer n dim) →
    (∀ G ∈ L, NativeGateAllowed q G) → List (ListGate n dim q)
  | [], _ => []
  | G :: L, hL =>
      nativeToLegacyGate G (hL G (by simp)) ::
        nativeToLegacyGateList L (fun H hH => hL H (by simp [hH]))

theorem nativeToLegacyGateList_support (L : NativeLayer n dim)
    (hL : ∀ G ∈ L, NativeGateAllowed q G) :
    (nativeToLegacyGateList L hL).map ListGate.support = L.map Prod.fst := by
  induction L with
  | nil => rfl
  | cons G L ih =>
      simp only [nativeToLegacyGateList, List.map_cons, nativeToLegacyGate]
      exact congrArg (List.cons G.1) (ih _)

theorem nativeToLegacyGateList_gate (L : NativeLayer n dim)
    (hL : ∀ G ∈ L, NativeGateAllowed q G) :
    (nativeToLegacyGateList L hL).map ListGate.gate =
      L.map (fun G : NativeGateData n dim => G.2.val) := by
  induction L with
  | nil => rfl
  | cons G L ih =>
      simp only [nativeToLegacyGateList, List.map_cons, nativeToLegacyGate]
      exact congrArg (List.cons G.2.val) (ih _)

def nativeToLegacyLayer (L : NativeLayer n dim) (hL : NativeLayerAllowed q L) :
    ArbitraryLayer n dim q where
  gates := nativeToLegacyGateList L hL.1
  disjoint := by
    have hp : ((nativeToLegacyGateList L hL.1).map ListGate.support).Pairwise
        Disjoint := by
      rw [nativeToLegacyGateList_support]
      exact List.pairwise_map.mpr hL.2
    exact List.pairwise_map.mp hp

theorem nativeToLegacyLayer_eval (L : NativeLayer n dim) (hL : NativeLayerAllowed q L) :
    (nativeToLegacyLayer L hL).eval = (nativeLayerEval L).val := by
  unfold ArbitraryLayer.eval listGateEval nativeToLegacyLayer
  rw [nativeToLegacyGateList_gate]
  exact (nativeLayerEval_val L).symm

def nativeToLegacyCircuit (c : NativeCircuit n dim r) (hc : NativeCircuitAllowed q c) :
    ArbitraryCircuit n dim q r :=
  fun i => nativeToLegacyLayer (c i) (hc i)

theorem nativeToLegacyCircuit_eval (c : NativeCircuit n dim r)
    (hc : NativeCircuitAllowed q c) :
    arbitraryCircuitEval (nativeToLegacyCircuit c hc) =
      (nativeCircuitEval c).val := by
  rw [nativeCircuitEval_val]
  simp only [arbitraryCircuitEval, nativeToLegacyCircuit, nativeToLegacyLayer_eval]

def legacyToNativeGate (G : ListGate n dim q) : NativeGateData n dim :=
  (G.support, ⟨G.gate,
    (isUnitary_iff_mem_unitaryGroup (PhysicalBasis n dim) G.gate).mp G.unitary⟩)

def legacyToNativeLayer (L : ArbitraryLayer n dim q) : NativeLayer n dim :=
  L.gates.map legacyToNativeGate

theorem legacyToNativeLayer_allowed (L : ArbitraryLayer n dim q) :
    NativeLayerAllowed q (legacyToNativeLayer L) := by
  constructor
  · intro G hG
    obtain ⟨H, _, rfl⟩ := List.mem_map.mp hG
    exact ⟨H.arity, H.locality⟩
  · exact List.pairwise_map.mpr L.disjoint

theorem legacyToNativeLayer_eval (L : ArbitraryLayer n dim q) :
    (nativeLayerEval (legacyToNativeLayer L)).val = L.eval := by
  rw [nativeLayerEval_val]
  simp only [legacyToNativeLayer, List.map_map, Function.comp_def, legacyToNativeGate]
  rfl

def legacyToNativeCircuit (c : ArbitraryCircuit n dim q r) : NativeCircuit n dim r :=
  fun i => legacyToNativeLayer (c i)

theorem legacyToNativeCircuit_allowed (c : ArbitraryCircuit n dim q r) :
    NativeCircuitAllowed q (legacyToNativeCircuit c) :=
  fun i => legacyToNativeLayer_allowed (c i)

theorem legacyToNativeCircuit_eval (c : ArbitraryCircuit n dim q r) :
    (nativeCircuitEval (legacyToNativeCircuit c)).val =
      arbitraryCircuitEval c := by
  rw [nativeCircuitEval_val]
  simp only [legacyToNativeCircuit, legacyToNativeLayer_eval, arbitraryCircuitEval]

/-- Both finite-list models have exactly the same projective logical image.
The encoding's isometry is supplied only for the legacy proof adapter. -/
theorem nativeLogicalImage_eq_preimage
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (q h : ℕ) :
    nativeLogicalImage V q h = puToProjectiveOperator (Fin K) ⁻¹'
      arbitraryLogicalImageAtMost (⟨V, hV⟩ : Code n dim K g) q h := by
  ext a
  constructor
  · rintro ⟨r, hr, c, hc, W, Z, heval, hclass⟩
    refine ⟨r, hr, nativeToLegacyCircuit c hc, W.val, ?_, ?_⟩
    · refine ⟨(isUnitary_iff_mem_unitaryGroup (Fin K) W.val).mpr W.property,
        Z.val, (isUnitary_iff_mem_unitaryGroup (Fin g) Z.val).mpr Z.property, ?_⟩
      change arbitraryCircuitEval (nativeToLegacyCircuit c hc) * V =
        V * (W.val ⊗ₖ Z.val)
      rw [nativeToLegacyCircuit_eval]
      exact heval
    · rw [← hclass, puToProjectiveOperator_mk]
  · rintro ⟨r, hr, c, W, hW, hclass⟩
    obtain ⟨hW, Z, hZ, heval⟩ := hW
    let W' : Matrix.unitaryGroup (Fin K) ℂ :=
      ⟨W, (isUnitary_iff_mem_unitaryGroup (Fin K) W).mp hW⟩
    let Z' : Matrix.unitaryGroup (Fin g) ℂ :=
      ⟨Z, (isUnitary_iff_mem_unitaryGroup (Fin g) Z).mp hZ⟩
    refine ⟨r, hr, legacyToNativeCircuit c, legacyToNativeCircuit_allowed c,
      W', Z', ?_, ?_⟩
    · rw [legacyToNativeCircuit_eval]
      exact heval
    · apply puToProjectiveOperator_injective
      simpa only [puToProjectiveOperator_mk] using hclass

end CriticalDepth.ReviewV2
end -- explicit closure of the original file-level noncomputable section
end Merged_NativeCircuitModel

/- ===== Source block: NativeFiniteMain; SHA-256 7f7c61a7a054f99483975b7476ed85068282f430dfbd1cab5d0e778ca7da68d6 ===== -/
section Merged_NativeFiniteMain
noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix Manuscript
open scoped Kronecker

variable {n K g : ℕ} {dim : Fin n → ℕ}

def NativeGaugeOnly (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) ℂ) : Prop :=
  ∃ M : Matrix (Fin g) (Fin g) ℂ,
    V.conjTranspose * O * V = (1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ M

def NativeDetectsBelow (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card < d →
    ∀ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) ℂ,
      SupportedOn O S → NativeGaugeOnly V O

def NativeActualDistance (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (d : ℕ) : Prop :=
  NativeDetectsBelow V d ∧ ∃ S : Finset (Fin n), S.card = d ∧
    ∃ O : Matrix (PhysicalBasis n dim) (PhysicalBasis n dim) ℂ,
      SupportedOn O S ∧ ¬ NativeGaugeOnly V O

def NativeStabilizer {k : ℕ}
    (V : Matrix (PhysicalBasis n (fun _ => 2)) (Fin (2 ^ k) × Fin 1) ℂ) : Prop :=
  ∃ S : Subgroup (Matrix.unitaryGroup (PhysicalBasis n (fun _ => 2)) ℂ),
    (∀ U ∈ S, IsPauli (n := n) U.val) ∧
    Set.range (fun v => V.mulVec v) =
      {v | ∀ U ∈ S, U.val.mulVec v = v}

theorem nativeDetectsBelow_iff_legacy
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (d : ℕ) :
    NativeDetectsBelow V d ↔ DetectsBelow (⟨V, hV⟩ : Code n dim K g) d := Iff.rfl

theorem nativeActualDistance_iff_legacy
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (d : ℕ) :
    NativeActualDistance V d ↔ HasActualDistance (⟨V, hV⟩ : Code n dim K g) d := Iff.rfl

theorem nativeStabilizer_iff_legacy {k : ℕ}
    (V : Matrix (PhysicalBasis n (fun _ => 2)) (Fin (2 ^ k) × Fin 1) ℂ)
    (hV : V.conjTranspose * V = 1) :
    NativeStabilizer V ↔ IsStabilizer (⟨V, hV⟩ : Code n (fun _ => 2) (2 ^ k) 1) := Iff.rfl

theorem nativeLogicalImage_eq_oldPU_preimage
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (q h : ℕ) :
    nativeLogicalImage V q h =
      puHomeomorphOld (Fin K) ⁻¹'
        ReviewIntegration.logicalImagePU (⟨V, hV⟩ : Code n dim K g) q h := by
  rw [nativeLogicalImage_eq_preimage V hV q h]
  rfl

theorem nativeLogicalImage_finite_iff_legacy
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (q h : ℕ) :
    (nativeLogicalImage V q h).Finite ↔
      (arbitraryLogicalImageAtMost (⟨V, hV⟩ : Code n dim K g) q h).Finite := by
  rw [nativeLogicalImage_eq_oldPU_preimage V hV q h]
  constructor
  · intro hf
    apply (ReviewIntegration.logicalImage_finite_iff
      (⟨V, hV⟩ : Code n dim K g) q h).mp
    have himage := hf.image (puHomeomorphOld (Fin K))
    simpa only [Set.image_preimage_eq _ (puHomeomorphOld (Fin K)).surjective] using himage
  · intro hf
    exact Set.Finite.preimage (puHomeomorphOld (Fin K)).injective.injOn
      ((ReviewIntegration.logicalImage_finite_iff
        (⟨V, hV⟩ : Code n dim K g) q h).mpr hf)

def nativeCriticalDepth
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ) (q : ℕ) : ℕ∞ :=
  sInf {r | ∃ h : ℕ, 1 ≤ h ∧ r = (h : ℕ∞) ∧ (nativeLogicalImage V q h).Infinite}

theorem nativeCriticalDepth_eq_legacy
    (V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ)
    (hV : V.conjTranspose * V = 1) (q : ℕ) :
    nativeCriticalDepth V q =
      hInfinityPositiveAtMost (⟨V, hV⟩ : Code n dim K g) q := by
  unfold nativeCriticalDepth hInfinityPositiveAtMost
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨h, hp, hr, hi⟩
    exact ⟨h, hp, hr, (not_congr (nativeLogicalImage_finite_iff_legacy V hV q h)).mp hi⟩
  · rintro ⟨h, hp, hr, hi⟩
    exact ⟨h, hp, hr, (not_congr (nativeLogicalImage_finite_iff_legacy V hV q h)).mpr hi⟩

def NativeTheoremOne : Prop :=
  ∀ (n K g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ K → 1 ≤ g → 2 ≤ d →
    ∀ V : Matrix (PhysicalBasis n dim) (Fin K × Fin g) ℂ,
      V.conjTranspose * V = 1 → NativeDetectsBelow V d →
        ∀ q h : ℕ, 2 ≤ q → 1 ≤ h → h < Arithmetic.criticalDepth q d →
          (nativeLogicalImage V q h).Finite ∧ ¬ Dense (nativeLogicalImage V q h)

theorem nativeTheoremOne_proved : NativeTheoremOne := by
  intro n K g d dim hn hK hg hd V hV hdetect q h hq hp hb
  obtain ⟨hf, hnd⟩ := theoremOnePositive_proved n K g d dim hn hK hg hd
    (⟨V, hV⟩ : Code n dim K g) hdetect q h hq hp hb
  refine ⟨(nativeLogicalImage_finite_iff_legacy V hV q h).mpr hf, ?_⟩
  rw [nativeLogicalImage_eq_oldPU_preimage V hV q h]
  exact not_congr (puHomeomorphOld (Fin K)).isOpenQuotientMap.dense_preimage_iff |>.mpr hnd

end CriticalDepth.ReviewV2

end
end Merged_NativeFiniteMain

/- ===== Source block: StabilizerCircle; SHA-256 0a31213c26a9da98eb30cd76026de37219a98b869aaa7b0685081f03d88c3de3 ===== -/
section Merged_StabilizerCircle
/-!
# The closed-circle conclusion under the original stabilizer-code assumptions

The logical involution is derived from the actual-distance and stabilizer
hypotheses. It is not supplied as an extra witness. The ambient projective
unitary space and subgroup structures are the native Mathlib objects.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Manuscript

/-- The actual stabilizer construction contains a nontrivial closed circle
subgroup at the critical common depth budget. -/
theorem stabilizer_critical_closed_circle
    (n k d q : ℕ) (_hk : 1 ≤ k) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ S : Subgroup (PU (Fin (2 ^ k))),
      IsClosed (S : Set (PU (Fin (2 ^ k)))) ∧ S ≠ ⊥ ∧
      Nonempty (Circle ≃ₜ* S) ∧
      (S : Set (PU (Fin (2 ^ k)))) ⊆
        puToProjectiveOperator (Fin (2 ^ k)) ⁻¹'
          arbitraryLogicalImageAtMost C q (Arithmetic.criticalDepth q d) := by
  classical
  obtain ⟨p, W, hcard, hencoded, hself, hsq, hnonscalar⟩ :=
    stabilizer_exact_logicalPauli C hstabilizer hdistance
  refine ⟨circleRotationSubgroup W hself hsq,
    isClosed_circleRotationSubgroup hself hsq hnonscalar,
    circleRotationSubgroup_ne_bot hself hsq hnonscalar,
    ⟨circleRotationEquiv hself hsq hnonscalar⟩, ?_⟩
  apply circleRotationSubgroup_subset_of_rotation_mem W hself hsq
  intro t
  change puToProjectiveOperator (Fin (2 ^ k))
    (projectiveMk (ι := Fin (2 ^ k)) (unitaryRotation W hself hsq t)) ∈
      arbitraryLogicalImageAtMost C q (Arithmetic.criticalDepth q d)
  rw [puToProjectiveOperator_mk]
  have hpdist : 2 ≤ (pauliSupport p).card := by simpa only [hcard] using hd
  have hsynthesis := pauli_rotation_synthesis q hq p hpdist t
  rw [hcard] at hsynthesis
  obtain ⟨c, hceval⟩ := hsynthesis
  apply logicalImage_subset_atMost C q (Arithmetic.criticalDepth q d)
    (Arithmetic.criticalDepth q d) (le_refl _)
  refine ⟨c, rotation W t, ?_, rfl⟩
  rw [hceval]
  exact implements_rotation_subspace C _ W hencoded hself hsq t

/-- The same genuine logical Pauli has the exponential formula and exact
projective kernel; no additional generator hypothesis is assumed. -/
theorem stabilizer_logical_rotation_exp_and_kernel
    {n k d : ℕ} (C : Code n (fun _ => 2) (2 ^ k) 1)
    (hstabilizer : IsStabilizer C) (hdistance : HasActualDistance C d) :
    ∃ (W : Operator (Fin (2 ^ k))) (hself : star W = W) (hsq : W * W = 1),
      ¬ IsScalar W ∧ ∀ t : ℝ,
        NormedSpace.exp ((Complex.I * (t : ℂ)) • W) = rotation W t ∧
        (projectiveRotation W hself hsq t = 1 ↔
          ∃ j : ℤ, t = (j : ℝ) * Real.pi) := by
  obtain ⟨_p, W, _hcard, _hencoded, hself, hsq, hnonscalar⟩ :=
    stabilizer_exact_logicalPauli C hstabilizer hdistance
  exact ⟨W, hself, hsq, hnonscalar, fun t =>
    ⟨exp_involution_eq_rotation hsq t,
      projectiveRotation_eq_one_iff hself hsq hnonscalar t⟩⟩

namespace Examples

/-- A closed original-hypothesis application using the explicit [[4,2,2]] code. -/
theorem fourQubit_closed_circle_at_budget_one :
    ∃ S : Subgroup (PU (Fin (2 ^ 2))),
      IsClosed (S : Set (PU (Fin (2 ^ 2)))) ∧ S ≠ ⊥ ∧
      Nonempty (Circle ≃ₜ* S) ∧
      (S : Set (PU (Fin (2 ^ 2)))) ⊆
        puToProjectiveOperator (Fin (2 ^ 2)) ⁻¹'
          arbitraryLogicalImageAtMost FourQubit.code 2 1 := by
  simpa only [MainExamples.fourQubit_binary_criticalDepth] using
    stabilizer_critical_closed_circle 4 2 2 2 (by decide) (by decide) (by decide)
      FourQubit.code FourQubit.isStabilizer FourQubit.hasActualDistance_two

end Examples

end CriticalDepth.ReviewV2

end
end Merged_StabilizerCircle

/- ===== Source block: NativeMainStatements; SHA-256 89cde3ef892935517642e91d60fea529c174070fd820c98c330a4977a9d6a8a9 ===== -/
section Merged_NativeMainStatements
noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix Manuscript

def NativeTheoremTwo : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ V : Matrix (PhysicalBasis n (fun _ => 2)) (Fin (2 ^ k) × Fin 1) ℂ,
      V.conjTranspose * V = 1 → NativeStabilizer V → NativeActualDistance V d →
        nativeCriticalDepth V q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
          ∃ S : Subgroup (PU (Fin (2 ^ k))),
            IsClosed (S : Set (PU (Fin (2 ^ k)))) ∧ S ≠ ⊥ ∧
              Nonempty (Circle ≃ₜ* S) ∧
                (S : Set (PU (Fin (2 ^ k)))) ⊆
                  nativeLogicalImage V q (Arithmetic.criticalDepth q d)

theorem nativeTheoremTwo_proved : NativeTheoremTwo := by
  intro n k d q hk hd hq V hV hs hdist
  let C : Code n (fun _ => 2) (2 ^ k) 1 := ⟨V, hV⟩
  obtain ⟨hc, _⟩ := theoremTwoPositive_proved n k d q hk hd hq C hs hdist
  refine ⟨(nativeCriticalDepth_eq_legacy V hV q).trans hc, ?_⟩
  obtain ⟨S, hclosed, hnontrivial, hequiv, hsubset⟩ :=
    stabilizer_critical_closed_circle n k d q hk hd hq C hs hdist
  refine ⟨S, hclosed, hnontrivial, hequiv, ?_⟩
  simpa only [nativeLogicalImage_eq_preimage V hV q
    (Arithmetic.criticalDepth q d)] using hsubset

#print axioms CriticalDepth.ReviewV2.nativeTheoremOne_proved
#print axioms CriticalDepth.ReviewV2.nativeTheoremTwo_proved

end CriticalDepth.ReviewV2

end
end Merged_NativeMainStatements

/- ===== Source block: CriticalCircleWitness; SHA-256 cb73715414e191da78e5246d5e5e4261e6457a72d198bbd09f7af9f294f8db5a ===== -/
section Merged_CriticalCircleWitness
/-!
# One critical-depth witness for the exponential, exact kernel, and closed circle

The input is a raw complex encoding matrix with its isometry, stabilizer, and
actual-distance hypotheses. The legacy code structure is used only inside the
proof to reuse the accepted Pauli witness and synthesis theorems. The same
logical matrix W appears in every conclusion, including the exact range of S.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix Manuscript

/-- The original hypotheses supply one logical generator with all the stated
analytic, algebraic, topological, and circuit-budget properties together. -/
theorem critical_circle_joint_witness
    (n k d q : ℕ) (hk : 1 ≤ k) (hd : 2 ≤ d) (hq : 2 ≤ q)
    (V : Matrix (PhysicalBasis n (fun _ => 2)) (Fin (2 ^ k) × Fin 1) ℂ)
    (hV : V.conjTranspose * V = 1)
    (hstabilizer : NativeStabilizer V) (hdistance : NativeActualDistance V d) :
    nativeCriticalDepth V q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
    ∃ (W : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)
      (hself : star W = W) (hsq : W * W = 1)
      (S : Subgroup (PU (Fin (2 ^ k)))),
      ¬ IsScalar W ∧
      (∀ t : ℝ, NormedSpace.exp ((Complex.I * (t : ℂ)) • W) = rotation W t) ∧
      (∀ t : ℝ, projectiveRotation W hself hsq t = 1 ↔
        ∃ j : ℤ, t = (j : ℝ) * Real.pi) ∧
      (∀ t : ℝ, projectiveRotation W hself hsq t ∈
        nativeLogicalImage V q (Arithmetic.criticalDepth q d)) ∧
      IsClosed (S : Set (PU (Fin (2 ^ k)))) ∧ S ≠ ⊥ ∧
      Nonempty (Circle ≃ₜ* S) ∧
      (∀ x : PU (Fin (2 ^ k)), x ∈ S ↔
        ∃ t : ℝ, projectiveRotation W hself hsq t = x) := by
  classical
  let C : Code n (fun _ => 2) (2 ^ k) 1 := ⟨V, hV⟩
  have hlegacyStabilizer : IsStabilizer C :=
    (nativeStabilizer_iff_legacy V hV).mp hstabilizer
  have hlegacyDistance : HasActualDistance C d :=
    (nativeActualDistance_iff_legacy V hV d).mp hdistance
  have hcritical : nativeCriticalDepth V q = (Arithmetic.criticalDepth q d : ℕ∞) :=
    (nativeCriticalDepth_eq_legacy V hV q).trans
      (theoremTwoPositive_proved n k d q hk hd hq C hlegacyStabilizer hlegacyDistance).1
  refine ⟨hcritical, ?_⟩
  obtain ⟨p, W, hcard, hencoded, hself, hsq, hnonscalar⟩ :=
    stabilizer_exact_logicalPauli C hlegacyStabilizer hlegacyDistance
  have hmembership : ∀ t : ℝ, projectiveRotation W hself hsq t ∈
      nativeLogicalImage V q (Arithmetic.criticalDepth q d) := by
    intro t
    rw [nativeLogicalImage_eq_preimage V hV q (Arithmetic.criticalDepth q d)]
    change puToProjectiveOperator (Fin (2 ^ k))
      (projectiveMk (ι := Fin (2 ^ k)) (unitaryRotation W hself hsq t)) ∈
        arbitraryLogicalImageAtMost C q (Arithmetic.criticalDepth q d)
    rw [puToProjectiveOperator_mk]
    have hpdist : 2 ≤ (pauliSupport p).card := by simpa only [hcard] using hd
    have hsynthesis := pauli_rotation_synthesis q hq p hpdist t
    rw [hcard] at hsynthesis
    obtain ⟨c, hceval⟩ := hsynthesis
    apply logicalImage_subset_atMost C q (Arithmetic.criticalDepth q d)
      (Arithmetic.criticalDepth q d) (le_refl _)
    refine ⟨c, rotation W t, ?_, rfl⟩
    rw [hceval]
    exact implements_rotation_subspace C _ W hencoded hself hsq t
  refine ⟨W, hself, hsq, circleRotationSubgroup W hself hsq, hnonscalar,
    exp_involution_eq_rotation hsq,
    projectiveRotation_eq_one_iff hself hsq hnonscalar,
    hmembership, isClosed_circleRotationSubgroup hself hsq hnonscalar,
    circleRotationSubgroup_ne_bot hself hsq hnonscalar,
    ⟨circleRotationEquiv hself hsq hnonscalar⟩, ?_⟩
  exact mem_circleRotationSubgroup_iff W hself hsq

end CriticalDepth.ReviewV2

end
end Merged_CriticalCircleWitness

/- ===== Source block: HilbertCoordinates; SHA-256 0658cf098c7ba50388c72132b962da92b83a509f9809892442905d93a66014b8 ===== -/
section Merged_HilbertCoordinates
/-!
# Coordinate transport for arbitrary finite complex inner-product carriers

All carrier, isometry, operator, adjoint, tensor, matrix and unitary objects in
this file are Mathlib objects. No manuscript Code or custom unitary predicate
is used. These are the initial transport lemmas; arbitrary finite-register
support, circuit, projective-quotient and theorem transports are separate work.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertCoordinates

open Matrix
open scoped TensorProduct Kronecker

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The orthonormal coordinates exist for every finite complex carrier,
without supplying a basis or a coordinate-equivalence hypothesis. -/
def coordinates : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E)) :=
  (stdOrthonormalBasis ℂ E).repr

theorem exists_coordinates :
    Nonempty (E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :=
  ⟨coordinates E⟩

/-- Mathlib's star-algebra equivalence preserves multiplication and adjoints. -/
def operatorCoordinates :
    (E →ₗ[ℂ] E) ≃⋆ₐ[ℂ] Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  LinearMap.toMatrixOrthonormal (stdOrthonormalBasis ℂ E)

theorem operatorCoordinates_mul (A B : E →ₗ[ℂ] E) :
    operatorCoordinates E (A * B) = operatorCoordinates E A * operatorCoordinates E B :=
  map_mul (operatorCoordinates E) A B

theorem operatorCoordinates_star (A : E →ₗ[ℂ] E) :
    operatorCoordinates E (star A) = star (operatorCoordinates E A) :=
  map_star (operatorCoordinates E) A

/-- Both sides use Mathlib's standard unitary submonoid. -/
theorem operatorCoordinates_mem_unitary_iff (A : E →ₗ[ℂ] E) :
    operatorCoordinates E A ∈ Matrix.unitaryGroup (Fin (Module.finrank ℂ E)) ℂ ↔
      A ∈ unitary (E →ₗ[ℂ] E) := by
  constructor
  · intro h
    have hs := Unitary.map_mem (operatorCoordinates E).symm h
    simpa using hs
  · intro h
    exact Unitary.map_mem (operatorCoordinates E) h

/-- Coordinate transport preserves and reflects one global unitary scalar. -/
theorem operatorCoordinates_phase_iff (A B : E →ₗ[ℂ] E) :
    (∃ z : unitary ℂ, A = (z : ℂ) • B) ↔
      ∃ z : unitary ℂ, operatorCoordinates E A = (z : ℂ) • operatorCoordinates E B := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, map_smul (operatorCoordinates E) (z : ℂ) B⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, (operatorCoordinates E).injective ?_⟩
    exact hz.trans (map_smul (operatorCoordinates E) (z : ℂ) B).symm

variable {E}
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Rectangular encoding adjoints agree with conjugate transpose in ONB coordinates. -/
theorem matrix_adjoint (bE : OrthonormalBasis ι ℂ E) (bF : OrthonormalBasis κ ℂ F)
    (A : E →ₗ[ℂ] F) :
    LinearMap.toMatrix bF.toBasis bE.toBasis (LinearMap.adjoint A) =
      (LinearMap.toMatrix bE.toBasis bF.toBasis A).conjTranspose :=
  LinearMap.toMatrix_adjoint bE bF A

/-- An arbitrary Mathlib isometric encoding gives exactly V†V = I. -/
theorem isometric_encoding_matrix (bE : OrthonormalBasis ι ℂ E)
    (bF : OrthonormalBasis κ ℂ F) (V : E →ₗᵢ[ℂ] F) :
    (LinearMap.toMatrix bE.toBasis bF.toBasis V.toLinearMap).conjTranspose *
      LinearMap.toMatrix bE.toBasis bF.toBasis V.toLinearMap = 1 := by
  calc
    _ = LinearMap.toMatrix bE.toBasis bE.toBasis
        ((LinearMap.adjoint V.toLinearMap).comp V.toLinearMap) := by
      rw [LinearMap.toMatrix_comp bE.toBasis bF.toBasis bE.toBasis,
        LinearMap.toMatrix_adjoint bE bF]
    _ = 1 := by
      rw [V.adjoint_comp_self', LinearMap.toMatrix_id]

/-- The product ONB preserves the tensor factors and their order. Choosing an
arbitrary global ONB instead would not establish a locality transport. -/
theorem tensor_map_coordinates (bE : OrthonormalBasis ι ℂ E)
    (bF : OrthonormalBasis κ ℂ F) (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) :
    LinearMap.toMatrix (bE.tensorProduct bF).toBasis (bE.tensorProduct bF).toBasis
      (TensorProduct.map A B) =
      LinearMap.toMatrix bE.toBasis bE.toBasis A ⊗ₖ
        LinearMap.toMatrix bF.toBasis bF.toBasis B := by
  simpa only [OrthonormalBasis.toBasis_tensorProduct] using
    TensorProduct.toMatrix_map bE.toBasis bF.toBasis bE.toBasis bF.toBasis A B

#print axioms CriticalDepth.ReviewV2.HilbertCoordinates.exists_coordinates
#print axioms CriticalDepth.ReviewV2.HilbertCoordinates.isometric_encoding_matrix
#print axioms CriticalDepth.ReviewV2.HilbertCoordinates.tensor_map_coordinates

end CriticalDepth.ReviewV2.HilbertCoordinates

end
end Merged_HilbertCoordinates

/- ===== Source block: HilbertRegister; SHA-256 22cf6cf0e7ced42fd1dc9f924f9759bdefba8afb0df24dbfdc1a62116efeaaf6 ===== -/
section Merged_HilbertRegister
/-!
# Automatically constructed finite Hilbert registers

RegisterData only packages existing Mathlib structures during recursion. Its
carrier is built from binary Mathlib TensorProducts, and its basis is obtained
from the local orthonormal bases by tensoring and index reindexing. Callers of
registerFin supply arbitrary finite complex carriers, not a global basis or a
locality-preservation hypothesis. The arbitrary-support split below is proved
to send each full product-basis vector to the corresponding two product-basis
vectors. Circuit and main-theorem transport are subsequent obligations.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertRegister

open scoped TensorProduct Classical

universe u

/-- Internal dependent package of actual Mathlib data, not a replacement class. -/
structure RegisterData (ι : Type) [Fintype ι] where
  carrier : Type u
  normed : NormedAddCommGroup carrier
  inner : letI := normed; InnerProductSpace ℂ carrier
  basis : letI := normed; letI := inner; OrthonormalBasis ι ℂ carrier

namespace RegisterData

variable {ι κ : Type} [Fintype ι] [Fintype κ]

instance instNormed (D : RegisterData ι) : NormedAddCommGroup D.carrier := D.normed
instance instInner (D : RegisterData ι) : InnerProductSpace ℂ D.carrier := D.inner
instance instFinite (D : RegisterData ι) : FiniteDimensional ℂ D.carrier :=
  D.basis.toBasis.finiteDimensional_of_finite

def reindex (D : RegisterData.{u} ι) (e : ι ≃ κ) : RegisterData.{u} κ where
  carrier := D.carrier
  normed := D.normed
  inner := D.inner
  basis := D.basis.reindex e

def tensor (D : RegisterData.{u} ι) (F : RegisterData.{u} κ) : RegisterData.{u} (ι × κ) where
  carrier := D.carrier ⊗[ℂ] F.carrier
  normed := inferInstance
  inner := inferInstance
  basis := D.basis.tensorProduct F.basis

end RegisterData

def emptyIndexEquiv (dim : Fin 0 → ℕ) :
    PUnit.{u + 1} ≃ ((i : Fin 0) → Fin (dim i)) where
  toFun _ i := Fin.elim0 i
  invFun _ := PUnit.unit
  left_inv x := by cases x; rfl
  right_inv x := by funext i; exact Fin.elim0 i

/-- The empty tensor is a genuine Mathlib one-dimensional Euclidean space.
Using PUnit at the carrier universe keeps arbitrary carrier universes available. -/
def emptyData (dim : Fin 0 → ℕ) : RegisterData.{u} ((i : Fin 0) → Fin (dim i)) where
  carrier := EuclideanSpace ℂ PUnit.{u + 1}
  normed := inferInstance
  inner := inferInstance
  basis := (EuclideanSpace.basisFun PUnit.{u + 1} ℂ).reindex (emptyIndexEquiv dim)

/-- A right-associated binary tensor, in the original Fin-site order. -/
def buildData : {n : ℕ} → (dim : Fin n → ℕ) →
    (∀ i, RegisterData.{u} (Fin (dim i))) →
    RegisterData.{u} ((i : Fin n) → Fin (dim i))
  | 0, dim, _ => emptyData dim
  | n + 1, dim, H =>
    RegisterData.reindex
      ((H 0).tensor (buildData (fun i : Fin n => dim i.succ) (fun i => H i.succ)))
      (Fin.consEquiv (fun i => Fin (dim i)))

/-- The same construction on any finite site type, by an automatically chosen
enumeration. The final basis index retains the original site labels. -/
def finiteData (ι : Type) [Fintype ι] [DecidableEq ι] (dim : ι → ℕ)
    (H : ∀ i, RegisterData.{u} (Fin (dim i))) : RegisterData.{u} ((i : ι) → Fin (dim i)) :=
  let e := Fintype.equivFin ι
  RegisterData.reindex
    (buildData (fun j => dim (e.symm j)) (fun j => H (e.symm j)))
    (Equiv.piCongrLeft' (fun i => Fin (dim i)) e).symm

def siteData (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] : RegisterData.{u} (Fin (Module.finrank ℂ E)) where
  carrier := E
  normed := inferInstance
  inner := inferInstance
  basis := stdOrthonormalBasis ℂ E

variable {n : ℕ} (E : Fin n → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

def registerFin : RegisterData.{u} ((i : Fin n) → Fin (Module.finrank ℂ (E i))) :=
  buildData (fun i => Module.finrank ℂ (E i)) (fun i => siteData (E i))

def supportData (S : Finset (Fin n)) :
    RegisterData.{u} ((i : S) → Fin (Module.finrank ℂ (E i.1))) :=
  finiteData S (fun i => Module.finrank ℂ (E i.1)) (fun i => siteData (E i.1))

def complementData (S : Finset (Fin n)) :
    RegisterData.{u} ((i : {i : Fin n // i ∉ S}) → Fin (Module.finrank ℂ (E i.1))) :=
  finiteData {i : Fin n // i ∉ S} (fun i => Module.finrank ℂ (E i.1))
    (fun i => siteData (E i.1))

def splitIndex (dim : Fin n → ℕ) (S : Finset (Fin n)) :
    ((i : Fin n) → Fin (dim i)) ≃
      (((i : S) → Fin (dim i.1)) × ((i : {i : Fin n // i ∉ S}) → Fin (dim i.1))) where
  toFun x := (fun i => x i.1, fun i => x i.1)
  invFun x i := if hi : i ∈ S then x.1 ⟨i, hi⟩ else x.2 ⟨i, hi⟩
  left_inv x := by funext i; by_cases hi : i ∈ S <;> simp [hi]
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [i.property]
    · funext i
      simp [i.property]

/-- The split is constructed from product bases, not assumed as input. -/
def supportSplit (S : Finset (Fin n)) :
    (registerFin E).carrier ≃ₗᵢ[ℂ]
      ((supportData E S).carrier ⊗[ℂ] (complementData E S).carrier) :=
  (registerFin E).basis.equiv
    ((supportData E S).basis.tensorProduct (complementData E S).basis)
    (splitIndex (fun i => Module.finrank ℂ (E i)) S)

theorem supportSplit_productBasis (S : Finset (Fin n))
    (x : (i : Fin n) → Fin (Module.finrank ℂ (E i))) :
    supportSplit E S ((registerFin E).basis x) =
      (supportData E S).basis (fun i => x i.1) ⊗ₜ[ℂ]
        (complementData E S).basis (fun i => x i.1) := by
  calc
    _ = ((supportData E S).basis.tensorProduct (complementData E S).basis)
        ((splitIndex (fun i => Module.finrank ℂ (E i)) S) x) :=
      (registerFin E).basis.equiv_apply_basis
        ((supportData E S).basis.tensorProduct (complementData E S).basis)
        (splitIndex (fun i => Module.finrank ℂ (E i)) S) x
    _ = _ := OrthonormalBasis.tensorProduct_apply'
      (supportData E S).basis (complementData E S).basis
      ((splitIndex (fun i => Module.finrank ℂ (E i)) S) x)

/-- The physical coordinate equivalence is automatic for the iterated register. -/
def coordinates :
    (registerFin E).carrier ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((i : Fin n) → Fin (Module.finrank ℂ (E i))) :=
  (registerFin E).basis.repr

#print axioms CriticalDepth.ReviewV2.HilbertRegister.supportSplit_productBasis

end CriticalDepth.ReviewV2.HilbertRegister

end
end Merged_HilbertRegister

/- ===== Source block: HilbertLocality; SHA-256 87ae3acce105198c981f93852a68646902018d4ccb6a8d88e0018d979bb704a5 ===== -/
section Merged_HilbertLocality
/-!
# Tensor-local operators on arbitrary finite complex Hilbert registers

The local embedding is the conjugate of Mathlib's A tensor identity by the
automatically constructed product-basis split. The coefficient theorem proves
the exact supported-matrix formula; locality is not an input assumption about
an arbitrary global coordinate map.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertLocality

open HilbertRegister
open scoped TensorProduct Classical

universe u

variable {n : ℕ} (E : Fin n → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

def embedOn (S : Finset (Fin n))
    (A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier) :
    (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier :=
  (supportSplit E S).symm.toLinearMap.comp
    ((TensorProduct.map A LinearMap.id).comp (supportSplit E S).toLinearMap)

def SupportedOn (O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier)
    (S : Finset (Fin n)) : Prop :=
  ∃ A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier, O = embedOn E S A

theorem supportSplit_embedOn (S : Finset (Fin n))
    (A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier)
    (x : (registerFin E).carrier) :
    supportSplit E S (embedOn E S A x) =
      TensorProduct.map A LinearMap.id (supportSplit E S x) := by
  simp [embedOn]

theorem matrix_coeff_eq_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ F) (A : F →ₗ[ℂ] F) (i j : ι) :
    LinearMap.toMatrix b.toBasis b.toBasis A i j = inner ℂ (b i) (A (b j)) :=
  LinearMap.toMatrixOrthonormal_apply_apply b A i j

/-- The exact matrix support condition, including empty support and all local
dimensions. No nonzero-dimension assumption is added. -/
theorem embedOn_toMatrix_apply (S : Finset (Fin n))
    (A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier)
    (x y : (i : Fin n) → Fin (Module.finrank ℂ (E i))) :
    LinearMap.toMatrix (registerFin E).basis.toBasis (registerFin E).basis.toBasis
      (embedOn E S A) x y =
      if ∀ i, i ∉ S → x i = y i then
        LinearMap.toMatrix (supportData E S).basis.toBasis (supportData E S).basis.toBasis
          A (fun i => x i.1) (fun i => y i.1)
      else 0 := by
  have hcomp : (fun i : {i : Fin n // i ∉ S} => x i.1) =
      (fun i : {i : Fin n // i ∉ S} => y i.1) ↔ ∀ i, i ∉ S → x i = y i := by
    constructor
    · intro he i hi
      exact congrFun he ⟨i, hi⟩
    · intro he
      funext i
      exact he i.1 i.property
  calc
    _ = inner ℂ ((registerFin E).basis x) (embedOn E S A ((registerFin E).basis y)) :=
      matrix_coeff_eq_inner _ _ x y
    _ = inner ℂ ((supportData E S).basis (fun i => x i.1))
          (A ((supportData E S).basis (fun i => y i.1))) *
        inner ℂ ((complementData E S).basis (fun i => x i.1))
          ((complementData E S).basis (fun i => y i.1)) := by
      rw [← (supportSplit E S).inner_map_map, supportSplit_productBasis,
        supportSplit_embedOn, supportSplit_productBasis, TensorProduct.map_tmul,
        LinearMap.id_apply, TensorProduct.inner_tmul]
    _ = LinearMap.toMatrix (supportData E S).basis.toBasis (supportData E S).basis.toBasis
          A (fun i => x i.1) (fun i => y i.1) *
        (if (fun i : {i : Fin n // i ∉ S} => x i.1) =
          (fun i : {i : Fin n // i ∉ S} => y i.1) then 1 else 0) := by
      rw [OrthonormalBasis.inner_eq_ite, ← matrix_coeff_eq_inner]
    _ = _ := by
      by_cases hs : ∀ i, i ∉ S → x i = y i
      · rw [if_pos hs, if_pos (hcomp.mpr hs), mul_one]
      · have hc : (fun i : {i : Fin n // i ∉ S} => x i.1) ≠
            (fun i : {i : Fin n // i ∉ S} => y i.1) := fun he => hs (hcomp.mp he)
        rw [if_neg hs, if_neg hc, mul_zero]

#print axioms CriticalDepth.ReviewV2.HilbertLocality.embedOn_toMatrix_apply

end CriticalDepth.ReviewV2.HilbertLocality

end
end Merged_HilbertLocality

/- ===== Source block: HilbertMatrixTransport; SHA-256 6017379ae38a46182db26dc739b3516b00ec32c44a76ae10af72a9e63821822a ===== -/
section Merged_HilbertMatrixTransport
/-!
# Operator, locality and encoding transport to the native matrix theorem

The source encoding is a Mathlib LinearIsometry on arbitrary finite complex
carriers. The physical coordinates are the constructed product basis. No
matrix code, basis choice, or locality-transport premise is supplied by a caller.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertMatrixTransport

open HilbertRegister
open scoped TensorProduct Kronecker Classical

universe u v w

variable {n : ℕ} (E : Fin n → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

abbrev siteDims : Fin n → ℕ := fun i => Module.finrank ℂ (E i)

def physicalOperators :
    ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) ≃⋆ₐ[ℂ]
      Matrix (Manuscript.PhysicalBasis n (siteDims E))
        (Manuscript.PhysicalBasis n (siteDims E)) ℂ :=
  LinearMap.toMatrixOrthonormal (registerFin E).basis

def localOperators (S : Finset (Fin n)) :
    ((supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier) ≃⋆ₐ[ℂ]
      Matrix (Manuscript.LocalBasis (siteDims E) S) (Manuscript.LocalBasis (siteDims E) S) ℂ :=
  LinearMap.toMatrixOrthonormal (supportData E S).basis

set_option maxRecDepth 2048 in
theorem physicalOperators_apply
    (O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) :
    physicalOperators E O =
      LinearMap.toMatrix (registerFin E).basis.toBasis (registerFin E).basis.toBasis O := by
  unfold physicalOperators
  ext i j
  exact (LinearMap.toMatrixOrthonormal_apply_apply (registerFin E).basis O i j).trans
    (HilbertLocality.matrix_coeff_eq_inner (registerFin E).basis O i j).symm

set_option maxRecDepth 2048 in
theorem localOperators_apply (S : Finset (Fin n))
    (A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier) :
    localOperators E S A =
      LinearMap.toMatrix (supportData E S).basis.toBasis (supportData E S).basis.toBasis A := by
  unfold localOperators
  ext i j
  exact (LinearMap.toMatrixOrthonormal_apply_apply (supportData E S).basis A i j).trans
    (HilbertLocality.matrix_coeff_eq_inner (supportData E S).basis A i j).symm

set_option maxRecDepth 2048 in
theorem local_embedding_coordinates (S : Finset (Fin n))
    (A : (supportData E S).carrier →ₗ[ℂ] (supportData E S).carrier) :
    physicalOperators E (HilbertLocality.embedOn E S A) =
      Manuscript.localEmbed S (localOperators E S A) := by
  rw [physicalOperators_apply E (HilbertLocality.embedOn E S A), localOperators_apply E S A]
  ext x y
  have h := HilbertLocality.embedOn_toMatrix_apply E S A x y
  by_cases hxy : ∀ i, i ∉ S → x i = y i
  · rw [if_pos hxy] at h
    simpa only [Manuscript.localEmbed, if_pos hxy] using h
  · rw [if_neg hxy] at h
    simpa only [Manuscript.localEmbed, if_neg hxy] using h

theorem supported_iff_coordinates
    (O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) (S : Finset (Fin n)) :
    HilbertLocality.SupportedOn E O S ↔ Manuscript.SupportedOn (physicalOperators E O) S := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨localOperators E S A, local_embedding_coordinates E S A⟩
  · rintro ⟨A, hA⟩
    let T := (localOperators E S).symm A
    refine ⟨T, (physicalOperators E).injective ?_⟩
    change physicalOperators E O = physicalOperators E (HilbertLocality.embedOn E S T)
    rw [local_embedding_coordinates E S T]
    have hT : localOperators E S T = A := (localOperators E S).apply_symm_apply A
    rw [hT]
    exact hA

variable {E}

/-- Standard unitary groups are transported by a star-algebra equivalence. -/
def coordinateUnitaries {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ H) :
    unitary (H →ₗ[ℂ] H) ≃* Matrix.unitaryGroup ι ℂ :=
  let e := LinearMap.toMatrixOrthonormal b
  { toFun U := ⟨e U.val, Unitary.map_mem e U.property⟩
    invFun U := ⟨e.symm U.val, Unitary.map_mem e.symm U.property⟩
    left_inv U := Subtype.ext (e.symm_apply_apply U.val)
    right_inv U := Subtype.ext (e.apply_symm_apply U.val)
    map_mul' U V := Subtype.ext (e.map_mul U.val V.val) }

@[simp] theorem coordinateUnitaries_val {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℂ H)
    (U : unitary (H →ₗ[ℂ] H)) :
    ((coordinateUnitaries b U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) =
      LinearMap.toMatrix b.toBasis b.toBasis U.val := rfl

theorem compression_coordinates {H J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [NormedAddCommGroup J] [InnerProductSpace ℂ J] [FiniteDimensional ℂ J]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bH : OrthonormalBasis ι ℂ H) (bJ : OrthonormalBasis κ ℂ J)
    (V : H →ₗ[ℂ] J) (O : J →ₗ[ℂ] J) :
    LinearMap.toMatrix bH.toBasis bH.toBasis ((LinearMap.adjoint V).comp (O.comp V)) =
      (LinearMap.toMatrix bH.toBasis bJ.toBasis V).conjTranspose *
        LinearMap.toMatrix bJ.toBasis bJ.toBasis O *
        LinearMap.toMatrix bH.toBasis bJ.toBasis V := by
  rw [LinearMap.toMatrix_comp bH.toBasis bJ.toBasis bH.toBasis,
    LinearMap.toMatrix_comp bH.toBasis bJ.toBasis bJ.toBasis,
    LinearMap.toMatrix_adjoint bH bJ]
  exact (Matrix.mul_assoc _ _ _).symm

variable (E)
variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [FiniteDimensional ℂ L]
variable {G : Type w} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [FiniteDimensional ℂ G]

local instance tensorFinite : FiniteDimensional ℂ (L ⊗[ℂ] G) :=
  ((stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)).toBasis.finiteDimensional_of_finite

def encodingMatrix (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) :
    Matrix (Manuscript.PhysicalBasis n (siteDims E))
      (Fin (Module.finrank ℂ L) × Fin (Module.finrank ℂ G)) ℂ :=
  LinearMap.toMatrix
    ((stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)).toBasis
    (registerFin E).basis.toBasis V.toLinearMap

theorem encodingMatrix_isometry
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) :
    (encodingMatrix E V).conjTranspose * encodingMatrix E V = 1 :=
  HilbertCoordinates.isometric_encoding_matrix
    ((stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G))
    (registerFin E).basis V

def GaugeOnly (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier)
    (O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) : Prop :=
  ∃ M : G →ₗ[ℂ] G,
    (LinearMap.adjoint V.toLinearMap).comp (O.comp V.toLinearMap) =
      TensorProduct.map LinearMap.id M

def DetectsBelow (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card < d →
    ∀ O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier,
      HilbertLocality.SupportedOn E O S → GaugeOnly E V O

theorem gauge_tensor_coordinates (M : G →ₗ[ℂ] G) :
    LinearMap.toMatrix
      ((stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)).toBasis
      ((stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)).toBasis
      (TensorProduct.map (LinearMap.id : L →ₗ[ℂ] L) M) =
      (1 : Matrix (Fin (Module.finrank ℂ L)) (Fin (Module.finrank ℂ L)) ℂ) ⊗ₖ
        HilbertCoordinates.operatorCoordinates G M := by
  rw [HilbertCoordinates.tensor_map_coordinates
    (stdOrthonormalBasis ℂ L) (stdOrthonormalBasis ℂ G), LinearMap.toMatrix_id]
  rfl

theorem gaugeOnly_iff_coordinates
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier)
    (O : (registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) :
    GaugeOnly E V O ↔ NativeGaugeOnly (encodingMatrix E V) (physicalOperators E O) := by
  let b := (stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)
  let e := LinearMap.toMatrix b.toBasis b.toBasis
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨HilbertCoordinates.operatorCoordinates G M, ?_⟩
    have he := congrArg e hM
    change LinearMap.toMatrix b.toBasis b.toBasis _ =
      LinearMap.toMatrix b.toBasis b.toBasis _ at he
    rw [compression_coordinates b (registerFin E).basis,
      gauge_tensor_coordinates (L := L) (G := G)] at he
    exact he
  · rintro ⟨M, hM⟩
    let T := (HilbertCoordinates.operatorCoordinates G).symm M
    refine ⟨T, e.injective ?_⟩
    change LinearMap.toMatrix b.toBasis b.toBasis _ =
      LinearMap.toMatrix b.toBasis b.toBasis _
    rw [compression_coordinates b (registerFin E).basis,
      gauge_tensor_coordinates (L := L) (G := G)]
    have hT : HilbertCoordinates.operatorCoordinates G T = M :=
      (HilbertCoordinates.operatorCoordinates G).apply_symm_apply M
    rw [hT]
    rw [physicalOperators_apply E O] at hM
    simpa only [b, encodingMatrix] using hM

theorem detectsBelow_iff_coordinates
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) (d : ℕ) :
    DetectsBelow E V d ↔ NativeDetectsBelow (encodingMatrix E V) d := by
  constructor
  · intro hd S hS O hO
    let T := (physicalOperators E).symm O
    have hTs : HilbertLocality.SupportedOn E T S := by
      apply (supported_iff_coordinates E T S).mpr
      simpa [T] using hO
    have hT := (gaugeOnly_iff_coordinates E V T).mp (hd S hS T hTs)
    simpa [T] using hT
  · intro hd S hS O hO
    exact (gaugeOnly_iff_coordinates E V O).mpr
      (hd S hS (physicalOperators E O) ((supported_iff_coordinates E O S).mp hO))

#print axioms CriticalDepth.ReviewV2.HilbertMatrixTransport.supported_iff_coordinates
#print axioms CriticalDepth.ReviewV2.HilbertMatrixTransport.detectsBelow_iff_coordinates

end CriticalDepth.ReviewV2.HilbertMatrixTransport

end
end Merged_HilbertMatrixTransport

/- ===== Source block: HilbertCircuitTransport; SHA-256 f200aafc2a1dd9e766aa5cf6148701a4395324e613a4fe2b1aa1abecc178de68 ===== -/
section Merged_HilbertCircuitTransport
/-!
# Arbitrary-carrier finite circuits and the transported first theorem

Physical and logical operators are Mathlib linear maps and standard unitary
groups. Every coordinate map is constructed from local product bases or an
automatic logical/gauge orthonormal basis. The logical output lies directly
in Mathlib's matrix-unitary quotient PU(finrank L). The proof transports all
finite gate lists, supported operators, encodings and depth budgets both ways.
-/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertCircuitTransport

open HilbertRegister HilbertMatrixTransport
open scoped TensorProduct Kronecker Classical

universe u v w

variable {n : ℕ} (E : Fin n → Type u)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

abbrev GateData := Finset (Fin n) ×
  unitary ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier)
abbrev Layer := List (GateData E)
abbrev Circuit (r : ℕ) := Fin r → Layer E

def GateAllowed (q : ℕ) (G : GateData E) : Prop :=
  G.1.card ≤ q ∧ HilbertLocality.SupportedOn E G.2.val G.1

def LayerAllowed (q : ℕ) (L : Layer E) : Prop :=
  (∀ G ∈ L, GateAllowed E q G) ∧ L.Pairwise (fun G H => Disjoint G.1 H.1)

def CircuitAllowed {r : ℕ} (q : ℕ) (c : Circuit E r) : Prop :=
  ∀ i, LayerAllowed E q (c i)

def layerEval (L : Layer E) : unitary ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) :=
  (L.map Prod.snd).reverse.prod

def circuitEval {r : ℕ} (c : Circuit E r) :
    unitary ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier) :=
  (List.ofFn fun i => layerEval E (c i)).reverse.prod

def gateToNative (G : GateData E) : NativeGateData n (siteDims E) :=
  (G.1, coordinateUnitaries (registerFin E).basis G.2)

def gateFromNative (G : NativeGateData n (siteDims E)) : GateData E :=
  (G.1, (coordinateUnitaries (registerFin E).basis).symm G.2)

@[simp] theorem gateToNative_from (G : NativeGateData n (siteDims E)) :
    gateToNative E (gateFromNative E G) = G := by
  simp [gateToNative, gateFromNative]

@[simp] theorem gateFromNative_to (G : GateData E) :
    gateFromNative E (gateToNative E G) = G := by
  simp [gateToNative, gateFromNative]

def layerToNative (L : Layer E) : NativeLayer n (siteDims E) := L.map (gateToNative E)
def layerFromNative (L : NativeLayer n (siteDims E)) : Layer E := L.map (gateFromNative E)
def circuitToNative {r : ℕ} (c : Circuit E r) : NativeCircuit n (siteDims E) r :=
  fun i => layerToNative E (c i)
def circuitFromNative {r : ℕ} (c : NativeCircuit n (siteDims E) r) : Circuit E r :=
  fun i => layerFromNative E (c i)

@[simp] theorem layerToNative_from (L : NativeLayer n (siteDims E)) :
    layerToNative E (layerFromNative E L) = L := by
  simp [layerToNative, layerFromNative, List.map_map, Function.comp_def]

@[simp] theorem layerFromNative_to (L : Layer E) :
    layerFromNative E (layerToNative E L) = L := by
  simp [layerToNative, layerFromNative, List.map_map, Function.comp_def]

@[simp] theorem circuitToNative_from {r : ℕ} (c : NativeCircuit n (siteDims E) r) :
    circuitToNative E (circuitFromNative E c) = c := by
  funext i
  exact layerToNative_from E (c i)

@[simp] theorem circuitFromNative_to {r : ℕ} (c : Circuit E r) :
    circuitFromNative E (circuitToNative E c) = c := by
  funext i
  exact layerFromNative_to E (c i)

theorem gateAllowed_iff (q : ℕ) (G : GateData E) :
    GateAllowed E q G ↔ NativeGateAllowed q (gateToNative E G) := by
  change (G.1.card ≤ q ∧ HilbertLocality.SupportedOn E G.2.val G.1) ↔
    (G.1.card ≤ q ∧ Manuscript.SupportedOn (physicalOperators E G.2.val) G.1)
  exact and_congr Iff.rfl (supported_iff_coordinates E G.2.val G.1)

theorem layerAllowed_iff (q : ℕ) (L : Layer E) :
    LayerAllowed E q L ↔ NativeLayerAllowed q (layerToNative E L) := by
  constructor
  · rintro ⟨hG, hd⟩
    constructor
    · intro G hmem
      obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hmem
      exact (gateAllowed_iff E q H).mp (hG H hH)
    · exact List.pairwise_map.mpr hd
  · rintro ⟨hG, hd⟩
    constructor
    · intro G hmem
      exact (gateAllowed_iff E q G).mpr
        (hG (gateToNative E G) (List.mem_map.mpr ⟨G, hmem, rfl⟩))
    · change (L.map (gateToNative E)).Pairwise
        (fun G H : NativeGateData n (siteDims E) => Disjoint G.1 H.1) at hd
      rw [List.pairwise_map] at hd
      exact hd

theorem circuitAllowed_iff {r : ℕ} (q : ℕ) (c : Circuit E r) :
    CircuitAllowed E q c ↔ NativeCircuitAllowed q (circuitToNative E c) := by
  constructor
  · intro hc i
    exact (layerAllowed_iff E q (c i)).mp (hc i)
  · intro hc i
    exact (layerAllowed_iff E q (c i)).mpr (hc i)

theorem map_list_prod {A B : Type*} [Monoid A] [Monoid B] (f : A ≃* B) (L : List A) :
    f L.prod = (L.map f).prod := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.prod_cons, List.map_cons, map_mul, ih]

theorem layerEval_coordinates (L : Layer E) :
    coordinateUnitaries (registerFin E).basis (layerEval E L) =
      nativeLayerEval (layerToNative E L) := by
  unfold layerEval nativeLayerEval layerToNative
  rw [map_list_prod]
  simp only [List.map_reverse, List.map_map, Function.comp_def, gateToNative]

theorem circuitEval_coordinates {r : ℕ} (c : Circuit E r) :
    coordinateUnitaries (registerFin E).basis (circuitEval E c) =
      nativeCircuitEval (circuitToNative E c) := by
  unfold circuitEval nativeCircuitEval circuitToNative
  rw [map_list_prod]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_def, layerEval_coordinates]

variable {L : Type v} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [FiniteDimensional ℂ L]
variable {G : Type w} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [FiniteDimensional ℂ G]

def Implements (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier)
    (U : unitary ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier))
    (W : unitary (L →ₗ[ℂ] L)) (Z : unitary (G →ₗ[ℂ] G)) : Prop :=
  U.val.comp V.toLinearMap = V.toLinearMap.comp (TensorProduct.map W.val Z.val)

theorem implements_iff_coordinates
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier)
    (U : unitary ((registerFin E).carrier →ₗ[ℂ] (registerFin E).carrier))
    (W : unitary (L →ₗ[ℂ] L)) (Z : unitary (G →ₗ[ℂ] G)) :
    Implements E V U W Z ↔
      ((coordinateUnitaries (registerFin E).basis U : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          encodingMatrix E V =
        encodingMatrix E V *
          (((coordinateUnitaries (stdOrthonormalBasis ℂ L) W : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) ⊗ₖ
            ((coordinateUnitaries (stdOrthonormalBasis ℂ G) Z : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  let b := (stdOrthonormalBasis ℂ L).tensorProduct (stdOrthonormalBasis ℂ G)
  let e := LinearMap.toMatrix b.toBasis (registerFin E).basis.toBasis
  constructor
  · intro hi
    have he := congrArg e hi
    change LinearMap.toMatrix b.toBasis (registerFin E).basis.toBasis _ =
      LinearMap.toMatrix b.toBasis (registerFin E).basis.toBasis _ at he
    rw [LinearMap.toMatrix_comp b.toBasis (registerFin E).basis.toBasis (registerFin E).basis.toBasis,
      LinearMap.toMatrix_comp b.toBasis b.toBasis (registerFin E).basis.toBasis,
      HilbertCoordinates.tensor_map_coordinates
        (stdOrthonormalBasis ℂ L) (stdOrthonormalBasis ℂ G)] at he
    exact he
  · intro he
    apply e.injective
    change LinearMap.toMatrix b.toBasis (registerFin E).basis.toBasis _ =
      LinearMap.toMatrix b.toBasis (registerFin E).basis.toBasis _
    rw [LinearMap.toMatrix_comp b.toBasis (registerFin E).basis.toBasis (registerFin E).basis.toBasis,
      LinearMap.toMatrix_comp b.toBasis b.toBasis (registerFin E).basis.toBasis,
      HilbertCoordinates.tensor_map_coordinates
        (stdOrthonormalBasis ℂ L) (stdOrthonormalBasis ℂ G)]
    exact he

def logicalImage (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) (q h : ℕ) :
    Set (PU (Fin (Module.finrank ℂ L))) :=
  {a | ∃ r : ℕ, r ≤ h ∧ ∃ c : Circuit E r, CircuitAllowed E q c ∧
    ∃ W : unitary (L →ₗ[ℂ] L), ∃ Z : unitary (G →ₗ[ℂ] G),
      Implements E V (circuitEval E c) W Z ∧
        projectiveMk (ι := Fin (Module.finrank ℂ L))
          (coordinateUnitaries (stdOrthonormalBasis ℂ L) W) = a}

theorem logicalImage_eq_native
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier) (q h : ℕ) :
    logicalImage E V q h = nativeLogicalImage (encodingMatrix E V) q h := by
  ext a
  constructor
  · rintro ⟨r, hr, c, hc, W, Z, hi, hclass⟩
    refine ⟨r, hr, circuitToNative E c, (circuitAllowed_iff E q c).mp hc,
      coordinateUnitaries (stdOrthonormalBasis ℂ L) W,
      coordinateUnitaries (stdOrthonormalBasis ℂ G) Z, ?_, hclass⟩
    have hm := (implements_iff_coordinates E V (circuitEval E c) W Z).mp hi
    rw [circuitEval_coordinates] at hm
    exact hm
  · rintro ⟨r, hr, c, hc, W, Z, hi, hclass⟩
    let c' := circuitFromNative E c
    let W' := (coordinateUnitaries (stdOrthonormalBasis ℂ L)).symm W
    let Z' := (coordinateUnitaries (stdOrthonormalBasis ℂ G)).symm Z
    have hcn : circuitToNative E c' = c := circuitToNative_from E c
    have hc' : CircuitAllowed E q c' :=
      (circuitAllowed_iff E q c').mpr (by simpa only [hcn] using hc)
    refine ⟨r, hr, c', hc', W', Z', ?_, ?_⟩
    · apply (implements_iff_coordinates E V (circuitEval E c') W' Z').mpr
      rw [circuitEval_coordinates, hcn]
      simpa [W', Z'] using hi
    · simpa [W'] using hclass

/-- The first manuscript theorem for arbitrary finite local, logical and gauge
Hilbert carriers. Every adapter is proved above; none is an input hypothesis. -/
theorem theoremOne_arbitrary_carriers
    (hn : 1 ≤ n) (hL : 2 ≤ Module.finrank ℂ L) (hG : 1 ≤ Module.finrank ℂ G)
    (d : ℕ) (hd : 2 ≤ d)
    (V : (L ⊗[ℂ] G) →ₗᵢ[ℂ] (registerFin E).carrier)
    (hdetect : HilbertMatrixTransport.DetectsBelow E V d)
    (q h : ℕ) (hq : 2 ≤ q) (hp : 1 ≤ h) (hb : h < Arithmetic.criticalDepth q d) :
    (logicalImage E V q h).Finite ∧ ¬ Dense (logicalImage E V q h) := by
  rw [logicalImage_eq_native]
  exact nativeTheoremOne_proved n (Module.finrank ℂ L) (Module.finrank ℂ G) d
    (siteDims E) hn hL hG hd (encodingMatrix E V) (encodingMatrix_isometry E V)
    ((detectsBelow_iff_coordinates E V d).mp hdetect) q h hq hp hb

#print axioms CriticalDepth.ReviewV2.HilbertCircuitTransport.logicalImage_eq_native
#print axioms CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers

end CriticalDepth.ReviewV2.HilbertCircuitTransport

end
end Merged_HilbertCircuitTransport

/- ===== Source block: HilbertPhase; SHA-256 c29f01253c3e55f03b41e9551ea5b3f71b9028cbdaead4cf116c8a024ffe7ca9 ===== -/
section Merged_HilbertPhase
/-! The automatic logical coordinate class removes exactly one global
Mathlib-unitary complex scalar, for arbitrary finite logical carriers. -/

noncomputable section

namespace CriticalDepth.ReviewV2.HilbertPhase

open HilbertMatrixTransport

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [FiniteDimensional ℂ L]

theorem logicalClass_eq_iff (U V : unitary (L →ₗ[ℂ] L)) :
    projectiveMk (ι := Fin (Module.finrank ℂ L))
        (coordinateUnitaries (stdOrthonormalBasis ℂ L) U) =
      projectiveMk (ι := Fin (Module.finrank ℂ L))
        (coordinateUnitaries (stdOrthonormalBasis ℂ L) V) ↔
      ∃ z : unitary ℂ, U.val = (z : ℂ) • V.val := by
  rw [projectiveMk_eq_iff (ι := Fin (Module.finrank ℂ L))]
  change (∃ z : ℂ, star z * z = 1 ∧
    HilbertCoordinates.operatorCoordinates L U.val =
      z • HilbertCoordinates.operatorCoordinates L V.val) ↔ _
  constructor
  · rintro ⟨z, hz, he⟩
    let w : unitary ℂ := ⟨z, hz, by simpa only [mul_comm] using hz⟩
    exact (HilbertCoordinates.operatorCoordinates_phase_iff L U.val V.val).mpr ⟨w, he⟩
  · intro he
    obtain ⟨z, hz⟩ := (HilbertCoordinates.operatorCoordinates_phase_iff L U.val V.val).mp he
    exact ⟨(z : ℂ), z.property.1, hz⟩

#print axioms CriticalDepth.ReviewV2.HilbertPhase.logicalClass_eq_iff

end CriticalDepth.ReviewV2.HilbertPhase

end
end Merged_HilbertPhase

/- ===== Source block: FiveQubitExample; SHA-256 62c49846493e901975cba031009add10f8351c8e915b89e6e08d3d319c022470 ===== -/
section Merged_FiveQubitExample
/-!
# A closed five-qubit distance-three example

The computational basis is the unchanged five-qubit tensor basis. The encoding
has two columns and rational entries `0`, `1/4`, and `-1/4`. Its rows are
coordinatized by a logical parity bit and four generator bits; this is an
explicit bijection of all 32 physical basis vectors, not a restricted carrier.

The four usual stabilizer generators fix both encoding columns. A finite
integer syndrome certificate shows that every nonidentity Pauli of weight less
than three anticommutes with one of those generators. The existing complex
Pauli-span theorem then supplies detection for *every* supported operator.
An explicit weight-three operator supplies the opposite distance inequality.
The final declarations call the actual positive-depth Theorem 1 at budgets
one and two, with no code or distance hypothesis left as a parameter.

This file is a source candidate until the coordinator records compilation and
recursive axiom-audit results for its exact bytes. It does not construct the
separate subgroup/fixed-space package required by `IsStabilizer`.
-/

noncomputable section

namespace CriticalDepth.Manuscript.FiveQubit

open Matrix CriticalDepth.ReviewV2.PauliRowAction
open scoped BigOperators Kronecker

abbrev Orbit := Fin 4 → Fin 2

/-- Numerical normalization on bits must use their characteristic-two
arithmetic, rather than leave a ring-normalized `-1` representative. -/
@[simp] theorem bit_neg_one : (-1 : Fin 2) = 1 := by decide

@[simp] theorem bit_one_add_one : (1 : Fin 2) + 1 = 0 := by decide

def orbitWord (t : Orbit) : QubitBasis 5 :=
  ![t 0 + t 2, t 1 + t 3, t 2, t 0 + t 3, t 1]

def encodedWord (logical : Fin 2) (t : Orbit) : QubitBasis 5 :=
  fun i => orbitWord t i + logical

def wordParity (x : QubitBasis 5) : Fin 2 := ∑ i, x i

def orbitInverse (x : QubitBasis 5) : Fin 2 × Orbit :=
  let logical := wordParity x
  let y : QubitBasis 5 := fun i => x i + logical
  (logical, ![y 0 + y 2, y 4, y 2, y 1 + y 4])

set_option maxRecDepth 100000 in
def orbitEquiv : (Fin 2 × Orbit) ≃ QubitBasis 5 where
  toFun p := encodedWord p.1 p.2
  invFun := orbitInverse
  left_inv := by decide
  right_inv := by decide

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT orbitEquiv elaborated"

/-- The 16 generator-bit words, used only to expand finite sums and examples. -/
def orbitEnumeration : Fin 16 → Orbit :=
  ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1],
    ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 1, 1, 1],
    ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1],
    ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]]

set_option maxRecDepth 100000 in
theorem orbitEnumeration_bijective : Function.Bijective orbitEnumeration := by decide

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT orbitEnumeration_bijective elaborated"

theorem sum_orbit (f : Orbit → ℂ) :
    (∑ t : Orbit, f t) = ∑ u : Fin 16, f (orbitEnumeration u) := by
  exact (Fintype.sum_bijective orbitEnumeration orbitEnumeration_bijective
    (fun u => f (orbitEnumeration u)) f (fun _ => rfl)).symm

def amplitude (t : Orbit) : ℂ :=
  (-1 : ℂ) ^ ((∑ i : Fin 4, (t i).val).choose 2) / 4

def signInteger (t : Orbit) : ℤ :=
  (-1 : ℤ) ^ ((∑ i : Fin 4, (t i).val).choose 2)

theorem amplitude_eq_cast_sign (t : Orbit) :
    amplitude t = (signInteger t : ℂ) / 4 := by
  simp [amplitude, signInteger]

theorem card_orbit : Fintype.card Orbit = 16 := by
  norm_num [Orbit, Fintype.card_fun]

theorem amplitude_star_mul (t : Orbit) :
    star (amplitude t) * amplitude t = (1 / 16 : ℂ) := by
  have hstar : star (amplitude t) = amplitude t := by simp [amplitude]
  rw [hstar]
  unfold amplitude
  rw [div_mul_div_comm, ← mul_pow]
  norm_num

def encoding : Matrix (QubitBasis 5) (Fin 2 × Fin 1) ℂ :=
  fun x j =>
    if (orbitEquiv.symm x).1 = j.1 then amplitude (orbitEquiv.symm x).2 else 0

@[simp] theorem encoding_at_orbit (logical : Fin 2) (t : Orbit)
    (j : Fin 2 × Fin 1) :
    encoding (orbitEquiv (logical, t)) j =
      if logical = j.1 then amplitude t else 0 := by
  simp [encoding]

theorem encoding_isometry : encoding.conjTranspose * encoding = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a
  fin_cases b
  change (∑ x : QubitBasis 5, star (encoding x (i, 0)) * encoding x (j, 0)) =
    (1 : Operator (Fin 2 × Fin 1)) (i, 0) (j, 0)
  rw [← orbitEquiv.sum_comp
    (fun x => star (encoding x (i, 0)) * encoding x (j, 0)),
    Fintype.sum_prod_type]
  simp only [encoding_at_orbit]
  by_cases hij : i = j
  · subst j
    have hpoint (logical : Fin 2) (t : Orbit) :
        star (if logical = i then amplitude t else 0) *
            (if logical = i then amplitude t else 0) =
          if logical = i then (1 / 16 : ℂ) else 0 := by
      by_cases h : logical = i
      · simp only [if_pos h]
        exact amplitude_star_mul t
      · simp [h]
    simp_rw [hpoint]
    rw [Finset.sum_comm]
    norm_num [card_orbit, Matrix.one_apply]
  · have hpoint (logical : Fin 2) (t : Orbit) :
        star (if logical = i then amplitude t else 0) *
            (if logical = j then amplitude t else 0) = 0 := by
      by_cases hi : logical = i
      · subst logical
        simp [hij]
      · simp [hi]
    simp_rw [hpoint]
    simp [Matrix.one_apply, hij]

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT encoding_isometry elaborated"

def code : Code 5 (fun _ => 2) 2 1 where
  encoding := encoding
  isometry := encoding_isometry

/-- `XZZXI`, `IXZZX`, `XIXZZ`, and `ZXIXZ`, in the physical-site order. -/
def generator : Fin 4 → Fin 5 → SinglePauli :=
  ![![.X, .Z, .Z, .X, .I], ![.I, .X, .Z, .Z, .X],
    ![.X, .I, .X, .Z, .Z], ![.Z, .X, .I, .X, .Z]]

def flipOrbitBit (r : Fin 4) (t : Orbit) : Orbit :=
  fun i => if i = r then 1 - t i else t i

def singleRealInteger (p : SinglePauli) (x : Fin 2) : ℤ :=
  match p with
  | .I | .X => 1
  | .Y => 0
  | .Z => if x = 0 then 1 else -1

def generatorRowInteger (r : Fin 4) (x : QubitBasis 5) : ℤ :=
  ∏ i : Fin 5, singleRealInteger (generator r i) (x i)

theorem singleCoefficient_cast (p : SinglePauli) (x : Fin 2) (hp : p ≠ .Y) :
    singleCoefficient p x = (singleRealInteger p x : ℂ) := by
  cases p <;> by_cases hx : x = 0 <;>
    simp_all [singleCoefficient, singleRealInteger]

theorem generator_has_no_Y : ∀ (r : Fin 4) (i : Fin 5), generator r i ≠ .Y := by
  decide

theorem generator_rowCoefficient_cast (r : Fin 4) (x : QubitBasis 5) :
    rowCoefficient (generator r) x = (generatorRowInteger r x : ℂ) := by
  simp only [rowCoefficient, generatorRowInteger, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact singleCoefficient_cast (generator r i) (x i) (generator_has_no_Y r i)

/- Pure bit arithmetic; no complex matrices are normalized in this certificate. -/
set_option maxRecDepth 1000000 in
theorem generator_flip_word :
    ∀ (r : Fin 4) (logical : Fin 2) (t : Orbit),
      flipWord (generator r) (encodedWord logical t) =
        encodedWord logical (flipOrbitBit r t) := by
  decide

set_option maxRecDepth 1000000 in
theorem generator_integer_cocycle :
    ∀ (r : Fin 4) (logical : Fin 2) (t : Orbit),
      generatorRowInteger r (encodedWord logical t) * signInteger (flipOrbitBit r t) =
        signInteger t := by
  decide

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT generator integer certificates elaborated"

theorem generator_amplitude_cocycle (r : Fin 4) (logical : Fin 2) (t : Orbit) :
    rowCoefficient (generator r) (encodedWord logical t) * amplitude (flipOrbitBit r t) =
      amplitude t := by
  simp only [generator_rowCoefficient_cast, amplitude_eq_cast_sign]
  have h := congrArg (fun z : ℤ => (z : ℂ) / 4)
    (generator_integer_cocycle r logical t)
  simpa only [Int.cast_mul, mul_div_assoc] using h

/-- A reindexed matrix product, before any finite arithmetic is performed. -/
theorem pauli_encoding_entry (p : Fin 5 → SinglePauli)
    (logical : Fin 2) (t : Orbit) (j : Fin 2 × Fin 1) :
    (pauliMatrix 0 p * encoding) (orbitEquiv (logical, t)) j =
      ∑ a : Fin 2, ∑ u : Fin 16,
        pauliMatrix 0 p (encodedWord logical t) (encodedWord a (orbitEnumeration u)) *
          (if a = j.1 then amplitude (orbitEnumeration u) else 0) := by
  change (∑ y : QubitBasis 5,
    pauliMatrix 0 p (orbitEquiv (logical, t)) y * encoding y j) = _
  rw [← orbitEquiv.sum_comp (fun y =>
    pauliMatrix 0 p (orbitEquiv (logical, t)) y * encoding y j),
    Fintype.sum_prod_type]
  simp only [encoding_at_orbit]
  simp_rw [sum_orbit]
  rfl

theorem generator_fixes (r : Fin 4) :
    pauliMatrix 0 (generator r) * encoding = encoding := by
  ext x j
  obtain ⟨⟨logical, t⟩, rfl⟩ := orbitEquiv.surjective x
  rw [pauliMatrix_mul_apply]
  change rowCoefficient (generator r) (encodedWord logical t) *
    encoding (flipWord (generator r) (encodedWord logical t)) j =
      encoding (encodedWord logical t) j
  rw [generator_flip_word]
  change rowCoefficient (generator r) (encodedWord logical t) *
    encoding (orbitEquiv (logical, flipOrbitBit r t)) j =
      encoding (orbitEquiv (logical, t)) j
  simp only [encoding_at_orbit]
  by_cases h : logical = j.1
  · simp only [if_pos h]
    exact generator_amplitude_cocycle r logical t
  · simp [h]

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT generator_fixes elaborated"

/-- Integer-valued signs keep the exhaustive certificate independent of
decidability of complex equality. -/
def commutationInteger (p q : SinglePauli) : ℤ :=
  if p = .I ∨ q = .I ∨ p = q then 1 else -1

theorem commutationSign_eq_cast (p q : SinglePauli) :
    p.commutationSign q = (commutationInteger p q : ℂ) := by
  cases p <;> cases q <;>
    norm_num [SinglePauli.commutationSign, commutationInteger]

set_option profiler true in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 8000000 in
theorem smallPauli_integer_certificate :
    ∀ p : Fin 5 → SinglePauli, (pauliSupport p).card < 3 →
      (∀ i, p i = .I) ∨
        ∃ r : Fin 4, (∏ i : Fin 5, commutationInteger (generator r i) (p i)) = -1 := by
  have htuple : ∀ a b c d e : SinglePauli,
      (pauliSupport (![a, b, c, d, e] : Fin 5 → SinglePauli)).card < 3 →
        (∀ i : Fin 5, (![a, b, c, d, e] : Fin 5 → SinglePauli) i = .I) ∨
          ∃ r : Fin 4, (∏ i : Fin 5,
            commutationInteger (generator r i)
              ((![a, b, c, d, e] : Fin 5 → SinglePauli) i)) = -1 := by
    intro a b c d e
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
  intro p
  have hp : (![p 0, p 1, p 2, p 3, p 4] : Fin 5 → SinglePauli) = p := by
    funext i
    fin_cases i <;> rfl
  simpa only [hp] using htuple (p 0) (p 1) (p 2) (p 3) (p 4)

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT smallPauli_integer_certificate elaborated"

theorem smallPauli_gaugeOnly (p : Fin 5 → SinglePauli)
    (hp : (pauliSupport p).card < 3) : GaugeOnly code (pauliMatrix 0 p) := by
  obtain hidentity | ⟨r, hr⟩ := smallPauli_integer_certificate p hp
  · have hpidentity : p = fun _ => SinglePauli.I := funext hidentity
    rw [hpidentity, pauliMatrix_zero_eq_tensorEntries]
    change GaugeOnly code (tensorEntries (fun _ : Fin 5 => (1 : Operator (Fin 2))))
    rw [tensorEntries_one]
    refine ⟨1, ?_⟩
    simp [code, encoding_isometry]
  · have hsign : (∏ i : Fin 5, (generator r i).commutationSign (p i)) = (-1 : ℂ) := by
      calc
        _ = ((∏ i : Fin 5, commutationInteger (generator r i) (p i) : ℤ) : ℂ) := by
          simp only [commutationSign_eq_cast, Int.cast_prod]
        _ = -1 := by rw [hr]; norm_num
    have hanti : pauliMatrix 0 (generator r) * pauliMatrix 0 p =
        -(pauliMatrix 0 p * pauliMatrix 0 (generator r)) := by
      simpa only [hsign, neg_one_smul] using
        unphased_pauliMatrix_commutation (generator r) p
    exact anticommuting_fixed_operator_gaugeOnly code (pauliMatrix 0 p)
      (pauliMatrix 0 (generator r)) (unphased_pauliMatrix_isUnitary (generator r))
      (generator_fixes r) hanti

/-- Detection quantifies over all complex supported operators, with no Pauli
restriction on the operator supplied to this theorem. -/
theorem detectsBelow_three : DetectsBelow code 3 := by
  classical
  intro S hS O hO
  obtain ⟨A, hA⟩ := hO
  let B : Submodule ℂ (Operator (LocalBasis (fun _ : Fin 5 => 2) S)) :=
    (gaugeOnlyComplexSubmodule code).comap (localEmbedLinearMap S)
  have hPauli : ∀ p : S → SinglePauli,
      GaugeOnly code (pauliMatrix 0 (extendLocalPauli S p)) := by
    intro p
    apply smallPauli_gaugeOnly
    have hsubset : pauliSupport (extendLocalPauli S p) ⊆ S := by
      apply pauliSupport_subset_of_outside_identity
      intro i hi
      simp [extendLocalPauli, hi]
    exact (Finset.card_le_card hsubset).trans_lt hS
  have hspan : pauliTensorSpan S ≤ B := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change GaugeOnly code (localEmbed S (tensorPauli p))
    rw [← pauliMatrix_extendLocalPauli_eq_localEmbed S p]
    exact hPauli p
  rw [tensorPauli_span_eq_top] at hspan
  have hAB : A ∈ B := hspan (show A ∈ (⊤ : Submodule ℂ _) by trivial)
  change GaugeOnly code (localEmbed S A) at hAB
  simpa only [hA] using hAB

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT detectsBelow_three elaborated"

def weightThreePauli : Fin 5 → SinglePauli := ![.Y, .I, .I, .Y, .Z]

def logicalAction : Operator (Fin 2) := !![-1, 0; 0, 1]

def bitSignInteger (x : Fin 2) : ℤ := if x = 0 then 1 else -1

def weightThreeRowInteger (x : QubitBasis 5) : ℤ :=
  -(bitSignInteger (x 0) * bitSignInteger (x 3) * bitSignInteger (x 4))

def logicalSignInteger (logical : Fin 2) : ℤ := if logical = 0 then -1 else 1

theorem weightThree_rowCoefficient_cast (x : QubitBasis 5) :
    rowCoefficient weightThreePauli x = (weightThreeRowInteger x : ℂ) := by
  have htuple : ∀ a b c d e : Fin 2,
      rowCoefficient weightThreePauli (![a, b, c, d, e] : QubitBasis 5) =
        (weightThreeRowInteger (![a, b, c, d, e] : QubitBasis 5) : ℂ) := by
    intro a b c d e
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
      norm_num [rowCoefficient, weightThreePauli, Fin.prod_univ_succ,
        singleCoefficient, weightThreeRowInteger, bitSignInteger, Complex.I_mul_I]
  have hx : (![x 0, x 1, x 2, x 3, x 4] : QubitBasis 5) = x := by
    funext i
    fin_cases i <;> rfl
  simpa only [hx] using htuple (x 0) (x 1) (x 2) (x 3) (x 4)

theorem weightThree_flip_word (logical : Fin 2) (t : Orbit) :
    flipWord weightThreePauli (encodedWord logical t) =
      encodedWord logical (flipOrbitBit 0 t) := by
  have hflip : flipWord weightThreePauli (encodedWord logical t) =
      flipWord (generator 0) (encodedWord logical t) := by
    funext i
    fin_cases i <;> rfl
  rw [hflip, generator_flip_word]

set_option maxRecDepth 1000000 in
theorem weightThree_integer_cocycle :
    ∀ (logical : Fin 2) (t : Orbit),
      weightThreeRowInteger (encodedWord logical t) * signInteger (flipOrbitBit 0 t) =
        logicalSignInteger logical * signInteger t := by
  decide

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT weight-three integer certificate elaborated"

theorem weightThree_amplitude_cocycle (logical : Fin 2) (t : Orbit) :
    rowCoefficient weightThreePauli (encodedWord logical t) * amplitude (flipOrbitBit 0 t) =
      (logicalSignInteger logical : ℂ) * amplitude t := by
  simp only [weightThree_rowCoefficient_cast, amplitude_eq_cast_sign]
  have h := congrArg (fun z : ℤ => (z : ℂ) / 4)
    (weightThree_integer_cocycle logical t)
  simpa only [Int.cast_mul, mul_div_assoc] using h

theorem encoding_logicalAction_entry (x : QubitBasis 5) (j : Fin 2 × Fin 1) :
    (encoding * (logicalAction ⊗ₖ (1 : Operator (Fin 1)))) x j =
      (logicalSignInteger j.1 : ℂ) * encoding x j := by
  rcases j with ⟨j, a⟩
  fin_cases a
  fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ,
      logicalAction, logicalSignInteger, Matrix.kronecker_apply, Matrix.one_apply]

theorem weightThreePauli_action :
    pauliMatrix 0 weightThreePauli * encoding =
      encoding * (logicalAction ⊗ₖ (1 : Operator (Fin 1))) := by
  ext x j
  obtain ⟨⟨logical, t⟩, rfl⟩ := orbitEquiv.surjective x
  rw [pauliMatrix_mul_apply, encoding_logicalAction_entry]
  change rowCoefficient weightThreePauli (encodedWord logical t) *
    encoding (flipWord weightThreePauli (encodedWord logical t)) j =
      (logicalSignInteger j.1 : ℂ) * encoding (encodedWord logical t) j
  rw [weightThree_flip_word]
  change rowCoefficient weightThreePauli (encodedWord logical t) *
    encoding (orbitEquiv (logical, flipOrbitBit 0 t)) j =
      (logicalSignInteger j.1 : ℂ) * encoding (orbitEquiv (logical, t)) j
  simp only [encoding_at_orbit]
  by_cases h : logical = j.1
  · subst logical
    simp only [if_pos rfl]
    exact weightThree_amplitude_cocycle j.1 t
  · simp [h]

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT weightThreePauli_action elaborated"

theorem weightThreePauli_compression :
    encoding.conjTranspose * pauliMatrix 0 weightThreePauli * encoding =
      logicalAction ⊗ₖ (1 : Operator (Fin 1)) := by
  rw [Matrix.mul_assoc, weightThreePauli_action, ← Matrix.mul_assoc,
    encoding_isometry, Matrix.one_mul]

theorem weightThreePauli_supported :
    SupportedOn (pauliMatrix 0 weightThreePauli) ({0, 3, 4} : Finset (Fin 5)) := by
  apply pauliMatrix_supportedOn_of_outside_identity
  intro i hi
  fin_cases i <;> simp_all [weightThreePauli]

theorem weightThreePauli_nongauge : ¬ GaugeOnly code (pauliMatrix 0 weightThreePauli) := by
  rintro ⟨M, hM⟩
  change encoding.conjTranspose * pauliMatrix 0 weightThreePauli * encoding = _ at hM
  rw [weightThreePauli_compression] at hM
  have h0 := congrArg (fun A : Operator (Fin 2 × Fin 1) => A (0, 0) (0, 0)) hM
  have h1 := congrArg (fun A : Operator (Fin 2 × Fin 1) => A (1, 0) (1, 0)) hM
  have hneg : (-1 : ℂ) = M 0 0 := by
    simpa [logicalAction, Matrix.kronecker_apply] using h0
  have hpos : (1 : ℂ) = M 0 0 := by
    simpa [logicalAction, Matrix.kronecker_apply] using h1
  have hfalse : (-1 : ℂ) = 1 := hneg.trans hpos.symm
  norm_num at hfalse

theorem hasActualDistance_three : HasActualDistance code 3 := by
  refine ⟨detectsBelow_three, {0, 3, 4}, by decide,
    pauliMatrix 0 weightThreePauli, weightThreePauli_supported,
    weightThreePauli_nongauge⟩

theorem binary_criticalDepth : Arithmetic.criticalDepth 2 3 = 3 := by decide

/-- A closed positive-budget call with an actually constructed encoding and
a proved all-operator distance-detection premise. -/
theorem depthOne_finite_nondense :
    (arbitraryLogicalImageAtMost code 2 1).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 2) ⁻¹'
        arbitraryLogicalImageAtMost code 2 1) := by
  exact theoremOnePositive_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide) code detectsBelow_three 2 1
    (by decide) (by decide) (by rw [binary_criticalDepth]; decide)

/-- The same closed code also supplies the nonvacuous two-layer application. -/
theorem depthTwo_finite_nondense :
    (arbitraryLogicalImageAtMost code 2 2).Finite ∧
      ¬ Dense (projectiveUnitaryToOperator (Fin 2) ⁻¹'
        arbitraryLogicalImageAtMost code 2 2) := by
  exact theoremOnePositive_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide) code detectsBelow_three 2 2
    (by decide) (by decide) (by rw [binary_criticalDepth]; decide)

run_cmd Lean.Elab.Command.liftIO <| IO.eprintln "FIVE_QUBIT_CHECKPOINT closed_positive_depth_calls elaborated"

#print axioms encoding_isometry
#print axioms generator_fixes
#print axioms detectsBelow_three
#print axioms hasActualDistance_three
#print axioms depthOne_finite_nondense
#print axioms depthTwo_finite_nondense

end CriticalDepth.Manuscript.FiveQubit
end -- explicit closure of the original file-level noncomputable section
end Merged_FiveQubitExample

/- ===== Source block: NativeExamples; SHA-256 6e48d383db4911570ea742c6e18b9e46dabb13f69987ef4c91b38b6337d96ed1 ===== -/
section Merged_NativeExamples
/-! Closed applications through the new raw-matrix and Mathlib-unitary API. -/

noncomputable section

namespace CriticalDepth.ReviewV2.Examples

open Manuscript

theorem fiveQubit_native_depthOne :
    (nativeLogicalImage FiveQubit.encoding 2 1).Finite ∧
      ¬ Dense (nativeLogicalImage FiveQubit.encoding 2 1) := by
  exact nativeTheoremOne_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FiveQubit.encoding FiveQubit.encoding_isometry FiveQubit.detectsBelow_three
    2 1 (by decide) (by decide) (by decide)

theorem fiveQubit_native_depthTwo :
    (nativeLogicalImage FiveQubit.encoding 2 2).Finite ∧
      ¬ Dense (nativeLogicalImage FiveQubit.encoding 2 2) := by
  exact nativeTheoremOne_proved 5 2 1 3 (fun _ => 2)
    (by decide) (by decide) (by decide) (by decide)
    FiveQubit.encoding FiveQubit.encoding_isometry FiveQubit.detectsBelow_three
    2 2 (by decide) (by decide) (by decide)

#print axioms CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthOne
#print axioms CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthTwo

end CriticalDepth.ReviewV2.Examples

end
end Merged_NativeExamples

/- ===== Source block: HandoutBinding; SHA-256 34fdef93d61dc9ae8ad548777316d012f4080d4069a7b9f0b5fc84fd5b8242f7 ===== -/
section Merged_HandoutBinding
noncomputable section

namespace CriticalDepth.Manuscript.PureStatements

def theoremOne : Prop :=
  ∀ (n ℓ g d : ℕ) (dim : Fin n → ℕ), 1 ≤ n → 2 ≤ ℓ → 1 ≤ g → 2 ≤ d →
    ∀ C : Code n dim ℓ g, DetectsBelow C d → ∀ q h : ℕ,
      2 ≤ q → 1 ≤ h → h < Arithmetic.criticalDepth q d →
      (arbitraryLogicalImageAtMost C q h).Finite ∧
        ¬ Dense (projectiveUnitaryToOperator (Fin ℓ) ⁻¹'
          arbitraryLogicalImageAtMost C q h)

def theoremTwo : Prop :=
  ∀ (n k d q : ℕ), 1 ≤ k → 2 ≤ d → 2 ≤ q →
    ∀ C : Code n (fun _ => 2) (2 ^ k) 1,
      IsStabilizer C → HasActualDistance C d →
        hInfinityPositiveAtMost C q = (Arithmetic.criticalDepth q d : ℕ∞) ∧
          HasContinuousLogicalSubgroupAtMost C q (Arithmetic.criticalDepth q d)

end CriticalDepth.Manuscript.PureStatements

end

namespace CriticalDepth.ReviewV2.HandoutBinding

theorem original_theoremOne_proved :
    Manuscript.PureStatements.theoremOne :=
  Manuscript.theoremOnePositive_proved

theorem original_theoremTwo_proved :
    Manuscript.PureStatements.theoremTwo :=
  Manuscript.theoremTwoPositive_proved

#print axioms CriticalDepth.ReviewV2.HandoutBinding.original_theoremOne_proved
#print axioms CriticalDepth.ReviewV2.HandoutBinding.original_theoremTwo_proved

end CriticalDepth.ReviewV2.HandoutBinding
end Merged_HandoutBinding

/- ===== Source block: LogicalUniqueness; SHA-256 49d2efd54c789bcf399a6eebdf1c73c3193234da5bd94fd9f98f6c14344776b3 ===== -/
section Merged_LogicalUniqueness
/-!
Logical factors of the same exact encoded action are unique up to one global
phase.  All public data are matrices and Mathlib matrix unitary groups.  No
physical unitarity, detection, locality, scalarity or inverse premise is added.
-/

noncomputable section

namespace CriticalDepth.ReviewV2

open Matrix
open scoped Kronecker

theorem logical_factor_projective_unique
    {P : Type*} [Fintype P] [DecidableEq P] {K g : ℕ}
    (hK : 1 ≤ K) (hg : 1 ≤ g)
    (V : Matrix P (Fin K × Fin g) ℂ) (hV : V.conjTranspose * V = 1)
    (U : Matrix P P ℂ)
    (W W' : Matrix.unitaryGroup (Fin K) ℂ)
    (Z Z' : Matrix.unitaryGroup (Fin g) ℂ)
    (heq : U * V = V * (W.val ⊗ₖ Z.val))
    (heq' : U * V = V * (W'.val ⊗ₖ Z'.val)) :
    projectiveMk (ι := Fin K) W = projectiveMk (ι := Fin K) W' := by
  classical
  let i₀ : Fin K := ⟨0, by omega⟩
  let a₀ : Fin g := ⟨0, by omega⟩
  letI : Nonempty (Fin K) := ⟨i₀⟩
  have htensor : W.val ⊗ₖ Z.val = W'.val ⊗ₖ Z'.val := by
    calc
      W.val ⊗ₖ Z.val = (V.conjTranspose * V) * (W.val ⊗ₖ Z.val) := by
        rw [hV, Matrix.one_mul]
      _ = V.conjTranspose * (V * (W.val ⊗ₖ Z.val)) := by rw [Matrix.mul_assoc]
      _ = V.conjTranspose * (U * V) := by rw [← heq]
      _ = V.conjTranspose * (V * (W'.val ⊗ₖ Z'.val)) := by rw [heq']
      _ = W'.val ⊗ₖ Z'.val := by rw [← Matrix.mul_assoc, hV, Matrix.one_mul]
  let A : Matrix.unitaryGroup (Fin K) ℂ := W'⁻¹ * W
  let B : Matrix.unitaryGroup (Fin g) ℂ := Z'⁻¹ * Z
  have hAB : A.val ⊗ₖ B.val = (1 : Matrix (Fin K × Fin g) (Fin K × Fin g) ℂ) := by
    change ((W'⁻¹).val * W.val) ⊗ₖ ((Z'⁻¹).val * Z.val) = _
    calc
      ((W'⁻¹).val * W.val) ⊗ₖ ((Z'⁻¹).val * Z.val) =
          ((W'⁻¹).val ⊗ₖ (Z'⁻¹).val) * (W.val ⊗ₖ Z.val) :=
        Matrix.mul_kronecker_mul _ _ _ _
      _ = ((W'⁻¹).val ⊗ₖ (Z'⁻¹).val) * (W'.val ⊗ₖ Z'.val) := by rw [htensor]
      _ = ((W'⁻¹).val * W'.val) ⊗ₖ ((Z'⁻¹).val * Z'.val) :=
        (Matrix.mul_kronecker_mul _ _ _ _).symm
      _ = 1 := by
        change (star W'.val * W'.val) ⊗ₖ (star Z'.val * Z'.val) = _
        rw [W'.property.1, Z'.property.1, Matrix.one_kronecker_one]
  have hdiag : A.val i₀ i₀ * B.val a₀ a₀ = 1 := by
    have he := congrArg
      (fun M : Matrix (Fin K × Fin g) (Fin K × Fin g) ℂ => M (i₀, a₀) (i₀, a₀)) hAB
    simpa [Matrix.kronecker_apply, Matrix.one_apply] using he
  have hB : B.val a₀ a₀ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hdiag
    exact zero_ne_one hdiag
  let z : ℂ := (B.val a₀ a₀)⁻¹
  have hAscalar : A.val = z • (1 : Matrix (Fin K) (Fin K) ℂ) := by
    ext i j
    have hentry : A.val i j * B.val a₀ a₀ = (1 : Matrix (Fin K) (Fin K) ℂ) i j := by
      have he := congrArg
        (fun M : Matrix (Fin K × Fin g) (Fin K × Fin g) ℂ => M (i, a₀) (j, a₀)) hAB
      simpa [Matrix.kronecker_apply, Matrix.one_apply] using he
    calc
      A.val i j = (A.val i j * B.val a₀ a₀) * (B.val a₀ a₀)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hB, mul_one]
      _ = (1 : Matrix (Fin K) (Fin K) ℂ) i j * (B.val a₀ a₀)⁻¹ := by rw [hentry]
      _ = (z • (1 : Matrix (Fin K) (Fin K) ℂ)) i j := by
        change (1 : Matrix (Fin K) (Fin K) ℂ) i j * (B.val a₀ a₀)⁻¹ =
          (B.val a₀ a₀)⁻¹ * (1 : Matrix (Fin K) (Fin K) ℂ) i j
        exact mul_comm _ _
  have hWW' : W.val = z • W'.val := by
    calc
      W.val = W'.val * A.val := by
        change W.val = W'.val * (star W'.val * W.val)
        rw [← Matrix.mul_assoc, W'.property.2, Matrix.one_mul]
      _ = W'.val * (z • (1 : Matrix (Fin K) (Fin K) ℂ)) := by rw [hAscalar]
      _ = z • W'.val := by rw [mul_smul_comm, mul_one]
  apply (projectiveMk_eq_iff (ι := Fin K) W W').mpr
  exact ⟨z, CriticalDepth.unitary_smul_phase
    ((isUnitary_iff_mem_unitaryGroup (Fin K) W.val).mpr W.property)
    ((isUnitary_iff_mem_unitaryGroup (Fin K) W'.val).mpr W'.property) hWW', hWW'⟩

end CriticalDepth.ReviewV2
end -- explicit closure of the original file-level noncomputable section
end Merged_LogicalUniqueness

/- ===== Source block: AuditV2; SHA-256 561565862e5bacca9a3f0b850bf0b0f46d34202695f22668d9e9400854249e45 ===== -/
section Merged_AuditV2
/-!
Append this driver last in the flattened file, after all mathematics and real
calls.  Its imports are hoisted into that file's Mathlib-only import closure.

Every own mathematical constant is recursively audited, including private,
generated and unused declarations.  Only this driver's exact user namespace
is excluded from the mathematical inventory; the own-axiom scan excludes
nothing.  Named-proposition guards check the registered proposition constants,
not a second, independently handwritten semantic specification.

Declared and fully transparent weak-head types are printed without ellipses.
Weak-head reduction does not normalize underneath every binder.  Source and
artifact hashes, process receipts and semantic correspondence are separately
required evidence, not conclusions produced by this driver.
-/

open Lean Meta Elab Command

namespace CriticalDepth.StandaloneAuditV2

private def allowedAxioms : Array Name :=
  #[`propext, `Classical.choice, `Quot.sound]

private def publicImportRoots : Array Name :=
  #[`Mathlib, `Lean, `Init, `Std, `Lake, `Batteries, `Qq, `Aesop,
    `ProofWidgets, `ImportGraph, `LeanSearchClient, `Plausible, `Cli]

private def ownModuleRoots : Array Name :=
  #[`FullIntegrated, `CriticalDepth, `MathlibProjectiveUnitary,
    `NativeCircuitModel, `NativeFiniteMain, `NativeMainStatements,
    `HandoutBinding, `HilbertCoordinates, `HilbertRegister, `HilbertLocality,
    `HilbertMatrixTransport, `HilbertCircuitTransport, `HilbertPhase,
    `RotationPeriods, `CircleRotations, `StabilizerCircle,
    `CriticalCircleWitness, `PauliRowAction, `FiveQubitExample,
    `LogicalUniqueness, `NativeExamples, `AuditV2]

private def targets : Array Name :=
  #[`CriticalDepth.Manuscript.theoremOne_proved,
    `CriticalDepth.Manuscript.theoremOne_nondense,
    `CriticalDepth.Manuscript.theoremTwo_proved,
    `CriticalDepth.Manuscript.theoremOneAtMost_proved,
    `CriticalDepth.Manuscript.theoremTwoAtMost_proved,
    `CriticalDepth.Manuscript.theoremOnePositive_proved,
    `CriticalDepth.Manuscript.theoremTwoPositive_proved,
    `CriticalDepth.ReviewIntegration.theoremOne_proved,
    `CriticalDepth.ReviewIntegration.theoremTwo_proved,
    `CriticalDepth.ReviewV2.nativeTheoremOne_proved,
    `CriticalDepth.ReviewV2.nativeTheoremTwo_proved,
    `CriticalDepth.ReviewV2.HandoutBinding.original_theoremOne_proved,
    `CriticalDepth.ReviewV2.HandoutBinding.original_theoremTwo_proved,
    `CriticalDepth.ReviewV2.HilbertCircuitTransport.logicalImage_eq_native,
    `CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers,
    `CriticalDepth.ReviewV2.HilbertPhase.logicalClass_eq_iff,
    `CriticalDepth.ReviewV2.logical_factor_projective_unique,
    `CriticalDepth.ReviewV2.critical_circle_joint_witness,
    `CriticalDepth.ReviewV2.exp_involution_eq_rotation,
    `CriticalDepth.ReviewV2.rotation_projective_period_iff,
    `CriticalDepth.ReviewV2.exists_closed_circle_rotation_subgroup,
    `CriticalDepth.ReviewV2.stabilizer_critical_closed_circle,
    `CriticalDepth.Manuscript.FiveQubit.encoding_isometry,
    `CriticalDepth.Manuscript.FiveQubit.detectsBelow_three,
    `CriticalDepth.Manuscript.FiveQubit.hasActualDistance_three,
    `CriticalDepth.Manuscript.FiveQubit.depthOne_finite_nondense,
    `CriticalDepth.Manuscript.FiveQubit.depthTwo_finite_nondense,
    `CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthOne,
    `CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthTwo]

private def exactThreeTargets : Array Name :=
  #[`CriticalDepth.Manuscript.theoremOne_proved,
    `CriticalDepth.Manuscript.theoremOne_nondense,
    `CriticalDepth.Manuscript.theoremTwo_proved,
    `CriticalDepth.Manuscript.theoremOneAtMost_proved,
    `CriticalDepth.Manuscript.theoremTwoAtMost_proved,
    `CriticalDepth.Manuscript.theoremOnePositive_proved,
    `CriticalDepth.Manuscript.theoremTwoPositive_proved,
    `CriticalDepth.ReviewIntegration.theoremOne_proved,
    `CriticalDepth.ReviewIntegration.theoremTwo_proved,
    `CriticalDepth.ReviewV2.nativeTheoremOne_proved,
    `CriticalDepth.ReviewV2.nativeTheoremTwo_proved,
    `CriticalDepth.ReviewV2.HandoutBinding.original_theoremOne_proved,
    `CriticalDepth.ReviewV2.HandoutBinding.original_theoremTwo_proved,
    `CriticalDepth.ReviewV2.HilbertCircuitTransport.theoremOne_arbitrary_carriers,
    `CriticalDepth.ReviewV2.critical_circle_joint_witness,
    `CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthOne,
    `CriticalDepth.ReviewV2.Examples.fiveQubit_native_depthTwo]

private def foundationRegistry : Array Name :=
  #[`Matrix, `Matrix.unitaryGroup, `unitary, `Subgroup, `QuotientGroup.mk',
    `Circle, `ContinuousMulEquiv, `LinearIsometry, `TensorProduct,
    `EuclideanSpace, `OrthonormalBasis, `NormedSpace.exp]

private def expectedProposition? (name : Name) : Option Name :=
  if name == `CriticalDepth.Manuscript.theoremOne_proved then
    some `CriticalDepth.Manuscript.theoremOne
  else if name == `CriticalDepth.Manuscript.theoremTwo_proved then
    some `CriticalDepth.Manuscript.theoremTwo
  else if name == `CriticalDepth.Manuscript.theoremOneAtMost_proved then
    some `CriticalDepth.Manuscript.theoremOneAtMost
  else if name == `CriticalDepth.Manuscript.theoremTwoAtMost_proved then
    some `CriticalDepth.Manuscript.theoremTwoAtMost
  else if name == `CriticalDepth.Manuscript.theoremOnePositive_proved then
    some `CriticalDepth.Manuscript.theoremOnePositive
  else if name == `CriticalDepth.Manuscript.theoremTwoPositive_proved then
    some `CriticalDepth.Manuscript.theoremTwoPositive
  else if name == `CriticalDepth.ReviewIntegration.theoremOne_proved then
    some `CriticalDepth.ReviewIntegration.TheoremOne
  else if name == `CriticalDepth.ReviewIntegration.theoremTwo_proved then
    some `CriticalDepth.ReviewIntegration.TheoremTwo
  else if name == `CriticalDepth.ReviewV2.nativeTheoremOne_proved then
    some `CriticalDepth.ReviewV2.NativeTheoremOne
  else if name == `CriticalDepth.ReviewV2.nativeTheoremTwo_proved then
    some `CriticalDepth.ReviewV2.NativeTheoremTwo
  else if name == `CriticalDepth.ReviewV2.HandoutBinding.original_theoremOne_proved then
    some `CriticalDepth.Manuscript.PureStatements.theoremOne
  else if name == `CriticalDepth.ReviewV2.HandoutBinding.original_theoremTwo_proved then
    some `CriticalDepth.Manuscript.PureStatements.theoremTwo
  else none

private def declarationModule? (env : Environment) (name : Name) : Option Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]?
  | none => some env.mainModule

private def fromCurrentModule (env : Environment) (name : Name) : Bool :=
  declarationModule? env name == some env.mainModule

private def fromAuditNamespace (name : Name) : Bool :=
  (`CriticalDepth.StandaloneAuditV2).isPrefixOf
    (privateToUserName name.eraseMacroScopes)

private def namesText (names : Array Name) : String :=
  "[" ++ String.intercalate ", " (names.toList.map Name.toString) ++ "]"

private def fullPrintingOptions (opts : Options) : Options :=
  opts.setBool `pp.all true
    |>.setBool `pp.explicit true
    |>.setBool `pp.universes true
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs true
    |>.setBool `pp.instances true
    |>.setBool `pp.deepTerms true
    |>.setBool `pp.notation false
    |>.set `pp.maxSteps (10000000 : Nat)

private def printFullType (name : Name) : TermElabM Unit := do
  let info ← getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => throwError "V2 target {name} is not a theorem declaration"
  if let some propositionName := expectedProposition? name then
    unless ← withTransparency .all <| isDefEq info.type (mkConst propositionName) do
      throwError "V2 target {name} does not have exactly named proposition {propositionName}"
    logInfo m!"V2_NAMED_PROPOSITION_CHECK {name} proposition={propositionName}"
  withOptions fullPrintingOptions do
    let original := (← PrettyPrinter.ppExpr info.type).pretty 120
    let expandedType ← withTransparency .all <| whnf info.type
    let expanded := (← PrettyPrinter.ppExpr expandedType).pretty 120
    if original.contains '⋯' || expanded.contains '⋯' then
      throwError "V2 elaborated-type output for {name} was truncated"
    let levels := String.intercalate ", " (info.levelParams.map Name.toString)
    logInfo m!"V2_TARGET_TYPE_BEGIN {name}\nUNIVERSE_PARAMETERS [{levels}]\nDECLARED_TYPE\n{original}\nWHNF_ALL_TYPE\n{expanded}\nV2_TARGET_TYPE_END {name}"

run_cmd do
  let env := (← getEnv).setExporting false
  let forbiddenProjectImports := env.header.moduleNames.filter fun moduleName =>
    ownModuleRoots.any (fun root => root.isPrefixOf moduleName)
  let unapprovedImports := env.header.moduleNames.filter fun moduleName =>
    !(publicImportRoots.any (fun root => root.isPrefixOf moduleName))
  unless forbiddenProjectImports.isEmpty do
    throwError "V2 flattened verification imports own modules: {namesText forbiddenProjectImports}"
  unless unapprovedImports.isEmpty do
    throwError "V2 imports have unapproved public roots: {namesText unapprovedImports}"
  unless targets.size == 29 && exactThreeTargets.size == 17 && foundationRegistry.size == 12 do
    throwError "V2 registry sizes must be targets=29, exact-three=17, foundations=12"
  for name in targets do
    unless (targets.filter (fun other => other == name)).size == 1 do
      throwError "Duplicate V2 target {name}"
  for name in exactThreeTargets do
    unless targets.contains name &&
        (exactThreeTargets.filter (fun other => other == name)).size == 1 do
      throwError "Invalid or duplicate exact-three target {name}"
  for name in foundationRegistry do
    unless (foundationRegistry.filter (fun other => other == name)).size == 1 do
      throwError "Duplicate foundation target {name}"
  logInfo m!"V2_MAIN_MODULE {env.mainModule}"
  logInfo m!"V2_IMPORTED_MODULES {namesText env.header.moduleNames}"
  logInfo m!"V2_PUBLIC_IMPORT_ROOTS {namesText publicImportRoots}"
  logInfo "V2_IMPORTED_PROJECT_MODULES []"
  logInfo "V2_UNAPPROVED_IMPORTED_MODULES []"
  logInfo m!"V2_RECURSIVE_ALLOWLIST {namesText allowedAxioms}"

  -- No namespace exclusion is applied to this own-axiom scan.
  let ownAxioms : Array Name :=
    (env.constants.fold (init := #[]) fun acc name info =>
      if fromCurrentModule env name then
        match info with
        | .axiomInfo _ => acc.push name
        | _ => acc
      else acc).qsort Name.lt
  unless ownAxioms.isEmpty do
    throwError "V2 own axioms, including audit-driver axioms, are forbidden: {namesText ownAxioms}"

  let mathematicalConstants : Array Name :=
    (env.constants.fold (init := #[]) fun acc name _ =>
      if fromCurrentModule env name && !fromAuditNamespace name then acc.push name
      else acc).qsort Name.lt
  let mathematicalTheorems : Array Name :=
    (env.constants.fold (init := #[]) fun acc name info =>
      if fromCurrentModule env name && !fromAuditNamespace name then
        match info with
        | .thmInfo _ => acc.push name
        | _ => acc
      else acc).qsort Name.lt
  if mathematicalConstants.isEmpty || mathematicalTheorems.isEmpty then
    throwError "V2 refuses empty mathematical constant or theorem inventories"
  for name in mathematicalTheorems do
    unless mathematicalConstants.contains name &&
        declarationModule? env name == some env.mainModule do
      throwError "V2 own theorem {name} is absent from the consistent own-constant inventory"

  let mut foundationChecks : Nat := 0
  for name in foundationRegistry do
    unless (env.find? name).isSome do
      throwError "Missing Mathlib foundational declaration {name}"
    let some origin := declarationModule? env name
      | throwError "Missing module origin for foundational declaration {name}"
    unless origin != env.mainModule && (`Mathlib).isPrefixOf origin do
      throwError "Foundation {name} must be imported from Mathlib, actual origin={origin}"
    foundationChecks := foundationChecks + 1
    logInfo m!"V2_FOUNDATION_ORIGIN {name} origin={origin}"

  let mut propositionChecks : Nat := 0
  let mut exactThreeChecks : Nat := 0
  for name in targets do
    unless mathematicalTheorems.contains name do
      throwError "V2 required target {name} is absent from own mathematical theorems"
    liftTermElabM <| printFullType name
    if (expectedProposition? name).isSome then
      propositionChecks := propositionChecks + 1
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    unless forbidden.isEmpty do
      throwError "V2 target {name} has forbidden recursive axioms {namesText forbidden}"
    if exactThreeTargets.contains name then
      let missing := allowedAxioms.filter fun axiomName => !axioms.contains axiomName
      unless missing.isEmpty do
        throwError "V2 exact-three target {name} is missing {namesText missing}"
      exactThreeChecks := exactThreeChecks + 1
      logInfo m!"V2_TARGET_AXIOMS {name} mode=exact3 {namesText axioms}"
    else
      logInfo m!"V2_TARGET_AXIOMS {name} mode=subset {namesText axioms}"
  unless propositionChecks == 12 && exactThreeChecks == 17 && foundationChecks == 12 do
    throwError "V2 check counts differ: propositions={propositionChecks}, exact-three={exactThreeChecks}, foundations={foundationChecks}"

  for name in mathematicalConstants do
    unless declarationModule? env name == some env.mainModule do
      throwError "V2 audited constant {name} has an inconsistent module origin"
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun axiomName => !allowedAxioms.contains axiomName
    logInfo m!"V2_RECURSIVE_AXIOMS {name} origin={env.mainModule} {namesText axioms}"
    unless forbidden.isEmpty do
      throwError "V2 mathematical constant {name} has forbidden recursive axioms {namesText forbidden}"
  logInfo m!"STANDALONE_CRITICAL_DEPTH_V2_AUDIT_PASSED theorem_count={mathematicalTheorems.size} constant_count={mathematicalConstants.size} target_count={targets.size} exact_three_count={exactThreeChecks} proposition_check_count={propositionChecks} foundation_count={foundationChecks} own_axiom_count={ownAxioms.size} imported_project_module_count={forbiddenProjectImports.size} unapproved_import_count={unapprovedImports.size}"

end CriticalDepth.StandaloneAuditV2
end Merged_AuditV2
