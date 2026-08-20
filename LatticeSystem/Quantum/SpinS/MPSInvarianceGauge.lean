import LatticeSystem.Quantum.SpinS.AKLTMatrixProduct
import LatticeSystem.Quantum.SpinS.SPTSymmetryTransportedMPS

/-!
# From phase invariance to a unitary gauge for injective matrix product states

Tasaki's step from the assumed symmetry invariance of a matrix product state to a gauge relation on
its matrices: if `V̂(g)|Φ_L⟩ = e^{iη_L(g)}|Φ_L⟩` for every chain length `L` (eqs. (8.3.15) and
(8.3.45)), then the transported family `Ã_g^σ` of eq. (8.3.47) is related to `A^σ` by
`Ã_g^σ = e^{iζ(g)} U†(g) A^σ U(g)` (eqs. (8.3.16) and (8.3.48)).

The book's own justification (footnote 37, p. 265) is `B^σ = e^{−iη_L/L} Ã^σ` followed by "apply the
theorem", but that `B` depends on `L`, whereas Theorem 7.6 compares two *fixed* families.  The gap
is closed here in two steps:

* the phase is **exponential**, `η_L = c^L` for all `L` beyond twice the spanning length
  (`exists_phase_eq_pow`), proved from the multiplicativity `η_{a+b} = η_a η_b` (`phase_mul`); the
  latter comes from expanding `1` as a linear combination of ordered products of `A`, transporting
  that combination to `B`, and taking the trace, which removes the leftover constant;
* the rescaled family `c⁻¹ • Ã_g` is then independent of `L` and agrees with `A` on all
  sufficiently long chains, which is exactly the hypothesis of
  `mps_theorem_7_6_of_eventual_agreement`.

**Range of the book's claim.**  "`η_L = Lζ` for any `L`" is not literally true: at a length whose
trace coefficients all vanish — length one for a family of traceless matrices, as for the spin-`1`
Pauli family — the invariance hypothesis reads `0 = e^{iη_L} · 0` and constrains `η_L` not at all
(and `|Φ_L⟩ = 0` there, so the phase is not even defined).  The exponential law is therefore stated
for lengths at least twice the spanning length (the multiplicativity `η_{a+b} = η_a η_b` needs both
factors above that length), which is all that §8.3.5 uses: eqs. (8.3.49)–(8.3.54) consume only the
gauge relation (8.3.48) and never mention `η_L` again.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.4, eqs. (8.3.15)–(8.3.16) and footnote 37, p. 265; §8.3.5, eqs. (8.3.45)–(8.3.48),
pp. 278–279; §7.2.2, Theorem 7.6, p. 203.
-/

namespace LatticeSystem.Quantum

open Matrix
open LatticeSystem.Math (signConjMatrix_one_apply circle_smul_mem_unitaryGroup)

variable {D N : ℕ}

/-! ## The phased trace coefficients -/

/-- The coefficient form of the invariance hypothesis (8.3.15)/(8.3.45): every periodic trace
coefficient of `B` is the corresponding coefficient of `A` times a length-dependent phase `η_L`.
Expanding both sides of `V̂(g)|Φ_L⟩ = e^{iη_L(g)}|Φ_L⟩` in the product basis and using the linear
independence of the basis states turns the invariance into exactly this family of scalar
equations. -/
def GeneratesPhasedMPS (A B : MPSMatrices D N) (η : ℕ → Circle) : Prop :=
  ∀ (L : ℕ) (ss : Fin L → Fin (N + 1)),
    Matrix.trace (orderedProd B (List.ofFn ss)) =
      (η L : ℂ) * Matrix.trace (orderedProd A (List.ofFn ss))

variable {A B : MPSMatrices D N} {η : ℕ → Circle}

/-- The phased coefficient equation in list form. -/
private theorem trace_orderedProd_phase (hphase : GeneratesPhasedMPS A B η)
    (u : List (Fin (N + 1))) :
    Matrix.trace (orderedProd B u) = (η u.length : ℂ) * Matrix.trace (orderedProd A u) := by
  simpa only [List.ofFn_get] using hphase u.length u.get

/-- The phased coefficient equation for a fixed-length word. -/
private theorem trace_mpsWordEval_phase (hphase : GeneratesPhasedMPS A B η) {a : ℕ}
    (w : MPSWord N a) :
    Matrix.trace (mpsWordEval B w) = (η a : ℂ) * Matrix.trace (mpsWordEval A w) := by
  simpa only [mpsWordEval, List.length_ofFn] using trace_orderedProd_phase hphase (List.ofFn w)

/-- The phased coefficient equation for a fixed-length word followed by a second one: the phase of
the concatenation is the phase at the total length. -/
private theorem trace_mpsWordEval_mul_phase (hphase : GeneratesPhasedMPS A B η) {a b : ℕ}
    (w : MPSWord N a) (t : MPSWord N b) :
    Matrix.trace (mpsWordEval B w * mpsWordEval B t) =
      (η (a + b) : ℂ) * Matrix.trace (mpsWordEval A w * mpsWordEval A t) := by
  have hsplit (C : MPSMatrices D N) :
      mpsWordEval C w * mpsWordEval C t = orderedProd C (List.ofFn w ++ List.ofFn t) := by
    rw [orderedProd_append]
    rfl
  have hlen : (List.ofFn w ++ List.ofFn t).length = a + b := by simp
  rw [hsplit A, hsplit B, trace_orderedProd_phase hphase, hlen]

/-- The linear extension of the phased coefficient equation to formal combinations of fixed-length
words. -/
private theorem trace_mpsEvalWords_phase (hphase : GeneratesPhasedMPS A B η) {a : ℕ}
    (c : MPSWord N a →₀ ℂ) :
    Matrix.trace (mpsEvalWords B a c) = (η a : ℂ) * Matrix.trace (mpsEvalWords A a c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, Matrix.trace_add, Matrix.trace_add, h₁, h₂, mul_add]
  | single w z =>
      have hval (C : MPSMatrices D N) :
          mpsEvalWords C a (Finsupp.single w z) = z • mpsWordEval C w := by
        simp [mpsEvalWords]
      rw [hval A, hval B, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
        trace_mpsWordEval_phase hphase]
      ring

/-- The linear extension of the phased coefficient equation to a formal combination of fixed-length
words followed by a single word. -/
private theorem trace_mpsEvalWords_mul_word_phase (hphase : GeneratesPhasedMPS A B η) {a b : ℕ}
    (c : MPSWord N a →₀ ℂ) (t : MPSWord N b) :
    Matrix.trace (mpsEvalWords B a c * mpsWordEval B t) =
      (η (a + b) : ℂ) * Matrix.trace (mpsEvalWords A a c * mpsWordEval A t) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ =>
      rw [map_add, map_add, Matrix.add_mul, Matrix.add_mul, Matrix.trace_add, Matrix.trace_add,
        h₁, h₂, mul_add]
  | single w z =>
      have hval (C : MPSMatrices D N) :
          mpsEvalWords C a (Finsupp.single w z) = z • mpsWordEval C w := by
        simp [mpsEvalWords]
      rw [hval A, hval B, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul,
        smul_eq_mul, smul_eq_mul, trace_mpsWordEval_mul_phase hphase]
      ring

/-! ## Multiplicativity and exponentiality of the phase -/

/-- **The phase is multiplicative in the chain length.**  If the ordered products of `A` span at
length `a` and those of `B` span at length `b`, then `η_{a+b} = η_a η_b`.

Writing `1 = Σ_i c_i A^{w_i}` with words `w_i` of length `a` and transporting the combination to
`B`, the matrix `P = Σ_i c_i B^{w_i}` is pinned to the scalar `η_{a+b} η_b⁻¹` by testing it against
the length-`b` words of `B`.  Taking the trace of `P` in the two available ways then removes the
bond dimension and leaves `η_a = η_{a+b} η_b⁻¹`; this is the step the book's footnote replaces by
the `L`-dependent rescaling `e^{-iη_L/L}`. -/
theorem phase_mul [NeZero D] {a b : ℕ} (hspanA : mpsProductsSpanAt A a)
    (hspanB : mpsProductsSpanAt B b) (hphase : GeneratesPhasedMPS A B η) :
    η (a + b) = η a * η b := by
  classical
  obtain ⟨c, hc⟩ := mpsEvalWords_surjective hspanA (1 : Matrix (Fin D) (Fin D) ℂ)
  have hP : mpsEvalWords B a c = ((η (a + b) * (η b)⁻¹ : Circle) : ℂ) • 1 := by
    refine eq_of_trace_mul_words hspanB fun t => ?_
    have hlhs : Matrix.trace (mpsEvalWords B a c * mpsWordEval B t) =
        (η (a + b) : ℂ) * Matrix.trace (mpsWordEval A t) := by
      rw [trace_mpsEvalWords_mul_word_phase hphase, hc, Matrix.one_mul]
    have hrhs : Matrix.trace (((η (a + b) * (η b)⁻¹ : Circle) : ℂ) •
          (1 : Matrix (Fin D) (Fin D) ℂ) * mpsWordEval B t) =
        (η (a + b) : ℂ) * Matrix.trace (mpsWordEval A t) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul,
        trace_mpsWordEval_phase hphase, Circle.coe_mul, Circle.coe_inv]
      field_simp
    rw [hlhs, hrhs]
  have hone : Matrix.trace (1 : Matrix (Fin D) (Fin D) ℂ) = (D : ℂ) := by simp
  have htrace := congrArg Matrix.trace hP
  rw [trace_mpsEvalWords_phase hphase, hc, hone, Matrix.trace_smul, hone, smul_eq_mul] at htrace
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne D
  have hcirc : η a = η (a + b) * (η b)⁻¹ :=
    Circle.coe_injective (mul_right_cancel₀ hDne htrace)
  rw [hcirc]
  group

/-- **The phase is exponential beyond twice the spanning length.**  For injective families the phase
function of `GeneratesPhasedMPS` is `η_L = c^L` for all sufficiently long chains, with a single
`c : Circle`; the threshold returned here is twice the spanning length, since the multiplicativity
step splits a length into two summands that must both exceed it.  This is Tasaki's `η_L = Lζ`
(eq. (8.3.16)) with its correct range of validity: below the spanning length the trace coefficients
can vanish identically and leave `η_L` unconstrained. -/
theorem exists_phase_eq_pow [NeZero D] (hspanA : MPSSpansForAllLarge A)
    (hspanB : MPSSpansForAllLarge B) (hphase : GeneratesPhasedMPS A B η) :
    ∃ (c : Circle) (ℓ₀ : ℕ), ∀ L : ℕ, ℓ₀ ≤ L → η L = c ^ L := by
  obtain ⟨ℓA, hlargeA⟩ := hspanA
  obtain ⟨ℓB, hlargeB⟩ := hspanB
  set ℓ := max ℓA ℓB
  have hmul : ∀ a b : ℕ, ℓ ≤ a → ℓ ≤ b → η (a + b) = η a * η b := fun a b ha hb =>
    phase_mul (hlargeA a (le_trans (le_max_left _ _) ha))
      (hlargeB b (le_trans (le_max_right _ _) hb)) hphase
  refine ⟨η (ℓ + 1) * (η ℓ)⁻¹, 2 * ℓ, ?_⟩
  set c := η (ℓ + 1) * (η ℓ)⁻¹ with hc
  have hstep : ∀ M : ℕ, 2 * ℓ ≤ M → η (M + 1) = c * η M := by
    intro M hM
    obtain ⟨m, rfl⟩ : ∃ m, M = m + ℓ := ⟨M - ℓ, by omega⟩
    have hm : ℓ ≤ m := by omega
    have h1 : η (m + (ℓ + 1)) = η m * η (ℓ + 1) := hmul m (ℓ + 1) hm (by omega)
    have h2 : η (m + ℓ) = η m * η ℓ := hmul m ℓ hm le_rfl
    calc η (m + ℓ + 1) = η m * η (ℓ + 1) := by
          rw [show m + ℓ + 1 = m + (ℓ + 1) by omega, h1]
      _ = η (ℓ + 1) * (η ℓ)⁻¹ * (η m * η ℓ) := by
          rw [mul_comm (η m) (η ℓ), ← mul_assoc, mul_assoc (η (ℓ + 1)) (η ℓ)⁻¹ (η ℓ),
            inv_mul_cancel, mul_one, mul_comm]
      _ = c * η (m + ℓ) := by rw [hc, h2]
  have hpow : ∀ k : ℕ, η (2 * ℓ + k) = c ^ k * η (2 * ℓ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [show 2 * ℓ + (k + 1) = 2 * ℓ + k + 1 by omega, hstep _ (by omega), ih, pow_succ]
        group
  have hbase : η (2 * ℓ) = c ^ (2 * ℓ) := by
    have hsq : η (2 * ℓ + 2 * ℓ) = η (2 * ℓ) * η (2 * ℓ) := hmul _ _ (by omega) (by omega)
    have hk := hpow (2 * ℓ)
    rw [hsq] at hk
    exact mul_right_cancel hk
  intro L hL
  obtain ⟨k, rfl⟩ : ∃ k, L = 2 * ℓ + k := ⟨L - 2 * ℓ, by omega⟩
  rw [hpow k, hbase, ← pow_add, Nat.add_comm]

/-! ## The gauge relation -/

/-- Rescaling an MPS family by a phase preserves injectivity: the rescaling is the symmetry
transport with trivial sign and the (unitary) mixing matrix `z · 1`. -/
theorem isInjectiveMPS_smul (z : Circle) {lam : ℝ} (hA : IsInjectiveMPS A lam) :
    IsInjectiveMPS (fun σ => (z : ℂ) • A σ) lam := by
  have hu : ((z : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) ∈
      Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
    circle_smul_mem_unitaryGroup z (Submonoid.one_mem _)
  have hconj : mpsConjugate (1 : ℤˣ) A = A := funext fun σ => signConjMatrix_one_apply (A σ)
  have heq : symmetryTransportMPS (1 : ℤˣ) ((z : ℂ) • 1) A = fun σ => (z : ℂ) • A σ := by
    funext σ
    rw [symmetryTransportMPS, hconj]
    change (∑ τ : Fin (N + 1), ((z : ℂ) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) σ τ • A τ)
      = (z : ℂ) • A σ
    rw [Finset.sum_eq_single σ]
    · simp
    · intro τ _ hτ
      simp [Matrix.one_apply_ne (Ne.symm hτ)]
    · intro hσ
      exact absurd (Finset.mem_univ σ) hσ
  rw [← heq]
  exact isInjectiveMPS_symmetryTransportMPS hu hA

/-- **From phase invariance to a unitary gauge.**  Two injective MPS families whose periodic trace
coefficients differ by a length-dependent phase are related by a unitary gauge up to a single
overall phase, `B^σ = e^{iζ} U† A^σ U`.

The phase is exponential on long chains (`exists_phase_eq_pow`), so the rescaled family `c⁻¹ • B` is
a *fixed* family agreeing with `A` on all sufficiently long chains, and
`mps_theorem_7_6_of_eventual_agreement` applies to it.  At bond dimension zero the matrix space is a
subsingleton and the statement is vacuous — as it must be, since there the phase carries no
information. -/
theorem exists_unitary_gauge_of_phased {lamA lamB : ℝ} (hA : IsInjectiveMPS A lamA)
    (hB : IsInjectiveMPS B lamB) (hphase : GeneratesPhasedMPS A B η) :
    ∃ (ζ : Circle) (U : Matrix.unitaryGroup (Fin D) ℂ),
      ∀ σ, B σ = (ζ : ℂ) • ((U : Matrix (Fin D) (Fin D) ℂ).conjTranspose * A σ *
        (U : Matrix (Fin D) (Fin D) ℂ)) := by
  by_cases hD : D = 0
  · subst hD
    exact ⟨1, ⟨1, by simp⟩, fun σ => Subsingleton.elim _ _⟩
  letI : NeZero D := ⟨hD⟩
  obtain ⟨c, ℓ₀, hc⟩ := exists_phase_eq_pow hA.2.2.1 hB.2.2.1 hphase
  have hcne : (c : ℂ) ≠ 0 := Circle.coe_ne_zero c
  have hBinj : IsInjectiveMPS (fun σ => ((c⁻¹ : Circle) : ℂ) • B σ) lamB :=
    isInjectiveMPS_smul c⁻¹ hB
  have hsame : GeneratesSameMPSEventually A (fun σ => ((c⁻¹ : Circle) : ℂ) • B σ) := by
    refine ⟨ℓ₀, fun L hL ss => ?_⟩
    have hlen : (List.ofFn ss).length = L := by simp
    have hscaled : Matrix.trace (orderedProd (fun σ => ((c⁻¹ : Circle) : ℂ) • B σ)
          (List.ofFn ss)) =
        ((c : ℂ)⁻¹) ^ L * Matrix.trace (orderedProd B (List.ofFn ss)) := by
      rw [orderedProd_smul, Matrix.trace_smul, hlen, smul_eq_mul, Circle.coe_inv]
    rw [hscaled, trace_orderedProd_phase hphase, hlen, hc L hL, Circle.coe_pow, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hcne, one_pow, one_mul]
  obtain ⟨U, hUmem, hgauge, -⟩ :=
    mps_theorem_7_6_of_eventual_agreement A (fun σ => ((c⁻¹ : Circle) : ℂ) • B σ) lamA lamB hA
      hBinj hsame
  refine ⟨c, ⟨U, hUmem⟩, fun σ => ?_⟩
  have hσ : ((c⁻¹ : Circle) : ℂ) • B σ = U.conjTranspose * A σ * U := hgauge σ
  rw [← hσ, smul_smul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_smul]

/-- **Tasaki eq. (8.3.48)** (and its `s = 1` instance, eq. (8.3.16)).  If an injective MPS family is
invariant under a symmetry operation up to a length-dependent phase, then the transported family
`Ã_g^σ = Σ_{σ'} ⟨ψ^σ|û(g)|ψ^{σ'}⟩ C_g[A^{σ'}]` of eq. (8.3.47) satisfies
`Ã_g^σ = e^{iζ(g)} U†(g) A^σ U(g)` for a phase `ζ(g)` and a unitary `U(g)`.

The statement is for a single symmetry element, given as its sign `ε = s(g)` and its unitary matrix
`u = û(g)`; the group-indexed version and the cocycle relation among the `U(g)` belong to the next
stage of §8.3.5.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.3.5, eqs. (8.3.45)–(8.3.48), pp. 278–279. -/
theorem exists_unitary_gauge_of_invariance (A : MPSMatrices D N) (lam : ℝ)
    (hA : IsInjectiveMPS A lam) (ε : ℤˣ) (u : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ) (η : ℕ → Circle)
    (hinv : GeneratesPhasedMPS A (symmetryTransportMPS ε u A) η) :
    ∃ (ζ : Circle) (U : Matrix.unitaryGroup (Fin D) ℂ),
      ∀ σ, symmetryTransportMPS ε u A σ =
        (ζ : ℂ) • ((U : Matrix (Fin D) (Fin D) ℂ).conjTranspose * A σ *
          (U : Matrix (Fin D) (Fin D) ℂ)) :=
  exists_unitary_gauge_of_phased hA (isInjectiveMPS_symmetryTransportMPS hu hA) hinv

end LatticeSystem.Quantum
