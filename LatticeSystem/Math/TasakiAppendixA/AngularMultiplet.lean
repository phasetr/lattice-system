import LatticeSystem.Math.TasakiAppendixA.AngularQuantization

/-!
# Tasaki Appendix A.3.2: the SU(2)-multiplet degeneracy (Theorem A.16)

For an `su(2)`-invariant Hamiltonian `Ĥ` (one that commutes with each angular-momentum component,
`[Ĥ, Ĵ⁽ᵅ⁾] = 0`), Tasaki's Theorem A.16 says that an energy eigenstate inside one joint eigenspace
`H_{J,M0}` is accompanied by energy eigenstates in **every** `H_{J,M}` of the same multiplet
(`M = −J, −J+1, …, J`); hence each energy level is at least `(2J+1)`-fold degenerate, and the
companions are ladder images `|Φ_M⟩ = c_M (Ĵ⁻)^{J−M} |Φ_J⟩` (eq. (A.3.14)).

The proof reuses the ladder iterate `raiseIter` (`AngularQuantization.lean`): raise the given state
`J − M0` times to reach the top of the multiplet `H_{J,J}` (nonzero by Lemma A.14, energy `E`
preserved because `Ĥ` commutes with `Ĵ⁺`), then descend `k` times with `Ĵ⁻` — realized as the
*reflected* raising `raiseIter Ĵ⁽¹⁾ (−Ĵ⁽²⁾)` for the operators `(Ĵ⁽¹⁾, −Ĵ⁽²⁾, −Ĵ⁽³⁾)` — to land in
`H_{J,J−k}` for any `k ≤ 2J`.  All proved (axiom-free).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.3.2, Theorem A.16, eq. (A.3.14), p. 473.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d] (H J1 J2 J3 : Matrix d d ℂ)

omit [DecidableEq d] in
/-- An `su(2)`-invariant Hamiltonian preserves a raised state's energy: if `Ĥ` commutes with
`Ĵ⁽¹⁾` and `Ĵ⁽²⁾` and `Ĥ Φ = E Φ`, then `Ĥ (Ĵ⁺)^k Φ = E (Ĵ⁺)^k Φ` for every `k`, because `Ĥ`
commutes with `Ĵ⁺ = Ĵ⁽¹⁾ + i Ĵ⁽²⁾`.  Induction on `k`. -/
theorem ham_mulVec_raiseIter (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H) {Φ : d → ℂ} {E : ℂ}
    (hH : H.mulVec Φ = E • Φ) :
    ∀ k : ℕ, H.mulVec (raiseIter J1 J2 k Φ) = E • raiseIter J1 J2 k Φ := by
  have hcomm : H * (J1 + Complex.I • J2) = (J1 + Complex.I • J2) * H := by
    rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, hcH1, hcH2]
  intro k
  induction k with
  | zero => exact hH
  | succ k ih =>
    rw [show raiseIter J1 J2 (k + 1) Φ
          = (J1 + Complex.I • J2).mulVec (raiseIter J1 J2 k Φ) from rfl,
      Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul]

omit [DecidableEq d] in
/-- **Tasaki Theorem A.16 (SU(2)-multiplet degeneracy).**  Let `Ĥ` be `su(2)`-invariant
(`Ĥ Ĵ⁽ᵅ⁾ = Ĵ⁽ᵅ⁾ Ĥ`) and let `Φ ≠ 0` be a joint eigenstate in `H_{J,M0}` (`Ĵ² Φ = J(J+1) Φ`,
`Ĵ⁽³⁾ Φ = M0 Φ`) with `Ĥ Φ = E Φ` and `J ≥ 0`.  Then for every `k ≤ 2J` there is a *nonzero*
companion `Ψ ∈ H_{J,J−k}` (`Ĵ² Ψ = J(J+1) Ψ`, `Ĵ⁽³⁾ Ψ = (J−k) Ψ`) with the same energy
`Ĥ Ψ = E Ψ`.  As `k` runs `0,…,2J`, this realizes the `2J+1` magnetic numbers `M = J,…,−J`, so the
level `E` is at least `(2J+1)`-fold degenerate.  Proof: raise `Φ` to the top `H_{J,J}`
(`J − M0 ∈ ℤ≥0` by Lemma A.15), then lower `k` times via the reflected raising. -/
theorem ham_su2_multiplet (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H)
    (_hcH3 : H * J3 = J3 * H) (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) {Φ : d → ℂ} {Jr M0 : ℝ} {E : ℂ} (hΦ : Φ ≠ 0)
    (hJ : 0 ≤ Jr) (hsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ)
    (h3 : J3.mulVec Φ = (M0 : ℂ) • Φ) (hH : H.mulVec Φ = E • Φ) :
    ∀ k : ℕ, (k : ℝ) ≤ 2 * Jr →
      ∃ Ψ : d → ℂ, Ψ ≠ 0 ∧
        (J1 * J1 + J2 * J2 + J3 * J3).mulVec Ψ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Ψ ∧
        J3.mulVec Ψ = ((Jr - k : ℝ) : ℂ) • Ψ ∧ H.mulVec Ψ = E • Ψ := by
  -- Spin bound on the seed state and `J − M0 ∈ ℤ≥0` (Lemma A.15): write `J − M0 = t`.
  obtain ⟨hM0lb, hM0ub⟩ := angMom_abs_le_J J1 J2 J3 h1 h2 h12 hΦ hJ hsq h3
  obtain ⟨t, ht⟩ := angMom_sub_mem_nat J1 J2 J3 h1 h2 h12 h23 h31 hΦ hJ hsq h3
  have hMt : M0 + (t : ℝ) = Jr := by linarith
  -- Top state `T = (Ĵ⁺)^t Φ ∈ H_{J,J}`, nonzero, energy `E`.
  set T := raiseIter J1 J2 t Φ with hT
  have hTeig := raiseIter_eigenspace J1 J2 J3 h12 h23 h31 hsq h3 t
  have hTne : T ≠ 0 := by
    refine raiseIter_ne_zero J1 J2 J3 h12 h23 h31 hsq h3 hΦ (by linarith) t (fun i hi => ?_)
    have : (i : ℝ) < (t : ℝ) := by exact_mod_cast hi
    linarith
  have hTsq : (J1 * J1 + J2 * J2 + J3 * J3).mulVec T = ((Jr * (Jr + 1) : ℝ) : ℂ) • T := hTeig.1
  have hT3 : J3.mulVec T = ((Jr : ℝ) : ℂ) • T := by
    have := hTeig.2; rw [show ((M0 + (t : ℝ)) : ℝ) = Jr from hMt] at this; exact this
  have hHT : H.mulVec T = E • T := ham_mulVec_raiseIter H J1 J2 hcH1 hcH2 hH t
  -- Reflected operators `(Ĵ⁽¹⁾, −Ĵ⁽²⁾, −Ĵ⁽³⁾)`: same `su(2)` relations, raising = `Ĵ⁻`.
  have h12' := su2Reflect12 J1 J2 J3 h12
  have h23' := su2Reflect23 J1 J2 J3 h23
  have h31' := su2Reflect31 J1 J2 J3 h31
  have hsqT' : (J1 * J1 + (-J2) * (-J2) + (-J3) * (-J3)).mulVec T
      = ((Jr * (Jr + 1) : ℝ) : ℂ) • T := by
    rw [casimirReflect J1 J2 J3]; exact hTsq
  have h3T' : (-J3).mulVec T = ((-Jr : ℝ) : ℂ) • T := by
    rw [Matrix.neg_mulVec, hT3]; push_cast; module
  -- Descend `k` times: `Ψ = (Ĵ⁻)^k T = raiseIter J1 (−J2) k T`.
  intro k hk
  refine ⟨raiseIter J1 (-J2) k T, ?_, ?_, ?_, ?_⟩
  · refine raiseIter_ne_zero J1 (-J2) (-J3) h12' h23' h31' hsqT' h3T' hTne (by linarith) k
      (fun i hi => ?_)
    have : (i : ℝ) < (k : ℝ) := by exact_mod_cast hi
    linarith
  · have hRe := raiseIter_eigenspace J1 (-J2) (-J3) h12' h23' h31' hsqT' h3T' k
    rw [← casimirReflect J1 J2 J3]
    exact hRe.1
  · have hRe := raiseIter_eigenspace J1 (-J2) (-J3) h12' h23' h31' hsqT' h3T' k
    have h3R := hRe.2
    have h3R' : J3.mulVec (raiseIter J1 (-J2) k T)
        = -(((-Jr + k : ℝ) : ℂ) • raiseIter J1 (-J2) k T) := by
      rw [← neg_neg (J3.mulVec (raiseIter J1 (-J2) k T)), ← Matrix.neg_mulVec, h3R]
    rw [h3R', ← neg_smul]
    congr 1
    push_cast
    ring
  · exact ham_mulVec_raiseIter H J1 (-J2) hcH1 (by rw [Matrix.mul_neg, Matrix.neg_mul, hcH2]) hHT k

end LatticeSystem.Math
