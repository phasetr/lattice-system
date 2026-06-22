import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShiftCore

/-!
# Magnetic-quantum-number shifts via ladder operators on the
all-aligned state (build-speed companion)

Build-speed companion to `AllAlignedState.lean`. Hosts the
trailing sections "Single-step magnetic-quantum-number shifts on
the all-aligned state", "Generic single-step magnetic-quantum-
number shifts and iterated form", and "Ladder operators shift the
magnetization subspace" (originally lines 853..1090 of the parent
file).

Splitting these blocks out drops the parent file from ~1090 lines
to ~852 lines. Consumers of the moved theorems
(`Iterate*`, `Ladder*`, `MagnetizationDirectSum`,
`SaturatedFullLadderLI`, `SaturatedLadderJointEigenspace`,
`SaturatedPairLinearIndependent`) updated to additionally import
this companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.4, pp. 27–38 (saturated FM ground states).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Generic single-step magnetic-quantum-number shifts and iterated form

The single-step Cartan shifts `Ŝ^z · Ŝ^∓ · ψ = (λ ∓ 1) · Ŝ^∓ · ψ`
hold for **any** `Ŝ^z`-eigenvector `ψ` at eigenvalue `λ`. Iterating
gives the magnetic-quantum-number labelling along the full ladder
`(Ŝ^∓_{tot})^k · |σ_⊤⟩` (resp. `|σ_⊥⟩`) at eigenvalue `m_max ∓ k`.
-/

/-- **Generic single-step lowering shift**: for any `Ŝ^z_{tot}`-
eigenvector `ψ` at eigenvalue `λ`, the lowered state `Ŝ^-_{tot} · ψ`
is also a `Ŝ^z_{tot}`-eigenvector, at eigenvalue `λ − 1`.

Proof: rearrange Cartan
`Ŝ^z · Ŝ^- = Ŝ^- · Ŝ^z − Ŝ^-` (PR #883), then apply to `ψ`. -/
theorem totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec
    {lam : ℂ} {ψ : (V → Fin (N + 1)) → ℂ}
    (hψ : (totalSpinSOp3 V N).mulVec ψ = lam • ψ) :
    (totalSpinSOp3 V N).mulVec ((totalSpinSOpMinus V N).mulVec ψ) =
      (lam - 1) • (totalSpinSOpMinus V N).mulVec ψ := by
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSOp3 V N -
        totalSpinSOpMinus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpMinus (V := V) (N := N)
    have h' := sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_smul]
  rw [sub_smul, one_smul]

/-- **Generic single-step raising shift**: for any `Ŝ^z_{tot}`-
eigenvector `ψ` at eigenvalue `λ`, the raised state `Ŝ^+_{tot} · ψ`
is also a `Ŝ^z_{tot}`-eigenvector, at eigenvalue `λ + 1`. -/
theorem totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_eigenvec
    {lam : ℂ} {ψ : (V → Fin (N + 1)) → ℂ}
    (hψ : (totalSpinSOp3 V N).mulVec ψ = lam • ψ) :
    (totalSpinSOp3 V N).mulVec ((totalSpinSOpPlus V N).mulVec ψ) =
      (lam + 1) • (totalSpinSOpPlus V N).mulVec ψ := by
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSOp3 V N + totalSpinSOpPlus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpPlus (V := V) (N := N)
    have h' := sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hψ, Matrix.mulVec_smul]
  rw [add_smul, one_smul]

/-- **Iterated magnetic-quantum-number labelling, lowering ladder**:
for any `k : ℕ`,

  `Ŝ^z_{tot} · (Ŝ^-_{tot})^k · |σ_⊤⟩
    = (|V|·N/2 − k) · (Ŝ^-_{tot})^k · |σ_⊤⟩`.

Proof: induction on `k` using `totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec`
(generic single-step shift on any `Ŝ^z`-eigenvector). -/
theorem totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (k : ℕ) :
    (totalSpinSOp3 V N).mulVec
      (((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k : ℂ)) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
      magEigenvalueS_allAlignedConfigS]
    rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
    push_cast
    congr 1
    ring
  | succ k ih =>
    -- (Ŝ^-)^(k+1) · |⊤⟩ = Ŝ^- · ((Ŝ^-)^k · |⊤⟩).
    -- IH: Ŝ^z · ((Ŝ^-)^k · |⊤⟩) = (m_max - k) • (Ŝ^-)^k · |⊤⟩.
    -- Apply generic single-step shift with ψ = (Ŝ^-)^k · |⊤⟩, λ = m_max - k:
    --   Ŝ^z · (Ŝ^- · ((Ŝ^-)^k · |⊤⟩)) = (m_max - k - 1) • (Ŝ^- · ...).
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have h := totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_eigenvec ih
    rw [h]
    push_cast
    congr 1
    ring

/-- **Iterated magnetic-quantum-number labelling, raising ladder**:
for any `k : ℕ`,

  `Ŝ^z_{tot} · (Ŝ^+_{tot})^k · |σ_⊥⟩
    = (−|V|·N/2 + k) · (Ŝ^+_{tot})^k · |σ_⊥⟩`. -/
theorem totalSpinSOp3_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    (k : ℕ) :
    (totalSpinSOp3 V N).mulVec
      (((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + (k : ℂ)) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
      magEigenvalueS_allAlignedConfigS]
    rw [show ((Fin.last N).val : ℂ) = N from by simp [Fin.last]]
    push_cast
    congr 1
    ring
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    have h := totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_eigenvec ih
    rw [h]
    push_cast
    congr 1
    ring

/-! ## Ladder operators shift the magnetization subspace -/

/-- `Ŝ^-_tot` shifts magnetisation by `-1`: if `v ∈ magSubspaceS Λ N M`
then `Ŝ^-_tot · v ∈ magSubspaceS Λ N (M − 1)`.

Spin-`S` mirror of `totalSpinHalfOpMinus_mulVec_mem_magnetizationSubspace_of_mem`.
Uses the Cartan relation `[Ŝ_tot^(3), Ŝ^-_tot] = -Ŝ^-_tot`
(`totalSpinSOp3_commutator_totalSpinSOpMinus`). -/
theorem totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
    {M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS V N M) :
    (totalSpinSOpMinus V N).mulVec v ∈ magSubspaceS V N (M - 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  -- [Ŝtot^(3), Ŝtot^-] = -Ŝtot^- ⟹ Ŝtot^(3) · Ŝtot^- = Ŝtot^- · Ŝtot^(3) - Ŝtot^-
  have h := totalSpinSOp3_commutator_totalSpinSOpMinus (V := V) (N := N)
  have hcomm : totalSpinSOp3 V N * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSOp3 V N - totalSpinSOpMinus V N := by
    have hadd : totalSpinSOp3 V N * totalSpinSOpMinus V N =
        (totalSpinSOp3 V N * totalSpinSOpMinus V N -
          totalSpinSOpMinus V N * totalSpinSOp3 V N) +
        totalSpinSOpMinus V N * totalSpinSOp3 V N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ^+_tot` shifts magnetisation by `+1`: if `v ∈ magSubspaceS Λ N M`
then `Ŝ^+_tot · v ∈ magSubspaceS Λ N (M + 1)`.

Spin-`S` mirror of `totalSpinHalfOpPlus_mulVec_mem_magnetizationSubspace_of_mem`.
Uses `[Ŝ_tot^(3), Ŝ^+_tot] = +Ŝ^+_tot`
(`totalSpinSOp3_commutator_totalSpinSOpPlus`). -/
theorem totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem
    {M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS V N M) :
    (totalSpinSOpPlus V N).mulVec v ∈ magSubspaceS V N (M + 1) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  have h := totalSpinSOp3_commutator_totalSpinSOpPlus (V := V) (N := N)
  have hcomm : totalSpinSOp3 V N * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSOp3 V N + totalSpinSOpPlus V N := by
    have hadd : totalSpinSOp3 V N * totalSpinSOpPlus V N =
        (totalSpinSOp3 V N * totalSpinSOpPlus V N -
          totalSpinSOpPlus V N * totalSpinSOp3 V N) +
        totalSpinSOpPlus V N * totalSpinSOp3 V N := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

end LatticeSystem.Quantum
