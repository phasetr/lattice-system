import LatticeSystem.Quantum.SpinS.MultiSiteCartanPlusMinus
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Casimir rearrangement: `Ŝ^+_{tot} · Ŝ^-_{tot} = (Ŝ_{tot})² − (Ŝ^z_{tot})² + Ŝ^z_{tot}`

The standard SU(2) Casimir-rearrangement identity at the multi-site
level. From the single-site identity
`Ŝ^+ Ŝ^- = (Ŝ^{(1)})² + (Ŝ^{(2)})² + Ŝ^{(3)}` (proven by
`(Ŝ^{(1)} + i Ŝ^{(2)})(Ŝ^{(1)} − i Ŝ^{(2)}) = (Ŝ^{(1)})² + (Ŝ^{(2)})² −
i [Ŝ^{(1)}, Ŝ^{(2)}] = (Ŝ^{(1)})² + (Ŝ^{(2)})² − i · i · Ŝ^{(3)}`)
the same identity lifts directly to the multi-site total operators
via the multi-site Plus/Minus decomposition (`totalSpinSOpPlus_eq_add`,
`totalSpinSOpMinus_eq_sub`) and the multi-site Cartan
`[Ŝ^{(1)}_{tot}, Ŝ^{(2)}_{tot}] = i · Ŝ^{(3)}_{tot}`
(`totalSpinSOp1_commutator_totalSpinSOp2_named`). Then substitute
`(Ŝ^{(1)}_{tot})² + (Ŝ^{(2)}_{tot})² = (Ŝ_{tot})² − (Ŝ^{(3)}_{tot})²`
via `totalSpinSSquared_def`.

Symmetric: `Ŝ^-_{tot} · Ŝ^+_{tot} = (Ŝ_{tot})² − (Ŝ^z_{tot})² − Ŝ^z_{tot}`.

These identities are the operator-algebraic input to the
inductive non-vanishing argument for the saturated-ferromagnet
ladder iterates `(Ŝ^-_{tot})^k · |σ_⊤⟩` (k ≤ 2m_max), via the
eigenvalue identity
`Ŝ^+_{tot} Ŝ^-_{tot} v_k = ((m_max)(m_max+1) − (m_max−k)(m_max−k−1)) v_k
   = (k+1)(2m_max − k) v_k`,
which is non-zero for k = 0, ..., 2m_max − 1 and vanishes only at
k = 2m_max.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Sum identity:
`Ŝ^+_{tot} Ŝ^-_{tot} + Ŝ^-_{tot} Ŝ^+_{tot} =
  2 · ((Ŝ^{(1)}_{tot})² + (Ŝ^{(2)}_{tot})²)` -/

/-- The anticommutator-like sum
`Ŝ^+_{tot} · Ŝ^-_{tot} + Ŝ^-_{tot} · Ŝ^+_{tot} =
   2 · ((Ŝ^{(1)}_{tot})² + (Ŝ^{(2)}_{tot})²)`.

Proof: expand both products
`(Ŝ^{(1)} ± i Ŝ^{(2)})(Ŝ^{(1)} ∓ i Ŝ^{(2)})` and add — the
`±i [Ŝ^{(1)}, Ŝ^{(2)}]` parts cancel. -/
theorem totalSpinSOpPlus_mul_totalSpinSOpMinus_add_totalSpinSOpMinus_mul_totalSpinSOpPlus :
    (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N +
        totalSpinSOpMinus V N * totalSpinSOpPlus V N =
      (2 : ℂ) • ((totalSpinSOp1 V N) * (totalSpinSOp1 V N) +
        (totalSpinSOp2 V N) * (totalSpinSOp2 V N)) := by
  rw [totalSpinSOpPlus_eq_add, totalSpinSOpMinus_eq_sub]
  set A := totalSpinSOp1 V N
  set B := totalSpinSOp2 V N
  -- (A + iB)(A - iB) + (A - iB)(A + iB)
  -- = (A² - iAB + iBA + B²) + (A² + iAB - iBA + B²)
  -- = 2A² + 2B²
  have h1 : (A + Complex.I • B) * (A - Complex.I • B) =
      A * A + B * B + Complex.I • (B * A - A * B) := by
    rw [add_mul, mul_sub, mul_sub]
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul, sub_neg_eq_add]
    rw [smul_sub]
    abel
  have h2 : (A - Complex.I • B) * (A + Complex.I • B) =
      A * A + B * B + Complex.I • (A * B - B * A) := by
    rw [sub_mul, mul_add, mul_add]
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul]
    rw [show (A * A + Complex.I • (A * B) - (Complex.I • (B * A) + -(B * B))) =
        A * A + B * B + (Complex.I • (A * B) - Complex.I • (B * A)) from by abel]
    rw [smul_sub]
  rw [h1, h2]
  rw [show (A * A + B * B + Complex.I • (B * A - A * B) +
        (A * A + B * B + Complex.I • (A * B - B * A)) : ManyBodyOpS V N) =
      (2 : ℂ) • (A * A + B * B) +
      (Complex.I • (B * A - A * B) + Complex.I • (A * B - B * A)) from by
    rw [show ((2 : ℂ) • (A * A + B * B) : ManyBodyOpS V N) = (A*A + B*B) + (A*A + B*B) from by
      rw [show ((2 : ℂ) : ℂ) = 1 + 1 from by norm_num]
      rw [add_smul, one_smul]]
    abel]
  rw [show ((Complex.I • (B * A - A * B) + Complex.I • (A * B - B * A) :
        ManyBodyOpS V N) : ManyBodyOpS V N) =
      Complex.I • ((B * A - A * B) + (A * B - B * A)) from by
    rw [smul_add]]
  rw [show ((B * A - A * B) + (A * B - B * A) : ManyBodyOpS V N) = 0 from by abel]
  rw [smul_zero, add_zero]

/-! ## Casimir rearrangement -/

/-- **Casimir rearrangement (PlusMinus order)**:
`Ŝ^+_{tot} · Ŝ^-_{tot} = (Ŝ_{tot})² − (Ŝ^z_{tot})² + Ŝ^z_{tot}`.

Derivation: combine the sum identity (above) with the multi-site
Cartan ⁺⁻ (`totalSpinSOpPlus_commutator_totalSpinSOpMinus`):
- Sum: `S^+ S^- + S^- S^+ = 2(A² + B²)` where `A = Ŝ^{(1)}_{tot}, B = Ŝ^{(2)}_{tot}`.
- Diff: `S^+ S^- − S^- S^+ = 2 · Ŝ^{(3)}_{tot}`.
- Add: `2 · S^+ S^- = 2(A² + B²) + 2 · Ŝ^{(3)}_{tot}`.
- Divide by 2 and substitute `A² + B² = Ŝ_{tot}² − (Ŝ^{(3)}_{tot})²`. -/
theorem totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z :
    (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N +
        totalSpinSOp3 V N := by
  have h_sum :=
    totalSpinSOpPlus_mul_totalSpinSOpMinus_add_totalSpinSOpMinus_mul_totalSpinSOpPlus
      (V := V) (N := N)
  have h_diff :=
    totalSpinSOpPlus_commutator_totalSpinSOpMinus (V := V) (N := N)
  -- Add: 2 · S^+ S^- = 2(A² + B²) + 2 · S^z.
  have h_two_PM : (2 : ℂ) • ((totalSpinSOpPlus V N : ManyBodyOpS V N) *
        totalSpinSOpMinus V N) =
      (2 : ℂ) • ((totalSpinSOp1 V N) * (totalSpinSOp1 V N) +
          (totalSpinSOp2 V N) * (totalSpinSOp2 V N)) +
        (2 : ℂ) • totalSpinSOp3 V N := by
    have hadd : (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N +
        totalSpinSOpMinus V N * totalSpinSOpPlus V N +
        ((totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N -
          totalSpinSOpMinus V N * totalSpinSOpPlus V N) =
        (2 : ℂ) • ((totalSpinSOpPlus V N : ManyBodyOpS V N) *
          totalSpinSOpMinus V N) := by
      rw [show ((2 : ℂ) : ℂ) = 1 + 1 from by norm_num]
      rw [add_smul, one_smul]
      abel
    rw [← hadd, h_sum, h_diff]
  -- Cancel the 2 •.
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have h_PM : (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      (totalSpinSOp1 V N) * (totalSpinSOp1 V N) +
        (totalSpinSOp2 V N) * (totalSpinSOp2 V N) +
        totalSpinSOp3 V N := by
    have h := h_two_PM
    rw [← smul_add] at h
    exact (smul_right_injective (ManyBodyOpS V N) h2ne) h
  rw [h_PM, totalSpinSSquared_def]
  abel

/-- **Casimir rearrangement (MinusPlus order)**:
`Ŝ^-_{tot} · Ŝ^+_{tot} = (Ŝ_{tot})² − (Ŝ^z_{tot})² − Ŝ^z_{tot}`.

Derivation: use sum + (-diff). -/
theorem totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z :
    (totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
      totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N -
        totalSpinSOp3 V N := by
  have h_PM := totalSpinSOpPlus_mul_totalSpinSOpMinus_eq_casimir_minus_z_sq_add_z
    (V := V) (N := N)
  have h_diff :=
    totalSpinSOpPlus_commutator_totalSpinSOpMinus (V := V) (N := N)
  -- S^- S^+ = S^+ S^- − 2 S^z.
  have hMP : (totalSpinSOpMinus V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
      (totalSpinSOpPlus V N : ManyBodyOpS V N) * totalSpinSOpMinus V N -
        (2 : ℂ) • totalSpinSOp3 V N := by
    rw [← h_diff]; abel
  rw [hMP, h_PM]
  rw [show ((2 : ℂ) • totalSpinSOp3 V N : ManyBodyOpS V N) =
      totalSpinSOp3 V N + totalSpinSOp3 V N from by
    rw [show ((2 : ℂ) : ℂ) = 1 + 1 from by norm_num]
    rw [add_smul, one_smul]]
  abel

end LatticeSystem.Quantum
