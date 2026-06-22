import LatticeSystem.Quantum.SpinS.MultiSiteCasimirCore

/-!
# Multi-site spin-`S` Casimir decomposition (Tasaki §2.4 / §2.5 setup)

This file proves the **diagonal/off-diagonal decomposition** of the
total spin-`S` Casimir `(Ŝ_tot)²` on the multi-site Hilbert space:

  `(Ŝ_tot)² = Σ_x (Ŝ_x · Ŝ_x) + Σ_{x ≠ y} (Ŝ_x · Ŝ_y)
           = |Λ| · (N(N+2)/4) · 1 + Σ_{x ≠ y} (Ŝ_x · Ŝ_y)`

starting from the existing identity
`totalSpinSSquared_eq_sum_spinSDot`. Specialising to `Λ = Fin 2`
gives the **two-site Casimir-Heisenberg identity**

  `(Ŝ_tot)² = (N(N+2)/2) · 1 + 2 · (Ŝ_0 · Ŝ_1)`

which solves for `Ŝ_0 · Ŝ_1` as a polynomial in `(Ŝ_tot)²` — the
operator-level form of Tasaki Problem 2.5.a in the single-bond
(`z = 1`) case.

Tracked as part of Tasaki §2.5 spin-`S` infrastructure (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Two-site spin-`S` Heisenberg eigenvalue formula from Casimir -/

/-- **Eigenvalue conversion from `(Ŝ_tot)²` to `Ŝ_0 · Ŝ_1`** on the
two-site Hilbert space. If `Φ` is a `(Ŝ_tot)²`-eigenvector at
eigenvalue `λ`, then `Φ` is a `Ŝ_0 · Ŝ_1`-eigenvector at eigenvalue
`λ/2 − N(N+2)/4`.

This is the ABSTRACT operator-eigenvalue form of Tasaki Problem 2.5.a
(single-bond, `z = 1` case): every joint eigenstate of `(Ŝ_tot)²` is
also an eigenstate of `Ŝ_0 · Ŝ_1`, with the conversion formula
`μ = λ/2 − S(S+1)`.

In particular, on a `(Ŝ_tot)² = 0` eigenstate (the singlet sector,
total-spin quantum number `j = 0`), `Ŝ_0 · Ŝ_1 = −N(N+2)/4 = −S(S+1)`. -/
theorem spinSDot_fin_two_mulVec_of_totalSpinSSquared_eigenvec
    (N : ℕ) {lam : ℂ} {Φ : (Fin 2 → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared (Fin 2) N).mulVec Φ = lam • Φ) :
    (spinSDot (0 : Fin 2) 1 N).mulVec Φ =
      ((lam / 2) - ((N : ℂ) * (N + 2) / 4)) • Φ := by
  rw [spinSDot_fin_two_eq, Matrix.sub_mulVec]
  -- LHS = ((1/2) • (Ŝ_tot)²).mulVec Φ - ((N(N+2)/4) • 1).mulVec Φ.
  rw [show ((1 / 2 : ℂ) • totalSpinSSquared (Fin 2) N).mulVec Φ =
        (1 / 2 : ℂ) • (totalSpinSSquared (Fin 2) N).mulVec Φ from
        Matrix.smul_mulVec _ _ _]
  rw [show (((N : ℂ) * (N + 2) / 4) • (1 : ManyBodyOpS (Fin 2) N)).mulVec Φ =
        ((N : ℂ) * (N + 2) / 4) • (1 : ManyBodyOpS (Fin 2) N).mulVec Φ from
        Matrix.smul_mulVec _ _ _]
  rw [Matrix.one_mulVec, hΦ]
  rw [show ((1 / 2 : ℂ) • lam • Φ : (Fin 2 → Fin (N + 1)) → ℂ) =
        ((1 / 2 : ℂ) * lam) • Φ from by rw [smul_smul]]
  rw [show ((lam / 2 - (N : ℂ) * (N + 2) / 4) • Φ : (Fin 2 → Fin (N + 1)) → ℂ) =
        ((1 / 2) * lam) • Φ - ((N : ℂ) * (N + 2) / 4) • Φ from by
    rw [show (lam / 2 - (N : ℂ) * (N + 2) / 4) =
          ((1 / 2) * lam) - ((N : ℂ) * (N + 2) / 4) from by ring]
    rw [sub_smul]]

/-- **Single-bond Heisenberg eigenvalue formula** on the two-site
spin-`S` system. For the single-bond Hamiltonian `J • Ŝ_0 · Ŝ_1`
(coupling constant `J : ℂ`), if `Φ` is a `(Ŝ_tot)²`-eigenvector at
`λ`, then `Φ` is a `J • Ŝ_0 · Ŝ_1`-eigenvector at
`J · (λ/2 − N(N+2)/4)`. -/
theorem smul_spinSDot_fin_two_mulVec_of_totalSpinSSquared_eigenvec
    (N : ℕ) (J : ℂ) {lam : ℂ} {Φ : (Fin 2 → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared (Fin 2) N).mulVec Φ = lam • Φ) :
    (J • spinSDot (0 : Fin 2) 1 N).mulVec Φ =
      (J * ((lam / 2) - ((N : ℂ) * (N + 2) / 4))) • Φ := by
  rw [Matrix.smul_mulVec,
    spinSDot_fin_two_mulVec_of_totalSpinSSquared_eigenvec N hΦ,
    smul_smul]

/-- **Singlet specialisation** (`λ = 0`): a `(Ŝ_tot)²`-zero eigenvector
on the two-site spin-`S` system has `Ŝ_0 · Ŝ_1`-eigenvalue
`−N(N+2)/4 = −S(S+1)`.

This is the operator-level form of **Tasaki Problem 2.5.a** in the
single-bond (`z = 1`) case: the ground-state energy of the two-site
spin-`S` antiferromagnetic Heisenberg model is `−S(S+1)`. -/
theorem spinSDot_fin_two_mulVec_of_totalSpinSSquared_zero
    (N : ℕ) {Φ : (Fin 2 → Fin (N + 1)) → ℂ}
    (hΦ : (totalSpinSSquared (Fin 2) N).mulVec Φ = 0) :
    (spinSDot (0 : Fin 2) 1 N).mulVec Φ =
      (-((N : ℂ) * (N + 2) / 4)) • Φ := by
  have hΦ' : (totalSpinSSquared (Fin 2) N).mulVec Φ = (0 : ℂ) • Φ := by
    rw [hΦ, zero_smul]
  rw [spinSDot_fin_two_mulVec_of_totalSpinSSquared_eigenvec N hΦ']
  congr 1
  ring

end LatticeSystem.Quantum
