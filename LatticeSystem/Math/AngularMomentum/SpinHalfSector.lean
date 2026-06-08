import LatticeSystem.Math.AngularMomentum.Multiplet

/-!
# Tasaki Appendix A.3.2: every level has a spin-0 or spin-1/2 representative (Theorem A.17)

Tasaki's Theorem A.17, "used repeatedly in the present book": for an `su(2)`-invariant Hamiltonian
`Ĥ`, every energy eigenvalue `E` admits a corresponding eigenstate `|Φ⟩` with either
`Ĵ⁽³⁾|Φ⟩ = 0` or `Ĵ⁽³⁾|Φ⟩ = (1/2)|Φ⟩`.  In words, to find all energy eigenvalues one only needs to
look at the `Ĵ⁽³⁾ = 0` and `Ĵ⁽³⁾ = 1/2` sectors.

It is a corollary of the multiplet degeneracy (Theorem A.16): starting from a joint
energy/`Ĵ²`/`Ĵ⁽³⁾` eigenstate of spin `J = n/2` (Theorem A.13), the multiplet contains a state at
the magnetic number `M = J − ⌊J⌋ ∈ {0, 1/2}` — explicitly `M = 0` when `2J` is even and `M = 1/2`
when `2J` is odd, obtained from Theorem A.16 with `k = ⌊J⌋`.  The one ingredient not provable from
finite-matrix algebra alone is the *existence* of a simultaneous eigenstate of the commuting
self-adjoint family `Ĥ, Ĵ², Ĵ⁽³⁾` inside the `E`-eigenspace (simultaneous diagonalization of
commuting Hermitian operators); this is recorded as a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.3.2, Theorem A.17, p. 473.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d] (H J1 J2 J3 : Matrix d d ℂ)

/-- **Simultaneous diagonalization of the commuting self-adjoint family `Ĥ, Ĵ², Ĵ⁽³⁾`, AXIOM.**
For self-adjoint `Ĥ` and angular-momentum components `Ĵ⁽ᵅ⁾` (`su(2)` relations, each commuting with
`Ĥ`), any energy eigenvector `v ≠ 0` (`Ĥ v = E v`) has, inside the same `E`-eigenspace, a nonzero
*joint* eigenstate `Φ` of `Ĵ²` and `Ĵ⁽³⁾`: there are reals `J ≥ 0` and `M` with
`Ĵ² Φ = J(J+1) Φ`, `Ĵ⁽³⁾ Φ = M Φ` and `Ĥ Φ = E Φ`.  This is the standard simultaneous
diagonalizability of a commuting family of Hermitian operators; recorded as a documented axiom. -/
axiom exists_joint_su2_energy_eigenstate {d : Type*} [Fintype d]
    (H J1 J2 J3 : Matrix d d ℂ) (hH : H.IsHermitian) (h1 : J1.IsHermitian) (h2 : J2.IsHermitian)
    (h3 : J3.IsHermitian) (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H) (hcH3 : H * J3 = J3 * H)
    (h12 : J1 * J2 - J2 * J1 = Complex.I • J3) (h23 : J2 * J3 - J3 * J2 = Complex.I • J1)
    (h31 : J3 * J1 - J1 * J3 = Complex.I • J2) {E : ℂ} {v : d → ℂ} (hv : v ≠ 0)
    (hEv : H.mulVec v = E • v) :
    ∃ (Φ : d → ℂ) (Jr M : ℝ), Φ ≠ 0 ∧ 0 ≤ Jr ∧
      (J1 * J1 + J2 * J2 + J3 * J3).mulVec Φ = ((Jr * (Jr + 1) : ℝ) : ℂ) • Φ ∧
      J3.mulVec Φ = (M : ℂ) • Φ ∧ H.mulVec Φ = E • Φ

omit [DecidableEq d] in
/-- **Tasaki Theorem A.17 (spin-0 / spin-1/2 sector suffices).**  For an `su(2)`-invariant
self-adjoint `Ĥ` (each `Ĵ⁽ᵅ⁾` self-adjoint, `su(2)` relations, `[Ĥ, Ĵ⁽ᵅ⁾] = 0`), every energy
eigenvalue `E` (witnessed by some `v ≠ 0`, `Ĥ v = E v`) has a corresponding eigenstate `Φ ≠ 0`
(`Ĥ Φ = E Φ`) with either `Ĵ⁽³⁾ Φ = 0` or `Ĵ⁽³⁾ Φ = (1/2) Φ`.  From a joint eigenstate of spin
`J = n/2` (Theorem A.13) the multiplet (Theorem A.16) contains the magnetic number `M = J − ⌊J⌋`,
which is `0` for even `n` and `1/2` for odd `n` (take `k = ⌊J⌋`). -/
theorem ham_eigenstate_spin_zero_or_half (hH : H.IsHermitian) (h1 : J1.IsHermitian)
    (h2 : J2.IsHermitian) (h3 : J3.IsHermitian) (hcH1 : H * J1 = J1 * H) (hcH2 : H * J2 = J2 * H)
    (hcH3 : H * J3 = J3 * H) (h12 : J1 * J2 - J2 * J1 = Complex.I • J3)
    (h23 : J2 * J3 - J3 * J2 = Complex.I • J1) (h31 : J3 * J1 - J1 * J3 = Complex.I • J2)
    {E : ℂ} {v : d → ℂ} (hv : v ≠ 0) (hEv : H.mulVec v = E • v) :
    ∃ Φ : d → ℂ, Φ ≠ 0 ∧ H.mulVec Φ = E • Φ ∧
      (J3.mulVec Φ = 0 ∨ J3.mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ) := by
  -- Joint `Ĥ`/`Ĵ²`/`Ĵ⁽³⁾` eigenstate in the `E`-eigenspace (simultaneous diagonalization).
  obtain ⟨Φ0, Jr, M, hΦ0, hJr, hsq, h3eq, hHΦ⟩ :=
    exists_joint_su2_energy_eigenstate H J1 J2 J3 hH h1 h2 h3 hcH1 hcH2 hcH3 h12 h23 h31 hv hEv
  -- `J = n/2` (Theorem A.13).
  obtain ⟨n, hn⟩ := angMom_J_eq_half_nat J1 J2 J3 h1 h2 h12 h23 h31 hΦ0 hJr hsq h3eq
  have hmult := ham_su2_multiplet H J1 J2 J3 hcH1 hcH2 hcH3 h1 h2 h12 h23 h31 hΦ0 hJr hsq h3eq hHΦ
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `n = m + m` even ⇒ `J = m` ⇒ companion at `M = 0`.
    have hJrm : Jr = (m : ℝ) := by rw [hn, hm]; push_cast; ring
    obtain ⟨Ψ, hΨ, _, h3Ψ, hHΨ⟩ := hmult m (by rw [hJrm]; linarith)
    refine ⟨Ψ, hΨ, hHΨ, Or.inl ?_⟩
    rw [h3Ψ, show ((Jr - (m : ℝ) : ℝ) : ℂ) = 0 by rw [hJrm]; push_cast; ring, zero_smul]
  · -- `n = 2m + 1` odd ⇒ `J = m + 1/2` ⇒ companion at `M = 1/2`.
    have hJrm : Jr = (m : ℝ) + 1 / 2 := by rw [hn, hm]; push_cast; ring
    obtain ⟨Ψ, hΨ, _, h3Ψ, hHΨ⟩ := hmult m (by rw [hJrm]; linarith)
    refine ⟨Ψ, hΨ, hHΨ, Or.inr ?_⟩
    rw [h3Ψ, show ((Jr - (m : ℝ) : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) by rw [hJrm]; push_cast; ring]

end LatticeSystem.Math
