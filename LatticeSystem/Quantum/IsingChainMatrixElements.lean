import LatticeSystem.Quantum.IsingChain
import LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance

/-!
# Configuration-basis matrix elements of the open-chain quantum Ising Hamiltonian

The entries of `quantumIsingHamiltonian N J h`, viewed as a matrix over the computational-basis
configurations `τ : Fin (N + 1) → Fin 2`, expressed through the domain-wall bond count and the
single-site flip `siteFlipAt`
(`LatticeSystem.Quantum.TimeReversalMulti.SpinOpEquivariance`):

* the action on an arbitrary vector splits into a diagonal `σ^z σ^z` part and an off-diagonal
  `σ^x` part (`quantumIsingHamiltonian_mulVec_apply`);
* the diagonal entry is `-J` times the signed bond sum (`quantumIsingHamiltonian_apply_diag`);
* the entry between a configuration and its single-site flip is `-h`
  (`quantumIsingHamiltonian_apply_siteFlip`);
* every other entry vanishes (`quantumIsingHamiltonian_apply_eq_zero`).

The chain is **open**: the bond sum runs over `Fin N`, so there are `L - 1 = N` bonds on
`L = N + 1` sites and the constant configurations have energy `-J N`. The periodic
`isingCycleHamiltonian` is a different operator and is deliberately not used here.

These are the matrix elements behind Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Problem 3.3.a (statement p. 59, solution pp. 498-501), eqs. (S.24)-(S.27), for the
spin-`1/2` chain `Ĥ = -Σ_x Ŝ_x^(3) Ŝ_{x+1}^(3) - λ Σ_x Ŝ_x^(1)` of eq. (3.3.1), p. 56; with the
convention `Ŝ^α = σ^α / 2` that Hamiltonian is `quantumIsingHamiltonian N (1/4) (λ/2)`.

The module is pure reuse: `quantumIsingHamiltonian` (`LatticeSystem.Quantum.IsingChain`),
`siteFlipAt`, `onSite_pauliZ_mulVec_apply`, `onSite_pauliX_mulVec_apply`
(`…TimeReversalMulti.SpinOpEquivariance`), `basisVec`, `mulVec_basisVec_apply`
(`LatticeSystem.Quantum.ManyBody`). No spin-flip or sign convention is introduced here.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- Product of the two `σ^z` eigenvalue signs at the endpoints of a bond: it is `+1` on an
aligned bond and `-1` across a domain wall. -/
private theorem pauliZ_sign_mul (a b : Fin 2) :
    (if a = 0 then (1 : ℂ) else -1) * (if b = 0 then (1 : ℂ) else -1) =
      if a = b then (1 : ℂ) else -1 := by
  fin_cases a <;> fin_cases b <;> norm_num

/-- Action of a nearest-neighbour `σ^z σ^z` bond term on a vector: multiplication by the bond
sign `+1` (aligned) or `-1` (domain wall). -/
private theorem spinZ_bond_mulVec_apply (N : ℕ) (i : Fin N)
    (v : (Fin (N + 1) → Fin 2) → ℂ) (τ : Fin (N + 1) → Fin 2) :
    ((spinZ N i.castSucc * spinZ N i.succ) *ᵥ v) τ =
      (if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) * v τ := by
  rw [← Matrix.mulVec_mulVec]
  unfold spinZ
  simp only [onSite_pauliZ_mulVec_apply, ← mul_assoc, pauliZ_sign_mul]

/-- **(A1)** Pointwise action of the open-chain quantum Ising Hamiltonian on a vector: the
`σ^z σ^z` part multiplies by the signed bond sum, the transverse `σ^x` part sums the values at
all single-site flips.

  `(Ĥ *ᵥ v) τ = -J (Σ_i ±1) v τ - h Σ_x v (siteFlipAt τ x)`,

the sign in the bond sum being `+1` when `τ` is aligned across bond `i` and `-1` across a domain
wall. This is the identity all configuration-basis matrix elements below are read off from. -/
theorem quantumIsingHamiltonian_mulVec_apply (N : ℕ) (J h : ℝ)
    (v : (Fin (N + 1) → Fin 2) → ℂ) (τ : Fin (N + 1) → Fin 2) :
    (quantumIsingHamiltonian N J h *ᵥ v) τ =
      -(J : ℂ) * (∑ i : Fin N, if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) * v τ
        - (h : ℂ) * ∑ i : Fin (N + 1), v (siteFlipAt τ i) := by
  unfold quantumIsingHamiltonian
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec,
    Matrix.sum_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    spinZ_bond_mulVec_apply, spinX, onSite_pauliX_mulVec_apply, ← Finset.sum_mul]
  ring

/-- Two configurations of `Fin 2` never satisfy `1 - a = a`, so a single-site flip always
changes the configuration. -/
private theorem fin2_one_sub_ne (a : Fin 2) : (1 : Fin 2) - a ≠ a := by
  revert a
  decide

/-- A single-site flip never returns the original configuration. -/
private theorem siteFlipAt_ne {Λ : Type*} [DecidableEq Λ] (τ : Λ → Fin 2) (x : Λ) :
    siteFlipAt τ x ≠ τ := by
  intro hEq
  refine fin2_one_sub_ne (τ x) ?_
  rw [← siteFlipAt_self τ x]
  exact congrFun hEq x

/-- **(A2)** Diagonal matrix element, Tasaki eqs. (S.24) and (S.25): `⟨Φ_τ|Ĥ|Φ_τ⟩` is `-J` times
the signed bond sum of `τ`, with no contribution from the transverse field (a single-site flip
never reproduces `τ`). For the constant configurations this is `-J N = -(L - 1) J`. -/
theorem quantumIsingHamiltonian_apply_diag (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2) :
    quantumIsingHamiltonian N J h τ τ =
      -(J : ℂ) * ∑ i : Fin N, (if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) := by
  rw [← mulVec_basisVec_apply (quantumIsingHamiltonian N J h) τ τ,
    quantumIsingHamiltonian_mulVec_apply, basisVec_self,
    Finset.sum_eq_zero (fun i _ => basisVec_of_ne (siteFlipAt_ne τ i))]
  ring

/-- **(A3)** Off-diagonal matrix element between a configuration and its flip at a single site,
Tasaki eqs. (S.26) and (S.27): `⟨Φ_{siteFlipAt τ x}|Ĥ|Φ_τ⟩ = -h`, independently of `J`, of `τ`
and of the flipped site `x`. -/
theorem quantumIsingHamiltonian_apply_siteFlip (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2)
    (x : Fin (N + 1)) :
    quantumIsingHamiltonian N J h (siteFlipAt τ x) τ = -(h : ℂ) := by
  rw [← mulVec_basisVec_apply (quantumIsingHamiltonian N J h) (siteFlipAt τ x) τ,
    quantumIsingHamiltonian_mulVec_apply, basisVec_of_ne (siteFlipAt_ne τ x),
    Finset.sum_eq_single x]
  · rw [siteFlipAt_involutive, basisVec_self]
    ring
  · intro i _ hix
    refine basisVec_of_ne ?_
    intro hEq
    refine fin2_one_sub_ne (τ x) ?_
    rw [← siteFlipAt_self τ x, ← siteFlipAt_of_ne (siteFlipAt τ x) (Ne.symm hix)]
    exact congrFun hEq x
  · intro hx
    exact absurd (Finset.mem_univ x) hx

end LatticeSystem.Quantum
