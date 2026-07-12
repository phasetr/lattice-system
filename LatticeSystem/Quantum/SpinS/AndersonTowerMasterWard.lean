import LatticeSystem.Quantum.SpinS.AndersonTowerTelescoping
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBoundPhat

/-!
# Tasaki §4.2.2 Proposition 4.10: the master Ward identity for Cartesian order words

This module extracts the **master Ward identity** at the core of the singlet-isotropy mechanism of
Proposition 4.10 (arc PR-3.2b, sub-step L4b-i).  It is the expectation-value shadow of the operator
telescoping identity `totalSpinSOpVec_mul_cartWord_eq` (`AndersonTowerTelescoping`).

For a total-spin singlet `Φ` (`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`, hence `Ŝ²_tot Φ = 0`) evaluate the
scalar `⟨Φ, Ŝ^{(γ)}_tot (ô^{w} Φ)⟩` two ways.  Moving the Hermitian generator `Ŝ^{(γ)}_tot` to the
left (`hermitian_dotProduct_shift`) annihilates it against the singlet, so the scalar is `0`.
Moving it to the right through the word (`totalSpinSOpVec_mulVec_cartWord_singlet`) rewrites it as
`i Σ_k Σ_δ ε_{γ w_k δ} ⟨Φ, ô^{w[k ↦ δ]} Φ⟩`.  Cancelling the nonzero factor `i` gives the

**master Ward identity**

`Σ_k Σ_δ ε_{γ w_k δ} ⟨Φ, ô^{w[k ↦ δ]} Φ⟩ = 0`     (∀ γ, ∀ w),

where `w[k ↦ δ] = w.set k δ` is the axis word with its `k`-th letter rotated from `w_k` to `δ`.
This is the algebraic statement that the so(3) generators kill the expectation tensor
`⟨Φ, ô^{w} Φ⟩`; downstream (L4b-ii) it is read as the vanishing of the rotation derivative of the
directional moment `g(n) = ⟨Φ, (ô·n)^{2M} Φ⟩`.  Only the algebraic core is established here; the
directional-moment application and its global constancy are the next steps.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.57)–(4.2.61), p.108–109; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Master Ward identity** (Prop 4.10 arc PR-3.2b sub-step L4b-i).  For a total-spin singlet `Φ`
(`Ŝ³_tot Φ = 0`, `Ŝ¹_tot Φ = 0`), the Levi-Civita-weighted single-letter rotation sum of the
Cartesian order-word expectation vanishes,

`Σ_k Σ_δ ε_{γ w_k δ} ⟨Φ, ô^{w[k ↦ δ]} Φ⟩ = 0`,

for every axis `γ` and word `w`.  Proof: the scalar `⟨Φ, Ŝ^{(γ)}_tot (ô^{w} Φ)⟩` is `0` by moving
the Hermitian generator `Ŝ^{(γ)}_tot` (`hermitian_dotProduct_shift`, Hermitian by
`totalSpinSOp{1,2,3}_isHermitian`) onto the singlet, while the telescoping singlet corollary
`totalSpinSOpVec_mulVec_cartWord_singlet` rewrites the same scalar as `i` times the displayed sum;
cancelling `i ≠ 0` gives the identity.  This is the expectation-value core of the singlet-isotropy
mechanism; L4b-ii reads it as the vanishing rotation derivative of the directional moment. -/
theorem cartWord_ward_singlet (A : Λ → Bool) (γ : Fin 3) (w : List (Fin 3))
    (Φ : (Λ → Fin (N + 1)) → ℂ) (h3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (h1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (∑ k : Fin w.length, ∑ δ : Fin 3,
        leviCivita3 γ (w.get k) δ * (star Φ ⬝ᵥ (cartWord A N (w.set (k : ℕ) δ)).mulVec Φ)) = 0 := by
  -- The generator `Ŝ^{(γ)}_tot` is Hermitian and annihilates the singlet.
  have hHerm : (totalSpinSOpVec Λ N γ).IsHermitian := by
    fin_cases γ <;>
      simp only [totalSpinSOpVec, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · exact totalSpinSOp1_isHermitian Λ N
    · exact totalSpinSOp2_isHermitian Λ N
    · exact totalSpinSOp3_isHermitian Λ N
  have hzero : (totalSpinSOpVec Λ N γ).mulVec Φ = 0 := by
    fin_cases γ <;>
      simp only [totalSpinSOpVec, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    · exact h1
    · exact totalSpinSOp2_mulVec_eq_zero_of_singlet Φ h3 h1
    · exact h3
  -- Distributing `star Φ ⬝ᵥ ·` through the telescoping rotation sum.
  have hsum : (star Φ ⬝ᵥ ∑ k : Fin w.length, ∑ δ : Fin 3,
        leviCivita3 γ (w.get k) δ • (cartWord A N (w.set (k : ℕ) δ)).mulVec Φ)
      = ∑ k : Fin w.length, ∑ δ : Fin 3,
          leviCivita3 γ (w.get k) δ * (star Φ ⬝ᵥ (cartWord A N (w.set (k : ℕ) δ)).mulVec Φ) := by
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [dotProduct_smul, smul_eq_mul]
  -- Evaluate `⟨Φ, Ŝ^{(γ)}_tot (ô^{w} Φ)⟩` by shifting the Hermitian generator onto the singlet.
  have key : star Φ ⬝ᵥ (totalSpinSOpVec Λ N γ).mulVec ((cartWord A N w).mulVec Φ) = 0 := by
    rw [Matrix.mulVec_mulVec, hermitian_dotProduct_shift hHerm, hzero, star_zero,
      zero_dotProduct]
  -- The same scalar equals `i` times the Ward sum via the telescoping singlet corollary.
  rw [totalSpinSOpVec_mulVec_cartWord_singlet A γ w Φ h3 h1, dotProduct_smul, smul_eq_mul,
    hsum] at key
  exact (mul_eq_zero.mp key).resolve_left Complex.I_ne_zero

end LatticeSystem.Quantum
