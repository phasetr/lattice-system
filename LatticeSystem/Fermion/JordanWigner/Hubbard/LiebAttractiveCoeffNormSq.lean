import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveCoeffBridge

/-!
# The spin-reflection and block coefficient matrices have equal entry magnitudes (Tasaki §10.2.1)

Twenty-fifth layer (PR25) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

The reflection-positive energy assembly works in two coordinate systems: the
kinetic energy is a trace on the block coefficient matrix `hubbardBlockCoeff (Uᴴψ)`
(PR23), while the interaction energy and the positive-semidefinite / Perron–Frobenius
structure live on the spin-reflection coefficient matrix `spinReflectionCoeff ψ`
(PR24, PR1). PR17 relates the two entrywise by a Jordan–Wigner sign `ε`:
`spinReflectionCoeff (Uψ) = ε ⊙ hubbardBlockCoeff ψ`. Since `ε = ±1` is a root of
unity (`|ε| = 1`), the two matrices have **equal entry magnitudes**:

  `|spinReflectionCoeff ψ (u,h)|² = |hubbardBlockCoeff (Uᴴψ) (u,h)|²`.

This is the bridge that lets the spin-reflection variational replacement `C ↦ |C|`
(run on the positive-semidefinite `spinReflectionCoeff`) control the interaction
energy expressed on the block coefficient matrix, without transporting
positive-semidefiniteness through the (non-gauge) sign `ε`.

## Main results

* `translationJwSign_normSq` — the fermionic translation sign has unit magnitude.
* `normSq_translationJwSign_mul` — multiplying by the sign preserves `normSq`.
* `spinReflectionCoeff_normSq_eq_hubbardBlockCoeff` — equal entry magnitudes of the
  two coefficient matrices.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Complex
open scoped BigOperators

variable {M N : ℕ}

/-- The fermionic translation (Jordan–Wigner) sign is a `±1` root of unity, so it
has unit magnitude. -/
theorem translationJwSign_normSq (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2) :
    Complex.normSq (translationJwSign π σ) = 1 := by
  have h2 : (Complex.normSq (translationJwSign π σ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply, translationJwSign_star,
      translationJwSign_sq]
  exact_mod_cast h2

/-- Multiplying by the fermionic translation sign preserves the squared magnitude. -/
theorem normSq_translationJwSign_mul (π : Equiv.Perm (Fin M)) (σ : Fin M → Fin 2)
    (z : ℂ) :
    Complex.normSq (translationJwSign π σ * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, translationJwSign_normSq, one_mul]

/-- **The spin-reflection and block coefficient matrices have equal entry
magnitudes.** Since `spinReflectionCoeff ψ = ε ⊙ hubbardBlockCoeff (Uᴴψ)` with the
Jordan–Wigner sign `ε` of unit magnitude (PR17 at `φ = Uᴴψ`, using `U·Uᴴ = 1`), the
squared magnitudes agree entrywise. -/
theorem spinReflectionCoeff_normSq_eq_hubbardBlockCoeff (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) (u h : hubbardSpinConfig N) :
    Complex.normSq (spinReflectionCoeff N ψ u h)
      = Complex.normSq (hubbardBlockCoeff N
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) u h) := by
  have hψ : (hubbardBlockToSpinfulPermutationOperator N).mulVec
        ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) = ψ := by
    rw [Matrix.mulVec_mulVec, hubbardBlockToSpinfulPermutationOperator_mul_conjTranspose,
      Matrix.one_mulVec]
  have hbridge := congrFun (congrFun
    (spinReflectionCoeff_hubbardBlockToSpinfulPermutationOperator_mulVec N
      ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ)) u) h
  rw [hψ] at hbridge
  rw [hbridge, normSq_translationJwSign_mul]

end LatticeSystem.Fermion
