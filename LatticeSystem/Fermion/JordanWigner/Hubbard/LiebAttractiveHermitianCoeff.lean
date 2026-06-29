import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveReflection

/-!
# The spin-reflection coefficient matrix is Hermitian iff the state is θ-symmetric (Tasaki §10.2.4)

Twenty-eighth layer (PR28) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model). **First layer of the corrected spin-reflection endgame** (the earlier
"polar replacement" route was unsound; see
`.self-local/docs/lieb-10-2-endgame-hermitian-W-design.md`).

Lieb's spin-space reflection positivity argument (Tasaki §10.2.4, p.363–367) works with
the coefficient matrix of a state in the **Hermitian** form `W` (the `|Γ(W)⟩`
representation). The relevant Hermitian condition is exactly the **θ-symmetry** of the
state vector, where `θ = spin-flip ∘ particle-hole` is the antiunitary spin reflection:
since PR1 gives `spinReflectionCoeff (θψ) = (spinReflectionCoeff ψ)ᴴ`, the coefficient
matrix `spinReflectionCoeff ψ` is Hermitian if and only if `θψ = ψ`.

## Main results

* `spinReflectionCoeff_injective` — the coefficient map `ψ ↦ spinReflectionCoeff ψ`
  is injective.
* `spinReflectionCoeff_isHermitian_iff_thetaFixed` — `spinReflectionCoeff ψ` is
  Hermitian iff `ψ` is fixed by the spin reflection `θ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The spin-reflection coefficient map is injective: a state vector is determined by
its coefficient matrix (the down index is read as a hole configuration, a bijective
reindexing). -/
theorem spinReflectionCoeff_injective (N : ℕ) :
    Function.Injective (spinReflectionCoeff N) := by
  intro ψ φ h
  funext c
  have hc : hubbardMergeConfig N (hubbardUpConfig N c) (hubbardDownConfig N c) = c :=
    hubbardMergeConfig_up_down N c
  have hentry := congrFun (congrFun h (hubbardUpConfig N c))
    (particleHoleConfig N (hubbardDownConfig N c))
  simpa only [spinReflectionCoeff, particleHoleConfig_particleHoleConfig, hc] using hentry

/-- **The spin-reflection coefficient matrix is Hermitian iff the state is fixed by the
spin reflection `θ`.** This is the Hermitian-`W` condition underlying Lieb's
spin-space reflection-positivity argument. -/
theorem spinReflectionCoeff_isHermitian_iff_thetaFixed (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (spinReflectionCoeff N ψ).IsHermitian ↔ spinReflectionThetaVec N ψ = ψ := by
  constructor
  · intro hH
    refine spinReflectionCoeff_injective N ?_
    rw [spinReflectionCoeff_thetaVec]
    exact hH
  · intro hθ
    change (spinReflectionCoeff N ψ)ᴴ = spinReflectionCoeff N ψ
    rw [← spinReflectionCoeff_thetaVec, hθ]

end LatticeSystem.Fermion
