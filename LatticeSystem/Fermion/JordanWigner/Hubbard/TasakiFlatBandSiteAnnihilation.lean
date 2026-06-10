import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandCAR
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModel

/-!
# Tasaki §11.3.1: site annihilation against an `α` creation (toward weight-block ≤ 1)

The site annihilation `ĉ_{x,σ}` is the canonical dual of the mode creations: its anticommutator
with an `α` creation `â†_{p,τ}` collapses (via the spinful site CAR) to the single-particle overlap
`α_p(x)` when the spins match, and `0` otherwise:
`{ĉ_{x,σ}, â†_{p,τ}} = (α_p(x) if σ = τ else 0) · 1`.

This is the engine for peeling a site annihilation through an `α`-Slater product: it picks out, with
the `α` amplitude, the orbitals whose single-particle state is supported at `x`.  At the shared
internal site `int(p)` only `α_p` and `α_{p+1}` contribute (both with amplitude `−ν`), giving the
two-term relation behind the no-double-occupancy coefficient equality.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **`{ĉ_{x,σ}, â†_{p,τ}} = (α_p(x) if σ = τ else 0) · 1`.**  The site annihilation against an `α`
creation: the bilinear sum of spinful site anticommutators collapses on the matching site `y = x`,
yielding the single-particle amplitude `α_p(x)` precisely when the spins agree. -/
theorem flatBand_siteAnnihilation_ACreation_anticomm (K : ℕ) (ν : ℝ)
    (x : Fin (2 * K + 2)) (σ τ : Fin 2) (p : Fin (K + 1)) :
    fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
        flatBandACreation K ν p τ
      + flatBandACreation K ν p τ *
        fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
      = (if σ = τ then (flatBandAlpha K ν p x : ℂ) else 0) •
        (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) := by
  unfold flatBandACreation
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  have hterm : ∀ y : Fin (2 * K + 2),
      fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ) *
          ((flatBandAlpha K ν p y : ℂ) •
            fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ))
        + (flatBandAlpha K ν p y : ℂ) •
            fermionMultiCreation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) y τ) *
          fermionMultiAnnihilation (2 * (2 * K + 1) + 1) (spinfulIndex (2 * K + 1) x σ)
      = (flatBandAlpha K ν p y : ℂ) •
        (if x = y ∧ σ = τ then (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2))) else 0) := by
    intro y
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add, spinful_annihilation_creation_anticomm]
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  by_cases hστ : σ = τ
  · simp only [hστ, and_true, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [hστ, and_false, if_false, smul_zero, Finset.sum_const_zero, zero_smul]

end LatticeSystem.Fermion
