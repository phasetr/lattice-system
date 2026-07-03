import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveReflection

/-!
# The Shiba configuration involution (Tasaki §9.3.3, eq. (9.3.48))

Second layer (c2) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), Hal Tasaki, *Physics
and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §9.3.3,
pp. 334–337.

The Shiba transformation (eq. (9.3.48)) is a particle-hole transformation
applied to **one spin species only**, combined with a sublattice gauge.  At the
level of the occupation configurations `Fin (2|Λ|) → Fin 2` its permutation part
is the involution that **flips the down-spin occupations and leaves the up-spin
occupations fixed**:
`(n̂↑, n̂↓) ↦ (n̂↑, 1 − n̂↓)`.

Tasaki's original text applies the particle-hole map to the up spin; this file
uses the down spin, which is only a relabeling of the two spin species (`Ĥint'`
and `Ĥhop` are both up↔down symmetric) and lets us reuse the attractive-side
particle-hole infrastructure (`particleHoleConfig`,
`hubbardHoleOccupationDiag_eq_permConj`) that already acts on the down species.

## Main definitions

* `shibaConfig` — the down-spin particle-hole configuration map.
* `shibaConfigEquiv` — its packaging as an `Equiv` (it is an involution).

## Main results

* `shibaConfig_involutive` — `shibaConfig` is an involution.
* `shibaConfig_up` / `shibaConfig_down` — its up/down projections
  (up fixed, down flipped).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §9.3.3, eq. (9.3.48), p. 335; E. H. Lieb, *Phys. Rev.
Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open scoped BigOperators

variable {N : ℕ}

/-- The **Shiba configuration map**: flip the down-spin occupations, keep the
up-spin occupations, i.e. `(n̂↑, n̂↓) ↦ (n̂↑, 1 − n̂↓)` (the permutation part of
the Shiba transformation, Tasaki eq. (9.3.48), with the particle-hole map on the
down species). -/
def shibaConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : Fin (2 * N + 2) → Fin 2 :=
  hubbardMergeConfig N (hubbardUpConfig N c) (particleHoleConfig N (hubbardDownConfig N c))

/-- The up projection of the Shiba map is the identity:
`up (shiba c) = up c`. -/
@[simp]
theorem shibaConfig_up (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    hubbardUpConfig N (shibaConfig N c) = hubbardUpConfig N c := by
  simp [shibaConfig]

/-- The down projection of the Shiba map is the particle-hole flip:
`down (shiba c) = 1 − down c`. -/
@[simp]
theorem shibaConfig_down (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    hubbardDownConfig N (shibaConfig N c) = particleHoleConfig N (hubbardDownConfig N c) := by
  simp [shibaConfig]

/-- The Shiba configuration map is an involution: flipping the down occupations
twice restores them, and the up occupations are untouched. -/
theorem shibaConfig_involutive (N : ℕ) : Function.Involutive (shibaConfig N) := by
  intro c
  simp only [shibaConfig, hubbardUpConfig_merge, hubbardDownConfig_merge,
    particleHoleConfig_particleHoleConfig, hubbardMergeConfig_up_down]

/-- The Shiba configuration map is an involution (simp form). -/
@[simp]
theorem shibaConfig_shibaConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    shibaConfig N (shibaConfig N c) = c :=
  shibaConfig_involutive N c

/-- The **Shiba configuration involution** as a permutation of the occupation
configurations (Tasaki eq. (9.3.48), permutation part). -/
def shibaConfigEquiv (N : ℕ) : (Fin (2 * N + 2) → Fin 2) ≃ (Fin (2 * N + 2) → Fin 2) :=
  (shibaConfig_involutive N).toPerm

/-- The Shiba permutation acts as `shibaConfig`. -/
@[simp]
theorem shibaConfigEquiv_apply (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    shibaConfigEquiv N c = shibaConfig N c := rfl

/-- The Shiba permutation is its own inverse. -/
@[simp]
theorem shibaConfigEquiv_symm (N : ℕ) :
    (shibaConfigEquiv N).symm = shibaConfigEquiv N := rfl

end LatticeSystem.Fermion
