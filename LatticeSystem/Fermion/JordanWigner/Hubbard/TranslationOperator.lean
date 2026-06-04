import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularHubbardModel
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tasaki §11.4.2: the lattice translation on the decorated chain (towards Theorem 11.19)

Theorem 11.19 (spin-wave excitation bounds) is stated in terms of the fermionic
translation operator `τ̂_z` (eq. (11.4.30)) and the crystal momentum `k`.  This file
supplies the underlying combinatorial datum: the **site-translation permutation** of the
spinful Jordan–Wigner mode space induced by translating the decorated chain by `z`
lattice cells.

In the interleaved decorated chain (§11.3.1) the physical sites are `Fin (2K+2)`
(external `2i`, internal `2i+1`), and a spinful mode is `spinfulIndex (2K+1) p σ = 2p + σ`,
so the mode space `Fin (2·(2K+1)+2) = Fin ((2K+2)·2)` factors as
`(physical site) × (spin)`.  One lattice cell is two physical sites, so translating by `z`
cells shifts the physical site by `2z` (cyclically, periodic boundary conditions) and
leaves the spin untouched.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.2, eq. (11.4.30) (p. 423).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The mode space factors as `(physical site) × (spin)`: mode `2p + σ ↔ (p, σ)`
(matching `spinfulIndex (2K+1) p σ = 2p + σ` and `finProdFinEquiv (p,σ) = σ + 2·p`). -/
def modeSiteSpinEquiv (K : ℕ) :
    Fin (2 * (2 * K + 1) + 2) ≃ Fin (2 * K + 2) × Fin 2 :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- The physical-site shift amount for a translation by `z` lattice cells: `2z`
(one cell = two physical sites), as an element of `Fin (2K+2)`. -/
def siteShiftAmount (K : ℕ) (z : Fin (K + 1)) : Fin (2 * K + 2) :=
  ⟨2 * z.val, by have := z.isLt; omega⟩

/-- **The site-translation permutation** of the spinful mode space induced by translating
the decorated chain by `z` lattice cells: cyclically shift the physical site by `2z`,
leaving the spin fixed.  This is the combinatorial datum underlying the fermionic
translation operator `τ̂_z` (eq. (11.4.30)). -/
noncomputable def siteTranslationPerm (K : ℕ) (z : Fin (K + 1)) :
    Equiv.Perm (Fin (2 * (2 * K + 1) + 2)) :=
  haveI : NeZero (2 * K + 2) := ⟨by omega⟩
  (modeSiteSpinEquiv K).trans
    (((finCycle (siteShiftAmount K z)).prodCongr (Equiv.refl (Fin 2))).trans
      (modeSiteSpinEquiv K).symm)

/-- Translating by `z = 0` cells is the identity permutation. -/
theorem siteTranslationPerm_zero (K : ℕ) :
    siteTranslationPerm K 0 = Equiv.refl _ := by
  haveI : NeZero (2 * K + 2) := ⟨by omega⟩
  have hshift : siteShiftAmount K 0 = 0 := by
    apply Fin.ext; simp [siteShiftAmount]
  simp only [siteTranslationPerm, hshift]
  rw [show (finCycle (0 : Fin (2 * K + 2))) = Equiv.refl _ from by
    ext i; simp [finCycle]]
  ext i
  simp

end LatticeSystem.Fermion
