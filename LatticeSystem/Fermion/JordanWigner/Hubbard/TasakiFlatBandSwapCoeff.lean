import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandWeightSupport
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModePeel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandDoubleOcc

/-!
# Tasaki §11.3.1: the no-double-occupancy spin-swap coefficient relation (toward block ≤ 1)

Applying the double annihilation `ĉ_{int(p)↓} ĉ_{int(p)↑}` (which kills a ground vector) and reading
one occupation-basis coordinate isolates exactly the two orbital-spin configurations that differ by
swapping the spins of the overlapping orbitals `p` and `p+1`: only `α_p` and `α_{p+1}` are supported
at the shared internal site `int(p)` (both with amplitude `−ν`).  The two contributions carry the
same scalar `ν²` and a relative Koszul sign of `−1` — *independent* of where `p, p+1` sit in the
occupation list — so the two coefficients are equal: `c_S = c_{S with p,(p+1) spins swapped}`.

This file sets up the position-independent Koszul sign identity and the orbital-spin ↔ occupation
config map; the coefficient extraction and the swap relation itself follow.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Position-independent relative Koszul sign for a two-mode erase.**  Whatever the lengths of the
list segments before / between the two erased modes, the two ways of erasing them (in the two spin
orders) differ by an overall sign of `−1`: both sides reduce to `(-1)^(2m+n)`. -/
theorem koszul_two_erase_sign_split (m n : ℕ) :
    (-1 : ℂ) ^ m * (-1 : ℂ) ^ (m + n) = -((-1 : ℂ) ^ (m + n + 1) * (-1 : ℂ) ^ m) := by
  rw [← pow_add, ← pow_add, show m + n + 1 + m = m + (m + n) + 1 by ring, pow_succ]
  ring

/-- **Orbital-spin → occupation config.**  An up/down assignment `s : Fin (K+1) → Fin 2` of the
`K+1` flat-band orbitals (`s p` the chosen spin) maps to the occupation config that occupies the
single mode `(inl p, s p)` for each orbital `p` and no `β` mode. -/
def flatBandAlphaSpinOcc (K : ℕ) (s : Fin (K + 1) → Fin 2) :
    (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2 :=
  fun q => match q.1 with
    | Sum.inl p => if q.2 = s p then 1 else 0
    | Sum.inr _ => 0

/-- The `α`-spin occupation config has no `β` occupation. -/
theorem flatBandAlphaSpinOcc_inr (s : Fin (K + 1) → Fin 2) (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandAlphaSpinOcc K s (Sum.inr u, σ) = 0 := rfl

/-- The mode `(inl p, σ)` is occupied in the `α`-spin config exactly when `σ` is the chosen spin. -/
theorem flatBandAlphaSpinOcc_inl (s : Fin (K + 1) → Fin 2) (p : Fin (K + 1)) (σ : Fin 2) :
    flatBandAlphaSpinOcc K s (Sum.inl p, σ) = if σ = s p then 1 else 0 := rfl

/-- **Occupied modes of an `α`-spin config.**  A mode `q` is occupied exactly when it is the chosen
spin mode `(inl p, s p)` of some orbital `p`. -/
theorem mem_occFinset_alphaSpinOcc (s : Fin (K + 1) → Fin 2)
    (q : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2) :
    q ∈ occFinset (flatBandAlphaSpinOcc K s) ↔ ∃ p, q = (Sum.inl p, s p) := by
  rw [occFinset, Finset.mem_filter]
  obtain ⟨m, σ⟩ := q
  constructor
  · rintro ⟨_, hq⟩
    cases m with
    | inl p =>
      rw [flatBandAlphaSpinOcc_inl] at hq
      split_ifs at hq with h
      · exact ⟨p, by rw [h]⟩
      · exact absurd hq (by decide)
    | inr u => rw [flatBandAlphaSpinOcc_inr] at hq; exact absurd hq (by decide)
  · rintro ⟨p, hp⟩
    obtain ⟨hm, hσ⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
    subst hm; subst hσ
    exact ⟨Finset.mem_univ _, by rw [flatBandAlphaSpinOcc_inl, if_pos rfl]⟩

/-- The `α`-spin occupation set is the image of the chosen-spin embedding `p ↦ (inl p, s p)`. -/
theorem occFinset_alphaSpinOcc_eq_image (s : Fin (K + 1) → Fin 2) :
    occFinset (flatBandAlphaSpinOcc K s)
      = Finset.univ.image (fun p : Fin (K + 1) => (Sum.inl p, s p)) := by
  ext q
  rw [mem_occFinset_alphaSpinOcc, Finset.mem_image]
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨p, Finset.mem_univ _, rfl⟩
  · rintro ⟨p, _, rfl⟩; exact ⟨p, rfl⟩

/-- The `α`-spin config occupies exactly `K+1` modes (one per orbital). -/
theorem occFinset_alphaSpinOcc_card (s : Fin (K + 1) → Fin 2) :
    (occFinset (flatBandAlphaSpinOcc K s)).card = K + 1 := by
  rw [occFinset_alphaSpinOcc_eq_image,
    Finset.card_image_of_injective _ (fun a b hab => Sum.inl_injective (congrArg Prod.fst hab)),
    Finset.card_univ, Fintype.card_fin]

end LatticeSystem.Fermion
