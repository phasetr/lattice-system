import LatticeSystem.Math.PosSemidef.Basics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Gate D2: exact AKLT sectors two through four, sequentially

This module checks the unique rational certificate frozen by Issue #5094 Gate C.
Sectors are added only after the preceding sector passes its whole proof boundary.
-/

namespace LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential

open Matrix
open scoped MatrixOrder

/-! ## Sector-local physical entry model -/

/-- A four-site spin-label configuration. -/
abbrev SpinConfig := Fin 4 → Fin 3

/-- A four-site configuration written in site order. -/
def spinConfig (a b c d : Fin 3) : SpinConfig := ![a, b, c, d]

/-- Canonical evaluation of a four-site configuration literal. -/
@[simp] private theorem spinConfig_apply (a b c d : Fin 3) (i : Fin 4) :
    spinConfig a b c d i =
      if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d := by
  fin_cases i <;> rfl

/-- The exact matrix entry of the two-site spin-two projector, for **every** two-site total
label. Despite the historical name (kept because the sector-two chain and the sector-three
literal chain are frozen against it), this is not specific to total-label sector two: the two
sites carry labels `a, b` and `c, d` in `Fin 3`, and the entry is the `⟨a b| P₂ |c d⟩` matrix
element of the projector onto the spin-two multiplet of two spin-one sites. The projector
conserves the two-site sublabel `a + b`, so the entry vanishes unless `a + b = c + d`, and on
each sublabel it is the outer square of the normalised Clebsch–Gordan `S = 2` vector:
sublabel `0` and `4` are one-dimensional (entry `1`), sublabels `1` and `3` are spanned by the
symmetric combination of the two configurations (entry `1/2`), and sublabel `2` uses the
weights `(1, 2, 1)/√6` (entry `w a * w c / 6`).

Sublabels `3` and `4` occur in total-label sector three and above; omitting them (as an earlier
version of this definition did) makes `physicalHEntry` wrong outside sector two. -/
def sector2P2Entry (a b c d : Fin 3) : ℚ :=
  if a.val + b.val = 0 ∧ c.val + d.val = 0 then 1
  else if a.val + b.val = 1 ∧ c.val + d.val = 1 then 1 / 2
  else if a.val + b.val = 2 ∧ c.val + d.val = 2 then
    ((if a.val = 1 then 2 else 1) * (if c.val = 1 then 2 else 1) : ℚ) / 6
  else if a.val + b.val = 3 ∧ c.val + d.val = 3 then 1 / 2
  else if a.val + b.val = 4 ∧ c.val + d.val = 4 then 1
  else 0

/-- The physical matrix entry of the bond on sites zero and one. -/
def bond01Entry (a b : SpinConfig) : ℚ :=
  if a 2 = b 2 ∧ a 3 = b 3 then
    sector2P2Entry (a 0) (a 1) (b 0) (b 1)
  else 0

/-- The physical matrix entry of the bond on sites one and two. -/
def bond12Entry (a b : SpinConfig) : ℚ :=
  if a 0 = b 0 ∧ a 3 = b 3 then
    sector2P2Entry (a 1) (a 2) (b 1) (b 2)
  else 0

/-- The physical matrix entry of the bond on sites two and three. -/
def bond23Entry (a b : SpinConfig) : ℚ :=
  if a 0 = b 0 ∧ a 1 = b 1 then
    sector2P2Entry (a 2) (a 3) (b 2) (b 3)
  else 0

/-- The physical matrix entry of the three-bond open Hamiltonian. -/
def physicalHEntry (a b : SpinConfig) : ℚ :=
  bond01Entry a b + bond12Entry a b + bond23Entry a b

end LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
