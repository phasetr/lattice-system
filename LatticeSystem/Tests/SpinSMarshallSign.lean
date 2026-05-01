import LatticeSystem.Quantum.SpinS.MarshallSign

/-!
# Test coverage for spin-`S` Marshall sign
(Tasaki §2.5 Phase B-β β-4h)
-/

namespace LatticeSystem.Tests.SpinSMarshallSign

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V]

/-- All-`s = 0` Marshall sign is `+1`. -/
example {N : ℕ} (A : V → Bool) :
    marshallSignS A (fun _ : V => (0 : Fin (N + 1))) = 1 :=
  marshallSignS_const_zero A

/-- Marshall-dressed basis vector. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ =
      marshallSignS A σ • basisVecS σ :=
  rfl

/-- Diagonal: `marshallDressedBasisS A σ σ = marshallSignS A σ`. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ σ = marshallSignS A σ :=
  marshallDressedBasisS_self A σ

/-- Off-diagonal: zero for `τ ≠ σ`. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool)
    {σ τ : V → Fin (N + 1)} (hne : τ ≠ σ) :
    marshallDressedBasisS A σ τ = 0 :=
  marshallDressedBasisS_of_ne A hne

/-- All-`0` config dressed basis equals plain basis. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool) :
    marshallDressedBasisS A (fun _ : V => (0 : Fin (N + 1))) =
      basisVecS (fun _ : V => (0 : Fin (N + 1))) :=
  marshallDressedBasisS_const_zero A

end LatticeSystem.Tests.SpinSMarshallSign
