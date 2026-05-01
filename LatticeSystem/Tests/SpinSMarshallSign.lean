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

/-- Marshall sign is non-zero. -/
example {N : ℕ} (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ ≠ 0 :=
  marshallSignS_ne_zero A σ

/-- Marshall sign squared is 1. -/
example {N : ℕ} (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ = 1 :=
  marshallSignS_sq A σ

/-- Marshall sign is real: star = self. -/
example {N : ℕ} (A : V → Bool) (σ : V → Fin (N + 1)) :
    star (marshallSignS A σ) = marshallSignS A σ :=
  marshallSignS_star A σ

/-- Marshall-dressed basis orthonormality. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    (∑ τ : V → Fin (N + 1),
        star (marshallDressedBasisS A σ τ) *
          marshallDressedBasisS A σ' τ) =
      if σ = σ' then 1 else 0 :=
  marshallDressedBasisS_inner_product A σ σ'

/-- Marshall-dressed basis lies in its own magnetization subspace. -/
example {N : ℕ} [DecidableEq V] (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallDressedBasisS A σ : (V → Fin (N + 1)) → ℂ) ∈
      magSubspaceS V N (magEigenvalueS σ) :=
  marshallDressedBasisS_mem_magSubspaceS A σ

end LatticeSystem.Tests.SpinSMarshallSign
