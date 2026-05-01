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

end LatticeSystem.Tests.SpinSMarshallSign
