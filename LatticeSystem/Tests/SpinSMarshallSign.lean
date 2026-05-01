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

end LatticeSystem.Tests.SpinSMarshallSign
