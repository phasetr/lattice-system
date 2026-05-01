import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Hermitian

/-!
# Test coverage for the multi-site spin-`S` operator space
(Tasaki §2.5 Phase B-β β-3a)
-/

namespace LatticeSystem.Tests.SpinSMultiSite

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- `onSiteS i A` is Hermitian when `A` is. -/
example (i : Λ) {A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} (hA : A.IsHermitian) :
    (onSiteS (Λ := Λ) (N := N) i A).IsHermitian :=
  onSiteS_isHermitian i hA

/-- `Ŝ_i^{(3)}` is Hermitian as a multi-site operator. -/
example (i : Λ) (N : ℕ) :
    (spinSSiteOp3 (Λ := Λ) i N).IsHermitian :=
  onSiteS_isHermitian i (spinSOp3_isHermitian N)

end LatticeSystem.Tests.SpinSMultiSite
