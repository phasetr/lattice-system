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

/-- Operators at distinct sites commute. -/
example {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS j B : ManyBodyOpS Λ N) =
      onSiteS j B * onSiteS i A :=
  onSiteS_mul_onSiteS_of_ne hij A B

/-- Same-site product reduces to a single embedding. -/
example (i : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS i B : ManyBodyOpS Λ N) = onSiteS i (A * B) :=
  onSiteS_mul_onSiteS_same i A B

/-- `onSiteS i 1 = 1`. -/
example (i : Λ) (N : ℕ) :
    (onSiteS i (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
        ManyBodyOpS Λ N) = 1 :=
  onSiteS_one i

/-- `onSiteS` is `ℂ`-linear: scalar pull-out. -/
example (i : Λ) (c : ℂ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (c • A) : ManyBodyOpS Λ N) = c • onSiteS i A :=
  onSiteS_smul i c A

end LatticeSystem.Tests.SpinSMultiSite
