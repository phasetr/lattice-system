import LatticeSystem.Quantum.SpinS.MultiSiteCommutator

/-!
# Test coverage for multi-site spin-`S` same-site commutators
(Tasaki §2.5 Phase B-β β-3k)
-/

namespace LatticeSystem.Tests.SpinSMultiSiteCommutator

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Same-site lifting: `[onSiteS i A, onSiteS i B] = onSiteS i [A, B]`. -/
example (i : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A * onSiteS i B - onSiteS i B * onSiteS i A :
        ManyBodyOpS Λ N) =
      onSiteS i (A * B - B * A) :=
  onSiteS_commutator_same i A B

/-- `[Ŝ_x^(1), Ŝ_x^(2)] = i · Ŝ_x^(3)`. -/
example (x : Λ) :
    (onSiteS x (spinSOp1 N) * onSiteS x (spinSOp2 N) -
        onSiteS x (spinSOp2 N) * onSiteS x (spinSOp1 N) :
        ManyBodyOpS Λ N) =
      Complex.I • onSiteS x (spinSOp3 N) :=
  spinSOp1_onSiteS_commutator_spinSOp2_onSiteS x

/-- `[onSiteS x A, ∑ z, onSiteS z B] = onSiteS x [A, B]`. -/
example (x : Λ) (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS x A : ManyBodyOpS Λ N) * (∑ z : Λ, onSiteS z B) -
        (∑ z : Λ, onSiteS z B) * onSiteS x A =
      onSiteS x (A * B - B * A) :=
  onSiteS_commutator_totalOnSiteS x A B

end LatticeSystem.Tests.SpinSMultiSiteCommutator
