import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Hermitian

/-!
# Total spin-`S` operators on a multi-site Hilbert space
(Tasaki §2.5 Phase B-β β-3i)

Total spin operators on the multi-site spin-`S` Hilbert space:

  `Ŝ_tot^{(α)} := Σ_{x ∈ Λ} onSiteS x Ŝ^{(α)}`,
  `Ŝ_tot^± := Σ_{x ∈ Λ} onSiteS x Ŝ^±`.

Direct generalisation of `totalSpinHalfOp{1,2,3,Plus,Minus}`
(`Quantum/TotalSpin.lean`) to arbitrary spin.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- Total spin-`S` operator in the 1-axis. -/
noncomputable def totalSpinSOp1 : ManyBodyOpS Λ N :=
  ∑ x : Λ, onSiteS x (spinSOp1 N)

/-- Total spin-`S` operator in the 2-axis. -/
noncomputable def totalSpinSOp2 : ManyBodyOpS Λ N :=
  ∑ x : Λ, onSiteS x (spinSOp2 N)

/-- Total spin-`S` operator in the 3-axis. -/
noncomputable def totalSpinSOp3 : ManyBodyOpS Λ N :=
  ∑ x : Λ, onSiteS x (spinSOp3 N)

/-- Total raising operator. -/
noncomputable def totalSpinSOpPlus : ManyBodyOpS Λ N :=
  ∑ x : Λ, onSiteS x (spinSOpPlus N)

/-- Total lowering operator. -/
noncomputable def totalSpinSOpMinus : ManyBodyOpS Λ N :=
  ∑ x : Λ, onSiteS x (spinSOpMinus N)

/-- A finite sum of Hermitian matrices is Hermitian. -/
private lemma isHermitian_sum_aux {ι : Type*} {n : Type*}
    (s : Finset ι) {f : ι → Matrix n n ℂ}
    (hf : ∀ i ∈ s, (f i).IsHermitian) :
    (∑ i ∈ s, f i).IsHermitian := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Matrix.IsHermitian]
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns]
    refine Matrix.IsHermitian.add (hf a (Finset.mem_insert_self a t)) ?_
    exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- `Ŝ_tot^{(1)}` is Hermitian. -/
theorem totalSpinSOp1_isHermitian : (totalSpinSOp1 Λ N).IsHermitian := by
  unfold totalSpinSOp1
  exact isHermitian_sum_aux Finset.univ
    (fun x _ => onSiteS_isHermitian x (spinSOp1_isHermitian N))

/-- `Ŝ_tot^{(2)}` is Hermitian. -/
theorem totalSpinSOp2_isHermitian : (totalSpinSOp2 Λ N).IsHermitian := by
  unfold totalSpinSOp2
  exact isHermitian_sum_aux Finset.univ
    (fun x _ => onSiteS_isHermitian x (spinSOp2_isHermitian N))

/-- `Ŝ_tot^{(3)}` is Hermitian. -/
theorem totalSpinSOp3_isHermitian : (totalSpinSOp3 Λ N).IsHermitian := by
  unfold totalSpinSOp3
  exact isHermitian_sum_aux Finset.univ
    (fun x _ => onSiteS_isHermitian x (spinSOp3_isHermitian N))

end LatticeSystem.Quantum
