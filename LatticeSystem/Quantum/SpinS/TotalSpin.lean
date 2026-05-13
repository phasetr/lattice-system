import LatticeSystem.Quantum.SpinS.MultiSite
import LatticeSystem.Quantum.SpinS.Hermitian
import LatticeSystem.Quantum.SpinS.PMAsOneTwo

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

/-! ## Total raising/lowering decomposition -/

/-- `Ŝ_tot^+ = Ŝ_tot^{(1)} + i · Ŝ_tot^{(2)}`. Multi-site
generalisation of the single-site identity β-26 (Issue #458),
proved by linearity of `onSiteS` and `Finset.sum`. -/
theorem totalSpinSOpPlus_eq_add :
    (totalSpinSOpPlus Λ N : ManyBodyOpS Λ N) =
      totalSpinSOp1 Λ N + Complex.I • totalSpinSOp2 Λ N := by
  unfold totalSpinSOpPlus totalSpinSOp1 totalSpinSOp2
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← onSiteS_smul, ← onSiteS_add, spinSOpPlus_eq_one_add_I_smul_two]

/-- `Ŝ_tot^- = Ŝ_tot^{(1)} − i · Ŝ_tot^{(2)}`. -/
theorem totalSpinSOpMinus_eq_sub :
    (totalSpinSOpMinus Λ N : ManyBodyOpS Λ N) =
      totalSpinSOp1 Λ N - Complex.I • totalSpinSOp2 Λ N := by
  unfold totalSpinSOpMinus totalSpinSOp1 totalSpinSOp2
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← onSiteS_smul, ← onSiteS_sub, spinSOpMinus_eq_one_sub_I_smul_two]

/-! ## Adjoint relations -/

/-- The conjugate transpose of `onSiteS i A` equals `onSiteS i Aᴴ`. -/
private lemma onSiteS_conjTranspose (i : Λ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N).conjTranspose =
      (onSiteS i A.conjTranspose : ManyBodyOpS Λ N) := by
  ext σ' σ
  simp only [Matrix.conjTranspose_apply, onSiteS_apply]
  by_cases h : ∀ k, k ≠ i → σ' k = σ k
  · have h' : ∀ k, k ≠ i → σ k = σ' k := fun k hk => (h k hk).symm
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ k, k ≠ i → σ k = σ' k := fun hp =>
      h (fun k hk => (hp k hk).symm)
    rw [if_neg h, if_neg h', star_zero]

omit [Fintype Λ] [DecidableEq Λ] in
/-- Conjugate transpose distributes over finite sums in `ManyBodyOpS Λ N`. -/
private lemma sum_conjTranspose_manyBodyS {N : ℕ}
    {s : Finset Λ} (f : Λ → ManyBodyOpS Λ N) :
    (∑ x ∈ s, f x).conjTranspose = ∑ x ∈ s, (f x).conjTranspose := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t hns ih =>
    rw [Finset.sum_insert hns, Finset.sum_insert hns,
      Matrix.conjTranspose_add, ih]

/-- `(Ŝ_tot^+)† = Ŝ_tot^-`. -/
theorem totalSpinSOpPlus_conjTranspose :
    (totalSpinSOpPlus Λ N).conjTranspose = totalSpinSOpMinus Λ N := by
  unfold totalSpinSOpPlus totalSpinSOpMinus
  rw [sum_conjTranspose_manyBodyS]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [onSiteS_conjTranspose, spinSOpPlus_conjTranspose]

/-- `(Ŝ_tot^-)† = Ŝ_tot^+`. -/
theorem totalSpinSOpMinus_conjTranspose :
    (totalSpinSOpMinus Λ N).conjTranspose = totalSpinSOpPlus Λ N := by
  unfold totalSpinSOpPlus totalSpinSOpMinus
  rw [sum_conjTranspose_manyBodyS]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [onSiteS_conjTranspose, spinSOpMinus_conjTranspose]

/-! ## Convenient spin-`S` total operator unfoldings -/

/-- Definitional unfolding of `Ŝ_tot^{(1)}`. -/
theorem totalSpinSOp1_def :
    totalSpinSOp1 Λ N = ∑ x : Λ, onSiteS x (spinSOp1 N) := rfl

/-- Definitional unfolding of `Ŝ_tot^{(2)}`. -/
theorem totalSpinSOp2_def :
    totalSpinSOp2 Λ N = ∑ x : Λ, onSiteS x (spinSOp2 N) := rfl

/-- Definitional unfolding of `Ŝ_tot^{(3)}`. -/
theorem totalSpinSOp3_def :
    totalSpinSOp3 Λ N = ∑ x : Λ, onSiteS x (spinSOp3 N) := rfl

/-- Definitional unfolding of `Ŝ_tot^+`. -/
theorem totalSpinSOpPlus_def :
    totalSpinSOpPlus Λ N = ∑ x : Λ, onSiteS x (spinSOpPlus N) := rfl

/-- Definitional unfolding of `Ŝ_tot^-`. -/
theorem totalSpinSOpMinus_def :
    totalSpinSOpMinus Λ N = ∑ x : Λ, onSiteS x (spinSOpMinus N) := rfl

/-- For trivial spin (`N = 0`), `Ŝ_tot^{(3)}` is the zero matrix.
The only configuration has all entries `0` so the sum is `0`. -/
theorem totalSpinSOp3_N_zero :
    (totalSpinSOp3 Λ 0 : ManyBodyOpS Λ 0) = 0 := by
  unfold totalSpinSOp3
  refine Finset.sum_eq_zero (fun x _ => ?_)
  ext σ' σ
  rw [Matrix.zero_apply, onSiteS_apply]
  by_cases h : ∀ k, k ≠ x → σ' k = σ k
  · rw [if_pos h]
    have hσ'x : σ' x = 0 := by apply Fin.ext; have := (σ' x).isLt; omega
    have hσx : σ x = 0 := by apply Fin.ext; have := (σ x).isLt; omega
    rw [hσ'x, hσx, spinSOp3_apply_diag]
    simp
  · rw [if_neg h]

end LatticeSystem.Quantum
