import LatticeSystem.Quantum.SpinS.Theorem23Predicted

/-!
# Tasaki §2.5 Theorem 2.3 predicted ladder bridges

This module contains the predicted-GS ladder-closure and lowered joint
subspace layer split from `Theorem23Predicted.lean`. The base predicted
module keeps the predicted-Casimir, predicted-GS, and cross-ladder bridges,
`Theorem23PredictedLadderCasimirTransfer.lean` contains the real-scalar and
predicted-Casimir transfer suffix, and `Theorem23PredictedSourceWeight.lean`
contains the source-weight suffix. This module packages the ladder stability
and joint sublattice-Casimir structure used by the adjacent-sector chain.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.

Tracked in Issue #412 (Tasaki §2.5: Marshall–Lieb–Mattis theorem).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS lowering closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-lowering image also lies in that subspace.

This packages the existing predicted-GS ladder invariance in the
pointwise form used by the adjacent-sector Theorem 2.3 chain, without
adding a new membership hypothesis for the lowered vector. -/
theorem tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpMinus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpMinus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 predicted-GS raising closure**:
if a full spin-`S` vector lies in the predicted toy ground-state
subspace, then its total-raising image also lies in that subspace.

This is the raising-direction companion to
`tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem tasaki23_totalSpinSOpPlus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (totalSpinSOpPlus V N).mulVec Ψ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N := by
  exact
    bipartiteToyGroundStateSubspacePredicted_totalSpinSOpPlus_invariant
      (Λ := V) A N ⟨Ψ, hΨ, by simp⟩

/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS `A`-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `A`-sublattice Casimir eigenvalue.

This combines predicted-GS lowering closure with the `A`-sublattice
Casimir bridge. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered predicted-GS complement-sublattice
Casimir bridge**: the total-lowering image of a predicted toy ground
state still has the maximum `¬A`-sublattice Casimir eigenvalue.

This is the complement companion to
`tasaki23_lowered_sublatticeSpinSquaredS_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem tasaki23_lowered_sublatticeSpinSquaredS_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((totalSpinSOpMinus V N).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((totalSpinSOpMinus V N).mulVec Ψ) := by
  exact
    tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
      (V := V) A N
      (tasaki23_totalSpinSOpMinus_mulVec_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state remains in the maximum `A`-sublattice
Casimir eigenspace.

This is the component-level version needed for comparing
`Ŝ_A^- Ψ` with `Ŝ_¬A^- Ψ` in the remaining lowered-Marshall positivity
argument. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state remains in the maximum complement
sublattice-Casimir eigenspace.

This is the complement companion to
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus N (fun x => !A x))
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered complement
sublattice-Casimir bridge**: the `A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum complement
sublattice-Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N (fun x => !A x)).mulVec
        ((sublatticeSpinSOpMinus N A).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • ((sublatticeSpinSOpMinus N A).mulVec Ψ) := by
  have hcomm :
      Commute (sublatticeSpinSquaredS N (fun x => ! A x))
        (sublatticeSpinSOpMinus N A) := by
    simpa using
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement
        N (fun x : V => ! A x))
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N hcomm
      (tasaki23_sublatticeSpinSquaredS_complement_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered `A`
sublattice-Casimir bridge**: the `¬A`-sublattice lowering component of
a predicted toy ground state also remains in the maximum `A`-sublattice
Casimir eigenspace.

Together with
`tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted`,
this places `Ŝ_¬A^- Ψ` in the joint maximum sublattice-Casimir
eigenspace needed for the remaining component comparison. -/
theorem
    tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    (sublatticeSpinSquaredS N A).mulVec
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) •
        ((sublatticeSpinSOpMinus N (fun x => !A x)).mulVec Ψ) := by
  exact
    mulVec_preserves_eigenvalue_of_commuteS_ladder
      N
      (sublatticeSpinSquaredS_commute_sublatticeSpinSOpMinus_complement N A)
      (tasaki23_sublatticeSpinSquaredS_mulVec_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 joint sublattice-Casimir eigenspace**:
the intersection of the maximum `A`- and `¬A`-sublattice Casimir
eigenspaces.

This names the structural target used by the component-lowering chain,
where both `Ŝ_A^- Ψ` and `Ŝ_¬A^- Ψ` are compared after being shown to
remain in the joint maximum sublattice-Casimir eigenspace. -/
noncomputable def tasaki23JointSublatticeCasimirEigenspace
    (A : V → Bool) (N : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) *
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
        ((N : ℂ) / 2)) + 1))
    ⊓ Module.End.eigenspace
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVecLin
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS `A`-lowered joint
sublattice-Casimir eigenspace bridge**: the `A`-sublattice lowering
component of a predicted toy ground state lies in the joint maximum
sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 predicted-GS complement-lowered joint
sublattice-Casimir eigenspace bridge**: the complement-sublattice
lowering component of a predicted toy ground state lies in the joint
maximum sublattice-Casimir eigenspace.

This packages the same-side and cross-side Casimir identities for
`Ŝ_¬A^- Ψ` in the exact intersection form needed by the remaining
component comparison. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈ bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec Ψ) ∈
      tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23JointSublatticeCasimirEigenspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact
      tasaki23_sublatticeSpinSquaredS_complement_sublatticeSpinSOpMinus_complement_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΨ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered component joint-magnetization
subspace**: the structural target for a lowered component of a
sector-`M` source vector.

It combines the joint maximum sublattice-Casimir eigenspace with the
successor magnetization subspace `magSumS = M + 1`, in centered
magnetization units.  The remaining comparison can then use one
submodule membership carrying both the Casimir and sector-support
facts for the lowered components. -/
noncomputable def tasaki23LoweredJointMagSubspace
    (A : V → Bool) (N M : ℕ) : Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  tasaki23JointSublatticeCasimirEigenspace (V := V) A N ⊓
    magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ))

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 `A`-lowered joint-magnetization bridge**:
if a sector-`M` representative is in the predicted toy ground-state
subspace, then its `A`-sublattice lowering component lies in the
combined joint-Casimir and successor-sector subspace.

This packages the PR #3408 joint-Casimir membership together with the
standard sublattice-lowering magnetization shift. -/
theorem
    tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N A).mulVec (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N A (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 complement-lowered joint-magnetization
bridge**: if a sector-`M` representative is in the predicted toy
ground-state subspace, then its complement-sublattice lowering component
lies in the combined joint-Casimir and successor-sector subspace.

This is the complement component version of
`tasaki23_sublatticeSpinSOpMinus_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted`.
-/
theorem
    tasaki23_sublatticeSpinSOpMinus_complement_mem_lowered_joint_magSubspace_of_mem_bipartiteToyGroundStateSubspacePredicted
    (A : V → Bool) (N : ℕ) {M : ℕ} {Φ : magConfigS V N M → ℂ}
    (hΦ : magSectorEmbedding Φ ∈
      bipartiteToyGroundStateSubspacePredicted (Λ := V) A N) :
    ((sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
        (magSectorEmbedding Φ)) ∈
      tasaki23LoweredJointMagSubspace (V := V) A N M := by
  unfold tasaki23LoweredJointMagSubspace
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact
      tasaki23_sublatticeSpinSOpMinus_complement_mem_joint_sublattice_casimir_eigenspace_of_mem_bipartiteToyGroundStateSubspacePredicted
        (V := V) A N hΦ
  · have hshift :
        (sublatticeSpinSOpMinus N (fun x => ! A x)).mulVec
            (magSectorEmbedding Φ) ∈
          magSubspaceS V N
            ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) - 1) :=
      sublatticeSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem
        N (fun x => ! A x) (magSectorEmbedding_mem_magSubspaceS Φ)
    convert hshift using 1
    norm_num
    ring_nf

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization Casimir
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the joint maximum sublattice-Casimir component.

This is an unpacking lemma for the cross-ladder comparison callback. -/
theorem tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ tasaki23JointSublatticeCasimirEigenspace (V := V) A N := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).1

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization sector
projection**: membership in `tasaki23LoweredJointMagSubspace` exposes
the successor magnetization support.

This is the sector-support companion to
`tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_mem_magSubspaceS_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    w ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((M + 1 : ℕ) : ℂ)) := by
  unfold tasaki23LoweredJointMagSubspace at hw
  exact (Submodule.mem_inf.mp hw).2

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization `A`-Casimir
equation**: a vector in `tasaki23LoweredJointMagSubspace` satisfies the
maximum `A`-sublattice Casimir eigenvector identity.

This turns the packed subspace membership used by the interval chain
into the explicit equation needed by the remaining representation-
theoretic comparison. -/
theorem tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N A).mulVec w =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => A x = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hA := (Submodule.mem_inf.mp hjoint).1
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hA
  exact hA

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 lowered joint-magnetization complement
Casimir equation**: a vector in `tasaki23LoweredJointMagSubspace`
satisfies the maximum `¬A`-sublattice Casimir eigenvector identity.

This is the complement-sublattice companion to
`tasaki23_sublatticeSpinSquaredS_eq_of_mem_lowered_joint_magSubspace`. -/
theorem tasaki23_sublatticeSpinSquaredS_complement_eq_of_mem_lowered_joint_magSubspace
    (A : V → Bool) (N M : ℕ) {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ tasaki23LoweredJointMagSubspace (V := V) A N M) :
    (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w =
      ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℂ) *
          ((N : ℂ) / 2)) + 1)) • w := by
  have hjoint :=
    tasaki23_mem_joint_sublattice_casimir_eigenspace_of_mem_lowered_joint_magSubspace
      (V := V) A N M hw
  unfold tasaki23JointSublatticeCasimirEigenspace at hjoint
  have hB := (Submodule.mem_inf.mp hjoint).2
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hB
  exact hB

end LatticeSystem.Quantum
