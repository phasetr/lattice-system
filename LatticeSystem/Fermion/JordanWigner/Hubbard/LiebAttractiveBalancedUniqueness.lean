import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveOverlapPositive
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedPosDefCompress
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedThetaSector
import LatticeSystem.Math.RealForm.AntilinearFixedFinrank
import LatticeSystem.Math.MatrixAnalysis.HermitianTrace

/-!
# Balanced ground eigenspace `finrank ℂ ≤ 1` — uniqueness capstone (Tasaki §10.2.4)

Uniqueness half of **Tasaki Theorem 10.2** (Lieb's theorem for the attractive Hubbard model).
Assembling the non-orthogonality core (`balanced_signDefinite_ground_dotProduct_ne_zero`), the
forall sign-definiteness of Hermitian-`W` balanced grounds
(`hermitianW_balanced_ground_signDefinite`, Lemma 10.9), the antilinear Γ-reflection `Θ`
(`gammaThetaVec`, ground/balanced preserving with `Θ`-fixed ⟺ Hermitian-`W`), and the generic
real-form finrank toolkit (`finrank_complex_le_finrank_real_antilinearFixed`,
`finrank_le_one_of_pairwise_bilinForm_ne_zero`), we prove that the **balanced ground eigenspace**
of `attractiveHubbardHamiltonian` — the vectors that are simultaneously `Ĥ`-eigenvectors at the
balanced-compression minimum energy `E` and per-spin number eigenvectors `N̂_↑ = N̂_↓ = k` — is at
most one-dimensional over `ℂ`.

The argument (§10.2.4, pp. 363–367):

* The `Θ`-fixed grounds `ℂ`-span the ground eigenspace `V` (antilinear involution decomposition),
  so `finrank ℂ V ≤ finrank ℝ W` with `W` the `Θ`-fixed real subspace
  (`finrank_complex_le_finrank_real_antilinearFixed`).
* On `W` every pair of nonzero `Θ`-fixed grounds `x, y` is non-orthogonal for the real pairing
  `B x y = (⟨x, y⟩).re`: each has a sign-definite compressed coefficient
  (`hermitianW_balanced_ground_signDefinite`), so the overlap `⟨x, y⟩ = tr(W'_S W_S)` is nonzero
  (`balanced_signDefinite_ground_dotProduct_ne_zero`); and being a trace of a product of two
  Hermitian matrices it is real (`Matrix.trace_mul_star_of_isHermitian`), so its real part is
  nonzero. Hence `finrank ℝ W ≤ 1` (`finrank_le_one_of_pairwise_bilinForm_ne_zero`).
* Combining, `finrank ℂ V ≤ 1`.

This is the participating uniqueness milestone consumed by the eventual Tasaki §10.2.1 Theorem 10.2
singlet capstone (lifting `Ŝ³ = 0` uniqueness to the whole `Ne`-electron sector via SU(2)).

## Main results

* `balancedGroundEigenspace` — the balanced ground eigenspace submodule
  `{φ | Ĥφ = Eφ ∧ N̂_↑φ = kφ ∧ N̂_↓φ = kφ}`.
* `mem_balancedGroundEigenspace_iff` — membership unfolds to the three eigenvector relations.
* `balanced_ground_eigenspace_finrank_le_one` — **the capstone:** `finrank ℂ` of the balanced
  ground eigenspace is `≤ 1` (unique ground state in the balanced `Ŝ³ = 0` sector).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4 (Theorem 10.2 uniqueness, Lemma 10.9), pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math LatticeSystem.Math.RealForm

variable {N : ℕ}

/-- The **balanced ground eigenspace** of the attractive Hubbard Hamiltonian: the `ℂ`-subspace of
configuration vectors that are simultaneously `Ĥ`-eigenvectors at the balanced-sector-compression
minimum energy `E` and per-spin number eigenvectors `N̂_↑ = N̂_↓ = k` (the balanced `Ŝ³ = 0`
sector). Realised as the intersection of the three `Module.End` eigenspaces of `Matrix.toLin'`. -/
noncomputable def balancedGroundEigenspace (k : ℕ) [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  End.eigenspace (Matrix.toLin' (attractiveHubbardHamiltonian N T U))
      ((hermitianMinEigenvalue (configSectorCompress_isHermitian
        (hubbardBalancedSectorPred N k)
        (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ)
    ⊓ End.eigenspace (Matrix.toLin' (fermionTotalUpNumber N)) (k : ℂ)
    ⊓ End.eigenspace (Matrix.toLin' (fermionTotalDownNumber N)) (k : ℂ)

/-- Membership in the balanced ground eigenspace unfolds to the three defining eigenvector
relations: `Ĥφ = Eφ` at the balanced minimum energy, `N̂_↑φ = kφ`, and `N̂_↓φ = kφ`. -/
theorem mem_balancedGroundEigenspace_iff (k : ℕ) [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    φ ∈ balancedGroundEigenspace k T U hT_symm ↔
      (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) : ℝ) : ℂ) • φ
        ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
        ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ := by
  rw [balancedGroundEigenspace, Submodule.mem_inf, Submodule.mem_inf, End.mem_eigenspace_iff,
    End.mem_eigenspace_iff, End.mem_eigenspace_iff, Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, and_assoc]

/-- **Balanced ground eigenspace uniqueness (Tasaki §10.2.4 Theorem 10.2 uniqueness).** For an
attractive Hubbard model with symmetric real hopping `T` whose support graph is connected and
strictly attractive on-site interaction `U > 0`, the balanced ground eigenspace — vectors that are
simultaneously `Ĥ`-eigenvectors at the balanced minimum energy `E` and satisfy `N̂_↑ = N̂_↓ = k` —
is at most one-dimensional over `ℂ`.

Proof (§10.2.4, pp. 363–367): the antilinear Γ-reflection `Θ` (`gammaThetaVec`) preserves the
eigenspace (`gammaThetaVec_preserves_eigenvector`, `gammaThetaVec_preserves_balanced`) and is an
additive antilinear involution, so its fixed real subspace `W` `ℂ`-spans the eigenspace `V`, giving
`finrank ℂ V ≤ finrank ℝ W` (`finrank_complex_le_finrank_real_antilinearFixed`). On `W` any two
nonzero `Θ`-fixed grounds (equivalently Hermitian-`W` grounds,
`blockWCoeff_isHermitian_iff_gammaThetaFixed`) have sign-definite compressed coefficients
(`hermitianW_balanced_ground_signDefinite`, Lemma 10.9), hence a nonzero overlap
`⟨x, y⟩` (`balanced_signDefinite_ground_dotProduct_ne_zero`); the overlap equals the trace of a
product of two Hermitian coefficient matrices, so it is real
(`Matrix.trace_mul_star_of_isHermitian`) and its real part is nonzero. Non-orthogonality then forces
`finrank ℝ W ≤ 1` (`finrank_le_one_of_pairwise_bilinForm_ne_zero`), and the two bounds compose to
`finrank ℂ V ≤ 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4 (Theorem 10.2 uniqueness, Lemma 10.9), pp. 363–367. -/
theorem balanced_ground_eigenspace_finrank_le_one (k : ℕ)
    [Nonempty (hubbardBalancedConfig N k)] [Nonempty (hubbardSpinCountSector N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) (hU_pos : ∀ x, 0 < U x)
    (hT_conn : (hoppingSupportGraph T).Preconnected) :
    finrank ℂ (balancedGroundEigenspace k T U hT_symm) ≤ 1 := by
  classical
  set V := balancedGroundEigenspace k T U hT_symm with hVdef
  -- The antilinear Γ-reflection `Θ` restricts to `V` (ground/balanced preserving).
  have hpres : ∀ x : V, gammaThetaVec N (x : (Fin (2 * N + 2) → Fin 2) → ℂ) ∈ V := by
    intro x
    obtain ⟨heig, hUp, hDn⟩ := (mem_balancedGroundEigenspace_iff k T U hT_symm _).mp x.2
    obtain ⟨hUpΘ, hDnΘ⟩ := gammaThetaVec_preserves_balanced k hUp hDn
    exact (mem_balancedGroundEigenspace_iff k T U hT_symm _).mpr
      ⟨gammaThetaVec_preserves_eigenvector T U _ _ heig, hUpΘ, hDnΘ⟩
  set Θ : V → V := fun x => ⟨gammaThetaVec N (x : (Fin (2 * N + 2) → Fin 2) → ℂ), hpres x⟩
    with hΘdef
  -- `Θ` is additive, antilinear, and an involution on `V`.
  have hadd : ∀ x y : V, Θ (x + y) = Θ x + Θ y := fun x y =>
    Subtype.ext (by simp only [hΘdef, Submodule.coe_add, gammaThetaVec_add])
  have hsmul : ∀ (z : ℂ) (x : V), Θ (z • x) = starRingEnd ℂ z • Θ x := fun z x =>
    Subtype.ext (by simp only [hΘdef, Submodule.coe_smul, gammaThetaVec_smul])
  have hinv : ∀ x : V, Θ (Θ x) = x := fun x =>
    Subtype.ext (by simp only [hΘdef, gammaThetaVec_gammaThetaVec])
  -- The real bilinear pairing `B x y = re ⟨x, y⟩` on `V`.
  set B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ
    (fun x y : V => (dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ)).re)
    (fun a m n => by
      simp only [Submodule.coe_add, star_add, add_dotProduct, Complex.add_re])
    (fun a m n => by
      change (star (↑(a • m) : (Fin (2 * N + 2) → Fin 2) → ℂ) ⬝ᵥ (↑n : _)).re
          = a • (star (↑m : (Fin (2 * N + 2) → Fin 2) → ℂ) ⬝ᵥ ↑n).re
      rw [Submodule.coe_smul_of_tower,
        show (a • (↑m : (Fin (2 * N + 2) → Fin 2) → ℂ)) = ((a : ℂ) • ↑m) from by
          rw [← IsScalarTower.algebraMap_smul ℂ a (↑m : (Fin (2 * N + 2) → Fin 2) → ℂ),
            Complex.coe_algebraMap],
        star_smul, RCLike.star_def, Complex.conj_ofReal, smul_dotProduct, smul_eq_mul,
        Complex.re_ofReal_mul, smul_eq_mul])
    (fun a m n => by
      simp only [Submodule.coe_add, dotProduct_add, Complex.add_re])
    (fun a m n => by
      change (star (↑m : (Fin (2 * N + 2) → Fin 2) → ℂ) ⬝ᵥ (↑(a • n) : _)).re
          = a • (star (↑m : (Fin (2 * N + 2) → Fin 2) → ℂ) ⬝ᵥ ↑n).re
      rw [Submodule.coe_smul_of_tower,
        show (a • (↑n : (Fin (2 * N + 2) → Fin 2) → ℂ)) = ((a : ℂ) • ↑n) from by
          rw [← IsScalarTower.algebraMap_smul ℂ a (↑n : (Fin (2 * N + 2) → Fin 2) → ℂ),
            Complex.coe_algebraMap],
        dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, smul_eq_mul])
    with hBdef
  -- Nonzero `Θ`-fixed grounds pair to a nonzero real value under `B`.
  have hne : ∀ x ∈ antilinearInvolutionFixed Θ hadd hsmul,
      ∀ y ∈ antilinearInvolutionFixed Θ hadd hsmul, x ≠ 0 → y ≠ 0 → B x y ≠ 0 := by
    intro x hxW y hyW hx0 hy0
    -- Extract the balanced-ground data of `x` and `y`.
    obtain ⟨hxEig, hxUp, hxDn⟩ := (mem_balancedGroundEigenspace_iff k T U hT_symm _).mp x.2
    obtain ⟨hyEig, hyUp, hyDn⟩ := (mem_balancedGroundEigenspace_iff k T U hT_symm _).mp y.2
    have hx0' : (x : (Fin (2 * N + 2) → Fin 2) → ℂ) ≠ 0 := fun h =>
      hx0 (by exact_mod_cast (ZeroMemClass.coe_eq_zero).mp h)
    have hy0' : (y : (Fin (2 * N + 2) → Fin 2) → ℂ) ≠ 0 := fun h =>
      hy0 (by exact_mod_cast (ZeroMemClass.coe_eq_zero).mp h)
    -- `Θ`-fixedness gives Hermitian reconciliation coefficients.
    have hxFix : gammaThetaVec N (x : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = (x : (Fin (2 * N + 2) → Fin 2) → ℂ) :=
      congrArg Subtype.val ((mem_antilinearInvolutionFixed).mp hxW)
    have hyFix : gammaThetaVec N (y : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = (y : (Fin (2 * N + 2) → Fin 2) → ℂ) :=
      congrArg Subtype.val ((mem_antilinearInvolutionFixed).mp hyW)
    have hxHerm : (blockWCoeff N (x : (Fin (2 * N + 2) → Fin 2) → ℂ)).IsHermitian :=
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr hxFix
    have hyHerm : (blockWCoeff N (y : (Fin (2 * N + 2) → Fin 2) → ℂ)).IsHermitian :=
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr hyFix
    -- Sign-definiteness of both compressed coefficients (Lemma 10.9, forall form).
    have hSDx := hermitianW_balanced_ground_signDefinite k T U hT_symm hU_pos hT_conn
      _ hx0' hxUp hxDn hxHerm hxEig
    have hSDy := hermitianW_balanced_ground_signDefinite k T U hT_symm hU_pos hT_conn
      _ hy0' hyUp hyDn hyHerm hyEig
    -- Non-orthogonality of the overlap `⟨x, y⟩`.
    have hoverlap : dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ) ≠ 0 :=
      balanced_signDefinite_ground_dotProduct_ne_zero k _ _ hyUp hyDn hxUp hxDn hSDy hSDx
    -- The overlap is real: `⟨x, y⟩ = tr((W_x)ᴴ W_y) = tr(W_x W_y)` with both Hermitian.
    have hcross : dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ)
        = Matrix.trace ((blockWCoeff N (x : (Fin (2 * N + 2) → Fin 2) → ℂ))ᴴ
            * blockWCoeff N (y : (Fin (2 * N + 2) → Fin 2) → ℂ)) :=
      blockWCoeff_dotProduct_cross_eq _ _
    have hstar : star (dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ))
        = dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
            (y : (Fin (2 * N + 2) → Fin 2) → ℂ) := by
      rw [hcross, hxHerm.eq]
      exact Matrix.trace_mul_star_of_isHermitian hxHerm hyHerm
    have him : (dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ)).im = 0 :=
      Complex.conj_eq_iff_im.mp (by rw [← starRingEnd_apply]; exact hstar)
    -- Hence the real part is nonzero.
    have : B x y = (dotProduct (star (x : (Fin (2 * N + 2) → Fin 2) → ℂ))
        (y : (Fin (2 * N + 2) → Fin 2) → ℂ)).re := by
      rw [hBdef, LinearMap.mk₂_apply]
    rw [this]
    intro hre
    exact hoverlap (Complex.ext hre him)
  -- Compose the two finrank bounds.
  calc finrank ℂ V
      ≤ finrank ℝ (antilinearInvolutionFixed Θ hadd hsmul) :=
        finrank_complex_le_finrank_real_antilinearFixed Θ hadd hsmul hinv
    _ ≤ 1 := finrank_le_one_of_pairwise_bilinForm_ne_zero _ B hne

end LatticeSystem.Fermion
