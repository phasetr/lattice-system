import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MultiSiteCasimir
import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.MultiSiteDot
import LatticeSystem.Quantum.SpinS.LadderBoundary
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` all-aligned (saturated ferromagnet) state
(Tasaki §2.4 generalised to spin-`S`)

For a multi-site spin-`S` system on a finite vertex set `V`, the
**all-aligned** (constant-spin) state with `σ x = c` for all `x : V`
is a basis vector of the multi-site Hilbert space.

This file proves:

1. The all-aligned state at any `c : Fin (N+1)` is a `Ŝ^z_tot`
   eigenvector with eigenvalue `|V|·N/2 − |V|·c`.
2. The two extreme cases `c = 0` (highest weight, "all up") and
   `c = N` (lowest weight, "all down") are the **unique** elements of
   their respective magnetization sectors (`magSumS = 0` and
   `magSumS = |V|·N`), hence automatically Heisenberg eigenvectors
   for ANY coupling via the magnetization-conservation identity
   `[H, Ŝ^z_tot] = 0`. The eigenvalue is the explicit diagonal
   `Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4`.

The `(Ŝ_tot)²` eigenvalue `(|V|·N/2)(|V|·N/2+1)` (the `J = |V|·S`
highest-weight irreducible representation) is left to a follow-up
textbook unit, since it requires the alternative Casimir form
`(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + (Ŝ^z_tot)² + Ŝ^z_tot` plus
`Ŝ^+_tot · |σ_⊤⟩ = 0`.

The spin-`S` extension of Tasaki §2.4 (which treats `S = 1/2` in
detail) and the operator-level form of the saturated-ferromagnetic
ground state on the bipartite Heisenberg model.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## All-aligned configuration and state -/

/-- The constant configuration `σ x = c` for all `x : V`. -/
def allAlignedConfigS (V : Type*) (N : ℕ) (c : Fin (N + 1)) :
    V → Fin (N + 1) := fun _ => c

/-- The all-aligned basis state at constant value `c`. -/
noncomputable def allAlignedStateS (V : Type*) [Fintype V] [DecidableEq V]
    (N : ℕ) (c : Fin (N + 1)) :
    (V → Fin (N + 1)) → ℂ :=
  basisVecS (allAlignedConfigS V N c)

/-! ## Magnetization properties -/

omit [DecidableEq V] in
/-- `magSumS (allAlignedConfigS V N c) = |V| · c.val`. -/
theorem magSumS_allAlignedConfigS (c : Fin (N + 1)) :
    magSumS (allAlignedConfigS V N c) = Fintype.card V * c.val := by
  unfold magSumS allAlignedConfigS
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq V] in
/-- `magEigenvalueS (allAlignedConfigS V N c) = |V|·N/2 − |V|·c`. -/
theorem magEigenvalueS_allAlignedConfigS (c : Fin (N + 1)) :
    magEigenvalueS (allAlignedConfigS V N c) =
      ((Fintype.card V : ℂ) * (N : ℂ)) / 2 -
        ((Fintype.card V : ℂ) * (c.val : ℂ)) := by
  unfold magEigenvalueS
  rw [magSumS_allAlignedConfigS]
  push_cast
  ring

/-! ## `Ŝ_tot^{(3)}` eigenvalue on the all-aligned state -/

/-- The all-aligned state at `c` is a `Ŝ_tot^{(3)}`-eigenvector with
eigenvalue `magEigenvalueS (allAlignedConfigS V N c) = |V|·N/2 − |V|·c`. -/
theorem totalSpinSOp3_mulVec_allAlignedStateS (c : Fin (N + 1)) :
    (totalSpinSOp3 V N).mulVec (allAlignedStateS V N c) =
      magEigenvalueS (allAlignedConfigS V N c) •
        allAlignedStateS V N c := by
  exact totalSpinSOp3_mulVec_basisVecS (allAlignedConfigS V N c)

/-! ## Highest-weight specialisation (`c = 0`, "all up")

The highest-weight all-aligned state corresponds to `σ x = 0` for all
`x` (in our `Fin (N+1)` basis convention, `σ x = 0` is the
`m_z = +N/2 = +S` state). It has `magSumS = 0`,
`Ŝ^z_tot`-eigenvalue `+|V|·N/2`, and is the unique configuration in
its sector. Hence by magnetization conservation it is automatically a
**Heisenberg-Hamiltonian eigenvector**.
-/

omit [DecidableEq V] in
/-- For `c = (0 : Fin (N+1))`, `magSumS = 0`. -/
theorem magSumS_allAlignedConfigS_zero :
    magSumS (allAlignedConfigS V N (0 : Fin (N + 1))) = 0 := by
  rw [magSumS_allAlignedConfigS]
  simp

omit [DecidableEq V] in
/-- The all-up configuration is the **unique** configuration with
`magSumS = 0`: every other configuration has `magSumS > 0`. -/
theorem magSumS_pos_of_ne_allAlignedConfigS_zero
    {σ : V → Fin (N + 1)} (h : σ ≠ allAlignedConfigS V N 0) :
    0 < magSumS σ := by
  rcases Nat.eq_zero_or_pos (magSumS σ) with hmag | hpos
  · exfalso
    apply h
    funext x
    unfold magSumS at hmag
    have hx : (σ x).val = 0 := by
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset V))
        (f := fun y => (σ y).val)
        (fun y _ => Nat.zero_le _) |>.mp hmag x (Finset.mem_univ x)
      exact this
    unfold allAlignedConfigS
    exact Fin.ext hx
  · exact hpos

/-- **The all-up state is a Heisenberg eigenvector** (any coupling
`J`): for the all-up basis state `|σ_⊤⟩` (`σ x = 0` for all `x`),

  `H · |σ_⊤⟩ = (H_{σ_⊤,σ_⊤}) · |σ_⊤⟩`.

By magnetization conservation `[H, Ŝ^z_tot] = 0`, the only matrix
element `H τ σ_⊤` non-zero requires `magSumS τ = magSumS σ_⊤ = 0`,
which forces `τ = σ_⊤`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_zero
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  funext τ
  unfold allAlignedStateS
  rw [heisenbergHamiltonianS_mulVec_basisVecS_apply]
  change heisenbergHamiltonianS J N τ (allAlignedConfigS V N 0) =
    (heisenbergHamiltonianS J N (allAlignedConfigS V N 0)
      (allAlignedConfigS V N 0)) * basisVecS (allAlignedConfigS V N 0) τ
  by_cases h : τ = allAlignedConfigS V N 0
  · subst h
    rw [basisVecS_apply, if_pos rfl]
    ring
  · -- τ ≠ σ_⊤. By magnetization conservation, H τ σ_⊤ = 0.
    rw [basisVecS_apply, if_neg h, mul_zero]
    -- magSumS τ ≠ 0 = magSumS σ_⊤.
    apply heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (Λ := V) J N
    -- Goal: magEigenvalueS σ_⊤ ≠ magEigenvalueS τ.
    intro hEig
    have hmag : magSumS τ = magSumS (allAlignedConfigS V N 0) := by
      have := congrArg (fun z : ℂ => -(z - ((Fintype.card V : ℂ) * (N : ℂ)) / 2)) hEig
      simp [magEigenvalueS] at this
      exact_mod_cast this.symm
    rw [magSumS_allAlignedConfigS_zero] at hmag
    have hpos := magSumS_pos_of_ne_allAlignedConfigS_zero h
    omega

/-- **Explicit Heisenberg eigenvalue formula on all-up**: combining
`heisenbergHamiltonianS_mulVec_allAlignedStateS_zero` with the
diagonal computation `heisenbergHamiltonianS_apply_diag` gives

  `H · |σ_⊤⟩ = (Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4) · |σ_⊤⟩`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_zero_eigenvalue
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)))) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  rw [heisenbergHamiltonianS_mulVec_allAlignedStateS_zero]
  congr 1
  rw [heisenbergHamiltonianS_apply_diag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    show J x y *
      (((N : ℂ) / 2 - ((allAlignedConfigS V N 0) x).val) *
        ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) y).val)) =
      J x y * ((N : ℂ) / 2 * ((N : ℂ) / 2))
    unfold allAlignedConfigS
    have h0 : ((0 : Fin (N + 1)).val : ℂ) = 0 := by simp
    rw [h0]
    ring

/-! ## Lowest-weight specialisation (`c = Fin.last N`, "all down")

The lowest-weight all-aligned state corresponds to `σ x = N` for all
`x` (in our `Fin (N+1)` basis convention, `σ x = N` is the
`m_z = -N/2 = -S` state). It has `magSumS = |V|·N`,
`Ŝ^z_tot`-eigenvalue `−|V|·N/2`, and is the unique configuration in
its sector. Hence by magnetization conservation it is automatically a
Heisenberg-Hamiltonian eigenvector — symmetric to the all-up case.
-/

omit [DecidableEq V] in
/-- For `c = Fin.last N`, `magSumS = |V| · N`. -/
theorem magSumS_allAlignedConfigS_last :
    magSumS (allAlignedConfigS V N (Fin.last N)) = Fintype.card V * N := by
  rw [magSumS_allAlignedConfigS]
  simp

omit [DecidableEq V] in
/-- The all-down configuration is the **unique** configuration with
`magSumS = |V|·N`: every other configuration has `magSumS < |V|·N`.

Short proof using the existing `magSumS_eq_max_iff` characterisation. -/
theorem magSumS_lt_card_mul_of_ne_allAlignedConfigS_last
    {σ : V → Fin (N + 1)} (h : σ ≠ allAlignedConfigS V N (Fin.last N)) :
    magSumS σ < Fintype.card V * N := by
  rcases lt_or_eq_of_le (magSumS_le σ) with hlt | heq
  · exact hlt
  · exfalso; apply h
    funext x
    exact (magSumS_eq_max_iff σ).mp heq x

/-- **The all-down state is a Heisenberg eigenvector** (any coupling
`J`): for the all-down basis state `|σ_⊥⟩` (`σ x = N` for all `x`),

  `H · |σ_⊥⟩ = (H_{σ_⊥,σ_⊥}) · |σ_⊥⟩`.

By magnetization conservation `[H, Ŝ^z_tot] = 0`, the only matrix
element `H τ σ_⊥` non-zero requires `magSumS τ = magSumS σ_⊥ = |V|·N`,
which forces `τ = σ_⊥`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_last
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (Fin.last N)) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N))) •
        allAlignedStateS V N (Fin.last N) := by
  funext τ
  unfold allAlignedStateS
  rw [heisenbergHamiltonianS_mulVec_basisVecS_apply]
  change heisenbergHamiltonianS J N τ (allAlignedConfigS V N (Fin.last N)) =
    (heisenbergHamiltonianS J N (allAlignedConfigS V N (Fin.last N))
      (allAlignedConfigS V N (Fin.last N))) *
        basisVecS (allAlignedConfigS V N (Fin.last N)) τ
  by_cases h : τ = allAlignedConfigS V N (Fin.last N)
  · subst h
    rw [basisVecS_apply, if_pos rfl]
    ring
  · rw [basisVecS_apply, if_neg h, mul_zero]
    apply heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (Λ := V) J N
    intro hEig
    have hmag : magSumS τ = magSumS (allAlignedConfigS V N (Fin.last N)) :=
      ((magEigenvalueS_eq_iff τ (allAlignedConfigS V N (Fin.last N))).mp
        hEig.symm)
    rw [magSumS_allAlignedConfigS_last] at hmag
    have hlt := magSumS_lt_card_mul_of_ne_allAlignedConfigS_last h
    omega

/-- **Explicit Heisenberg eigenvalue formula on all-down**: combining
`heisenbergHamiltonianS_mulVec_allAlignedStateS_last` with
`heisenbergHamiltonianS_apply_diag` gives the SAME eigenvalue as the
all-up case (since `(N/2 - N)² = (-N/2)² = N²/4 = (N/2)²`):

  `H · |σ_⊥⟩ = (Σ_x J(x,x) · N(N+2)/4 + Σ_{x≠y} J(x,y) · N²/4) · |σ_⊥⟩`. -/
theorem heisenbergHamiltonianS_mulVec_allAlignedStateS_last_eigenvalue
    (J : V → V → ℂ) :
    (heisenbergHamiltonianS J N).mulVec
      (allAlignedStateS V N (Fin.last N)) =
      ((∑ x : V, ∑ y : V,
        J x y * (if x = y then (N : ℂ) * (N + 2) / 4
                 else (N : ℂ) / 2 * ((N : ℂ) / 2)))) •
        allAlignedStateS V N (Fin.last N) := by
  rw [heisenbergHamiltonianS_mulVec_allAlignedStateS_last]
  congr 1
  rw [heisenbergHamiltonianS_apply_diag]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hxy : x = y
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy, if_neg hxy]
    show J x y *
      (((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) x).val) *
        ((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) y).val)) =
      J x y * ((N : ℂ) / 2 * ((N : ℂ) / 2))
    unfold allAlignedConfigS
    have hN : ((Fin.last N).val : ℂ) = N := by simp [Fin.last]
    rw [hN]
    ring

/-! ## Highest-weight annihilation by `Ŝ^+_tot`

The all-up basis state `|σ_⊤⟩` (`σ x = 0` for all `x`) is the
highest-weight state of the spin-`S` multi-site Hilbert space: the
total raising operator `Ŝ^+_tot = Σ_x Ŝ^+_x` annihilates it.

Symmetric: the all-down state is annihilated by `Ŝ^-_tot`. Together
with the existing `Ŝ_tot^z`-eigenvector statement (which gives
`Ŝ^z_tot · |σ_⊤⟩ = (|V|·N/2) · |σ_⊤⟩`), this characterises the
all-up state as the highest-weight vector of the
`J_tot = |V|·S = |V|·N/2` irreducible representation.

These annihilation identities are the operator-level form of
"highest weight" / "lowest weight" and are the key input to the
Casimir eigenvalue computation `(Ŝ_tot)² · |σ_⊤⟩
  = (|V|·N/2)·(|V|·N/2 + 1) · |σ_⊤⟩`.
-/

/-- For any site `x : V`, the on-site `Ŝ^+` matrix element with the
all-up configuration vanishes: `(onSiteS x Ŝ^+) σ' σ_⊤ = 0` for
every `σ'`. Direct corollary of `spinSOpPlus_apply_first_col`. -/
theorem onSiteS_spinSOpPlus_apply_allAlignedConfigS_zero
    (x : V) (σ' : V → Fin (N + 1)) :
    (onSiteS x (spinSOpPlus N) : ManyBodyOpS V N) σ'
        (allAlignedConfigS V N 0) = 0 := by
  by_cases h : ∀ k, k ≠ x → σ' k = (allAlignedConfigS V N 0) k
  · rw [onSiteS_apply_of_off_site_agree _ _ h]
    show spinSOpPlus N (σ' x) ((allAlignedConfigS V N 0) x) = 0
    unfold allAlignedConfigS
    rw [show (0 : Fin (N + 1)) = ⟨0, Nat.succ_pos N⟩ from rfl]
    exact spinSOpPlus_apply_first_col (σ' x)
  · exact onSiteS_apply_eq_zero_of_off_site_diff _ _ h

/-- **The on-site raising operator annihilates the all-up state**:
`(onSiteS x Ŝ^+).mulVec |σ_⊤⟩ = 0` for every site `x`. -/
theorem onSiteS_spinSOpPlus_mulVec_allAlignedStateS_zero
    (x : V) :
    (onSiteS x (spinSOpPlus N) : ManyBodyOpS V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) = 0 := by
  funext τ
  unfold allAlignedStateS
  rw [onSiteS_mulVec_basisVecS_apply]
  rw [onSiteS_spinSOpPlus_apply_allAlignedConfigS_zero]
  rfl

/-- **`Ŝ^+_tot` annihilates the all-up state** (highest-weight property):
`Ŝ^+_tot · |σ_⊤⟩ = 0`. -/
theorem totalSpinSOpPlus_mulVec_allAlignedStateS_zero :
    (totalSpinSOpPlus V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) = 0 := by
  unfold totalSpinSOpPlus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  exact onSiteS_spinSOpPlus_mulVec_allAlignedStateS_zero x

/-! ## Lowest-weight annihilation by `Ŝ^-_tot` -/

/-- For any site `x : V`, the on-site `Ŝ^-` matrix element with the
all-down configuration vanishes. Direct corollary of
`spinSOpMinus_apply_last_col`. -/
theorem onSiteS_spinSOpMinus_apply_allAlignedConfigS_last
    (x : V) (σ' : V → Fin (N + 1)) :
    (onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) σ'
        (allAlignedConfigS V N (Fin.last N)) = 0 := by
  by_cases h : ∀ k, k ≠ x → σ' k = (allAlignedConfigS V N (Fin.last N)) k
  · rw [onSiteS_apply_of_off_site_agree _ _ h]
    show spinSOpMinus N (σ' x)
        ((allAlignedConfigS V N (Fin.last N)) x) = 0
    unfold allAlignedConfigS
    exact spinSOpMinus_apply_last_col (σ' x)
  · exact onSiteS_apply_eq_zero_of_off_site_diff _ _ h

/-- **The on-site lowering operator annihilates the all-down state**:
`(onSiteS x Ŝ^-).mulVec |σ_⊥⟩ = 0` for every site `x`. -/
theorem onSiteS_spinSOpMinus_mulVec_allAlignedStateS_last
    (x : V) :
    (onSiteS x (spinSOpMinus N) : ManyBodyOpS V N).mulVec
      (allAlignedStateS V N (Fin.last N)) = 0 := by
  funext τ
  unfold allAlignedStateS
  rw [onSiteS_mulVec_basisVecS_apply]
  rw [onSiteS_spinSOpMinus_apply_allAlignedConfigS_last]
  rfl

/-- **`Ŝ^-_tot` annihilates the all-down state** (lowest-weight property):
`Ŝ^-_tot · |σ_⊥⟩ = 0`. -/
theorem totalSpinSOpMinus_mulVec_allAlignedStateS_last :
    (totalSpinSOpMinus V N).mulVec
      (allAlignedStateS V N (Fin.last N)) = 0 := by
  unfold totalSpinSOpMinus
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  exact onSiteS_spinSOpMinus_mulVec_allAlignedStateS_last x

/-! ## `(Ŝ_tot)²` eigenvector on the all-aligned state -/

/-- **The all-up state is a `(Ŝ_tot)²`-eigenvector**. The Casimir
`(Ŝ_tot)²` is the Heisenberg Hamiltonian with constant unit coupling
(`totalSpinSSquared_eq_heisenbergHamiltonianS_unit`), and the all-up
state is a Heisenberg eigenvector for any coupling
(`heisenbergHamiltonianS_mulVec_allAlignedStateS_zero`). The
eigenvalue is `(Ŝ_tot)²_{σ_⊤,σ_⊤}`. -/
theorem totalSpinSSquared_mulVec_allAlignedStateS_zero :
    (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((totalSpinSSquared V N : ManyBodyOpS V N)
        (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  rw [totalSpinSSquared_eq_heisenbergHamiltonianS_unit,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_zero (fun _ _ => (1 : ℂ)),
    ← totalSpinSSquared_eq_heisenbergHamiltonianS_unit]

/-- The diagonal `(Ŝ_tot)²_{σ_⊤,σ_⊤}` value on the all-up
configuration: `|V|·N(N+2)/4 + (|V|²-|V|)·N²/4`. -/
theorem totalSpinSSquared_apply_diag_allAlignedConfigS_zero [Nonempty V] :
    ((totalSpinSSquared V N : ManyBodyOpS V N)
      (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) =
    (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4) +
      ((Fintype.card V : ℂ) * (Fintype.card V : ℂ) -
        (Fintype.card V : ℂ)) * ((N : ℂ) / 2 * ((N : ℂ) / 2)) := by
  rw [totalSpinSSquared_eq_heisenbergHamiltonianS_unit,
    heisenbergHamiltonianS_apply_diag]
  -- ∑ x ∑ y, 1 · (if x=y then N(N+2)/4 else (N/2 - 0)(N/2 - 0))
  --   = |V|·N(N+2)/4 + (|V|²-|V|)·N²/4.
  -- Use Finset sum manipulation.
  have h_inner : ∀ x : V, (∑ y : V,
        (1 : ℂ) * (if x = y then (N : ℂ) * (N + 2) / 4
                    else ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) x).val) *
                      ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) y).val))) =
      (N : ℂ) * (N + 2) / 4 +
        ((Fintype.card V : ℂ) - 1) * ((N : ℂ) / 2 * ((N : ℂ) / 2)) := by
    intro x
    rw [show (∑ y : V,
          (1 : ℂ) * (if x = y then (N : ℂ) * (N + 2) / 4
                      else ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) x).val) *
                        ((N : ℂ) / 2 - ((allAlignedConfigS V N 0) y).val))) =
        ∑ y : V, (if x = y then (N : ℂ) * (N + 2) / 4
                    else ((N : ℂ) / 2 - 0) * ((N : ℂ) / 2 - 0)) from by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [one_mul]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos hxy]
      · rw [if_neg hxy, if_neg hxy]
        unfold allAlignedConfigS
        simp]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), if_pos rfl]
    rw [show (∑ y ∈ Finset.univ.erase x,
          if x = y then (N : ℂ) * (N + 2) / 4
          else ((N : ℂ) / 2 - 0) * ((N : ℂ) / 2 - 0)) =
        ∑ _ ∈ Finset.univ.erase x, ((N : ℂ) / 2) * ((N : ℂ) / 2) from by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [if_neg (fun heq => (Finset.mem_erase.mp hy).1 heq.symm)]
      ring]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, nsmul_eq_mul]
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hsub : ((Fintype.card V - 1 : ℕ) : ℂ) =
        (Fintype.card V : ℂ) - 1 := by
      rw [Nat.cast_sub hpos]
      simp
    rw [hsub]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h_inner x)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **Casimir eigenvalue formula on the all-up state**: the all-up
state is a `(Ŝ_tot)²`-eigenvector with eigenvalue
`(|V|·N/2) · (|V|·N/2 + 1)` — the highest-weight Casimir value of the
`J_tot = |V|·S = |V|·N/2` irreducible SU(2) representation. -/
theorem totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue [Nonempty V] :
    (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        allAlignedStateS V N (0 : Fin (N + 1)) := by
  rw [totalSpinSSquared_mulVec_allAlignedStateS_zero,
    totalSpinSSquared_apply_diag_allAlignedConfigS_zero]
  congr 1
  ring

/-! ## `(Ŝ_tot)²` eigenvector on the all-down state (lowest weight) -/

/-- **The all-down state is a `(Ŝ_tot)²`-eigenvector**. Same proof as
the all-up case via `totalSpinSSquared_eq_heisenbergHamiltonianS_unit`
and `heisenbergHamiltonianS_mulVec_allAlignedStateS_last` (PR #876). -/
theorem totalSpinSSquared_mulVec_allAlignedStateS_last :
    (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (Fin.last N)) =
      ((totalSpinSSquared V N : ManyBodyOpS V N)
        (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N))) •
        allAlignedStateS V N (Fin.last N) := by
  rw [totalSpinSSquared_eq_heisenbergHamiltonianS_unit,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_last (fun _ _ => (1 : ℂ)),
    ← totalSpinSSquared_eq_heisenbergHamiltonianS_unit]

/-- The diagonal `(Ŝ_tot)²_{σ_⊥,σ_⊥}` value on the all-down
configuration: same value as the all-up case since
`(N/2 - N)² = (-N/2)² = (N/2)²`. -/
theorem totalSpinSSquared_apply_diag_allAlignedConfigS_last [Nonempty V] :
    ((totalSpinSSquared V N : ManyBodyOpS V N)
      (allAlignedConfigS V N (Fin.last N))
      (allAlignedConfigS V N (Fin.last N))) =
    (Fintype.card V : ℂ) * ((N : ℂ) * (N + 2) / 4) +
      ((Fintype.card V : ℂ) * (Fintype.card V : ℂ) -
        (Fintype.card V : ℂ)) * ((N : ℂ) / 2 * ((N : ℂ) / 2)) := by
  rw [totalSpinSSquared_eq_heisenbergHamiltonianS_unit,
    heisenbergHamiltonianS_apply_diag]
  -- ∑ x ∑ y, 1 · (if x=y then N(N+2)/4 else (N/2 - N)(N/2 - N))
  --   = |V|·N(N+2)/4 + (|V|²-|V|)·N²/4 (since (N/2 - N)² = (N/2)²).
  have h_inner : ∀ x : V, (∑ y : V,
        (1 : ℂ) * (if x = y then (N : ℂ) * (N + 2) / 4
                    else ((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) x).val) *
                      ((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) y).val))) =
      (N : ℂ) * (N + 2) / 4 +
        ((Fintype.card V : ℂ) - 1) * ((N : ℂ) / 2 * ((N : ℂ) / 2)) := by
    intro x
    rw [show (∑ y : V,
          (1 : ℂ) * (if x = y then (N : ℂ) * (N + 2) / 4
                      else ((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) x).val) *
                        ((N : ℂ) / 2 - ((allAlignedConfigS V N (Fin.last N)) y).val))) =
        ∑ y : V, (if x = y then (N : ℂ) * (N + 2) / 4
                    else ((N : ℂ) / 2 - (N : ℂ)) * ((N : ℂ) / 2 - (N : ℂ))) from by
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [one_mul]
      by_cases hxy : x = y
      · rw [if_pos hxy, if_pos hxy]
      · rw [if_neg hxy, if_neg hxy]
        unfold allAlignedConfigS
        have hN : ((Fin.last N).val : ℂ) = N := by simp [Fin.last]
        rw [hN]]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x), if_pos rfl]
    rw [show (∑ y ∈ Finset.univ.erase x,
          if x = y then (N : ℂ) * (N + 2) / 4
          else ((N : ℂ) / 2 - (N : ℂ)) * ((N : ℂ) / 2 - (N : ℂ))) =
        ∑ _ ∈ Finset.univ.erase x, ((N : ℂ) / 2) * ((N : ℂ) / 2) from by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [if_neg (fun heq => (Finset.mem_erase.mp hy).1 heq.symm)]
      ring]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ x),
      Finset.card_univ, nsmul_eq_mul]
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hsub : ((Fintype.card V - 1 : ℕ) : ℂ) =
        (Fintype.card V : ℂ) - 1 := by
      rw [Nat.cast_sub hpos]
      simp
    rw [hsub]
    ring
  rw [Finset.sum_congr rfl (fun x _ => h_inner x)]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- **Casimir eigenvalue formula on the all-down state**: same value
as the all-up case — `(|V|·N/2)·(|V|·N/2 + 1)`, the `J_tot = |V|·S`
irreducible representation Casimir value. -/
theorem totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue [Nonempty V] :
    (totalSpinSSquared V N).mulVec
      (allAlignedStateS V N (Fin.last N)) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        allAlignedStateS V N (Fin.last N) := by
  rw [totalSpinSSquared_mulVec_allAlignedStateS_last,
    totalSpinSSquared_apply_diag_allAlignedConfigS_last]
  congr 1
  ring

/-! ## Heisenberg-eigenvalue preservation along the lowering ladder

The Heisenberg Hamiltonian commutes with each total-spin axis
operator `Ŝ^{(α)}_tot` (Tasaki §2.4 (2.4.7) operator-level), hence
also with the raising/lowering operators `Ŝ^±_tot`. Iterated
applications of `Ŝ^-_tot` to the highest-weight all-up state therefore
produce eigenvectors of the Heisenberg Hamiltonian at the SAME
eigenvalue, generating the full $J_{\rm tot} = |V|\cdot S$
irreducible representation as Heisenberg eigenstates. Symmetrically,
iterated `Ŝ^+_tot` applied to the all-down state.
-/

/-- The Heisenberg Hamiltonian commutes with `Ŝ^{(1)}_tot`. Restated
from `heisenbergHamiltonianS_commutator_totalSpinSOp1`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOp1
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOp1 V N) := by
  unfold Commute SemiconjBy
  have h := heisenbergHamiltonianS_commutator_totalSpinSOp1 (Λ := V) J N
  exact sub_eq_zero.mp h

/-- The Heisenberg Hamiltonian commutes with `Ŝ^{(2)}_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOp2
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOp2 V N) := by
  unfold Commute SemiconjBy
  have h := heisenbergHamiltonianS_commutator_totalSpinSOp2 (Λ := V) J N
  exact sub_eq_zero.mp h

/-- The Heisenberg Hamiltonian commutes with `Ŝ^+_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpPlus
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOpPlus V N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (heisenbergHamiltonianS_commute_totalSpinSOp1 J).add_right
    ((heisenbergHamiltonianS_commute_totalSpinSOp2 J).smul_right Complex.I)

/-- The Heisenberg Hamiltonian commutes with `Ŝ^-_tot`. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpMinus
    (J : V → V → ℂ) :
    Commute (heisenbergHamiltonianS J N) (totalSpinSOpMinus V N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (heisenbergHamiltonianS_commute_totalSpinSOp1 J).sub_right
    ((heisenbergHamiltonianS_commute_totalSpinSOp2 J).smul_right Complex.I)

/-- The Heisenberg Hamiltonian commutes with `(Ŝ^-_tot)^k` for any
`k : ℕ`, by induction. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpMinus_pow
    (J : V → V → ℂ) (k : ℕ) :
    Commute (heisenbergHamiltonianS J N)
      ((totalSpinSOpMinus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right (heisenbergHamiltonianS_commute_totalSpinSOpMinus J)

/-- **Heisenberg eigenvalue preservation along the lowering ladder
from all-up**: for any `k : ℕ`, the iterated lowering
`(Ŝ^-_tot)^k · |σ_⊤⟩` is a Heisenberg eigenvector with the SAME
eigenvalue as `|σ_⊤⟩` itself.

Proof: `[H, Ŝ^-_tot] = 0` ⟹ `H · (Ŝ^-_tot)^k = (Ŝ^-_tot)^k · H`,
combined with `H · |σ_⊤⟩ = E · |σ_⊤⟩`. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    (J : V → V → ℂ) (k : ℕ) :
    (heisenbergHamiltonianS J N).mulVec
      (((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  -- H · ((Ŝ^-)^k · |⊤⟩) = ((Ŝ^-)^k · H) · |⊤⟩  by commutation
  --                   = (Ŝ^-)^k · (E • |⊤⟩)   by H eigenvector
  --                   = E • ((Ŝ^-)^k · |⊤⟩).
  have hcomm : heisenbergHamiltonianS J N * ((totalSpinSOpMinus V N) ^ k) =
      ((totalSpinSOpMinus V N) ^ k) * heisenbergHamiltonianS J N :=
    (heisenbergHamiltonianS_commute_totalSpinSOpMinus_pow J k)
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_zero,
    Matrix.mulVec_smul]

/-- The Heisenberg Hamiltonian commutes with `(Ŝ^+_tot)^k` for any
`k : ℕ`, by induction. -/
theorem heisenbergHamiltonianS_commute_totalSpinSOpPlus_pow
    (J : V → V → ℂ) (k : ℕ) :
    Commute (heisenbergHamiltonianS J N)
      ((totalSpinSOpPlus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right (heisenbergHamiltonianS_commute_totalSpinSOpPlus J)

/-- **Heisenberg eigenvalue preservation along the raising ladder
from all-down**: for any `k : ℕ`, `(Ŝ^+_tot)^k · |σ_⊥⟩` is a Heisenberg
eigenvector with the same eigenvalue as `|σ_⊥⟩`. -/
theorem heisenbergHamiltonianS_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    (J : V → V → ℂ) (k : ℕ) :
    (heisenbergHamiltonianS J N).mulVec
      (((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ((heisenbergHamiltonianS J N)
        (allAlignedConfigS V N (Fin.last N))
        (allAlignedConfigS V N (Fin.last N))) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  have hcomm : heisenbergHamiltonianS J N * ((totalSpinSOpPlus V N) ^ k) =
      ((totalSpinSOpPlus V N) ^ k) * heisenbergHamiltonianS J N :=
    (heisenbergHamiltonianS_commute_totalSpinSOpPlus_pow J k)
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    heisenbergHamiltonianS_mulVec_allAlignedStateS_last,
    Matrix.mulVec_smul]

/-! ## Casimir-eigenvalue preservation along the iterated ladder

The Casimir `(Ŝ_tot)²` commutes with each `Ŝ^{(α)}_tot` (and hence
with `Ŝ^±_tot`), so iterated `(Ŝ^-_tot)^k` applied to the highest-
weight all-up state preserves the Casimir eigenvalue
`(|V|·N/2)·(|V|·N/2 + 1)`. Symmetric for `(Ŝ^+_tot)^k` on all-down.
-/

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^{(1)}_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOp1 :
    Commute (totalSpinSSquared V N) (totalSpinSOp1 V N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (totalSpinSSquared_commutator_totalSpinSOp1 V N)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^{(2)}_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOp2 :
    Commute (totalSpinSSquared V N) (totalSpinSOp2 V N) := by
  unfold Commute SemiconjBy
  exact sub_eq_zero.mp (totalSpinSSquared_commutator_totalSpinSOp2 V N)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^+_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOpPlus :
    Commute (totalSpinSSquared V N) (totalSpinSOpPlus V N) := by
  rw [totalSpinSOpPlus_eq_add]
  exact (totalSpinSSquared_commute_totalSpinSOp1).add_right
    ((totalSpinSSquared_commute_totalSpinSOp2).smul_right Complex.I)

/-- The total Casimir `(Ŝ_tot)²` commutes with `Ŝ^-_tot`. -/
theorem totalSpinSSquared_commute_totalSpinSOpMinus :
    Commute (totalSpinSSquared V N) (totalSpinSOpMinus V N) := by
  rw [totalSpinSOpMinus_eq_sub]
  exact (totalSpinSSquared_commute_totalSpinSOp1).sub_right
    ((totalSpinSSquared_commute_totalSpinSOp2).smul_right Complex.I)

/-- The total Casimir commutes with `(Ŝ^-_tot)^k` for any `k : ℕ`. -/
theorem totalSpinSSquared_commute_totalSpinSOpMinus_pow (k : ℕ) :
    Commute (totalSpinSSquared V N) ((totalSpinSOpMinus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right totalSpinSSquared_commute_totalSpinSOpMinus

/-- The total Casimir commutes with `(Ŝ^+_tot)^k` for any `k : ℕ`. -/
theorem totalSpinSSquared_commute_totalSpinSOpPlus_pow (k : ℕ) :
    Commute (totalSpinSSquared V N) ((totalSpinSOpPlus V N) ^ k) := by
  induction k with
  | zero => simp [Commute, SemiconjBy]
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul_right totalSpinSSquared_commute_totalSpinSOpPlus

/-- **Casimir eigenvalue preservation along the lowering ladder**
from the all-up state: for any `k : ℕ`, the iterated lowering
`(Ŝ^-_tot)^k · |σ_⊤⟩` is a `(Ŝ_tot)²`-eigenvector with the same
eigenvalue `(|V|·N/2)·(|V|·N/2 + 1)`. -/
theorem totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    [Nonempty V] (k : ℕ) :
    (totalSpinSSquared V N).mulVec
      (((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        ((totalSpinSOpMinus V N) ^ k).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  have hcomm : totalSpinSSquared V N * ((totalSpinSOpMinus V N) ^ k) =
      ((totalSpinSOpMinus V N) ^ k) * totalSpinSSquared V N :=
    totalSpinSSquared_commute_totalSpinSOpMinus_pow k
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    totalSpinSSquared_mulVec_allAlignedStateS_zero_eigenvalue,
    Matrix.mulVec_smul]

/-- **Casimir eigenvalue preservation along the raising ladder**
from the all-down state. -/
theorem totalSpinSSquared_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
    [Nonempty V] (k : ℕ) :
    (totalSpinSSquared V N).mulVec
      (((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 *
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)) •
        ((totalSpinSOpPlus V N) ^ k).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  have hcomm : totalSpinSSquared V N * ((totalSpinSOpPlus V N) ^ k) =
      ((totalSpinSOpPlus V N) ^ k) * totalSpinSSquared V N :=
    totalSpinSSquared_commute_totalSpinSOpPlus_pow k
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec,
    totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue,
    Matrix.mulVec_smul]

/-! ## Multi-site Cartan relations `[Ŝ^z_{tot}, Ŝ^±_{tot}] = ±Ŝ^±_{tot}`

These are the multi-site lift of the single-site Cartan relations
`[Ŝ^z, Ŝ^±] = ±Ŝ^±` (`spinSOp3_commutator_spinSOp{Plus,Minus}` in
`SpinS/Algebra.lean`). They are the operator-level statement that
`Ŝ^+_{tot}` (resp. `Ŝ^-_{tot}`) shifts the magnetic quantum number
by `+1` (resp. `−1`).

These relations are the operator-algebraic input to the
magnetic-quantum-number labelling along the iterated ladder
`(Ŝ^±_{tot})^k`, which identifies the iterated states with the
`m_z`-basis of the `J_{tot} = |V|·S` irreducible SU(2)
representation.
-/

/-- Multi-site Cartan relation:
`[Ŝ^z_{tot}, Ŝ^-_{tot}] = -Ŝ^-_{tot}`.

Proof: lift the single-site Cartan
`[Ŝ^z, Ŝ^-] = -Ŝ^-` (spinSOp3_commutator_spinSOpMinus) to multi-site
via `onSiteS_commutator_totalOnSiteS` (off-site terms vanish, on-site
terms collapse to single-site commutators) summed over `x : V`. -/
theorem totalSpinSOp3_commutator_totalSpinSOpMinus :
    (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N -
      totalSpinSOpMinus V N * totalSpinSOp3 V N =
      -totalSpinSOpMinus V N := by
  unfold totalSpinSOp3 totalSpinSOpMinus
  -- LHS = (Σ_x onSiteS x Ŝ^z) * (Σ_y onSiteS y Ŝ^-) -
  --       (Σ_y onSiteS y Ŝ^-) * (Σ_x onSiteS x Ŝ^z)
  -- Distribute outer sums; for each fixed x:
  --   onSiteS x Ŝ^z * (Σ_y onSiteS y Ŝ^-) - (Σ_y onSiteS y Ŝ^-) * onSiteS x Ŝ^z
  --   = onSiteS x [Ŝ^z, Ŝ^-]   (by onSiteS_commutator_totalOnSiteS)
  --   = onSiteS x (-Ŝ^-)
  --   = -onSiteS x Ŝ^-.
  -- Summing over x gives -Σ_x onSiteS x Ŝ^- = -Ŝ^-_{tot}.
  rw [Finset.sum_mul]
  rw [show ((∑ x : V, onSiteS x (spinSOp3 N) * (∑ y : V, onSiteS y (spinSOpMinus N)) :
            ManyBodyOpS V N) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            (∑ x : V, onSiteS x (spinSOp3 N))) =
        ∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOp3 N)) from by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]]
  rw [show (∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpMinus N)) -
          (∑ y : V, onSiteS y (spinSOpMinus N)) *
            onSiteS x (spinSOp3 N))) =
        ∑ x : V, (onSiteS x (-spinSOpMinus N) : ManyBodyOpS V N) from by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [onSiteS_commutator_totalOnSiteS x (spinSOp3 N) (spinSOpMinus N),
      spinSOp3_commutator_spinSOpMinus]]
  rw [show (∑ x : V, (onSiteS x (-spinSOpMinus N) : ManyBodyOpS V N)) =
        -∑ x : V, (onSiteS x (spinSOpMinus N) : ManyBodyOpS V N) from by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [show (-spinSOpMinus N : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-1 : ℂ) • spinSOpMinus N from by rw [neg_one_smul]]
    rw [onSiteS_smul, neg_one_smul]]

/-- Multi-site Cartan relation:
`[Ŝ^z_{tot}, Ŝ^+_{tot}] = +Ŝ^+_{tot}`. Symmetric proof via
`spinSOp3_commutator_spinSOpPlus`. -/
theorem totalSpinSOp3_commutator_totalSpinSOpPlus :
    (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N -
      totalSpinSOpPlus V N * totalSpinSOp3 V N =
      totalSpinSOpPlus V N := by
  unfold totalSpinSOp3 totalSpinSOpPlus
  rw [Finset.sum_mul]
  rw [show ((∑ x : V, onSiteS x (spinSOp3 N) * (∑ y : V, onSiteS y (spinSOpPlus N)) :
            ManyBodyOpS V N) -
          (∑ y : V, onSiteS y (spinSOpPlus N)) *
            (∑ x : V, onSiteS x (spinSOp3 N))) =
        ∑ x : V, ((onSiteS x (spinSOp3 N) : ManyBodyOpS V N) *
            (∑ y : V, onSiteS y (spinSOpPlus N)) -
          (∑ y : V, onSiteS y (spinSOpPlus N)) *
            onSiteS x (spinSOp3 N)) from by
    rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [onSiteS_commutator_totalOnSiteS x (spinSOp3 N) (spinSOpPlus N),
    spinSOp3_commutator_spinSOpPlus]

/-! ## Single-step magnetic-quantum-number shifts on the all-aligned state

The Cartan relations `[Ŝ^z_{tot}, Ŝ^±_{tot}] = ±Ŝ^±_{tot}` immediately
give the single-step magnetic-quantum-number shifts:

  `Ŝ^z_{tot} · Ŝ^-_{tot} · |σ_⊤⟩ = (|V|·N/2 − 1) · Ŝ^-_{tot} · |σ_⊤⟩`
  `Ŝ^z_{tot} · Ŝ^+_{tot} · |σ_⊥⟩ = (−|V|·N/2 + 1) · Ŝ^+_{tot} · |σ_⊥⟩`

These are the operator-level form of "the single application of
`Ŝ^-_{tot}` (resp. `Ŝ^+_{tot}`) shifts the magnetic quantum number
by `−1` (resp. `+1`)" — the building block for the iterated-ladder
labelling along the full `J_{tot} = |V|·S` irreducible SU(2)
representation (deferred to a follow-up textbook unit using
inductive Cartan).
-/

/-- **Single-step magnetic-quantum-number shift** along the lowering
ladder from the all-up state:

  `Ŝ^z_{tot} · Ŝ^-_{tot} · |σ_⊤⟩ = (|V|·N/2 − 1) · Ŝ^-_{tot} · |σ_⊤⟩`.

Direct corollary of `totalSpinSOp3_commutator_totalSpinSOpMinus`
(Cartan relation, PR #883) and `totalSpinSOp3_mulVec_allAlignedStateS`
(`Ŝ^z` eigenvalue of all-up). -/
theorem totalSpinSOp3_mulVec_totalSpinSOpMinus_mulVec_allAlignedStateS_zero :
    (totalSpinSOp3 V N).mulVec
      ((totalSpinSOpMinus V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1)))) =
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - 1) •
        (totalSpinSOpMinus V N).mulVec
          (allAlignedStateS V N (0 : Fin (N + 1))) := by
  -- Cartan: Ŝ^z · Ŝ^- = Ŝ^- · Ŝ^z - Ŝ^- (rearranged form of #883).
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
      totalSpinSOpMinus V N * totalSpinSOp3 V N -
        totalSpinSOpMinus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpMinus (V := V) (N := N)
    -- h : Ŝ^z · Ŝ^- − Ŝ^- · Ŝ^z = −Ŝ^-.
    have h' : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpMinus V N =
        -totalSpinSOpMinus V N + totalSpinSOpMinus V N * totalSpinSOp3 V N :=
      sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS, Matrix.mulVec_smul]
  rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp,
    mul_zero, sub_zero]
  -- Goal: m_max • (Ŝ^- · |⊤⟩) - (Ŝ^- · |⊤⟩) = (m_max - 1) • (Ŝ^- · |⊤⟩).
  rw [sub_smul, one_smul]

/-- **Single-step magnetic-quantum-number shift** along the raising
ladder from the all-down state:

  `Ŝ^z_{tot} · Ŝ^+_{tot} · |σ_⊥⟩ = (−|V|·N/2 + 1) · Ŝ^+_{tot} · |σ_⊥⟩`. -/
theorem totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_allAlignedStateS_last :
    (totalSpinSOp3 V N).mulVec
      ((totalSpinSOpPlus V N).mulVec
        (allAlignedStateS V N (Fin.last N))) =
      (-((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1) •
        (totalSpinSOpPlus V N).mulVec
          (allAlignedStateS V N (Fin.last N)) := by
  -- Cartan: Ŝ^z · Ŝ^+ = Ŝ^+ · Ŝ^z + Ŝ^+ (rearranged form of #883).
  have hcart : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
      totalSpinSOpPlus V N * totalSpinSOp3 V N + totalSpinSOpPlus V N := by
    have h := totalSpinSOp3_commutator_totalSpinSOpPlus (V := V) (N := N)
    -- h : Ŝ^z · Ŝ^+ − Ŝ^+ · Ŝ^z = Ŝ^+.
    have h' : (totalSpinSOp3 V N : ManyBodyOpS V N) * totalSpinSOpPlus V N =
        totalSpinSOpPlus V N + totalSpinSOpPlus V N * totalSpinSOp3 V N :=
      sub_eq_iff_eq_add.mp h
    rw [h']; abel
  rw [Matrix.mulVec_mulVec, hcart, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, totalSpinSOp3_mulVec_allAlignedStateS,
    magEigenvalueS_allAlignedConfigS, Matrix.mulVec_smul]
  rw [show ((Fin.last N).val : ℂ) = N from by simp [Fin.last]]
  rw [show ((Fintype.card V : ℂ) * (N : ℂ) / 2 -
        (Fintype.card V : ℂ) * (N : ℂ)) =
      -((Fintype.card V : ℂ) * (N : ℂ) / 2) from by ring]
  -- Goal: -(m_max) • (Ŝ^+ · |⊥⟩) + (Ŝ^+ · |⊥⟩) = (-m_max + 1) • (Ŝ^+ · |⊥⟩).
  rw [add_smul, one_smul]

end LatticeSystem.Quantum
