import LatticeSystem.Quantum.SpinS.ConfigPermMatrixS
import LatticeSystem.Quantum.SpinS.ManyBodyReversalS

/-!
# §8.3.2 item (3) — generic configuration-permutation-matrix layer

Signature and regression tests for the generic layer `configPermMatrixS`
(`LatticeSystem.Quantum.SpinS.ConfigPermMatrixS`), which factors out the shared "permutation
matrix of an involutive configuration map" pattern behind `manyBodyReversalS`
(`ManyBodyReversalS.lean`) and the bond-inversion unitary `bondInversionUnitaryS`
(`VBSInversionParity.lean`).

No production code lives here: every `example` below only pins down the intended statement of
`ConfigPermMatrixS.lean` and the `manyBodyReversalS := configPermMatrixS revConfigS` refactor of
`ManyBodyReversalS.lean`.
-/

namespace LatticeSystem.Tests.ConfigPermMatrixS

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## 1. Signature: `configPermMatrixS` -/

/-- `configPermMatrixS f : ManyBodyOpS Λ N` for any configuration map `f`, not just an
involution — the type itself carries no involutivity hypothesis. -/
example (f : (Λ → Fin (N + 1)) → (Λ → Fin (N + 1))) :
    configPermMatrixS (Λ := Λ) (N := N) f = configPermMatrixS f := rfl

/-! ## 2. `configPermMatrixS_apply` -/

example (f : (Λ → Fin (N + 1)) → (Λ → Fin (N + 1))) (σ' σ : Λ → Fin (N + 1)) :
    configPermMatrixS f σ' σ = if σ' = f σ then (1 : ℂ) else 0 :=
  configPermMatrixS_apply f σ' σ

/-! ## 3. `configPermMatrixS_mulVec` (needs involutivity) -/

example (f : (Λ → Fin (N + 1)) → (Λ → Fin (N + 1))) (hf : Function.Involutive f)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (configPermMatrixS f).mulVec Φ = fun σ => Φ (f σ) :=
  configPermMatrixS_mulVec hf Φ

/-! ## 4. `configPermMatrixS_conj_apply` -/

example (f : (Λ → Fin (N + 1)) → (Λ → Fin (N + 1))) (hf : Function.Involutive f)
    (M : ManyBodyOpS Λ N) (σ' σ : Λ → Fin (N + 1)) :
    (configPermMatrixS f * M * configPermMatrixS f) σ' σ = M (f σ') (f σ) :=
  configPermMatrixS_conj_apply hf M σ' σ

/-! ## 5. `configPermMatrixS_mul_self` -/

example (f : (Λ → Fin (N + 1)) → (Λ → Fin (N + 1))) (hf : Function.Involutive f) :
    configPermMatrixS f * configPermMatrixS f = (1 : ManyBodyOpS Λ N) :=
  configPermMatrixS_mul_self hf

/-! ## 6. Regression: `manyBodyReversalS` is the `revConfigS` specialization -/

/-- After the refactor, `manyBodyReversalS` must be *definitionally* the generic layer applied to
`revConfigS` — this is the load-bearing regression (no duplicated proof pattern; downstream
consumers `Theorem24FinrankLeTwoContradiction.lean` and `AndersonTowerTanakaMoments.lean` must
keep working through the existing lemma names). -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ) :
    manyBodyReversalS Λ N = configPermMatrixS (revConfigS (Λ := Λ) (N := N)) := rfl

end LatticeSystem.Tests.ConfigPermMatrixS
