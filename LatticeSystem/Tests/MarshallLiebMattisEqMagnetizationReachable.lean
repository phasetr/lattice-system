import LatticeSystem.Quantum.MarshallLiebMattis.EqMagnetizationReachable

/-!
# Test coverage for equal-magnetisation reachability
(Tasaki §2.5 p. 42 Proposition)
-/

namespace LatticeSystem.Tests.MarshallLiebMattisEqMagnetizationReachable

open LatticeSystem.Quantum

/-- Configuration distance is zero iff configurations are equal. -/
example (σ σ' : Fin 2 → Fin 2) :
    configDist σ σ' = 0 ↔ σ = σ' :=
  configDist_eq_zero_iff σ σ'

/-- For σ ≠ σ' with equal magnetisation, there exist swap pair sites. -/
example (σ σ' : Fin 2 → Fin 2) (hne : σ ≠ σ')
    (hmag : magnetization (Fin 2) σ = magnetization (Fin 2) σ') :
    ∃ x y : Fin 2, σ x = 0 ∧ σ' x = 1 ∧ σ y = 1 ∧ σ' y = 0 :=
  exists_swap_pair_of_eq_magnetization hne hmag

/-- Swap at the canonical pair reduces configuration distance. -/
example {σ σ' : Fin 2 → Fin 2} {x y : Fin 2}
    (hx0 : σ x = 0) (hx1 : σ' x = 1) (hy1 : σ y = 1) (hy0 : σ' y = 0) :
    configDist (basisSwap σ x y) σ' < configDist σ σ' :=
  configDist_basisSwap_lt hx0 hx1 hy1 hy0

/-- Tasaki §2.5 p. 42 Proposition: equal-magnetisation reachability. -/
example (G : SimpleGraph (Fin 2)) (hG : G.Preconnected)
    (σ σ' : Fin 2 → Fin 2)
    (hmag : magnetization (Fin 2) σ = magnetization (Fin 2) σ') :
    SwapReachable G σ σ' :=
  swapReachable_of_eq_magnetization hG σ σ' hmag

end LatticeSystem.Tests.MarshallLiebMattisEqMagnetizationReachable
