import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.Wallets.AtomicWallSet
import AMMLib.Wallets.MintedWallSet
import AMMLib.Swap.Rate

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to 
-- State to implement price updates.
abbrev 𝕆 := 𝕋 → PReal

-- State
structure Γ where
  atoms: 𝕊₀
  mints: 𝕊₁
  amms: 𝕊ₐ

theorem Γ.eq_iff (s s': Γ):
  s = s' ↔ s.atoms = s'.atoms ∧ s.mints = s'.mints ∧ s.amms = s'.amms := by
  apply Iff.intro
  . intro eq; simp [eq]
  . intro bruh
    rcases bruh with ⟨a,b,c⟩
    rcases s with ⟨atoms, mints, amms⟩
    rcases s' with ⟨atoms', mints', amms'⟩
    simp at a b c
    simp [a, b, c]