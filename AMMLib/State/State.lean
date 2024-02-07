import AMMLib.State.Tokens
import AMMLib.State.AMMs
import AMMLib.State.AtomicWallSet
import AMMLib.State.MintedWallSet

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to
-- State to implement price updates.
abbrev O := T → ℝ>0

-- State
structure Γ where
  atoms: S₀
  mints: S₁
  amms: AMMs

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
