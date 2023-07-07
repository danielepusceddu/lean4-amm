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
