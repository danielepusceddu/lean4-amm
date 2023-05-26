import AMMLib.Tokens
import AMMLib.AMMSet

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to 
-- State to implement price updates.
structure Config where
  sx: PReal → (PReal × PReal) → PReal
  o: AtomicTok → PReal

structure State where
  atoms: AtomicWalls
  mints: MintedWalls
  amms: AMMSet
