import «Tokens»
import «AMMSet»

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to 
-- State to implement price updates.
structure Config where
  sx: {a: AMM} → AtomicOf a → PReal → PReal
  o: AtomicTok → PReal

structure State where
  accs: AccountSet
  amms: AMMSet
