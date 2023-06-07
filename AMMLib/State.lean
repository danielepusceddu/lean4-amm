import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.Wallets

-- Config does not change between states.
-- This is where I would add φ.
-- The price oracle should be moved to 
-- State to implement price updates.
abbrev SX := PReal → PReal → PReal → PReal
structure Cfg where
  sx: SX
  o: 𝕋₀ → PReal

-- State
structure Γ where
  atoms: 𝕊₀
  mints: 𝕊₁
  amms: 𝕊ₐ

def SX.outputbound (sx: SX): Prop :=
  ∀ (x r0 r1: ℝ+),
     x*(sx x r0 r1) < r1

def SX.mono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ+),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1' ≤ r1
  →
  sx x r0 r1 ≤ sx x' r0' r1'

def SX.strictmono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ+),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1' ≤ r1
  →
  if x' < x ∨ r0' < r0 ∨ r1' < r1
  then sx x r0 r1 < sx x' r0' r1'
  else sx x r0 r1 ≤ sx x' r0' r1'

def SX.additive (sx: SX): Prop :=
∀ (x y r0 r1: ℝ+),
  sx (x+y) r0 r1
  =
  (x*(sx x r0 r1) + y*(sx y r0 r1))/(x + y)

def SX.reversible 
(sx: SX) (bound: sx.outputbound): Prop :=
  ∀ (x r0 r1: ℝ+),
    1 / (sx x r0 r1) = 
    sx ((sx x r0 r1)*x)
       (r1.sub (x*(sx x r0 r1)) (bound x r0 r1))
       (r0 + x)

def SX.homogeneous (sx: SX): Prop :=
∀ (a x r0 r1: ℝ+), sx (a*x) (a*r0) (a*r1) = sx x r0 r1
