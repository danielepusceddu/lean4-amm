import AMMLib.Wallets.MintedWall
import AMMLib.Wallets.AtomicWall
import AMMLib.State

/-
mintsupply that returns PReal:
Finsupp.add_sum_erase

in a reachable state
if s.amms.init t0 t1, then there must exist an 𝔸 in s.mints such that s.mints t0 t1 ≠ 0
choose that, destruct the supply and we'll get: 
s.mints t0 t1 + ((s.mints.drain a t0 t1).supply t0 t1)
which must be positive

this will turn Γ.𝕋₁Price into a PReal
however, 𝕎₀.worth and 𝕎₁.worth will remain NNReals 
so is it worth it?
-/

noncomputable def Γ.𝕋₁Price
(s: Γ) (o: 𝕋₀ → PReal)
(t0 t1: 𝕋₀): NNReal :=
  if h:s.amms.init t0 t1 then 
  ((s.amms.r0 t0 t1 h)*(o t0) + (s.amms.r1 t0 t1 h)*(o t1)) / (s.mints.supply t0 t1)
  else 0

noncomputable def Γ.networth
(s: Γ) (a: 𝔸) (o: 𝕋₀ → PReal): NNReal
:=
(𝕎₀.worth (s.atoms.get a) o)
+
(𝕎₁.worth (s.mints.get a) (s.𝕋₁Price o))

noncomputable def 𝔸.gain
(a: 𝔸) (o: 𝕋₀ → PReal) (s s': Γ)
: ℝ
:= ((s'.networth a o): ℝ) - ((s.networth a o): ℝ)
